use std::env;
use std::fs;
use std::process;
use std::time::{Duration, Instant};

use tzap::circuit::Circuit;
use tzap::optimize::{Metrics, Observer, Report, optimize_with};

mod cli;
mod progress;

use cli::{Opts, arg_error, parse_args};
use progress::{
    box_lines, end_progress_block, finish_inline, fmt_num, print_result, start_inline,
    start_progress_block, update_chunk_progress, update_fixpoint_progress,
    update_reduction_progress,
};

/// Renders a run's progress to the terminal: the per-pass result lines, the
/// SuperOpt table-load status, and the live redrawn progress boxes. The whole
/// of the CLI's output during optimization, and the only thing standing
/// between `tzap::optimize` and a silent run.
struct Terminal;

/// Number of bar rows in a reduction progress box — the Rz row only appears
/// for circuits that have Rz gates to report on.
fn reduction_rows(baseline: Metrics) -> usize {
    if baseline.rz > 0 { 5 } else { 4 }
}

/// Number of bar rows in the parallel chunk progress box (a Chunks row on top
/// of [`reduction_rows`]).
fn chunk_rows(baseline: Metrics) -> usize {
    reduction_rows(baseline) + 1
}

impl Observer for Terminal {
    fn tracks_chunks(&self) -> bool {
        true
    }

    /// Report one pass with timing and a result line, followed by a blank
    /// separator line — this and the SuperOpt table-load message each own a
    /// trailing blank line, so a live progress box that follows never needs to
    /// print one itself. [`read_circuit`] deliberately does *not* trail with a
    /// blank: it should stay flush with whatever comes right after it, whether
    /// that's this, the table message, or a box directly.
    fn pass_done(&self, name: &str, result: &Circuit, elapsed: Duration) {
        let metrics = Metrics::of(result);
        let rz_report = (metrics.rz > 0).then(|| format!(" · {} Rz", fmt_num(metrics.rz)));
        eprintln!(
            "  {}\n\t└─ {} gates · {} 2q gates · {} T{} · {} depth · {:.3}s",
            name,
            fmt_num(metrics.gates),
            fmt_num(metrics.two_qubit),
            fmt_num(metrics.t),
            rz_report.as_deref().unwrap_or(""),
            fmt_num(metrics.depth),
            elapsed.as_secs_f64()
        );
        eprintln!();
    }

    fn table_load_start(&self, cached: bool) {
        if cached {
            // Reading a large cached table off disk can itself take a
            // moment, so say so before it starts; overwritten in place with
            // the completed message below rather than left as its own line.
            start_inline("  Loading minimal unitary representatives...");
        } else {
            eprintln!(
                "  🔧 Generating semantic lookup table (one-time — cached for future use)..."
            );
        }
    }

    fn table_load_done(&self, cached: bool, size_bytes: Option<u64>, elapsed: Duration) {
        let size = size_bytes
            .map(|bytes| format!(" ({:.1} MB)", bytes as f64 / (1024.0 * 1024.0)))
            .unwrap_or_default();
        let message = format!(
            "  Loaded minimal unitary representatives{size} in {:.3}s",
            elapsed.as_secs_f64()
        );
        if cached {
            finish_inline(&message);
        } else {
            eprintln!("{message}");
        }
        eprintln!();
    }

    fn progress_start(&self, baseline: Metrics) {
        start_progress_block(box_lines(reduction_rows(baseline)));
    }

    fn progress_update(&self, round: Option<usize>, current: &Circuit, baseline: Metrics) {
        let m = Metrics::of(current);
        match round {
            Some(round) => update_fixpoint_progress(
                round,
                m.gates,
                m.two_qubit,
                m.depth,
                m.t,
                baseline.gates,
                baseline.two_qubit,
                baseline.depth,
                baseline.t,
                m.rz,
                baseline.rz,
            ),
            None => update_reduction_progress(
                "% reduction so far",
                m.gates,
                m.two_qubit,
                m.depth,
                m.t,
                baseline.gates,
                baseline.two_qubit,
                baseline.depth,
                baseline.t,
                m.rz,
                baseline.rz,
            ),
        }
    }

    fn progress_end(&self, baseline: Metrics) {
        end_progress_block(box_lines(reduction_rows(baseline)));
    }

    fn fixpoint_done(&self, rounds: usize, reached_fixpoint: bool) {
        if reached_fixpoint {
            eprintln!("  Fixpoint reached after {rounds} iteration(s)");
            eprintln!();
        }
    }

    fn chunks_start(&self, total: usize, baseline: Metrics) {
        start_progress_block(box_lines(chunk_rows(baseline)));
        self.chunk_done(0, total, baseline, baseline);
    }

    fn chunk_done(&self, done: usize, total: usize, current: Metrics, baseline: Metrics) {
        update_chunk_progress(
            done,
            total,
            baseline.gates,
            current.gates,
            baseline.two_qubit,
            current.two_qubit,
            baseline.depth,
            current.depth,
            baseline.t,
            current.t,
            baseline.rz,
            current.rz,
        );
    }

    fn chunks_end(&self, baseline: Metrics) {
        end_progress_block(box_lines(chunk_rows(baseline)));
    }
}

/// Write a circuit to the output path (if any), exiting on error.
fn write_output(output_path: &Option<String>, circuit: &Circuit) {
    if let Some(p) = output_path {
        let output = circuit.to_qasm();
        fs::write(p, &output).unwrap_or_else(|e| {
            eprintln!("Error writing {p}: {e}");
            process::exit(1);
        });
        eprintln!("  wrote {p}");
    }
}

/// Read and parse a QASM file into a circuit, logging parse stats. Exits on
/// error. Overwrites its own "Parsing..." line with "Parsed..." in place
/// (see [`start_inline`]/[`finish_inline`]) once done.
fn read_circuit(path: &str) -> Circuit {
    let file_size = fs::metadata(path).map(|m| m.len()).unwrap_or(0);
    let size_mb = file_size as f64 / (1024.0 * 1024.0);
    let parse_start = Instant::now();
    start_inline(&format!("  Parsing {path} ({size_mb:.1} MB)"));

    let qasm = fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("\nError reading {path}: {e}");
        process::exit(1);
    });
    let circuit = Circuit::from_qasm(&qasm).unwrap_or_else(|e| {
        eprintln!("\nError parsing {path}: {e}");
        process::exit(1);
    });
    finish_inline(&format!(
        "  Parsed {path} ({size_mb:.1} MB) in {:.3}s",
        parse_start.elapsed().as_secs_f64()
    ));
    eprintln!(
        "\t└─ {} qubits · {} gates",
        fmt_num(circuit.num_qubits),
        fmt_num(circuit.gates.len()),
    );
    circuit
}

/// Print the result banner against the pipeline's baseline counts (the
/// circuit as it stood after any eager decomposition, not as parsed), and
/// write the output file (if requested).
fn finish(report: &Report, result: &Circuit, opts: &Opts, start: Instant) {
    print_result(
        report.baseline.gates,
        report.output.gates,
        report.baseline.two_qubit,
        report.output.two_qubit,
        report.baseline.depth,
        report.output.depth,
        report.baseline.t,
        report.output.t,
        report.baseline.rz,
        report.output.rz,
        start.elapsed().as_secs_f64(),
    );

    write_output(&opts.output_path, result);
}

fn main() {
    let start = Instant::now();
    let args: Vec<String> = env::args().collect();
    let opts = parse_args(&args);

    eprintln!(
        "\x1b[1m⚡\u{FE0F} tzap\x1b[0m  \x1b[2mv{}\x1b[0m",
        env!("CARGO_PKG_VERSION")
    );

    let circuit = read_circuit(&opts.input_path);
    let (result, report) =
        optimize_with(&circuit, &opts.options, &Terminal).unwrap_or_else(|e| arg_error(e));
    finish(&report, &result, &opts, start);
}

#[cfg(test)]
mod tests {
    use super::*;
    use tzap::optimize::{Level, SuperOptBounds};

    /// The Rz row appears in a progress box exactly when the circuit has Rz
    /// gates to report on — the box's height must match, or the live redraw
    /// leaves a stray line behind.
    #[test]
    fn rz_row_only_counted_when_present() {
        let with_rz = Metrics {
            rz: 3,
            ..Metrics::default()
        };
        assert_eq!(reduction_rows(Metrics::default()), 4);
        assert_eq!(reduction_rows(with_rz), 5);
        assert_eq!(chunk_rows(Metrics::default()), 5);
        assert_eq!(chunk_rows(with_rz), 6);
    }

    /// An absent `-O` flag must behave exactly like `-O3`, and the hidden
    /// `--superopt-*` flags must reach the optimizer.
    #[test]
    fn parse_args_defaults_to_o3() {
        let args = ["tzap".to_string(), "in.qasm".to_string()];
        let opts = parse_args(&args);
        assert_eq!(opts.options.level, Level::O3);
        assert!(opts.options.passes.is_none());
        assert!(!opts.options.parallel);

        let args = [
            "tzap".to_string(),
            "in.qasm".to_string(),
            "--superopt-qubits".to_string(),
            "4".to_string(),
        ];
        let opts = parse_args(&args);
        let SuperOptBounds { qubits, .. } = opts.options.superopt;
        assert_eq!(qubits, Some(4));
    }
}
