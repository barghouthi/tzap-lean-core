use std::env;
use std::fs;
use std::io::{self, Write};
use std::process;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use rayon::prelude::*;

use tzap::cancel::CancelGates;
use tzap::circuit::{Circuit, Gate};
use tzap::decompose::{DecomposeCz, DecomposeRz, DecomposeToffoli};
use tzap::pass::{Pass, count_2q, count_t, depth};
use tzap::phase_fold_global_expr::PhaseFoldGlobalExpr;
use tzap::phase_fold_rand::PhaseFoldRand;
use tzap::super_opt::{SuperOpt, SuperOptTableConfig, table_is_cached};

/// Map-reduce chunks per logical core. Deliberately more than one thread per
/// core (see [`num_threads`]): chunks cost varies (some hit more SuperOpt
/// rewrites than others), so more chunks than threads lets rayon's
/// work-stealing load-balance that unevenness across a right-sized pool.
const CHUNK_MULTIPLIER: usize = 2;

/// A pass selectable by name via `--passes`.
#[derive(Clone, Copy)]
enum PassName {
    DecomposeToffoli,
    DecomposeCz,
    DecomposeRz,
    CancelGates,
    SuperOpt,
    PhaseFoldRand,
    PhaseFoldGlobalExpr,
}

impl PassName {
    /// All passes — `(name, variant, description)` — in the order shown by `--help`.
    const ALL: [(&'static str, PassName, &'static str); 7] = [
        (
            "DecomposeToffoli",
            PassName::DecomposeToffoli,
            "Decompose ccx (Toffoli) and ccz gates into Clifford+T",
        ),
        (
            "DecomposeCz",
            PassName::DecomposeCz,
            "Decompose cz gates into H+CX+H",
        ),
        (
            "DecomposeRz",
            PassName::DecomposeRz,
            "Decompose Rz gates into Clifford+T (gridsynth; see --epsilon)",
        ),
        (
            "CancelGates",
            PassName::CancelGates,
            "Cancel adjacent self-inverse gate pairs and reduce Hadamards",
        ),
        (
            "SuperOpt",
            PassName::SuperOpt,
            "Replace small subcircuit windows using a synthesis table",
        ),
        (
            "PhaseFoldRand",
            PassName::PhaseFoldRand,
            "Merge T/Rz rotations via randomized parity tracking",
        ),
        (
            "PhaseFoldGlobalExpr",
            PassName::PhaseFoldGlobalExpr,
            "Merge T/Rz rotations via symbolic parity expressions",
        ),
    ];

    fn parse(s: &str) -> Option<PassName> {
        Self::ALL
            .iter()
            .find(|(n, _, _)| *n == s)
            .map(|(_, p, _)| *p)
    }

    /// Comma-separated list of every valid name (for help / error messages).
    fn all_names() -> String {
        Self::ALL
            .iter()
            .map(|(n, _, _)| *n)
            .collect::<Vec<_>>()
            .join(", ")
    }
}

fn parse_pass_list(list: &str) -> Vec<PassName> {
    let parsed = list
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .map(|name| {
            PassName::parse(name).unwrap_or_else(|| {
                arg_error(format!(
                    "Unknown pass '{name}'. Available passes: {}",
                    PassName::all_names()
                ))
            })
        })
        .collect::<Vec<_>>();

    if parsed.is_empty() {
        arg_error(
            "--passes requires at least one pass name \
             (e.g. --passes CancelGates,PhaseFoldRand)",
        );
    }
    parsed
}

fn looks_like_pass_list_fragment(token: &str) -> bool {
    token
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .all(|name| PassName::parse(name).is_some())
}

/// Default SuperOpt window/table bounds, overridable by the hidden
/// `--superopt-*` flags (see `parse_args`). Not exposed in `--help`: these
/// exist for experimentation, not everyday use.
///
/// The window and table share both a qubit bound (`--superopt-qubits`) and a
/// gate-count bound (`--superopt-window-gates`): the `SuperOpt` library
/// itself allows window and table bounds to differ on either axis (e.g. a
/// window wider or deeper than the table backing it, to exercise window
/// mechanics beyond what the table can synthesize replacements for — see
/// `super_opt::tests`), but the CLI has no everyday use case for that, so it
/// only exposes one knob per axis.
///
/// `window_gates=10` leaves real T-count on the table suite-wide; the T
/// floor is reached by `window_gates≈15` and gate-count keeps improving
/// slowly beyond that, so 25 is used as a deliberately more thorough
/// default. `qubits` and `table_entries` showed no benefit worth their
/// added cost at this tier and were left alone.
const DEFAULT_SUPEROPT_QUBITS: usize = 3;
const DEFAULT_SUPEROPT_WINDOW_GATES: usize = 25;
const DEFAULT_SUPEROPT_TABLE_ENTRIES: usize = 200_000;

/// SuperOpt bounds for `-Osuper`: a materially bigger window/table than the
/// default. Confirmed (by direct comparison against `DEFAULT_SUPEROPT_*`
/// across the full feynman+cobble benchmark suite) to be a real,
/// zero-regression improvement — concentrated in circuits with long
/// single-qubit runs — at the cost of a slower one-time table build (still
/// cached to disk after the first run). `window_gates` was swept 15→20→30,
/// each step a further zero-or-near-zero-regression win (feynman gains
/// saturated by 20; cobble kept improving through 30 with zero regressions).
/// Two other axes stopped helping, though: bigger qubit widths hit an
/// out-of-memory wall during table construction, and a bigger entries cap
/// starts *regressing* output (a bigger table is a strict fingerprint
/// superset, but the greedy, non-backtracking rewrite-selection rule doesn't
/// turn "more matches available" into "better output" monotonically).
/// `window_gates=40` is the best gate-count point found at this
/// qubit/entries setting; T-count is unchanged from `window_gates=30`.
const SUPER_SUPEROPT_QUBITS: usize = 5;
const SUPER_SUPEROPT_WINDOW_GATES: usize = 40;
const SUPER_SUPEROPT_TABLE_ENTRIES: usize = 5_000_000;

/// Parsed command-line options.
struct Opts {
    input_path: String,
    output_path: Option<String>,
    expr: bool,
    decompose_rz: bool,
    decompose_cz: bool,
    rz_epsilon: f64,
    parallel: bool,
    /// Explicit pass pipeline from `--passes` (overrides the default pipeline).
    passes: Option<Vec<PassName>>,
    /// Re-run the optimization pipeline until gate count stops decreasing.
    fixpoint: bool,
    /// Explicit optimization level. Absence also uses O1, but keeps custom
    /// `--passes` and `--fixpoint` available.
    optimization_level: Option<OptimizationLevel>,
    /// SuperOpt window/table bounds. Hidden (undocumented in `--help`);
    /// `None` means "use whichever preset the optimization level implies"
    /// (`DEFAULT_SUPEROPT_*`, or `SUPER_SUPEROPT_*` under `-Osuper`) — an
    /// explicit flag always overrides the preset.
    superopt_qubits: Option<usize>,
    superopt_window_gates: Option<usize>,
    superopt_table_entries: Option<usize>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum OptimizationLevel {
    O1,
    /// Adds a SuperOpt pass to O1, capped at 2 rounds rather than run to a
    /// true fixpoint — see `optimize_default`'s `max_rounds`.
    O2,
    /// Like O2, but run to a true fixpoint instead of capped at 2 rounds.
    O3,
    /// Like O3 (SuperOpt run to fixpoint), but with `SUPER_SUPEROPT_*` bounds.
    Osuper,
}

fn fmt_num<N: std::fmt::Display>(n: N) -> String {
    let s = n.to_string();
    let is_negative = s.starts_with('-');
    let num_part = if is_negative { &s[1..] } else { &s[..] };
    let mut result = String::with_capacity(s.len() + s.len() / 3);
    if is_negative {
        result.push('-');
    }

    let rem = num_part.len() % 3;
    for (i, c) in num_part.chars().enumerate() {
        if i > 0 && i % 3 == rem {
            result.push(',');
        }
        result.push(c);
    }
    result
}

/// Percentage reduction from `before` to `after` (0.0 when `before` is 0).
fn pct(before: usize, after: usize) -> f64 {
    if before > 0 {
        (before as f64 - after as f64) / before as f64 * 100.0
    } else {
        0.0
    }
}

/// Number of logical cores, for sizing the rayon thread pool. CPU-bound work
/// like ours gets no benefit from oversubscribing OS threads beyond the core
/// count — it only adds context-switch and cache-thrashing overhead.
fn num_threads() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(8)
}

/// Number of map-reduce chunks to split the circuit into. See
/// [`CHUNK_MULTIPLIER`] for why this is more than [`num_threads`].
fn num_par_chunks() -> usize {
    num_threads() * CHUNK_MULTIPLIER
}

/// Build the global rayon pool, sized to the number of logical cores. A
/// no-op if already built (it is process-global).
fn init_global_pool() {
    rayon::ThreadPoolBuilder::new()
        .num_threads(num_threads())
        .build_global()
        .ok();
}

/// Run one pass with timing and a result line, followed by a blank
/// separator line — every "info" line that can precede a live progress box
/// (this, [`read_circuit`], and the SuperOpt table-build message) owns its
/// own trailing blank line, so the box itself never needs to print one.
fn run_logged(pass: &dyn Pass, circuit: &Circuit) -> Circuit {
    let start = Instant::now();
    let c = pass.run(circuit);
    eprintln!(
        "  {}\n\t└─ {} gates · {} 2q gates · {} T · {} depth · {:.3}s",
        pass.name(),
        fmt_num(c.gates.len()),
        fmt_num(count_2q(&c)),
        fmt_num(count_t(&c)),
        fmt_num(depth(&c)),
        start.elapsed().as_secs_f64()
    );
    eprintln!();
    c
}

/// Split a circuit into `num_chunks` gate-contiguous pieces for map-reduce
/// parallelism. Each chunk is later optimized completely independently (see
/// [`run_map_reduce`]) and the results concatenated back in order by
/// [`stitch`] — chunk boundaries are fixed up front and never revisited.
/// `max(1)` guards the empty case where `slice::chunks(0)` would panic.
fn chunk_circuit(circuit: &Circuit, num_chunks: usize) -> Vec<Circuit> {
    let chunk_size = circuit.gates.len().div_ceil(num_chunks).max(1);
    circuit
        .gates
        .chunks(chunk_size)
        .map(|slice| {
            let mut c = Circuit::with_cbits(circuit.num_qubits, circuit.num_cbits);
            for g in slice {
                c.apply(g.clone());
            }
            c
        })
        .collect()
}

/// Concatenate optimized chunks back into a single circuit, in order.
fn stitch(num_qubits: usize, num_cbits: usize, chunks: &[Circuit]) -> Circuit {
    let mut out = Circuit::with_cbits(num_qubits, num_cbits);
    for c in chunks {
        for g in &c.gates {
            out.apply(g.clone());
        }
    }
    out
}

/// Print the closing result banner. Assumes whatever ran just before it
/// (a progress box's erasure, or an "info" line like "Fixpoint reached")
/// already left exactly one blank line behind — this prints no leading
/// blank of its own.
fn print_result(
    in_gates: usize,
    out_gates: usize,
    in_2q: usize,
    out_2q: usize,
    in_depth: usize,
    out_depth: usize,
    in_t: usize,
    out_t: usize,
    secs: f64,
) {
    let in_values = [
        fmt_num(in_gates),
        fmt_num(in_2q),
        fmt_num(in_t),
        fmt_num(in_depth),
    ];
    let out_values = [
        fmt_num(out_gates),
        fmt_num(out_2q),
        fmt_num(out_t),
        fmt_num(out_depth),
    ];
    let in_width = in_values.iter().map(String::len).max().unwrap_or(0);
    let out_width = out_values.iter().map(String::len).max().unwrap_or(0);

    eprintln!("\x1b[1m  Final result\x1b[0m");
    eprintln!(
        "\t├─ {label:<8} {input:>in_width$} → {output:>out_width$} (↓{reduction:.1}%)",
        label = "Gates",
        input = in_values[0],
        output = out_values[0],
        reduction = pct(in_gates, out_gates),
    );
    eprintln!(
        "\t├─ {label:<8} {input:>in_width$} → {output:>out_width$} (↓{reduction:.1}%)",
        label = "2q gates",
        input = in_values[1],
        output = out_values[1],
        reduction = pct(in_2q, out_2q),
    );
    eprintln!(
        "\t├─ {label:<8} {input:>in_width$} → {output:>out_width$} (↓{reduction:.1}%)",
        label = "T/Tdg",
        input = in_values[2],
        output = out_values[2],
        reduction = pct(in_t, out_t),
    );
    eprintln!(
        "\t├─ {label:<8} {input:>in_width$} → {output:>out_width$} (↓{reduction:.1}%)",
        label = "Depth",
        input = in_values[3],
        output = out_values[3],
        reduction = pct(in_depth, out_depth),
    );
    eprintln!(
        "\t└─ {label:<8} {time:>in_width$}",
        label = "Time",
        time = format!("{secs:.3}s"),
    );
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

/// Read and parse a QASM file into a circuit, logging parse stats. Exits on error.
fn read_circuit(path: &str) -> Circuit {
    let qasm = fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("Error reading {path}: {e}");
        process::exit(1);
    });
    let parse_start = Instant::now();
    let circuit = Circuit::from_qasm(&qasm).unwrap_or_else(|e| {
        eprintln!("Error parsing {path}: {e}");
        process::exit(1);
    });
    eprintln!(
        "\t└─ {} qubits · {} gates · {} 2q gates · {} T/Tdg · {} depth · {:.3}s",
        fmt_num(circuit.num_qubits),
        fmt_num(circuit.gates.len()),
        fmt_num(count_2q(&circuit)),
        fmt_num(count_t(&circuit)),
        fmt_num(depth(&circuit)),
        parse_start.elapsed().as_secs_f64()
    );
    eprintln!();
    circuit
}

/// Run a pass pipeline once over `circuit`, in order. When `verbose`, shows
/// a live "% reduction so far" progress box (see [`update_reduction_progress`]),
/// redrawn after each pass — no iteration number, since (unlike the fixpoint
/// driver) this only ever makes one pass over `passes`. Suppressed for
/// map-reduce chunk workers, where concurrent chunks would otherwise
/// interleave garbled output.
fn run_pipeline(circuit: &Circuit, passes: &[&dyn Pass], verbose: bool) -> Circuit {
    let baseline_gates = circuit.gates.len();
    let baseline_2q = count_2q(circuit);
    let baseline_depth = depth(circuit);
    let baseline_t = count_t(circuit);
    let mut c = circuit.clone();
    if verbose {
        start_progress_block(box_lines(4));
        update_reduction_progress(
            "% reduction so far",
            c.gates.len(),
            count_2q(&c),
            depth(&c),
            count_t(&c),
            baseline_gates,
            baseline_2q,
            baseline_depth,
            baseline_t,
        );
    }
    for p in passes {
        c = p.run(&c);
        if verbose {
            update_reduction_progress(
                "% reduction so far",
                c.gates.len(),
                count_2q(&c),
                depth(&c),
                count_t(&c),
                baseline_gates,
                baseline_2q,
                baseline_depth,
                baseline_t,
            );
        }
    }
    if verbose {
        end_progress_block(box_lines(4));
    }
    c
}

/// Width, in characters, of a progress bar's fill/track region.
const BAR_WIDTH: usize = 32;
/// Width of a progress box row's label field, with one column of padding after
/// the longest label ("2q gates").
const LABEL_WIDTH: usize = 9;

/// Green fill, used for the map-reduce chunk-completion bar.
const CHUNK_BAR_COLOR: &str = "\x1b[32m";
/// Cyan fill, used for the gate-count reduction bar.
const GATES_BAR_COLOR: &str = "\x1b[36m";
/// Yellow fill, used for the two-qubit-gate reduction bar.
const TWO_QUBIT_BAR_COLOR: &str = "\x1b[33m";
/// Magenta fill, used for the T-count reduction bar.
const T_BAR_COLOR: &str = "\x1b[35m";
/// Blue fill, used for the depth reduction bar.
const DEPTH_BAR_COLOR: &str = "\x1b[34m";

/// Render a thin bar — heavy `color` fill, a partial tip glyph at the exact
/// boundary, dim light-line track for the remainder — in the style of
/// indicatif's `{bar:.color/dim}` with `━╸─` progress chars. `fraction` is
/// clamped to `[0, 1]`.
fn render_bar(fraction: f64, width: usize, color: &str) -> String {
    let fraction = fraction.clamp(0.0, 1.0);
    let exact = fraction * width as f64;
    let full = (exact.floor() as usize).min(width);
    let has_tip = full < width && exact > full as f64;
    let empty = width - full - usize::from(has_tip);

    let mut bar = String::with_capacity(width + 16);
    bar.push_str(color);
    for _ in 0..full {
        bar.push('━');
    }
    if has_tip {
        bar.push('╸');
    }
    bar.push_str("\x1b[0m\x1b[2m");
    for _ in 0..empty {
        bar.push('─');
    }
    bar.push_str("\x1b[0m");
    bar
}

/// Number of lines a progress box with `num_rows` bar rows occupies (a top
/// and bottom border, plus one line per row).
fn box_lines(num_rows: usize) -> usize {
    num_rows + 2
}

/// Build the lines of a live progress box: a top border with `title`
/// embedded, one line per `(label, colored_bar, trailing)` row, and a bottom
/// border. Every line is padded to equal *visible* width — the ANSI escapes
/// inside `bar` don't count — so the box grows to fit large counts and stays
/// rectangular as values change. Indented two spaces to
/// line up with the rest of tzap's output (e.g. "  Parsing ...").
fn progress_box(title: &str, rows: &[(&str, String, String)]) -> Vec<String> {
    let row_width = |trailing: &str| LABEL_WIDTH + BAR_WIDTH + 1 + trailing.chars().count();
    let title_segment = format!("─ {title} ");
    let content_width = rows
        .iter()
        .map(|(_, _, trailing)| row_width(trailing))
        .max()
        .unwrap_or(0)
        .max(title_segment.chars().count());
    let inner_width = content_width + 2;

    let dashes = inner_width.saturating_sub(title_segment.chars().count());
    let mut lines = vec![format!("  ┌{title_segment}{}┐", "─".repeat(dashes))];
    for (label, bar, trailing) in rows {
        let pad = inner_width - (row_width(trailing) + 2);
        lines.push(format!(
            "  │ {label:<LABEL_WIDTH$}{bar} {trailing}{} │",
            " ".repeat(pad)
        ));
    }
    lines.push(format!("  └{}┘", "─".repeat(inner_width)));
    lines
}

/// Reserve `n` blank lines for a live-redrawn progress block and leave the
/// cursor at its top-left. Pair with a later [`end_progress_block`] once the
/// block's final frame has been drawn.
fn start_progress_block(n: usize) {
    eprint!("{}\x1b[{n}A", "\n".repeat(n));
    let _ = io::stderr().flush();
}

/// Erase a live progress block of `n` lines entirely — every line cleared,
/// cursor returned to the block's top-left — instead of leaving its last
/// frame on screen. Called once optimization finishes, so the box
/// disappears rather than lingering under the closing result banner.
fn end_progress_block(n: usize) {
    for i in 0..n {
        eprint!("\x1b[2K");
        if i + 1 < n {
            eprint!("\n");
        } else if n > 1 {
            eprint!("\x1b[{}A", n - 1);
        }
    }
    let _ = io::stderr().flush();
}

/// Redraw a live progress block in place: clear and reprint each of
/// `lines`, then return the cursor to the block's top-left for the next
/// redraw. Must be bracketed by [`start_progress_block`] / [`end_progress_block`]
/// with a matching line count.
fn redraw_progress_block(lines: &[String]) {
    let mut out = String::new();
    for (i, line) in lines.iter().enumerate() {
        out.push_str("\r\x1b[2K");
        out.push_str(line);
        if i + 1 < lines.len() {
            out.push('\n');
        }
    }
    if lines.len() > 1 {
        out.push_str(&format!("\x1b[{}A\r", lines.len() - 1));
    } else {
        out.push('\r');
    }
    eprint!("{out}");
    let _ = io::stderr().flush();
}

/// Redraw a live "% reduction so far" progress box under `title`: a
/// gate, two-qubit, depth, and T-count reduction bars (reduction relative to
/// the corresponding baselines at the start of this run), each in its own
/// color. Shared by the fixpoint driver (title carries the
/// iteration number) and the plain pipeline driver (no iteration — it
/// doesn't loop). Must be bracketed by `start_progress_block(box_lines(4))`
/// / `end_progress_block(box_lines(4))`.
fn update_reduction_progress(
    title: &str,
    gates: usize,
    two_qubit: usize,
    circuit_depth: usize,
    t_count: usize,
    baseline_gates: usize,
    baseline_two_qubit: usize,
    baseline_depth: usize,
    baseline_t: usize,
) {
    let gates_pct = pct(baseline_gates, gates);
    let two_qubit_pct = pct(baseline_two_qubit, two_qubit);
    let depth_pct = pct(baseline_depth, circuit_depth);
    let t_pct = pct(baseline_t, t_count);
    let gates_str = fmt_num(gates);
    let gates_width = fmt_num(baseline_gates).chars().count();
    let two_qubit_str = fmt_num(two_qubit);
    let two_qubit_width = fmt_num(baseline_two_qubit).chars().count();
    let depth_str = fmt_num(circuit_depth);
    let depth_width = fmt_num(baseline_depth).chars().count();
    let t_str = fmt_num(t_count);
    let t_width = fmt_num(baseline_t).chars().count();
    redraw_progress_block(&progress_box(
        title,
        &[
            (
                "Gates",
                render_bar(gates_pct / 100.0, BAR_WIDTH, GATES_BAR_COLOR),
                format!("{gates_pct:>5.1}% · {gates_str:<gates_width$}"),
            ),
            (
                "2q gates",
                render_bar(two_qubit_pct / 100.0, BAR_WIDTH, TWO_QUBIT_BAR_COLOR),
                format!("{two_qubit_pct:>5.1}% · {two_qubit_str:<two_qubit_width$}"),
            ),
            (
                "T/Tdg",
                render_bar(t_pct / 100.0, BAR_WIDTH, T_BAR_COLOR),
                format!("{t_pct:>5.1}% · {t_str:<t_width$}"),
            ),
            (
                "Depth",
                render_bar(depth_pct / 100.0, BAR_WIDTH, DEPTH_BAR_COLOR),
                format!("{depth_pct:>5.1}% · {depth_str:<depth_width$}"),
            ),
        ],
    ));
}

/// Redraw the live fixpoint progress box — [`update_reduction_progress`]
/// with the current iteration number in the title.
fn update_fixpoint_progress(
    iteration: usize,
    gates: usize,
    two_qubit: usize,
    circuit_depth: usize,
    t_count: usize,
    baseline_gates: usize,
    baseline_two_qubit: usize,
    baseline_depth: usize,
    baseline_t: usize,
) {
    update_reduction_progress(
        &format!("Iteration {iteration} — % reduction so far"),
        gates,
        two_qubit,
        circuit_depth,
        t_count,
        baseline_gates,
        baseline_two_qubit,
        baseline_depth,
        baseline_t,
    );
}

/// Redraw the live parallel map-reduce progress box: how many chunks have
/// finished, and the whole circuit's gate/T reduction achieved so far.
/// Finished chunks contribute their optimized metrics while chunks still
/// pending contribute their original metrics. Must be bracketed by
/// `start_progress_block(box_lines(5))` / `end_progress_block(box_lines(5))`.
fn update_chunk_progress(
    done: usize,
    total: usize,
    baseline_gates: usize,
    current_gates: usize,
    baseline_2q: usize,
    current_2q: usize,
    baseline_depth: usize,
    current_depth: usize,
    baseline_t: usize,
    current_t: usize,
) {
    let chunk_fraction = if total > 0 {
        done as f64 / total as f64
    } else {
        1.0
    };
    let chunk_pct = chunk_fraction * 100.0;
    let gates_pct = pct(baseline_gates, current_gates);
    let two_qubit_pct = pct(baseline_2q, current_2q);
    let depth_pct = pct(baseline_depth, current_depth);
    let t_pct = pct(baseline_t, current_t);
    let done_str = fmt_num(done);
    let done_width = fmt_num(total).chars().count();
    let total_str = fmt_num(total);
    let gates_str = fmt_num(current_gates);
    let gates_width = fmt_num(baseline_gates).chars().count();
    let two_qubit_str = fmt_num(current_2q);
    let two_qubit_width = fmt_num(baseline_2q).chars().count();
    let depth_str = fmt_num(current_depth);
    let depth_width = fmt_num(baseline_depth).chars().count();
    let t_str = fmt_num(current_t);
    let t_width = fmt_num(baseline_t).chars().count();
    redraw_progress_block(&progress_box(
        "Parallel optimization — % reduction so far",
        &[
            (
                "Chunks",
                render_bar(chunk_fraction, BAR_WIDTH, CHUNK_BAR_COLOR),
                format!("{chunk_pct:>5.1}% · {done_str:<done_width$}/{total_str}"),
            ),
            (
                "Gates",
                render_bar(gates_pct / 100.0, BAR_WIDTH, GATES_BAR_COLOR),
                format!("{gates_pct:>5.1}% · {gates_str:<gates_width$}"),
            ),
            (
                "2q gates",
                render_bar(two_qubit_pct / 100.0, BAR_WIDTH, TWO_QUBIT_BAR_COLOR),
                format!("{two_qubit_pct:>5.1}% · {two_qubit_str:<two_qubit_width$}"),
            ),
            (
                "T/Tdg",
                render_bar(t_pct / 100.0, BAR_WIDTH, T_BAR_COLOR),
                format!("{t_pct:>5.1}% · {t_str:<t_width$}"),
            ),
            (
                "Depth",
                render_bar(depth_pct / 100.0, BAR_WIDTH, DEPTH_BAR_COLOR),
                format!("{depth_pct:>5.1}% · {depth_str:<depth_width$}"),
            ),
        ],
    ));
}

/// Run one fixpoint sweep over `circuit`. When `verbose`, redraws the live
/// progress box with the most recent counts as each pass completes.
fn run_fixpoint_sweep(
    circuit: &Circuit,
    passes: &[&dyn Pass],
    iteration: usize,
    verbose: bool,
    baseline_gates: usize,
    baseline_2q: usize,
    baseline_depth: usize,
    baseline_t: usize,
) -> Circuit {
    let mut c = circuit.clone();
    if verbose {
        update_fixpoint_progress(
            iteration,
            c.gates.len(),
            count_2q(&c),
            depth(&c),
            count_t(&c),
            baseline_gates,
            baseline_2q,
            baseline_depth,
            baseline_t,
        );
    }
    for pass in passes {
        c = pass.run(&c);
        if verbose {
            update_fixpoint_progress(
                iteration,
                c.gates.len(),
                count_2q(&c),
                depth(&c),
                count_t(&c),
                baseline_gates,
                baseline_2q,
                baseline_depth,
                baseline_t,
            );
        }
    }
    c
}

/// Repeatedly run `passes` until a sweep fails to reduce the gate count, or
/// (when `max_rounds` is given) until that many sweeps have run, whichever
/// comes first. When `rz_decompose` is given, run it exactly once after the
/// first sweep and force another sweep if there were Rz gates to decompose
/// — this extra sweep isn't itself subject to the `max_rounds` cap. Returns
/// the result, how many sweeps ran, and whether that was a true fixpoint
/// (as opposed to hitting the round cap first).
fn run_to_fixpoint(
    circuit: &Circuit,
    passes: &[&dyn Pass],
    rz_decompose: Option<&dyn Pass>,
    verbose: bool,
    max_rounds: Option<usize>,
) -> (Circuit, usize, bool) {
    let baseline_gates = circuit.gates.len();
    let baseline_2q = count_2q(circuit);
    let baseline_depth = depth(circuit);
    let baseline_t = count_t(circuit);
    let mut c = circuit.clone();
    let mut round = 0;
    let mut reduced;
    if verbose {
        start_progress_block(box_lines(4));
    }
    loop {
        round += 1;
        let before = c.gates.len();
        c = run_fixpoint_sweep(
            &c,
            passes,
            round,
            verbose,
            baseline_gates,
            baseline_2q,
            baseline_depth,
            baseline_t,
        );
        reduced = c.gates.len() < before;

        if round == 1
            && let Some(pass) = rz_decompose
        {
            let had_rz = c.gates.iter().any(|g| matches!(g, Gate::rz(..)));
            c = pass.run(&c);
            if verbose {
                update_fixpoint_progress(
                    round,
                    c.gates.len(),
                    count_2q(&c),
                    depth(&c),
                    count_t(&c),
                    baseline_gates,
                    baseline_2q,
                    baseline_depth,
                    baseline_t,
                );
            }
            if had_rz {
                continue;
            }
        }

        if !reduced || max_rounds.is_some_and(|m| round >= m) {
            break;
        }
    }
    if verbose {
        end_progress_block(box_lines(4));
    }
    (c, round, !reduced)
}

/// Build a fresh `SuperOpt` instance. Callers must construct one of these
/// per map-reduce chunk (never share or reuse one instance across chunks):
/// each instance owns its own matrix cache and incremental-diff state, so a
/// fresh instance per chunk means `.incremental()` is always sound here —
/// every instance only ever sees successive versions of the one circuit it
/// was built for. `level` selects which bounds preset an unset
/// `--superopt-*` flag falls back to — `SUPER_SUPEROPT_*` under `-Osuper`,
/// `DEFAULT_SUPEROPT_*` otherwise. `verbose` controls whether the one-time
/// table-build diagnostics are printed (see the note above `table_config`).
fn initialize_superopt(opts: &Opts, level: OptimizationLevel, verbose: bool) -> SuperOpt {
    let (default_qubits, default_window_gates, default_table_entries) =
        if level == OptimizationLevel::Osuper {
            (
                SUPER_SUPEROPT_QUBITS,
                SUPER_SUPEROPT_WINDOW_GATES,
                SUPER_SUPEROPT_TABLE_ENTRIES,
            )
        } else {
            (
                DEFAULT_SUPEROPT_QUBITS,
                DEFAULT_SUPEROPT_WINDOW_GATES,
                DEFAULT_SUPEROPT_TABLE_ENTRIES,
            )
        };
    let qubits = opts.superopt_qubits.unwrap_or(default_qubits);
    let window_gates = opts.superopt_window_gates.unwrap_or(default_window_gates);
    let table_entries = opts.superopt_table_entries.unwrap_or(default_table_entries);

    // A table entry needs strictly fewer gates than the window it replaces
    // (see `ActiveWindow::consider`'s `local.len() >= gate_indices.len()`
    // rejection), and no window ever exceeds `window_gates`. So a stored
    // circuit at exactly `window_gates` depth could never be strictly
    // smaller than the largest possible window — `window_gates - 1` is the
    // deepest depth any table entry can ever be used at.
    let table_gates = window_gates.saturating_sub(1);
    let table_config = SuperOptTableConfig::new(qubits, table_gates, table_entries);
    // Quiet for map-reduce chunk workers: with one fresh instance per chunk,
    // this would otherwise print once per chunk. The caller instead does one
    // verbose warm-up call before fanning out, so the table build (and its
    // one-time cost message) is reported exactly once.
    if verbose && !table_is_cached(table_config) {
        eprintln!("  🔧 Generating semantic lookup table (one-time — cached for future use)...");
    }
    let start = Instant::now();
    let pass = SuperOpt::new(qubits, window_gates, table_config)
        .unwrap_or_else(|error| arg_error(format!("failed to initialize SuperOpt: {error}")));
    if verbose {
        eprintln!(
            "  Initialized SuperOpt table in {:.3}s",
            start.elapsed().as_secs_f64()
        );
        eprintln!();
    }
    pass.without_subcircuits().incremental()
}

/// Print the result banner against `input`'s counts, check Rz invariants,
/// and write the output file (if requested).
fn finish(input: &Circuit, result: &Circuit, opts: &Opts, start: Instant) {
    print_result(
        input.gates.len(),
        result.gates.len(),
        count_2q(input),
        count_2q(result),
        depth(input),
        depth(result),
        count_t(input),
        count_t(result),
        start.elapsed().as_secs_f64(),
    );

    let input_has_rz = input.gates.iter().any(|g| matches!(g, Gate::rz(..)));
    let output_has_rz = result.gates.iter().any(|g| matches!(g, Gate::rz(..)));
    if output_has_rz && !input_has_rz {
        panic!("BUG: output contains Rz gates but input did not");
    }
    if output_has_rz && opts.decompose_rz {
        panic!("BUG: output contains Rz gates after --decompose-rz");
    }

    write_output(&opts.output_path, result);
}

/// Run the fixpoint driver and (when `verbose`) log the round count. Not
/// verbose for map-reduce chunk workers — each chunk reaches its own
/// fixpoint independently, so a per-chunk round count would just be noise;
/// the chunk progress bar in [`run_map_reduce`] is the only progress
/// reporting during parallel runs.
fn run_to_fixpoint_logged(
    circuit: &Circuit,
    passes: &[&dyn Pass],
    rz_decompose: Option<&dyn Pass>,
    verbose: bool,
    max_rounds: Option<usize>,
) -> Circuit {
    let (result, rounds, reached_fixpoint) =
        run_to_fixpoint(circuit, passes, rz_decompose, verbose, max_rounds);
    if verbose && reached_fixpoint {
        eprintln!("  Fixpoint reached after {rounds} iteration(s)");
        eprintln!();
    }
    result
}

/// Run `optimize` once on the whole circuit when sequential, or independently
/// on each of `num_chunks` chunks in parallel (map), recombining the results
/// in order (reduce). Each chunk is optimized completely independently: no
/// state — not even a synthesis table's matrix cache — is shared between
/// chunks, so `optimize` must construct every stateful pass (`SuperOpt`)
/// fresh on every call.
fn run_map_reduce(
    circuit: &Circuit,
    parallel: bool,
    num_chunks: usize,
    optimize: impl Fn(&Circuit, bool) -> Circuit + Sync + Send,
) -> Circuit {
    if !parallel {
        return optimize(circuit, true);
    }
    let chunks = chunk_circuit(circuit, num_chunks);
    let total = chunks.len();

    // Whole-circuit baselines: pending chunks (not yet optimized) contribute
    // their original metrics, while completed chunks contribute their current
    // metrics.
    let baseline_gates = circuit.gates.len();
    let baseline_2q = count_2q(circuit);
    let baseline_depth = depth(circuit);
    let baseline_t = count_t(circuit);
    let progress_chunks = Arc::new(Mutex::new(chunks.clone()));
    let done = AtomicUsize::new(0);
    let sum_before_gates = AtomicUsize::new(0);
    let sum_after_gates = AtomicUsize::new(0);
    let sum_before_t = AtomicUsize::new(0);
    let sum_after_t = AtomicUsize::new(0);

    start_progress_block(box_lines(5));
    update_chunk_progress(
        0,
        total,
        baseline_gates,
        baseline_gates,
        baseline_2q,
        baseline_2q,
        baseline_depth,
        baseline_depth,
        baseline_t,
        baseline_t,
    );
    let optimized: Vec<Circuit> = chunks
        .par_iter()
        .enumerate()
        .map(|(chunk_index, chunk)| {
            let before_gates = chunk.gates.len();
            let before_t = count_t(chunk);
            let result = optimize(chunk, false);
            let after_gates = result.gates.len();
            let after_t = count_t(&result);

            let n = done.fetch_add(1, Ordering::Relaxed) + 1;
            let sum_before_gates =
                sum_before_gates.fetch_add(before_gates, Ordering::Relaxed) + before_gates;
            let sum_after_gates =
                sum_after_gates.fetch_add(after_gates, Ordering::Relaxed) + after_gates;
            let sum_before_t = sum_before_t.fetch_add(before_t, Ordering::Relaxed) + before_t;
            let sum_after_t = sum_after_t.fetch_add(after_t, Ordering::Relaxed) + after_t;

            let current_gates = baseline_gates - sum_before_gates + sum_after_gates;
            let current_t = baseline_t - sum_before_t + sum_after_t;
            let (current_2q, current_depth) = {
                let mut progress_chunks = progress_chunks.lock().unwrap();
                progress_chunks[chunk_index] = result.clone();
                let current = stitch(circuit.num_qubits, circuit.num_cbits, &progress_chunks);
                (count_2q(&current), depth(&current))
            };
            update_chunk_progress(
                n,
                total,
                baseline_gates,
                current_gates,
                baseline_2q,
                current_2q,
                baseline_depth,
                current_depth,
                baseline_t,
                current_t,
            );
            result
        })
        .collect();
    end_progress_block(box_lines(5));
    stitch(circuit.num_qubits, circuit.num_cbits, &optimized)
}

/// Run the explicit `--passes` pipeline on `circuit`, constructing a fresh
/// `SuperOpt` if it's selected. Used as one map-reduce worker per chunk.
fn optimize_explicit(circuit: &Circuit, opts: &Opts, verbose: bool) -> Circuit {
    let listed_names = opts
        .passes
        .as_ref()
        .expect("only called when --passes is set");
    let names: Vec<PassName> = if opts.decompose_cz {
        std::iter::once(PassName::DecomposeCz)
            .chain(
                listed_names
                    .iter()
                    .copied()
                    .filter(|p| !matches!(p, PassName::DecomposeCz)),
            )
            .collect()
    } else {
        listed_names.clone()
    };
    let decompose_toffoli = DecomposeToffoli;
    let decompose_cz = DecomposeCz;
    let rz_decompose = DecomposeRz {
        epsilon: opts.rz_epsilon,
    };
    let cancel_pass = CancelGates;
    let global = PhaseFoldRand;
    let global_expr = PhaseFoldGlobalExpr;

    let uses_superopt = names.iter().any(|p| matches!(p, PassName::SuperOpt));
    let superopt_pass =
        uses_superopt.then(|| initialize_superopt(opts, OptimizationLevel::O1, verbose));

    let passes: Vec<&dyn Pass> = names
        .iter()
        .map(|p| -> &dyn Pass {
            match p {
                PassName::DecomposeToffoli => &decompose_toffoli,
                PassName::DecomposeCz => &decompose_cz,
                PassName::DecomposeRz => &rz_decompose,
                PassName::CancelGates => &cancel_pass,
                PassName::SuperOpt => superopt_pass
                    .as_ref()
                    .expect("constructed when the pass is selected"),
                PassName::PhaseFoldRand => &global,
                PassName::PhaseFoldGlobalExpr => &global_expr,
            }
        })
        .collect();

    if opts.fixpoint {
        run_to_fixpoint_logged(circuit, &passes, None, verbose, None)
    } else {
        run_pipeline(circuit, &passes, verbose)
    }
}

/// Run the default pipeline (chosen by `-O1`/`-O2`/`-O3`/`-Osuper`) on
/// `circuit`, constructing a fresh `SuperOpt` whenever the level uses one.
/// Used as one map-reduce worker per chunk.
fn optimize_default(circuit: &Circuit, opts: &Opts, verbose: bool) -> Circuit {
    let rz_decompose = DecomposeRz {
        epsilon: opts.rz_epsilon,
    };
    let cancel_pass = CancelGates;
    let global = PhaseFoldRand;
    let global_expr = PhaseFoldGlobalExpr;

    let optimization_level = opts.optimization_level.unwrap_or(OptimizationLevel::O1);
    if matches!(
        optimization_level,
        OptimizationLevel::O2 | OptimizationLevel::O3 | OptimizationLevel::Osuper
    ) {
        // O2 runs a fixed 2 rounds rather than to a true fixpoint — O3 and
        // Osuper are the "run it out fully" tiers; O2 is the cheap, bounded
        // one.
        let max_rounds = (optimization_level == OptimizationLevel::O2).then_some(2);
        let superopt_pass = initialize_superopt(opts, optimization_level, verbose);
        let passes: Vec<&dyn Pass> = vec![&cancel_pass, &superopt_pass, &global];
        let decompose: Option<&dyn Pass> = opts.decompose_rz.then_some(&rz_decompose);
        run_to_fixpoint_logged(circuit, &passes, decompose, verbose, max_rounds)
    } else {
        let phase_fold: &dyn Pass = if opts.expr { &global_expr } else { &global };
        let optimization_passes: Vec<&dyn Pass> = vec![&cancel_pass, phase_fold];

        // Optimize, then (for --decompose-rz) decompose Rz and optimize the result
        // again — so the selected optimization pipeline runs on both sides of gridsynth.
        let mut passes = optimization_passes.clone();
        if opts.decompose_rz && circuit.gates.iter().any(|g| matches!(g, Gate::rz(..))) {
            passes.push(&rz_decompose);
            passes.extend(optimization_passes);
        }

        if opts.fixpoint {
            run_to_fixpoint_logged(circuit, &passes, None, verbose, None)
        } else {
            run_pipeline(circuit, &passes, verbose)
        }
    }
}

/// Default pipeline: decompose ccx/ccz (and optionally Rz), then cancel + phase-fold.
/// `--passes` overrides this with an explicit, user-ordered pipeline. Under
/// `--parallel`, the chosen pipeline runs map-reduce style (see
/// [`run_map_reduce`]): the circuit is split into independent chunks, each
/// optimized start-to-finish on its own (own `SuperOpt` instance, no shared
/// state), then the results are stitched back together in order.
fn run_optimize(circuit: Circuit, opts: &Opts, start: Instant) {
    let num_chunks = num_par_chunks();

    // Explicit pipeline via --passes: run exactly what the user listed, in order.
    if let Some(names) = &opts.passes {
        let uses_rz = names.iter().any(|p| matches!(p, PassName::DecomposeRz));
        let uses_superopt = names.iter().any(|p| matches!(p, PassName::SuperOpt));
        if opts.parallel || uses_rz {
            init_global_pool();
        }
        // Warm the (process-wide cached) synthesis table once, verbosely,
        // before fanning out — each chunk's own SuperOpt build stays quiet.
        if opts.parallel && uses_superopt {
            initialize_superopt(opts, OptimizationLevel::O1, true);
        }
        let result = run_map_reduce(&circuit, opts.parallel, num_chunks, |c, verbose| {
            optimize_explicit(c, opts, verbose)
        });
        finish(&circuit, &result, opts, start);
        return;
    }

    if opts.parallel || opts.decompose_rz {
        init_global_pool();
    }

    // Decompose CCX/CCZ eagerly, once, over the whole circuit — before any
    // chunking — so post-decomp counts form the baseline.
    let decompose_toffoli = DecomposeToffoli;
    let circuit = if circuit.has_toffoli || circuit.has_ccz {
        run_logged(&decompose_toffoli, &circuit)
    } else {
        circuit
    };

    let decompose_cz = DecomposeCz;
    let circuit = if opts.decompose_cz
        && circuit.gates.iter().any(|g| matches!(g, Gate::cz { .. }))
    {
        run_logged(&decompose_cz, &circuit)
    } else {
        circuit
    };

    let optimization_level = opts.optimization_level.unwrap_or(OptimizationLevel::O1);
    let uses_superopt = matches!(
        optimization_level,
        OptimizationLevel::O2 | OptimizationLevel::O3 | OptimizationLevel::Osuper
    );
    if opts.parallel && uses_superopt {
        initialize_superopt(opts, optimization_level, true);
    }

    let result = run_map_reduce(&circuit, opts.parallel, num_chunks, |c, verbose| {
        optimize_default(c, opts, verbose)
    });
    finish(&circuit, &result, opts, start);
}

fn print_help() {
    println!();
    println!(
        "  \x1b[1m⚡\u{FE0F} tzap\x1b[0m  —  fast quantum circuit optimizer  \x1b[2mv{}\x1b[0m",
        env!("CARGO_PKG_VERSION")
    );
    println!();
    println!("  \x1b[1;33mUSAGE\x1b[0m");
    println!("    tzap <input.qasm> [output.qasm] [options]");
    println!();
    println!("  Decomposes Toffoli (ccx) gates into Clifford+T by default.");
    println!("  Pass --decompose-cz to decompose CZ gates into H+CX+H.");
    println!("  Pass --decompose-rz to also decompose Rz gates via gridsynth.");
    println!();
    println!("  \x1b[1;33mARGS\x1b[0m");
    println!("    \x1b[1m<input.qasm>\x1b[0m     Input OpenQASM 2.0 file");
    println!("    \x1b[1m[output.qasm]\x1b[0m    Output file (no output if omitted)");
    println!();
    println!("  \x1b[1;33mOPTIONS\x1b[0m");
    println!("    \x1b[1m-o\x1b[0m <file>        Write output to <file>");
    println!("    \x1b[1m--decompose-rz\x1b[0m   Decompose Rz gates into Clifford+T (gridsynth)");
    println!("    \x1b[1m--decompose-cz\x1b[0m   Decompose CZ gates into H+CX+H");
    println!(
        "    \x1b[1m--epsilon\x1b[0m <eps>  Approximation epsilon for --decompose-rz (default: 1e-10)"
    );
    println!("    \x1b[1m--parallel\x1b[0m       Enable parallel mode (off by default)");
    println!(
        "    \x1b[1m--passes\x1b[0m <list>  Run these passes in order, overriding the default pipeline"
    );
    println!("                     (see PASSES). --decompose-cz is prepended when set.");
    println!("                     Excludes --decompose-rz; --epsilon still");
    println!("                     configures DecomposeRz.");
    println!(
        "    \x1b[1m--fixpoint\x1b[0m       Repeat the pipeline until gate count stops decreasing"
    );
    println!("    \x1b[1m-O1\x1b[0m              Default, fast optimization pass schedule");
    println!("    \x1b[1m-O2\x1b[0m              Adds a superoptimization pass to O1 (2 rounds)");
    println!("    \x1b[1m-O3\x1b[0m              Like -O2, run to a fixpoint instead of 2 rounds");
    println!(
        "    \x1b[1m-Osuper\x1b[0m          Like -O3, with a larger SuperOpt window/table (slower"
    );
    println!("                     first run; the table is cached to disk afterward)");
    println!("    \x1b[1m-h, --help\x1b[0m       Print this help message");
    println!("    \x1b[1m-v, --version\x1b[0m    Print the version");
    println!();
    println!("  \x1b[1;33mPASSES\x1b[0m (names for --passes)");
    for (name, pass, desc) in PassName::ALL {
        if matches!(pass, PassName::PhaseFoldGlobalExpr) {
            continue;
        }
        println!("    \x1b[1m{name:<19}\x1b[0m  {desc}");
    }
    println!();
}

/// Print `Error: {msg}` and exit 1. The single entry point for every
/// argument-parsing failure, so all CLI errors share one unmistakable
/// prefix instead of some being phrased as errors and others not.
fn arg_error(msg: impl std::fmt::Display) -> ! {
    eprintln!("Error: {msg}");
    process::exit(1);
}

/// Parse the next argument as a `usize`, exiting with `flag_name` in the
/// error message on failure, if there is no next argument, or if it parses
/// to 0 — every caller of this (the hidden `--superopt-*` bounds) feeds a
/// count or width that must be at least 1, and the message already promises
/// "positive integer", so 0 must be rejected too rather than silently
/// accepted as a valid `usize`.
fn parse_usize_arg(args: &[String], i: usize, flag_name: &str) -> usize {
    let value = args
        .get(i)
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| arg_error(format!("{flag_name} requires a positive integer")));
    if value == 0 {
        arg_error(format!("{flag_name} requires a positive integer, got 0"));
    }
    value
}

fn parse_args(args: &[String]) -> Opts {
    let mut input_path: Option<String> = None;
    let mut output_path: Option<String> = None;
    let mut expr = false;
    let mut decompose_rz = false;
    let mut decompose_cz = false;
    let mut rz_epsilon: f64 = 1e-10;
    let mut parallel = false;
    let mut passes: Option<Vec<PassName>> = None;
    let mut fixpoint = false;
    let mut optimization_level = None;
    let mut superopt_qubits: Option<usize> = None;
    let mut superopt_window_gates: Option<usize> = None;
    let mut superopt_table_entries: Option<usize> = None;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--help" | "-h" => {
                print_help();
                process::exit(0);
            }
            "--version" | "-v" => {
                println!("tzap {}", env!("CARGO_PKG_VERSION"));
                process::exit(0);
            }
            "--expr" => expr = true,
            "--decompose-rz" => decompose_rz = true,
            "--decompose-cz" => decompose_cz = true,
            "--epsilon" => {
                i += 1;
                let value: f64 = args
                    .get(i)
                    .and_then(|s| s.parse().ok())
                    .unwrap_or_else(|| arg_error("--epsilon requires a number (e.g. 1e-10)"));
                if !(value.is_finite() && value > 0.0) {
                    arg_error(format!(
                        "--epsilon must be a positive, finite number, got {value} \
                         (e.g. 1e-10) — zero or negative values make Rz synthesis undefined"
                    ));
                }
                rz_epsilon = value;
            }
            "--passes" => {
                i += 1;
                let list = args.get(i).unwrap_or_else(|| {
                    arg_error(
                        "--passes requires a comma-separated list of pass names \
                         (e.g. --passes CancelGates,PhaseFoldRand)",
                    )
                });
                let mut list = list.clone();
                while let Some(next) = args.get(i + 1) {
                    if next.starts_with('-') || !looks_like_pass_list_fragment(next) {
                        break;
                    }
                    list.push(',');
                    list.push_str(next);
                    i += 1;
                }
                passes = Some(parse_pass_list(&list));
            }
            "--parallel" => parallel = true,
            "--fixpoint" => fixpoint = true,
            "-O1" | "-O2" | "-O3" | "-Osuper" => {
                if optimization_level.is_some() {
                    arg_error("-O1, -O2, -O3, and -Osuper cannot be combined — pick exactly one");
                }
                optimization_level = Some(match args[i].as_str() {
                    "-O1" => OptimizationLevel::O1,
                    "-O2" => OptimizationLevel::O2,
                    "-O3" => OptimizationLevel::O3,
                    "-Osuper" => OptimizationLevel::Osuper,
                    _ => unreachable!(),
                });
            }
            "-o" => {
                i += 1;
                output_path = Some(
                    args.get(i)
                        .cloned()
                        .unwrap_or_else(|| arg_error("-o requires an output file path")),
                );
            }
            // Hidden: not listed in --help, for experimentation with SuperOpt's
            // window/table bounds without a rebuild.
            "--superopt-qubits" => {
                i += 1;
                superopt_qubits = Some(parse_usize_arg(args, i, "--superopt-qubits"));
            }
            "--superopt-window-gates" => {
                i += 1;
                superopt_window_gates = Some(parse_usize_arg(args, i, "--superopt-window-gates"));
            }
            "--superopt-table-entries" => {
                i += 1;
                superopt_table_entries = Some(parse_usize_arg(args, i, "--superopt-table-entries"));
            }
            _ if args[i].starts_with('-') => {
                arg_error(format!(
                    "unknown flag '{}'. Run `tzap --help` for the list of valid options",
                    args[i]
                ));
            }
            _ => {
                if input_path.is_none() {
                    input_path = Some(args[i].clone());
                } else if output_path.is_none() {
                    output_path = Some(args[i].clone());
                } else {
                    arg_error(format!(
                        "unexpected extra argument '{}' — tzap takes at most \
                         <input.qasm> and [output.qasm]",
                        args[i]
                    ));
                }
            }
        }
        i += 1;
    }

    let Some(input_path) = input_path else {
        arg_error(
            "missing required <input.qasm> argument\n\n  \
             Usage: tzap <input.qasm> [-o output.qasm] [-O1|-O2|-O3|-Osuper] \
             [--decompose-cz] [--decompose-rz] [--expr] [--passes <list>] [--parallel] [--fixpoint]\n  \
             Run `tzap --help` for the full option list.",
        );
    };

    if optimization_level.is_some() && (passes.is_some() || fixpoint) {
        arg_error("-O1, -O2, -O3, and -Osuper cannot be combined with --passes or --fixpoint");
    }
    if passes.is_some() && (expr || decompose_rz) {
        arg_error("--passes cannot be combined with --decompose-rz or --expr");
    }
    Opts {
        input_path,
        output_path,
        expr,
        decompose_rz,
        decompose_cz,
        rz_epsilon,
        parallel,
        passes,
        fixpoint,
        optimization_level,
        superopt_qubits,
        superopt_window_gates,
        superopt_table_entries,
    }
}

fn main() {
    let start = Instant::now();
    let args: Vec<String> = env::args().collect();
    let opts = parse_args(&args);

    eprintln!("\x1b[1m⚡\u{FE0F} tzap\x1b[0m");
    let file_size = fs::metadata(&opts.input_path).map(|m| m.len()).unwrap_or(0);
    eprintln!(
        "  Parsing {} ({:.1} MB)",
        opts.input_path,
        file_size as f64 / (1024.0 * 1024.0)
    );

    let circuit = read_circuit(&opts.input_path);
    run_optimize(circuit, &opts, start);
}

#[cfg(test)]
mod tests {
    use super::*;
    use tzap::qasm;

    #[test]
    fn progress_box_grows_for_large_counts() {
        let rows = [(
            "2q gates",
            render_bar(1.0, BAR_WIDTH, TWO_QUBIT_BAR_COLOR),
            "↓0.0% · 1,234,567,890,123".to_string(),
        )];
        let lines = progress_box("Large counts", &rows);
        let width = lines[0].chars().count();
        let visible_row = lines[1]
            .replace("\x1b[33m", "")
            .replace("\x1b[0m\x1b[2m", "")
            .replace("\x1b[0m", "");

        assert_eq!(lines[2].chars().count(), width);
        assert!(width > 60);
        assert!(visible_row.contains("1,234,567,890,123"));
    }

    /// Parallel (map-reduce) optimization of a measured circuit must
    /// round-trip to valid QASM. Regression guard: the stitched
    /// reconstruction must use the circuit's `num_cbits` (not `Circuit::new`,
    /// which zeroes it and drops the `creg` declaration).
    #[test]
    fn parallel_mode_preserves_creg() {
        let mut c = Circuit::with_cbits(1, 1);
        c.apply(Gate::h(0));
        c.apply(Gate::measure { qubit: 0, cbit: 0 });

        let cancel = CancelGates;
        let par = run_map_reduce(&c, true, 4, |chunk, verbose| {
            run_pipeline(chunk, &[&cancel], verbose)
        });

        assert_eq!(
            par.num_cbits, 1,
            "parallel reconstruction must preserve num_cbits"
        );

        let out = qasm::serialize(&par);
        assert!(
            out.contains("creg"),
            "parallel output has measurements but no creg declaration:\n{out}"
        );
        assert!(
            qasm::parse(&out).is_ok(),
            "parallel output must round-trip to valid QASM:\n{out}"
        );
    }

    /// Optimizing an empty circuit in parallel must not panic. Regression guard:
    /// chunk_size must never be 0 (else `slice::chunks(0)` panics).
    #[test]
    fn parallel_mode_handles_empty_circuit() {
        let empty = Circuit::new(1);
        let out = run_map_reduce(&empty, true, 4, |chunk, verbose| {
            run_pipeline(chunk, &[], verbose)
        });
        assert!(out.gates.is_empty());
    }

    /// Each map-reduce chunk must get its own independent `SuperOpt`
    /// instance — the whole point of this design (no shared `MatrixStore`,
    /// no `Arc`, no cross-chunk locking). Regression guard: running the same
    /// SuperOpt-using pipeline on a circuit split into several chunks must
    /// not panic or deadlock, and must produce a valid, gate-count-bounded
    /// output (each chunk's `SuperOpt` instance only ever rewrites within
    /// its own chunk).
    #[test]
    fn parallel_mode_gives_each_chunk_its_own_superopt() {
        let mut c = Circuit::new(2);
        for _ in 0..8 {
            c.apply(Gate::h(0));
            c.apply(Gate::cnot {
                control: 0,
                target: 1,
            });
        }

        let opts = Opts {
            input_path: String::new(),
            output_path: None,
            expr: false,
            decompose_rz: false,
            decompose_cz: false,
            rz_epsilon: 1e-10,
            parallel: true,
            passes: None,
            fixpoint: false,
            optimization_level: Some(OptimizationLevel::O2),
            superopt_qubits: None,
            superopt_window_gates: None,
            superopt_table_entries: None,
        };

        let out = run_map_reduce(&c, true, 4, |chunk, verbose| {
            optimize_default(chunk, &opts, verbose)
        });
        assert!(out.gates.len() <= c.gates.len());
    }
}
