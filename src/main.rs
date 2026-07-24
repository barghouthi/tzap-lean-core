use std::env;
use std::fs;
use std::process;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use rayon::prelude::*;

use tzap::cancel::CancelGates;
use tzap::circuit::{Circuit, Gate};
use tzap::decompose::{DecomposeCz, DecomposeRz, DecomposeToffoli};
use tzap::pass::{Pass, count_2q, count_rz, count_t, depth};
use tzap::phase_fold_global_expr::PhaseFoldGlobalExpr;
use tzap::phase_fold_rand::PhaseFoldRand;
use tzap::super_opt::{SuperOpt, SuperOptTableConfig, table_cache_size_bytes, table_is_cached};

mod cli;
mod progress;

use cli::{OptimizationLevel, Opts, PassName, arg_error, parse_args};
use progress::{
    box_lines, end_progress_block, finish_inline, fmt_num, print_result, start_inline,
    start_progress_block, update_chunk_progress, update_fixpoint_progress,
    update_reduction_progress,
};

/// Map-reduce chunks per logical core. Deliberately more than one thread per
/// core (see [`num_threads`]): chunks cost varies (some hit more SuperOpt
/// rewrites than others), so more chunks than threads lets rayon's
/// work-stealing load-balance that unevenness across a right-sized pool.
const CHUNK_MULTIPLIER: usize = 2;

/// Default SuperOpt window/table bounds, overridable by the hidden
/// `--superopt-*` flags (see `cli::parse_args`). Not exposed in `--help`:
/// these exist for experimentation, not everyday use.
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
/// separator line — this and the SuperOpt table-build message each own a
/// trailing blank line, so a live progress box that follows never needs to
/// print one itself. [`read_circuit`] deliberately does *not* trail with a
/// blank: it should stay flush with whatever comes right after it, whether
/// that's this, the table message, or a box directly.
fn run_logged(pass: &dyn Pass, circuit: &Circuit) -> Circuit {
    let start = Instant::now();
    let c = pass.run(circuit);
    let rz = count_rz(&c);
    let rz_report = (rz > 0).then(|| format!(" · {} Rz", fmt_num(rz)));
    eprintln!(
        "  {}\n\t└─ {} gates · {} 2q gates · {} T{} · {} depth · {:.3}s",
        pass.name(),
        fmt_num(c.gates.len()),
        fmt_num(count_2q(&c)),
        fmt_num(count_t(&c)),
        rz_report.as_deref().unwrap_or(""),
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
    let baseline_rz = count_rz(circuit);
    let mut c = circuit.clone();
    if verbose {
        start_progress_block(box_lines(if baseline_rz > 0 { 5 } else { 4 }));
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
            count_rz(&c),
            baseline_rz,
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
                count_rz(&c),
                baseline_rz,
            );
        }
    }
    if verbose {
        end_progress_block(box_lines(if baseline_rz > 0 { 5 } else { 4 }));
    }
    c
}

/// Run one fixpoint sweep over `circuit`. When `verbose`, redraws the live
/// progress box with the most recent counts as each pass completes.
#[allow(clippy::too_many_arguments)]
fn run_fixpoint_sweep(
    circuit: &Circuit,
    passes: &[&dyn Pass],
    iteration: usize,
    verbose: bool,
    baseline_gates: usize,
    baseline_2q: usize,
    baseline_depth: usize,
    baseline_t: usize,
    baseline_rz: usize,
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
            count_rz(&c),
            baseline_rz,
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
                count_rz(&c),
                baseline_rz,
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
    let baseline_rz = count_rz(circuit);
    let mut c = circuit.clone();
    let mut round = 0;
    let mut reduced;
    if verbose {
        start_progress_block(box_lines(if baseline_rz > 0 { 5 } else { 4 }));
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
            baseline_rz,
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
                    count_rz(&c),
                    baseline_rz,
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
        end_progress_block(box_lines(if baseline_rz > 0 { 5 } else { 4 }));
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
    // Captured once, before the build/load below can create the cache file
    // (which would make a second `table_is_cached` call always say "cached").
    let cached = verbose && table_is_cached(table_config);
    if verbose {
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
    let start = Instant::now();
    let pass = SuperOpt::new(qubits, window_gates, table_config)
        .unwrap_or_else(|error| arg_error(format!("failed to initialize SuperOpt: {error}")));
    if verbose {
        let size = table_cache_size_bytes(table_config)
            .map(|bytes| format!(" ({:.1} MB)", bytes as f64 / (1024.0 * 1024.0)))
            .unwrap_or_default();
        let message = format!(
            "  Loaded minimal unitary representatives{size} in {:.3}s",
            start.elapsed().as_secs_f64()
        );
        if cached {
            finish_inline(&message);
        } else {
            eprintln!("{message}");
        }
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
        count_rz(input),
        count_rz(result),
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
    let baseline_rz = count_rz(circuit);
    let progress_chunks = Arc::new(Mutex::new(chunks.clone()));
    let done = AtomicUsize::new(0);
    let sum_before_gates = AtomicUsize::new(0);
    let sum_after_gates = AtomicUsize::new(0);
    let sum_before_t = AtomicUsize::new(0);
    let sum_after_t = AtomicUsize::new(0);
    let sum_before_rz = AtomicUsize::new(0);
    let sum_after_rz = AtomicUsize::new(0);

    start_progress_block(box_lines(if baseline_rz > 0 { 6 } else { 5 }));
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
        baseline_rz,
        baseline_rz,
    );
    let optimized: Vec<Circuit> = chunks
        .par_iter()
        .enumerate()
        .map(|(chunk_index, chunk)| {
            let before_gates = chunk.gates.len();
            let before_t = count_t(chunk);
            let before_rz = count_rz(chunk);
            let result = optimize(chunk, false);
            let after_gates = result.gates.len();
            let after_t = count_t(&result);
            let after_rz = count_rz(&result);

            let n = done.fetch_add(1, Ordering::Relaxed) + 1;
            let sum_before_gates =
                sum_before_gates.fetch_add(before_gates, Ordering::Relaxed) + before_gates;
            let sum_after_gates =
                sum_after_gates.fetch_add(after_gates, Ordering::Relaxed) + after_gates;
            let sum_before_t = sum_before_t.fetch_add(before_t, Ordering::Relaxed) + before_t;
            let sum_after_t = sum_after_t.fetch_add(after_t, Ordering::Relaxed) + after_t;
            let sum_before_rz = sum_before_rz.fetch_add(before_rz, Ordering::Relaxed) + before_rz;
            let sum_after_rz = sum_after_rz.fetch_add(after_rz, Ordering::Relaxed) + after_rz;

            let current_gates = baseline_gates - sum_before_gates + sum_after_gates;
            let current_t = baseline_t - sum_before_t + sum_after_t;
            let current_rz = baseline_rz - sum_before_rz + sum_after_rz;
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
                baseline_rz,
                current_rz,
            );
            result
        })
        .collect();
    end_progress_block(box_lines(if baseline_rz > 0 { 6 } else { 5 }));
    stitch(circuit.num_qubits, circuit.num_cbits, &optimized)
}

/// Run the explicit `--passes` pipeline on `circuit`, constructing a fresh
/// `SuperOpt` if it's selected. Used as one map-reduce worker per chunk.
fn optimize_explicit(circuit: &Circuit, opts: &Opts, verbose: bool) -> Circuit {
    let names = opts
        .passes
        .as_ref()
        .expect("only called when --passes is set");
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

    let optimization_level = opts.optimization_level.unwrap_or(OptimizationLevel::O3);
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
    let circuit = if opts.decompose_cz && circuit.gates.iter().any(|g| matches!(g, Gate::cz { .. }))
    {
        run_logged(&decompose_cz, &circuit)
    } else {
        circuit
    };

    let optimization_level = opts.optimization_level.unwrap_or(OptimizationLevel::O3);
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

fn main() {
    let start = Instant::now();
    let args: Vec<String> = env::args().collect();
    let opts = parse_args(&args);

    eprintln!(
        "\x1b[1m⚡\u{FE0F} tzap\x1b[0m  \x1b[2mv{}\x1b[0m",
        env!("CARGO_PKG_VERSION")
    );

    let circuit = read_circuit(&opts.input_path);
    run_optimize(circuit, &opts, start);
}

#[cfg(test)]
mod tests {
    use super::*;
    use tzap::qasm;

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
