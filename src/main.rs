use std::env;
use std::fs;
use std::io::{self, Write};
use std::process;
use std::time::{Duration, Instant};

use rayon::prelude::*;

use tzap::cancel::CancelGates;
use tzap::circuit::{Circuit, Gate};
use tzap::decompose::{DecomposeCz, DecomposeRz, DecomposeToffoli};
use tzap::pass::{Pass, count_t};
use tzap::phase_fold_global_expr::PhaseFoldGlobalExpr;
use tzap::phase_fold_rand::PhaseFoldRand;
use tzap::super_opt::{SuperOpt, SuperOptTableConfig};

/// Chunks (and rayon threads) per logical core.
const CHUNK_MULTIPLIER: usize = 4;

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
                eprintln!(
                    "Unknown pass '{name}'. Available passes: {}",
                    PassName::all_names()
                );
                process::exit(1);
            })
        })
        .collect::<Vec<_>>();

    if parsed.is_empty() {
        eprintln!("--passes requires at least one pass name");
        process::exit(1);
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

/// Parsed command-line options.
struct Opts {
    input_path: String,
    output_path: Option<String>,
    expr: bool,
    decompose_rz: bool,
    rz_epsilon: f64,
    parallel: bool,
    /// Explicit pass pipeline from `--passes` (overrides the default pipeline).
    passes: Option<Vec<PassName>>,
    /// Re-run the optimization pipeline until gate count stops decreasing.
    fixpoint: bool,
    /// Explicit optimization level. Absence also uses O1, but keeps custom
    /// `--passes` and `--fixpoint` available.
    optimization_level: Option<OptimizationLevel>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum OptimizationLevel {
    O1,
    O2,
    O3,
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

/// Number of parallel chunks / rayon threads to use.
fn num_par_chunks() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get() * CHUNK_MULTIPLIER)
        .unwrap_or(8)
}

/// Build the global rayon pool. A no-op if already built (it is process-global).
fn init_global_pool(num_threads: usize) {
    rayon::ThreadPoolBuilder::new()
        .num_threads(num_threads)
        .build_global()
        .ok();
}

/// The optimization passes: gate cancellation followed by phase folding
/// (expr-based when `expr` is set). Borrows the (stateless) pass values, which
/// must outlive the returned slice.
fn build_passes<'a>(
    cancel_pass: &'a CancelGates,
    global: &'a PhaseFoldRand,
    global_expr: &'a PhaseFoldGlobalExpr,
    expr: bool,
) -> Vec<&'a dyn Pass> {
    let phase_fold: &dyn Pass = if expr { global_expr } else { global };
    vec![cancel_pass, phase_fold]
}

/// Run one pass with timing and a result line. Returns the transformed circuit
/// and how long the pass took. `indent` is prepended to every log line so the
/// caller can nest output under a header.
fn run_logged(pass: &dyn Pass, circuit: &Circuit, indent: &str) -> (Circuit, Duration) {
    let start = Instant::now();
    let c = pass.run(circuit);
    let elapsed = start.elapsed();
    eprintln!(
        "{indent}  {}\n{indent}\t└─ {} gates · {} T · {:.3}s",
        pass.name(),
        fmt_num(c.gates.len()),
        fmt_num(count_t(&c)),
        elapsed.as_secs_f64()
    );
    (c, elapsed)
}

/// Split a circuit into `num_chunks` ordered slices, each its own `Circuit`.
/// `max(1)` guards the empty case where `slice::chunks(0)` would panic.
fn split_chunks(circuit: &Circuit, num_chunks: usize) -> Vec<Circuit> {
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

/// Run each pass across all chunks in parallel, with per-pass logging.
/// Returns the result and the total pass time.
fn run_passes_parallel_logged(
    circuit: &Circuit,
    passes: &[&dyn Pass],
    num_chunks: usize,
    indent: &str,
) -> (Circuit, Duration) {
    let mut chunks = split_chunks(circuit, num_chunks);
    let mut total = Duration::ZERO;
    for p in passes {
        let start = Instant::now();
        chunks = chunks.par_iter().map(|chunk| p.run(chunk)).collect();
        let elapsed = start.elapsed();
        total += elapsed;

        let gates: usize = chunks.iter().map(|c| c.gates.len()).sum();
        let t: usize = chunks.iter().map(count_t).sum();
        eprintln!(
            "{indent}  {}\n{indent}\t└─ {} gates · {} T · {:.3}s",
            p.name(),
            fmt_num(gates),
            fmt_num(t),
            elapsed.as_secs_f64()
        );
    }
    (
        stitch(circuit.num_qubits, circuit.num_cbits, &chunks),
        total,
    )
}

/// Print the closing result banner.
fn print_result(in_gates: usize, out_gates: usize, in_t: usize, out_t: usize, secs: f64) {
    eprintln!("\n\x1b[1m  ⚡\u{FE0F} Result\x1b[0m");
    eprintln!(
        "\t├─ Gates  {} → {} (↓{:.1}%)",
        fmt_num(in_gates),
        fmt_num(out_gates),
        pct(in_gates, out_gates)
    );
    eprintln!(
        "\t├─ T/Tdg  {} → {} (↓{:.1}%)",
        fmt_num(in_t),
        fmt_num(out_t),
        pct(in_t, out_t)
    );
    eprintln!("\t└─ Time   {secs:.3}s");
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
        "\t└─ {} qubits · {} gates · {} T/Tdg · {:.3}s\n",
        fmt_num(circuit.num_qubits),
        fmt_num(circuit.gates.len()),
        fmt_num(count_t(&circuit)),
        parse_start.elapsed().as_secs_f64()
    );
    circuit
}

/// Run a pass pipeline (parallel chunked or sequential), with per-pass logging.
/// Returns the result and the total pass time.
fn run_pipeline(
    circuit: &Circuit,
    passes: &[&dyn Pass],
    parallel: bool,
    num_chunks: usize,
    indent: &str,
) -> (Circuit, Duration) {
    if parallel {
        eprintln!(
            "{indent}  Parallel mode: {} chunks / {} threads\n",
            fmt_num(num_chunks),
            fmt_num(rayon::current_num_threads())
        );
        run_passes_parallel_logged(circuit, passes, num_chunks, indent)
    } else {
        let mut c = circuit.clone();
        let mut total = Duration::ZERO;
        for p in passes {
            let (next, elapsed) = run_logged(*p, &c, indent);
            c = next;
            total += elapsed;
        }
        (c, total)
    }
}

/// Replace the current progress line with the latest fixpoint state.
fn update_fixpoint_progress(iteration: usize, gates: usize, t_count: usize) {
    eprint!(
        "\r\x1b[2K  Iteration {} · {} gates · {} T",
        fmt_num(iteration),
        fmt_num(gates),
        fmt_num(t_count)
    );
    let _ = io::stderr().flush();
}

/// Run one fixpoint sweep without per-pass logs, updating a single progress
/// line with the most recent counts as each pass completes.
fn run_fixpoint_sweep(
    circuit: &Circuit,
    passes: &[&dyn Pass],
    parallel: bool,
    num_chunks: usize,
    iteration: usize,
) -> (Circuit, Duration) {
    update_fixpoint_progress(iteration, circuit.gates.len(), count_t(circuit));

    if parallel {
        let mut chunks = split_chunks(circuit, num_chunks);
        let mut total = Duration::ZERO;
        for pass in passes {
            let start = Instant::now();
            chunks = chunks.par_iter().map(|chunk| pass.run(chunk)).collect();
            total += start.elapsed();
            update_fixpoint_progress(
                iteration,
                chunks.iter().map(|chunk| chunk.gates.len()).sum(),
                chunks.iter().map(count_t).sum(),
            );
        }
        (
            stitch(circuit.num_qubits, circuit.num_cbits, &chunks),
            total,
        )
    } else {
        let mut c = circuit.clone();
        let mut total = Duration::ZERO;
        for pass in passes {
            let start = Instant::now();
            c = pass.run(&c);
            total += start.elapsed();
            update_fixpoint_progress(iteration, c.gates.len(), count_t(&c));
        }
        (c, total)
    }
}

/// Repeatedly run `passes` until a sweep fails to reduce the gate count.
/// Returns the result, total pass time, and how many sweeps ran.
fn run_to_fixpoint(
    circuit: &Circuit,
    passes: &[&dyn Pass],
    parallel: bool,
    num_chunks: usize,
) -> (Circuit, Duration, usize) {
    let mut c = circuit.clone();
    let mut total = Duration::ZERO;
    let mut round = 0;
    loop {
        round += 1;
        let before = c.gates.len();
        let (next, elapsed) = run_fixpoint_sweep(&c, passes, parallel, num_chunks, round);
        c = next;
        total += elapsed;
        if c.gates.len() >= before {
            break;
        }
    }
    eprintln!();
    (c, total, round)
}

/// Run the O3 optimization pipeline to a fixpoint. When Rz decomposition
/// is requested, insert it exactly once after the first optimization sweep and
/// force another sweep when there were Rz gates to decompose.
fn run_o3_to_fixpoint(
    circuit: &Circuit,
    passes: &[&dyn Pass],
    rz_decompose: Option<&dyn Pass>,
    parallel: bool,
    num_chunks: usize,
) -> (Circuit, Duration, usize) {
    let mut c = circuit.clone();
    let mut total = Duration::ZERO;
    let mut round = 0;
    loop {
        round += 1;
        let before = c.gates.len();
        let (next, elapsed) = run_fixpoint_sweep(&c, passes, parallel, num_chunks, round);
        let reduced = next.gates.len() < before;
        c = next;
        total += elapsed;

        if round == 1
            && let Some(pass) = rz_decompose
        {
            let had_rz = c.gates.iter().any(|g| matches!(g, Gate::rz(..)));
            let start = Instant::now();
            c = pass.run(&c);
            total += start.elapsed();
            update_fixpoint_progress(round, c.gates.len(), count_t(&c));
            if had_rz {
                continue;
            }
        }

        if !reduced {
            break;
        }
    }
    eprintln!();
    (c, total, round)
}

fn initialize_superopt() -> SuperOpt {
    let start = Instant::now();
    let pass = SuperOpt::new(3, 10, SuperOptTableConfig::default()).unwrap_or_else(|error| {
        eprintln!("Failed to initialize SuperOpt: {error}");
        process::exit(1);
    });
    eprintln!(
        "  Initialized SuperOpt table in {:.3}s",
        start.elapsed().as_secs_f64()
    );
    pass.without_subcircuits()
}

/// Default pipeline: decompose ccx/ccz (and optionally Rz), then cancel + phase-fold.
/// `--passes` overrides this with an explicit, user-ordered pipeline.
fn run_optimize(circuit: Circuit, opts: &Opts) {
    let parallel = opts.parallel;
    let num_chunks = num_par_chunks();

    let decompose_toffoli = DecomposeToffoli;
    let decompose_cz = DecomposeCz;
    let rz_decompose = DecomposeRz {
        epsilon: opts.rz_epsilon,
    };
    let cancel_pass = CancelGates;
    let global = PhaseFoldRand;
    let global_expr = PhaseFoldGlobalExpr;

    // Explicit pipeline via --passes: run exactly what the user listed, in order.
    if let Some(names) = &opts.passes {
        let uses_rz = names.iter().any(|p| matches!(p, PassName::DecomposeRz));
        let uses_superopt = names.iter().any(|p| matches!(p, PassName::SuperOpt));
        if parallel || uses_rz {
            init_global_pool(num_chunks);
        }
        let superopt_pass = if uses_superopt {
            Some(initialize_superopt())
        } else {
            None
        };
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
        let baseline_gates = circuit.gates.len();
        let baseline_t = count_t(&circuit);
        let (result, total) = if opts.fixpoint {
            let (r, t, rounds) = run_to_fixpoint(&circuit, &passes, parallel, num_chunks);
            eprintln!("  Fixpoint reached after {rounds} iteration(s)");
            (r, t)
        } else {
            run_pipeline(&circuit, &passes, parallel, num_chunks, "")
        };
        print_result(
            baseline_gates,
            result.gates.len(),
            baseline_t,
            count_t(&result),
            total.as_secs_f64(),
        );
        write_output(&opts.output_path, &result);
        return;
    }

    if parallel || opts.decompose_rz {
        init_global_pool(num_chunks);
    }

    // Decompose CCX/CCZ eagerly so post-decomp counts form the baseline.
    let circuit = if circuit.has_toffoli || circuit.has_ccz {
        run_logged(&decompose_toffoli, &circuit, "").0
    } else {
        circuit
    };

    let baseline_gates = circuit.gates.len();
    let baseline_t = count_t(&circuit);

    let optimization_level = opts.optimization_level.unwrap_or(OptimizationLevel::O1);
    let (result, total_pass_time) = if optimization_level == OptimizationLevel::O3 {
        let superopt_pass = initialize_superopt();
        let passes: Vec<&dyn Pass> = vec![&cancel_pass, &superopt_pass, &global];
        let decompose: Option<&dyn Pass> = opts.decompose_rz.then_some(&rz_decompose);
        let (r, t, rounds) = run_o3_to_fixpoint(&circuit, &passes, decompose, parallel, num_chunks);
        eprintln!("  Fixpoint reached after {rounds} iteration(s)");
        (r, t)
    } else {
        let superopt_pass = (optimization_level == OptimizationLevel::O2).then(initialize_superopt);
        let mut optimization_passes = build_passes(&cancel_pass, &global, &global_expr, opts.expr);
        if let Some(pass) = &superopt_pass {
            optimization_passes.insert(1, pass);
        }

        // Optimize, then (for --decompose-rz) decompose Rz and optimize the result
        // again — so the selected optimization pipeline runs on both sides of gridsynth.
        let mut passes = optimization_passes.clone();
        if opts.decompose_rz && circuit.gates.iter().any(|g| matches!(g, Gate::rz(..))) {
            passes.push(&rz_decompose);
            passes.extend(optimization_passes);
        }

        if opts.fixpoint {
            let (r, t, rounds) = run_to_fixpoint(&circuit, &passes, parallel, num_chunks);
            eprintln!("  Fixpoint reached after {rounds} iteration(s)");
            (r, t)
        } else {
            run_pipeline(&circuit, &passes, parallel, num_chunks, "")
        }
    };

    print_result(
        baseline_gates,
        result.gates.len(),
        baseline_t,
        count_t(&result),
        total_pass_time.as_secs_f64(),
    );

    let input_has_rz = circuit.gates.iter().any(|g| matches!(g, Gate::rz(..)));
    let output_has_rz = result.gates.iter().any(|g| matches!(g, Gate::rz(..)));
    if output_has_rz && !input_has_rz {
        panic!("BUG: output contains Rz gates but input did not");
    }
    if output_has_rz && opts.decompose_rz {
        panic!("BUG: output contains Rz gates after --decompose-rz");
    }

    write_output(&opts.output_path, &result);
}

fn print_help() {
    println!();
    println!("  \x1b[1m⚡\u{FE0F} tzap\x1b[0m  —  fast quantum circuit optimizer");
    println!();
    println!("  Decomposes Toffoli (ccx) gates into Clifford+T by default.");
    println!("  Pass --decompose-rz to also decompose Rz gates via gridsynth.");
    println!();
    println!("  \x1b[1;33mUSAGE\x1b[0m");
    println!("    tzap <input.qasm> [output.qasm] [options]");
    println!();
    println!("  \x1b[1;33mARGS\x1b[0m");
    println!("    \x1b[1m<input.qasm>\x1b[0m     Input OpenQASM 2.0 file");
    println!("    \x1b[1m[output.qasm]\x1b[0m    Output file (no output if omitted)");
    println!();
    println!("  \x1b[1;33mOPTIONS\x1b[0m");
    println!("    \x1b[1m-o\x1b[0m <file>        Write output to <file>");
    println!("    \x1b[1m--decompose-rz\x1b[0m   Decompose Rz gates into Clifford+T (gridsynth)");
    println!(
        "    \x1b[1m--epsilon\x1b[0m <eps>  Approximation epsilon for --decompose-rz (default: 1e-10)"
    );
    println!("    \x1b[1m--parallel\x1b[0m       Enable parallel mode (off by default)");
    println!(
        "    \x1b[1m--passes\x1b[0m <list>  Run these passes in order, overriding the default pipeline"
    );
    println!("                     (see PASSES). Excludes --decompose-rz; --epsilon still");
    println!("                     configures DecomposeRz.");
    println!(
        "    \x1b[1m--fixpoint\x1b[0m       Repeat the pipeline until gate count stops decreasing"
    );
    println!("    \x1b[1m-O1\x1b[0m              Default, fast optimization pass schedule");
    println!("    \x1b[1m-O2\x1b[0m              Adds a superoptimization pass to O1");
    println!("    \x1b[1m-O3\x1b[0m              Runs O2 iteratively until a fixpoint is reached");
    println!("    \x1b[1m-h, --help\x1b[0m       Print this help message");
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

fn parse_args(args: &[String]) -> Opts {
    let mut input_path: Option<String> = None;
    let mut output_path: Option<String> = None;
    let mut expr = false;
    let mut decompose_rz = false;
    let mut rz_epsilon: f64 = 1e-10;
    let mut parallel = false;
    let mut passes: Option<Vec<PassName>> = None;
    let mut fixpoint = false;
    let mut optimization_level = None;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--help" | "-h" => {
                print_help();
                process::exit(0);
            }
            "--expr" => expr = true,
            "--decompose-rz" => decompose_rz = true,
            "--epsilon" => {
                i += 1;
                rz_epsilon = args.get(i).and_then(|s| s.parse().ok()).unwrap_or_else(|| {
                    eprintln!("--epsilon requires a number (e.g. 1e-10)");
                    process::exit(1);
                });
            }
            "--passes" => {
                i += 1;
                let list = args.get(i).unwrap_or_else(|| {
                    eprintln!("--passes requires a comma-separated list of pass names");
                    process::exit(1);
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
            "-O1" | "-O2" | "-O3" => {
                if optimization_level.is_some() {
                    eprintln!("-O1, -O2, and -O3 cannot be combined");
                    process::exit(1);
                }
                optimization_level = Some(match args[i].as_str() {
                    "-O1" => OptimizationLevel::O1,
                    "-O2" => OptimizationLevel::O2,
                    "-O3" => OptimizationLevel::O3,
                    _ => unreachable!(),
                });
            }
            "-o" => {
                i += 1;
                output_path = args.get(i).cloned();
            }
            _ if args[i].starts_with('-') => {
                eprintln!("Unknown flag: {}", args[i]);
                process::exit(1);
            }
            _ => {
                if input_path.is_none() {
                    input_path = Some(args[i].clone());
                } else if output_path.is_none() {
                    output_path = Some(args[i].clone());
                }
            }
        }
        i += 1;
    }

    let Some(input_path) = input_path else {
        eprintln!(
            "\x1b[1m⚡\u{FE0F} tzap\x1b[0m <input.qasm> [-o output.qasm] [-O1|-O2|-O3] [--decompose-rz] [--expr] [--passes <list>] [--parallel] [--fixpoint]"
        );
        process::exit(1);
    };

    if optimization_level.is_some() && (passes.is_some() || fixpoint) {
        eprintln!("-O1, -O2, and -O3 cannot be combined with --passes or --fixpoint");
        process::exit(1);
    }
    if passes.is_some() && (expr || decompose_rz) {
        eprintln!("--passes cannot be combined with --decompose-rz or --expr");
        process::exit(1);
    }
    Opts {
        input_path,
        output_path,
        expr,
        decompose_rz,
        rz_epsilon,
        parallel,
        passes,
        fixpoint,
        optimization_level,
    }
}

fn main() {
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
    run_optimize(circuit, &opts);
}

#[cfg(test)]
mod tests {
    use super::*;
    use tzap::qasm;

    /// Parallel optimization of a measured circuit must round-trip to valid
    /// QASM. Regression guard: the parallel reconstruction must build chunks and
    /// the stitched result with the circuit's `num_cbits` (not `Circuit::new`,
    /// which zeroes it and drops the `creg` declaration).
    #[test]
    fn parallel_mode_preserves_creg() {
        let mut c = Circuit::with_cbits(1, 1);
        c.apply(Gate::h(0));
        c.apply(Gate::measure { qubit: 0, cbit: 0 });

        let cancel = CancelGates;
        let passes: Vec<&dyn Pass> = vec![&cancel];
        let par = run_passes_parallel_logged(&c, &passes, 4, "").0;

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
        let passes: Vec<&dyn Pass> = vec![];
        let out = run_passes_parallel_logged(&empty, &passes, 4, "").0;
        assert!(out.gates.is_empty());
    }
}
