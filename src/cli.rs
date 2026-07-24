//! Command-line argument parsing, `Opts`, and `--help` text. The pass and
//! optimization-level enums, and everything they select, live in
//! `tzap::optimize` — this module only maps flags onto an
//! [`Options`](tzap::optimize::Options).

use std::process;

use tzap::optimize::{DEFAULT_RZ_EPSILON, Level, Options, PassName, SuperOptBounds};

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

/// Parsed command-line options: the file paths the CLI itself owns, plus the
/// optimizer configuration to hand to `tzap::optimize`.
pub(crate) struct Opts {
    pub(crate) input_path: String,
    pub(crate) output_path: Option<String>,
    pub(crate) options: Options,
}

/// Print `Error: {msg}` and exit 1. The single entry point for every
/// argument-parsing failure, so all CLI errors share one unmistakable
/// prefix instead of some being phrased as errors and others not.
pub(crate) fn arg_error(msg: impl std::fmt::Display) -> ! {
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

pub(crate) fn parse_args(args: &[String]) -> Opts {
    let mut input_path: Option<String> = None;
    let mut output_path: Option<String> = None;
    let mut expr = false;
    let mut decompose_rz = false;
    let mut decompose_cz = false;
    let mut rz_epsilon: f64 = DEFAULT_RZ_EPSILON;
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
                    "-O1" => Level::O1,
                    "-O2" => Level::O2,
                    "-O3" => Level::O3,
                    "-Osuper" => Level::Osuper,
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
    if passes.is_some() && (expr || decompose_rz || decompose_cz) {
        arg_error(
            "--passes cannot be combined with --decompose-rz, --decompose-cz, or --expr \
             — list DecomposeRz/DecomposeCz as pass names instead",
        );
    }
    Opts {
        input_path,
        output_path,
        // An absent `-O` flag means O3 too; the distinction only ever mattered
        // for the validation above, which has already run.
        options: Options {
            level: optimization_level.unwrap_or(Level::O3),
            passes,
            fixpoint,
            decompose_rz,
            decompose_cz,
            rz_epsilon,
            expr,
            parallel,
            // Hidden (undocumented in `--help`) bounds overrides; `None` means
            // "use whichever preset the optimization level implies".
            superopt: SuperOptBounds {
                qubits: superopt_qubits,
                window_gates: superopt_window_gates,
                table_entries: superopt_table_entries,
            },
        },
    }
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
    println!("                     (see PASSES). Excludes --decompose-rz and");
    println!("                     --decompose-cz — list DecomposeRz/DecomposeCz as pass");
    println!("                     names instead. --epsilon still configures DecomposeRz.");
    println!(
        "    \x1b[1m--fixpoint\x1b[0m       Repeat the pipeline until gate count stops decreasing"
    );
    println!("    \x1b[1m-O1\x1b[0m              Fastest: phase folding + gate cancellation only");
    println!("    \x1b[1m-O2\x1b[0m              Adds a superoptimization pass to O1 (2 rounds)");
    println!(
        "    \x1b[1m-O3\x1b[0m              Like -O2, run to a fixpoint instead of 2 rounds (default)"
    );
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
