//! The optimization driver: optimization levels, pass pipelines, the fixpoint
//! loop, `SuperOpt` construction, and map-reduce parallelism.
//!
//! This is everything the `tzap` binary used to own itself, so that every
//! frontend — the CLI, a Rust caller, a language binding — runs the exact same
//! pipeline rather than reimplementing `-O3`. The CLI keeps only argument
//! parsing, file I/O, and terminal rendering; it plugs the latter in through
//! [`Observer`].

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use rayon::prelude::*;

use crate::cancel::CancelGates;
use crate::circuit::{Circuit, Gate};
use crate::decompose::{DecomposeCz, DecomposeRz, DecomposeToffoli};
use crate::pass::{Pass, count_2q, count_rz, count_t, depth};
use crate::phase_fold_global_expr::PhaseFoldGlobalExpr;
use crate::phase_fold_rand::PhaseFoldRand;
use crate::super_opt::{
    SuperOpt, SuperOptError, SuperOptTableConfig, table_cache_size_bytes, table_is_cached,
};

/// Map-reduce chunks per logical core. Deliberately more than one thread per
/// core (see [`num_threads`]): chunks cost varies (some hit more SuperOpt
/// rewrites than others), so more chunks than threads lets rayon's
/// work-stealing load-balance that unevenness across a right-sized pool.
const CHUNK_MULTIPLIER: usize = 2;

/// Default approximation epsilon for [`Options::rz_epsilon`].
pub const DEFAULT_RZ_EPSILON: f64 = 1e-10;

/// Default SuperOpt window/table bounds, overridable per-run via
/// [`SuperOptBounds`].
///
/// The window and table share both a qubit bound and a gate-count bound: the
/// [`SuperOpt`] pass itself allows window and table bounds to differ on either
/// axis (e.g. a window wider or deeper than the table backing it, to exercise
/// window mechanics beyond what the table can synthesize replacements for —
/// see `super_opt::tests`), but the driver has no everyday use case for that,
/// so it only exposes one knob per axis.
///
/// `window_gates=10` leaves real T-count on the table suite-wide; the T
/// floor is reached by `window_gates≈15` and gate-count keeps improving
/// slowly beyond that, so 25 is used as a deliberately more thorough
/// default. `qubits` and `table_entries` showed no benefit worth their
/// added cost at this tier and were left alone.
pub const DEFAULT_SUPEROPT_QUBITS: usize = 3;
/// See [`DEFAULT_SUPEROPT_QUBITS`].
pub const DEFAULT_SUPEROPT_WINDOW_GATES: usize = 25;
/// See [`DEFAULT_SUPEROPT_QUBITS`].
pub const DEFAULT_SUPEROPT_TABLE_ENTRIES: usize = 200_000;

/// SuperOpt bounds for [`Level::Osuper`]: a materially bigger window/table
/// than the default. Confirmed (by direct comparison against
/// `DEFAULT_SUPEROPT_*` across the full feynman+cobble benchmark suite) to be
/// a real, zero-regression improvement — concentrated in circuits with long
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
pub const SUPER_SUPEROPT_QUBITS: usize = 5;
/// See [`SUPER_SUPEROPT_QUBITS`].
pub const SUPER_SUPEROPT_WINDOW_GATES: usize = 40;
/// See [`SUPER_SUPEROPT_QUBITS`].
pub const SUPER_SUPEROPT_TABLE_ENTRIES: usize = 5_000_000;

/// An optimization level: which default pipeline [`optimize`] runs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Level {
    /// Randomized phase folding + gate cancellation. Fastest.
    O1,
    /// Adds a SuperOpt pass to [`Level::O1`], capped at 2 rounds rather than
    /// run to a true fixpoint — see `optimize_default`'s `max_rounds`.
    O2,
    /// Like [`Level::O2`], but run to a true fixpoint instead of capped at 2
    /// rounds. The default.
    O3,
    /// Like [`Level::O3`], but with the `SUPER_SUPEROPT_*` bounds.
    Osuper,
}

/// A pass selectable by name in [`Options::passes`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PassName {
    DecomposeToffoli,
    DecomposeCz,
    DecomposeRz,
    CancelGates,
    SuperOpt,
    PhaseFoldRand,
    PhaseFoldGlobalExpr,
}

impl PassName {
    /// All passes — `(name, variant, description)` — in a stable order
    /// suitable for listing to a user.
    pub const ALL: [(&'static str, PassName, &'static str); 7] = [
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

    /// Look up a pass by its exact name, as listed in [`PassName::ALL`].
    pub fn parse(s: &str) -> Option<PassName> {
        Self::ALL
            .iter()
            .find(|(n, _, _)| *n == s)
            .map(|(_, p, _)| *p)
    }

    /// Comma-separated list of every valid name (for help / error messages).
    pub fn all_names() -> String {
        Self::ALL
            .iter()
            .map(|(n, _, _)| *n)
            .collect::<Vec<_>>()
            .join(", ")
    }
}

/// Per-run overrides for the SuperOpt window/table bounds. `None` means "use
/// whichever preset the optimization level implies" (`DEFAULT_SUPEROPT_*`, or
/// `SUPER_SUPEROPT_*` under [`Level::Osuper`]).
#[derive(Clone, Copy, Debug, Default)]
pub struct SuperOptBounds {
    pub qubits: Option<usize>,
    pub window_gates: Option<usize>,
    pub table_entries: Option<usize>,
}

/// Everything [`optimize`] needs to know about how to optimize a circuit.
///
/// `Default` is the CLI's default: `-O3`, sequential, no Rz/CZ decomposition.
#[derive(Clone, Debug)]
pub struct Options {
    /// Which default pipeline to run. Ignored when `passes` is set.
    pub level: Level,
    /// An explicit, ordered pass pipeline, replacing the `level` pipeline.
    pub passes: Option<Vec<PassName>>,
    /// Repeat the pipeline until the gate count stops decreasing. Only
    /// consulted for pipelines that aren't already a fixpoint loop (`passes`,
    /// or [`Level::O1`]).
    pub fixpoint: bool,
    /// Decompose Rz gates into Clifford+T via gridsynth.
    pub decompose_rz: bool,
    /// Decompose CZ gates into H+CX+H before optimizing.
    pub decompose_cz: bool,
    /// Approximation epsilon for `decompose_rz`.
    pub rz_epsilon: f64,
    /// Use the symbolic phase-folding pass instead of the randomized one.
    /// Only consulted under [`Level::O1`].
    pub expr: bool,
    /// Optimize gate-contiguous chunks of the circuit in parallel, then
    /// concatenate the results (see [`optimize`]).
    pub parallel: bool,
    /// SuperOpt window/table bounds.
    pub superopt: SuperOptBounds,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            level: Level::O3,
            passes: None,
            fixpoint: false,
            decompose_rz: false,
            decompose_cz: false,
            rz_epsilon: DEFAULT_RZ_EPSILON,
            expr: false,
            parallel: false,
            superopt: SuperOptBounds::default(),
        }
    }
}

/// The metrics tzap reports on a circuit, all counted in one place so callers
/// and progress renderers agree on what "2q gates" or "depth" means.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Metrics {
    pub gates: usize,
    pub two_qubit: usize,
    pub depth: usize,
    pub t: usize,
    pub rz: usize,
}

impl Metrics {
    pub fn of(circuit: &Circuit) -> Metrics {
        Metrics {
            gates: circuit.gates.len(),
            two_qubit: count_2q(circuit),
            depth: depth(circuit),
            t: count_t(circuit),
            rz: count_rz(circuit),
        }
    }
}

/// What [`optimize`] achieved.
#[derive(Clone, Copy, Debug)]
pub struct Report {
    /// The circuit as handed in.
    pub input: Metrics,
    /// The circuit after the eager ccx/ccz (and, under
    /// [`Options::decompose_cz`], cz) decomposition that precedes
    /// optimization — the baseline the optimization passes actually worked
    /// against, and so the honest comparison point for a reduction
    /// percentage. Equal to `input` when nothing needed decomposing.
    pub baseline: Metrics,
    /// The optimized circuit.
    pub output: Metrics,
}

/// Anything that can go wrong in [`optimize`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// The synthesis table backing [`PassName::SuperOpt`] could not be built.
    SuperOpt(SuperOptError),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::SuperOpt(error) => write!(f, "failed to initialize SuperOpt: {error}"),
        }
    }
}

impl std::error::Error for Error {}

impl From<SuperOptError> for Error {
    fn from(error: SuperOptError) -> Error {
        Error::SuperOpt(error)
    }
}

/// A sink for a run's progress events, so the driver can report what it's
/// doing without knowing anything about terminals. Every method defaults to
/// doing nothing; implement only the events you care about.
///
/// Events fire from whichever thread reached them: in a `parallel` run,
/// `chunk_done` is called concurrently from rayon workers, which is why an
/// `Observer` must be `Sync`. The chunk workers themselves are always
/// observed by [`Silent`] — their pipelines run concurrently, so their
/// progress events would interleave into garbage.
pub trait Observer: Sync {
    /// Whether this observer consumes the per-chunk events. When false (the
    /// default), a parallel run skips `chunks_start`/`chunk_done`/`chunks_end`
    /// *and* the whole-circuit stitch needed to compute their metrics — pure
    /// overhead for a run nobody is watching.
    fn tracks_chunks(&self) -> bool {
        false
    }

    /// A whole-circuit pass (the eager ccx/ccz or cz decomposition) finished.
    fn pass_done(&self, _name: &str, _result: &Circuit, _elapsed: Duration) {}

    /// The SuperOpt synthesis table is about to be loaded from disk
    /// (`cached`) or built from scratch.
    fn table_load_start(&self, _cached: bool) {}

    /// The SuperOpt synthesis table is ready, and now occupies `size_bytes`
    /// on disk.
    fn table_load_done(&self, _cached: bool, _size_bytes: Option<u64>, _elapsed: Duration) {}

    /// A pass pipeline is starting, against `baseline`. Paired with
    /// [`Observer::progress_end`].
    fn progress_start(&self, _baseline: Metrics) {}

    /// A pass within that pipeline finished. `round` is the (1-based)
    /// fixpoint iteration, or `None` for a pipeline that runs once.
    fn progress_update(&self, _round: Option<usize>, _current: &Circuit, _baseline: Metrics) {}

    /// The pipeline finished. Paired with [`Observer::progress_start`].
    fn progress_end(&self, _baseline: Metrics) {}

    /// The fixpoint driver stopped after `rounds` sweeps, either because a
    /// sweep stopped reducing the gate count (`reached_fixpoint`) or because
    /// it hit its round cap.
    fn fixpoint_done(&self, _rounds: usize, _reached_fixpoint: bool) {}

    /// A parallel run split the circuit into `total` chunks. Only called when
    /// [`Observer::tracks_chunks`] is true.
    fn chunks_start(&self, _total: usize, _baseline: Metrics) {}

    /// `done` of `total` chunks have been optimized; `current` is the whole
    /// circuit's metrics counting finished chunks as optimized and pending
    /// ones as-is. Only called when [`Observer::tracks_chunks`] is true.
    fn chunk_done(&self, _done: usize, _total: usize, _current: Metrics, _baseline: Metrics) {}

    /// Every chunk is done. Only called when [`Observer::tracks_chunks`] is
    /// true.
    fn chunks_end(&self, _baseline: Metrics) {}
}

/// The observer that reports nothing — what [`optimize`] uses, and what every
/// map-reduce chunk worker gets.
pub struct Silent;

impl Observer for Silent {}

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

/// Run one pass over the whole circuit, timed, reporting it as
/// [`Observer::pass_done`].
fn run_logged(pass: &dyn Pass, circuit: &Circuit, observer: &dyn Observer) -> Circuit {
    let start = Instant::now();
    let c = pass.run(circuit);
    observer.pass_done(pass.name(), &c, start.elapsed());
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

/// Run a pass pipeline once over `circuit`, in order, reporting each pass to
/// `observer` with no round number — unlike the fixpoint driver, this only
/// ever makes one pass over `passes`.
fn run_pipeline(circuit: &Circuit, passes: &[&dyn Pass], observer: &dyn Observer) -> Circuit {
    let baseline = Metrics::of(circuit);
    let mut c = circuit.clone();
    observer.progress_start(baseline);
    observer.progress_update(None, &c, baseline);
    for p in passes {
        c = p.run(&c);
        observer.progress_update(None, &c, baseline);
    }
    observer.progress_end(baseline);
    c
}

/// Run one fixpoint sweep over `circuit`, reporting each pass under
/// `iteration`.
fn run_fixpoint_sweep(
    circuit: &Circuit,
    passes: &[&dyn Pass],
    iteration: usize,
    observer: &dyn Observer,
    baseline: Metrics,
) -> Circuit {
    let mut c = circuit.clone();
    observer.progress_update(Some(iteration), &c, baseline);
    for pass in passes {
        c = pass.run(&c);
        observer.progress_update(Some(iteration), &c, baseline);
    }
    c
}

/// Repeatedly run `passes` until a sweep fails to reduce the gate count, or
/// (when `max_rounds` is given) until that many sweeps have run, whichever
/// comes first. When `rz_decompose` is given, run it exactly once after the
/// first sweep and force another sweep if there were Rz gates to decompose
/// — this extra sweep isn't itself subject to the `max_rounds` cap.
fn run_to_fixpoint(
    circuit: &Circuit,
    passes: &[&dyn Pass],
    rz_decompose: Option<&dyn Pass>,
    observer: &dyn Observer,
    max_rounds: Option<usize>,
) -> Circuit {
    let baseline = Metrics::of(circuit);
    let mut c = circuit.clone();
    let mut round = 0;
    let mut reduced;
    observer.progress_start(baseline);
    loop {
        round += 1;
        let before = c.gates.len();
        c = run_fixpoint_sweep(&c, passes, round, observer, baseline);
        reduced = c.gates.len() < before;

        if round == 1
            && let Some(pass) = rz_decompose
        {
            let had_rz = c.gates.iter().any(|g| matches!(g, Gate::rz(..)));
            c = pass.run(&c);
            observer.progress_update(Some(round), &c, baseline);
            if had_rz {
                continue;
            }
        }

        if !reduced || max_rounds.is_some_and(|m| round >= m) {
            break;
        }
    }
    observer.progress_end(baseline);
    observer.fixpoint_done(round, !reduced);
    c
}

/// Build a fresh `SuperOpt` instance. Callers must construct one of these
/// per map-reduce chunk (never share or reuse one instance across chunks):
/// each instance owns its own matrix cache and incremental-diff state, so a
/// fresh instance per chunk means `.incremental()` is always sound here —
/// every instance only ever sees successive versions of the one circuit it
/// was built for. `level` selects which bounds preset an unset
/// [`SuperOptBounds`] field falls back to — `SUPER_SUPEROPT_*` under
/// [`Level::Osuper`], `DEFAULT_SUPEROPT_*` otherwise.
fn initialize_superopt(
    options: &Options,
    level: Level,
    observer: &dyn Observer,
) -> Result<SuperOpt, Error> {
    let (default_qubits, default_window_gates, default_table_entries) = if level == Level::Osuper {
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
    let qubits = options.superopt.qubits.unwrap_or(default_qubits);
    let window_gates = options
        .superopt
        .window_gates
        .unwrap_or(default_window_gates);
    let table_entries = options
        .superopt
        .table_entries
        .unwrap_or(default_table_entries);

    // A table entry needs strictly fewer gates than the window it replaces
    // (see `ActiveWindow::consider`'s `local.len() >= gate_indices.len()`
    // rejection), and no window ever exceeds `window_gates`. So a stored
    // circuit at exactly `window_gates` depth could never be strictly
    // smaller than the largest possible window — `window_gates - 1` is the
    // deepest depth any table entry can ever be used at.
    let table_gates = window_gates.saturating_sub(1);
    let table_config = SuperOptTableConfig::new(qubits, table_gates, table_entries);
    // Captured before the build/load below can create the cache file (which
    // would make a second `table_is_cached` call always say "cached").
    let cached = table_is_cached(table_config);
    observer.table_load_start(cached);
    let start = Instant::now();
    let pass = SuperOpt::new(qubits, window_gates, table_config)?;
    observer.table_load_done(
        cached,
        table_cache_size_bytes(table_config),
        start.elapsed(),
    );
    Ok(pass.without_subcircuits().incremental())
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
    observer: &dyn Observer,
    optimize: impl Fn(&Circuit, &dyn Observer) -> Result<Circuit, Error> + Sync + Send,
) -> Result<Circuit, Error> {
    if !parallel {
        return optimize(circuit, observer);
    }
    let chunks = chunk_circuit(circuit, num_chunks);
    let total = chunks.len();
    let tracking = observer.tracks_chunks();

    // Whole-circuit baselines: pending chunks (not yet optimized) contribute
    // their original metrics, while completed chunks contribute their current
    // metrics.
    let baseline = Metrics::of(circuit);
    let progress_chunks = tracking.then(|| Arc::new(Mutex::new(chunks.clone())));
    let done = AtomicUsize::new(0);
    let sum_before_gates = AtomicUsize::new(0);
    let sum_after_gates = AtomicUsize::new(0);
    let sum_before_t = AtomicUsize::new(0);
    let sum_after_t = AtomicUsize::new(0);
    let sum_before_rz = AtomicUsize::new(0);
    let sum_after_rz = AtomicUsize::new(0);

    if tracking {
        observer.chunks_start(total, baseline);
    }
    let optimized: Vec<Result<Circuit, Error>> = chunks
        .par_iter()
        .enumerate()
        .map(|(chunk_index, chunk)| {
            let before_gates = chunk.gates.len();
            let before_t = count_t(chunk);
            let before_rz = count_rz(chunk);
            let result = optimize(chunk, &Silent)?;
            if !tracking {
                return Ok(result);
            }
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

            let current_gates = baseline.gates - sum_before_gates + sum_after_gates;
            let current_t = baseline.t - sum_before_t + sum_after_t;
            let current_rz = baseline.rz - sum_before_rz + sum_after_rz;
            let (current_2q, current_depth) = {
                let progress_chunks = progress_chunks
                    .as_ref()
                    .expect("allocated whenever `tracking`");
                let mut progress_chunks = progress_chunks.lock().unwrap();
                progress_chunks[chunk_index] = result.clone();
                let current = stitch(circuit.num_qubits, circuit.num_cbits, &progress_chunks);
                (count_2q(&current), depth(&current))
            };
            observer.chunk_done(
                n,
                total,
                Metrics {
                    gates: current_gates,
                    two_qubit: current_2q,
                    depth: current_depth,
                    t: current_t,
                    rz: current_rz,
                },
                baseline,
            );
            Ok(result)
        })
        .collect();
    if tracking {
        observer.chunks_end(baseline);
    }
    let optimized = optimized.into_iter().collect::<Result<Vec<_>, _>>()?;
    Ok(stitch(circuit.num_qubits, circuit.num_cbits, &optimized))
}

/// Run the explicit [`Options::passes`] pipeline on `circuit`, constructing a
/// fresh `SuperOpt` if it's selected. Used as one map-reduce worker per chunk.
fn optimize_explicit(
    circuit: &Circuit,
    options: &Options,
    observer: &dyn Observer,
) -> Result<Circuit, Error> {
    let names = options
        .passes
        .as_ref()
        .expect("only called when `passes` is set");
    let decompose_toffoli = DecomposeToffoli;
    let decompose_cz = DecomposeCz;
    let rz_decompose = DecomposeRz {
        epsilon: options.rz_epsilon,
    };
    let cancel_pass = CancelGates;
    let global = PhaseFoldRand;
    let global_expr = PhaseFoldGlobalExpr;

    let uses_superopt = names.iter().any(|p| matches!(p, PassName::SuperOpt));
    let superopt_pass = match uses_superopt {
        true => Some(initialize_superopt(options, Level::O1, observer)?),
        false => None,
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

    Ok(if options.fixpoint {
        run_to_fixpoint(circuit, &passes, None, observer, None)
    } else {
        run_pipeline(circuit, &passes, observer)
    })
}

/// Run the default pipeline for [`Options::level`] on `circuit`, constructing
/// a fresh `SuperOpt` whenever the level uses one. Used as one map-reduce
/// worker per chunk.
fn optimize_default(
    circuit: &Circuit,
    options: &Options,
    observer: &dyn Observer,
) -> Result<Circuit, Error> {
    let rz_decompose = DecomposeRz {
        epsilon: options.rz_epsilon,
    };
    let cancel_pass = CancelGates;
    let global = PhaseFoldRand;
    let global_expr = PhaseFoldGlobalExpr;

    if level_uses_superopt(options.level) {
        // O2 runs a fixed 2 rounds rather than to a true fixpoint — O3 and
        // Osuper are the "run it out fully" tiers; O2 is the cheap, bounded
        // one.
        let max_rounds = (options.level == Level::O2).then_some(2);
        let superopt_pass = initialize_superopt(options, options.level, observer)?;
        let passes: Vec<&dyn Pass> = vec![&cancel_pass, &superopt_pass, &global];
        let decompose: Option<&dyn Pass> = options.decompose_rz.then_some(&rz_decompose);
        Ok(run_to_fixpoint(
            circuit, &passes, decompose, observer, max_rounds,
        ))
    } else {
        let phase_fold: &dyn Pass = if options.expr { &global_expr } else { &global };
        let optimization_passes: Vec<&dyn Pass> = vec![&cancel_pass, phase_fold];

        // Optimize, then (for decompose_rz) decompose Rz and optimize the result
        // again — so the selected optimization pipeline runs on both sides of gridsynth.
        let mut passes = optimization_passes.clone();
        if options.decompose_rz && circuit.gates.iter().any(|g| matches!(g, Gate::rz(..))) {
            passes.push(&rz_decompose);
            passes.extend(optimization_passes);
        }

        Ok(if options.fixpoint {
            run_to_fixpoint(circuit, &passes, None, observer, None)
        } else {
            run_pipeline(circuit, &passes, observer)
        })
    }
}

/// Whether `level`'s pipeline includes a SuperOpt pass (and so pays for a
/// synthesis table).
fn level_uses_superopt(level: Level) -> bool {
    matches!(level, Level::O2 | Level::O3 | Level::Osuper)
}

/// Assert the driver's Rz invariants: optimization never introduces an Rz
/// gate into a circuit that had none, and [`Options::decompose_rz`] always
/// leaves none behind.
fn check_rz_invariants(input: &Circuit, result: &Circuit, options: &Options) {
    let input_has_rz = input.gates.iter().any(|g| matches!(g, Gate::rz(..)));
    let output_has_rz = result.gates.iter().any(|g| matches!(g, Gate::rz(..)));
    if output_has_rz && !input_has_rz {
        panic!("BUG: output contains Rz gates but input did not");
    }
    if output_has_rz && options.decompose_rz {
        panic!("BUG: output contains Rz gates after --decompose-rz");
    }
}

/// Optimize `circuit`, reporting nothing along the way.
///
/// ```rust,ignore
/// use tzap::circuit::Circuit;
/// use tzap::optimize::{Level, Options, optimize};
///
/// let circuit = Circuit::from_qasm(qasm)?;
/// let (optimized, report) = optimize(&circuit, &Options::default())?;
/// println!("{} → {} T", report.baseline.t, report.output.t);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub fn optimize(circuit: &Circuit, options: &Options) -> Result<(Circuit, Report), Error> {
    optimize_with(circuit, options, &Silent)
}

/// Optimize `circuit`, reporting progress to `observer`.
///
/// The default pipeline decomposes ccx/ccz (and optionally cz) over the whole
/// circuit first, then runs [`Options::level`]'s cancel + phase-fold (+
/// SuperOpt) pipeline. [`Options::passes`] overrides that with an explicit,
/// user-ordered pipeline. Under [`Options::parallel`], the chosen pipeline
/// runs map-reduce style (see [`run_map_reduce`]): the circuit is split into
/// independent gate-contiguous chunks, each optimized start-to-finish on its
/// own (own `SuperOpt` instance, no shared state), then the results are
/// stitched back together in order.
pub fn optimize_with(
    circuit: &Circuit,
    options: &Options,
    observer: &dyn Observer,
) -> Result<(Circuit, Report), Error> {
    let input = Metrics::of(circuit);
    let num_chunks = num_par_chunks();

    // Explicit pipeline via `passes`: run exactly what the caller listed, in
    // order — no eager decomposition, so the baseline is the input as-is.
    if let Some(names) = &options.passes {
        let uses_rz = names.iter().any(|p| matches!(p, PassName::DecomposeRz));
        let uses_superopt = names.iter().any(|p| matches!(p, PassName::SuperOpt));
        if options.parallel || uses_rz {
            init_global_pool();
        }
        // Warm the (process-wide cached) synthesis table once, observed,
        // before fanning out — each chunk's own SuperOpt build stays quiet.
        if options.parallel && uses_superopt {
            initialize_superopt(options, Level::O1, observer)?;
        }
        let result = run_map_reduce(circuit, options.parallel, num_chunks, observer, |c, obs| {
            optimize_explicit(c, options, obs)
        })?;
        check_rz_invariants(circuit, &result, options);
        let report = Report {
            input,
            baseline: input,
            output: Metrics::of(&result),
        };
        return Ok((result, report));
    }

    if options.parallel || options.decompose_rz {
        init_global_pool();
    }

    // Decompose CCX/CCZ eagerly, once, over the whole circuit — before any
    // chunking — so post-decomp counts form the baseline.
    let mut decomposed: Option<Circuit> = None;
    if circuit.has_toffoli || circuit.has_ccz {
        decomposed = Some(run_logged(&DecomposeToffoli, circuit, observer));
    }
    if options.decompose_cz {
        let source = decomposed.as_ref().unwrap_or(circuit);
        if source.gates.iter().any(|g| matches!(g, Gate::cz { .. })) {
            let next = run_logged(&DecomposeCz, source, observer);
            decomposed = Some(next);
        }
    }
    let base = decomposed.as_ref().unwrap_or(circuit);

    if options.parallel && level_uses_superopt(options.level) {
        initialize_superopt(options, options.level, observer)?;
    }

    let result = run_map_reduce(base, options.parallel, num_chunks, observer, |c, obs| {
        optimize_default(c, options, obs)
    })?;
    check_rz_invariants(base, &result, options);
    let report = Report {
        input,
        // Nothing was decomposed, so `base` *is* the input — no need to count
        // a million-gate circuit twice.
        baseline: match decomposed.is_some() {
            true => Metrics::of(base),
            false => input,
        },
        output: Metrics::of(&result),
    };
    Ok((result, report))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::qasm;

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
        let par = run_map_reduce(&c, true, 4, &Silent, |chunk, obs| {
            Ok(run_pipeline(chunk, &[&cancel], obs))
        })
        .expect("no SuperOpt pass, so nothing can fail");

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
        let out = run_map_reduce(&empty, true, 4, &Silent, |chunk, obs| {
            Ok(run_pipeline(chunk, &[], obs))
        })
        .expect("no SuperOpt pass, so nothing can fail");
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

        let options = Options {
            level: Level::O2,
            parallel: true,
            ..Options::default()
        };

        let out = run_map_reduce(&c, true, 4, &Silent, |chunk, obs| {
            optimize_default(chunk, &options, obs)
        })
        .expect("the default SuperOpt table must build");
        assert!(out.gates.len() <= c.gates.len());
    }

    /// `optimize` must report the post-decomposition baseline, not the raw
    /// input, as what the optimization passes worked against — a Toffoli
    /// circuit's `input` and `baseline` gate counts therefore differ.
    #[test]
    fn report_baseline_is_post_decomposition() {
        let mut c = Circuit::new(3);
        c.apply(Gate::ccx {
            control1: 0,
            control2: 1,
            target: 2,
        });

        let options = Options {
            level: Level::O1,
            ..Options::default()
        };
        let (_, report) = optimize(&c, &options).expect("O1 builds no SuperOpt table");

        assert_eq!(report.input.gates, 1);
        assert!(report.baseline.gates > 1, "ccx must be decomposed first");
        assert_eq!(report.baseline.t, 7, "the standard 7-T Toffoli");
    }

    /// A circuit needing no decomposition reports `input == baseline`.
    #[test]
    fn report_baseline_equals_input_without_decomposition() {
        let mut c = Circuit::new(1);
        c.apply(Gate::h(0));
        c.apply(Gate::h(0));

        let options = Options {
            level: Level::O1,
            ..Options::default()
        };
        let (out, report) = optimize(&c, &options).expect("O1 builds no SuperOpt table");

        assert_eq!(report.input, report.baseline);
        assert_eq!(out.gates.len(), 0, "HH must cancel");
        assert_eq!(report.output.gates, 0);
    }
}
