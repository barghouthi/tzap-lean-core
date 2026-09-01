//! The optimization driver: optimization levels, pass pipelines, the fixpoint
//! loop, `SuperOpt` construction, and map-reduce parallelism.
//!
//! This is everything the `tzap` binary used to own itself, so that every
//! frontend — the CLI, a Rust caller, a language binding — runs the exact same
//! pipeline rather than reimplementing `-O3`. The CLI keeps only argument
//! parsing, file I/O, and terminal rendering; it plugs the latter in through
//! [`Observer`].

use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use rayon::prelude::*;

use crate::cancel::CancelGates;
use crate::circuit::{Circuit, Gate, qubit_operands};
use crate::cnot_min::CnotMin;
use crate::decompose::{DecomposeCz, DecomposeRz, DecomposeToffoli};
use crate::pass::Pass;
use crate::phase_fold_rand::PhaseFoldRand;
use crate::super_opt::{SuperOpt, SuperOptError, SuperOptTableConfig, table_is_cached};

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
    /// run to a true fixpoint — see `optimize_default`'s `max_rounds`. With
    /// `decompose_rz` the cap allows one extra round, so Rz synthesis lands in
    /// the same place it does at the uncapped levels (see [`run_to_fixpoint`]).
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
    CnotMin,
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
            "CnotMin",
            PassName::CnotMin,
            "Re-synthesize CNOT-dihedral blocks to cut two-qubit gates",
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
    /// Every counter from one walk of the gate list rather than four.
    ///
    /// This runs after every pass of every fixpoint round, purely to drive the
    /// progress display, so on a multi-million-gate circuit the difference
    /// between one traversal and four is a measurable share of total runtime.
    /// `count_2q`/`count_t`/`count_rz`/`depth` remain as published, separately
    /// callable API; this just doesn't route through them.
    pub fn of(circuit: &Circuit) -> Metrics {
        let mut two_qubit = 0;
        let mut t = 0;
        let mut rz = 0;
        // Depth, computed exactly as `pass::depth` does: a gate lands one layer
        // past the deepest layer already occupied by any of its operands.
        let mut next_layer = vec![0usize; circuit.num_qubits];
        let mut depth = 0;
        for gate in &circuit.gates {
            match gate {
                Gate::cnot { .. } | Gate::cz { .. } => two_qubit += 1,
                Gate::t(_) | Gate::tdg(_) => t += 1,
                Gate::rz(..) => rz += 1,
                _ => {}
            }
            let (arity, operands) = qubit_operands(gate);
            let layer = operands[..arity]
                .iter()
                .map(|&qubit| next_layer[qubit as usize])
                .max()
                .unwrap_or(0)
                + 1;
            for &qubit in &operands[..arity] {
                next_layer[qubit as usize] = layer;
            }
            depth = depth.max(layer);
        }
        Metrics {
            gates: circuit.gates.len(),
            two_qubit,
            depth,
            t,
            rz,
        }
    }

    /// These metrics with `before`'s contribution swapped out for `after`'s —
    /// how a parallel run reports partial progress: the whole circuit's
    /// baseline, adjusted by the chunks finished so far (see
    /// [`run_map_reduce`]).
    ///
    /// Exact for the counting metrics, which are plain sums over the gate
    /// list. Depth is carried through untouched, because it is *not* a sum:
    /// concatenated chunks share layers, so a chunk halving its own depth may
    /// barely move the circuit's. Adjusting it the same way came out 32% low
    /// on `qft_q010_d14171` — a bar that would overstate the reduction all
    /// run and then snap back once the real number arrived. Getting it right
    /// means measuring the whole partially optimized circuit, which is
    /// exactly the O(chunks x circuit) work this exists to avoid.
    ///
    /// Saturating, so a progress bar can never panic a real run.
    fn adjusted(self, before: Metrics, after: Metrics) -> Metrics {
        let adjust =
            |base: usize, before: usize, after: usize| (base + after).saturating_sub(before);
        Metrics {
            gates: adjust(self.gates, before.gates, after.gates),
            two_qubit: adjust(self.two_qubit, before.two_qubit, after.two_qubit),
            depth: self.depth,
            t: adjust(self.t, before.t, after.t),
            rz: adjust(self.rz, before.rz, after.rz),
        }
    }
}

/// Running totals of the per-chunk metrics a parallel run reports, each chunk
/// adding its own as it finishes.
#[derive(Default)]
struct MetricSums {
    gates: AtomicUsize,
    two_qubit: AtomicUsize,
    t: AtomicUsize,
    rz: AtomicUsize,
}

impl MetricSums {
    /// Add `m` to the totals and return them, this addition included. Fields
    /// are summed independently, so a concurrent add can land between two of
    /// them: the result is a live reading, not a consistent snapshot. Depth
    /// is not summed (see [`Metrics::adjusted`]) and reads back as 0.
    fn add(&self, m: Metrics) -> Metrics {
        let add = |total: &AtomicUsize, n: usize| total.fetch_add(n, Ordering::Relaxed) + n;
        Metrics {
            gates: add(&self.gates, m.gates),
            two_qubit: add(&self.two_qubit, m.two_qubit),
            depth: 0,
            t: add(&self.t, m.t),
            rz: add(&self.rz, m.rz),
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
    /// *and* the per-chunk metric walks that feed them — pure overhead for a
    /// run nobody is watching.
    fn tracks_chunks(&self) -> bool {
        false
    }

    /// A whole-circuit pass (the eager ccx/ccz or cz decomposition) finished.
    /// Both sides are reported: a decomposition *grows* the circuit, so a
    /// renderer that only showed `result` would leave its counts looking
    /// unexplained next to the input's.
    fn pass_done(&self, _name: &str, _input: &Circuit, _result: &Circuit, _elapsed: Duration) {}

    /// The SuperOpt synthesis table is about to be loaded from disk
    /// (`cached`) or built from scratch.
    fn table_load_start(&self, _cached: bool) {}

    /// The SuperOpt synthesis table is ready.
    fn table_load_done(&self, _cached: bool, _elapsed: Duration) {}

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
    /// ones as-is.
    ///
    /// The counts are exact. `current.depth` is *not* tracked — it stays at
    /// `baseline.depth` for the whole run, because depth can only be measured
    /// on the assembled circuit (see [`Metrics::adjusted`]). Only called when
    /// [`Observer::tracks_chunks`] is true.
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
    observer.pass_done(pass.name(), circuit, &c, start.elapsed());
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

/// Sweep `passes` until one fails to reduce the gate count, or until
/// `max_rounds` sweeps have run, whichever comes first. Rounds are numbered
/// from `first_round` so a caller running two phases (see [`run_to_fixpoint`])
/// reports one continuous sequence to the observer. Returns the circuit, the
/// last round number used, and whether it converged (as opposed to stopping on
/// the cap).
fn run_fixpoint_phase(
    circuit: &Circuit,
    passes: &[&dyn Pass],
    observer: &dyn Observer,
    baseline: Metrics,
    first_round: usize,
    max_rounds: Option<usize>,
) -> (Circuit, usize, bool) {
    let mut c = circuit.clone();
    let mut round = first_round - 1;
    let mut reduced;
    let mut swept = 0;
    loop {
        round += 1;
        swept += 1;
        let before = c.gates.len();
        c = run_fixpoint_sweep(&c, passes, round, observer, baseline);
        reduced = c.gates.len() < before;
        if !reduced || max_rounds.is_some_and(|m| swept >= m) {
            break;
        }
    }
    (c, round, !reduced)
}

/// Repeatedly run `passes` until a sweep fails to reduce the gate count, or
/// (when `max_rounds` is given) until that many sweeps have run, whichever
/// comes first.
///
/// When `rz_decompose` is given it runs exactly once, after the pre-synthesis
/// sweeps have converged — identically at every SuperOpt level (O2, O3,
/// Osuper), which all reach this through `optimize_default`.
///
/// That placement matters a lot: what gridsynth expands into is what
/// `SuperOpt`'s greedy, non-backtracking window selection has to work with
/// afterwards, and converging first can shrink that circuit by several-fold (on
/// cobble's ols-ridge, 180k gates after one sweep vs 25k at the fixpoint).
/// Synthesizing into the smaller circuit measured 2-22% fewer T across cobble,
/// and *faster* despite running more rounds, since every post-synthesis round
/// then sweeps far fewer gates.
///
/// Afterwards, if there were Rz gates to decompose, the sweeps resume on the
/// synthesized circuit. `max_rounds` is a budget shared across both phases,
/// except that the post-synthesis phase always gets at least one sweep —
/// freshly synthesized Clifford+T sequences are never left unoptimized just
/// because the pre-synthesis phase used up the cap. So O2, the one capped
/// level, runs up to `max_rounds + 1` sweeps when synthesis intervenes; paying
/// that extra sweep is what buys O2 the same Rz placement as the uncapped
/// levels rather than silently degrading to synthesize-after-one-sweep.
fn run_to_fixpoint(
    circuit: &Circuit,
    passes: &[&dyn Pass],
    rz_decompose: Option<&dyn Pass>,
    observer: &dyn Observer,
    max_rounds: Option<usize>,
) -> Circuit {
    let baseline = Metrics::of(circuit);
    observer.progress_start(baseline);

    let (mut c, mut round, mut converged) =
        run_fixpoint_phase(circuit, passes, observer, baseline, 1, max_rounds);

    if let Some(pass) = rz_decompose {
        let had_rz = c.gates.iter().any(|g| matches!(g, Gate::rz(..)));
        c = pass.run(&c);
        observer.progress_update(Some(round), &c, baseline);
        if had_rz {
            let spent = round;
            let post_cap = max_rounds.map(|m| m.saturating_sub(spent).max(1));
            (c, round, converged) =
                run_fixpoint_phase(&c, passes, observer, baseline, round + 1, post_cap);
        }
    }

    observer.progress_end(baseline);
    observer.fixpoint_done(round, converged);
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
    observer.table_load_done(cached, start.elapsed());
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

    // Whole-circuit baseline, which each finished chunk then adjusts by its
    // own before/after difference: pending chunks (not yet optimized)
    // contribute their original metrics, completed ones their current metrics.
    //
    // Measuring the partially optimized circuit directly instead — stitching
    // every chunk back together under a lock on each completion — cost
    // O(chunks x circuit) and serialized the workers behind it: ~20% of a
    // parallel run on a 4M-gate circuit, all of it to move a progress bar.
    let baseline = Metrics::of(circuit);
    let done = AtomicUsize::new(0);
    let sum_before = MetricSums::default();
    let sum_after = MetricSums::default();

    if tracking {
        observer.chunks_start(total, baseline);
    }
    let optimized: Vec<Result<Circuit, Error>> = chunks
        .par_iter()
        .map(|chunk| {
            // Walked only when someone is watching: two passes over the chunk
            // that a `Silent` run has no use for.
            let before = tracking.then(|| Metrics::of(chunk));
            let result = optimize(chunk, &Silent)?;
            if let Some(before) = before {
                let n = done.fetch_add(1, Ordering::Relaxed) + 1;
                let current =
                    baseline.adjusted(sum_before.add(before), sum_after.add(Metrics::of(&result)));
                observer.chunk_done(n, total, current, baseline);
            }
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
    let cnot_min_pass = CnotMin::default();

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
                PassName::CnotMin => &cnot_min_pass,
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
    let cnot_min_pass = CnotMin::default();

    if level_uses_superopt(options.level) {
        // O2 runs a fixed 2 rounds rather than to a true fixpoint — O3 and
        // Osuper are the "run it out fully" tiers; O2 is the cheap, bounded
        // one.
        let max_rounds = (options.level == Level::O2).then_some(2);
        let superopt_pass = initialize_superopt(options, options.level, observer)?;
        // CnotMin leads the sweep: it re-synthesizes whole CNOT-dihedral
        // blocks, which reshapes the circuit far more than the peephole
        // rewriter does, and the passes after it then work on the result.
        let passes: Vec<&dyn Pass> = vec![&cnot_min_pass, &cancel_pass, &superopt_pass, &global];
        let decompose: Option<&dyn Pass> = options.decompose_rz.then_some(&rz_decompose);
        Ok(run_to_fixpoint(
            circuit, &passes, decompose, observer, max_rounds,
        ))
    } else {
        let optimization_passes: Vec<&dyn Pass> = vec![&cancel_pass, &global];

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

    /// The parallel progress numbers are derived from per-chunk deltas rather
    /// than measured off the partially stitched circuit, so the counting
    /// metrics must still land exactly on the real output's once every chunk
    /// has reported.
    #[test]
    fn chunk_progress_counts_match_the_finished_circuit() {
        #[derive(Default)]
        struct LastChunk(std::sync::Mutex<Option<Metrics>>);
        impl Observer for LastChunk {
            fn tracks_chunks(&self) -> bool {
                true
            }
            fn chunk_done(&self, _done: usize, _total: usize, current: Metrics, _: Metrics) {
                *self.0.lock().unwrap() = Some(current);
            }
        }

        let qasm = "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[3];\n".to_string()
            + &"h q[0];\ncx q[0],q[1];\nt q[1];\ncx q[1],q[2];\ntdg q[2];\nrz(0.3) q[0];\n"
                .repeat(20);
        let c = Circuit::from_qasm(&qasm).unwrap();
        let cancel = CancelGates;
        let observer = LastChunk::default();
        let out = run_map_reduce(&c, true, 4, &observer, |chunk, obs| {
            Ok(run_pipeline(chunk, &[&cancel], obs))
        })
        .unwrap();

        let reported = observer.0.lock().unwrap().expect("every chunk reports");
        let actual = Metrics::of(&out);
        assert_eq!(reported.gates, actual.gates);
        assert_eq!(reported.two_qubit, actual.two_qubit);
        assert_eq!(reported.t, actual.t);
        assert_eq!(reported.rz, actual.rz);
    }

    /// Depth is not a sum over chunks, so a chunk reporting its own depth
    /// collapsing must leave the circuit's reported depth alone rather than
    /// subtracting from it.
    #[test]
    fn adjusted_leaves_depth_at_the_baseline() {
        let baseline = Metrics {
            gates: 10,
            two_qubit: 4,
            depth: 6,
            t: 2,
            rz: 0,
        };
        // A chunk that locally held more depth than the whole circuit did,
        // and optimized all of it away.
        let before = Metrics {
            depth: 9,
            ..baseline
        };
        let adjusted = baseline.adjusted(before, Metrics::default());
        assert_eq!(adjusted.depth, baseline.depth);
        assert_eq!(adjusted.gates, 0, "the counts still adjust exactly");
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

    /// Rz synthesis must wait for the pre-synthesis sweeps to converge, so
    /// gridsynth expands into the smallest circuit available. Regression
    /// guard: a circuit whose Clifford+T body keeps shrinking for several
    /// sweeps must reach synthesis already reduced, which is what makes the
    /// default placement worth 2-22% T on cobble. Counted via the round at
    /// which the Rz count drops to zero: synthesizing after the first sweep
    /// would zero it in round 1, so holding it past round 1 is the observable
    /// signature of the placement. Must hold at *every* SuperOpt level — O2's
    /// round cap must not quietly degrade it back to synthesize-after-one-sweep.
    #[test]
    fn rz_synthesis_waits_for_the_presynthesis_fixpoint_at_every_level() {
        /// Records the round in which the observed circuit first has no Rz.
        struct RzRound(std::sync::Mutex<Option<usize>>);
        impl Observer for RzRound {
            fn progress_update(&self, iteration: Option<usize>, c: &Circuit, _: Metrics) {
                let has_rz = c.gates.iter().any(|g| matches!(g, Gate::rz(..)));
                let mut first = self.0.lock().unwrap();
                if !has_rz && first.is_none() {
                    *first = iteration;
                }
            }
        }

        // An H·H / CNOT·CNOT body (so sweep 1 finds real reduction and the
        // pre-synthesis phase runs past round 1) plus a single non-π/4 Rz for
        // gridsynth to synthesize.
        let mut c = Circuit::new(3);
        for _ in 0..12 {
            c.apply(Gate::h(0));
            c.apply(Gate::h(0));
            c.apply(Gate::cnot {
                control: 0,
                target: 1,
            });
            c.apply(Gate::cnot {
                control: 0,
                target: 1,
            });
        }
        c.apply(Gate::rz(0.37, 2));

        for level in [Level::O2, Level::O3, Level::Osuper] {
            let options = Options {
                level,
                decompose_rz: true,
                // Osuper's real bounds (5 qubits, 5M entries) would spend
                // minutes building a table; the placement logic is
                // bound-independent, so shrink them to the default preset and
                // exercise the *level* cheaply.
                superopt: SuperOptBounds {
                    qubits: Some(DEFAULT_SUPEROPT_QUBITS),
                    window_gates: Some(DEFAULT_SUPEROPT_WINDOW_GATES),
                    table_entries: Some(DEFAULT_SUPEROPT_TABLE_ENTRIES),
                },
                ..Options::default()
            };
            let observer = RzRound(std::sync::Mutex::new(None));
            let out = optimize_default(&c, &options, &observer).expect("pipeline must run");

            assert!(
                !out.gates.iter().any(|g| matches!(g, Gate::rz(..))),
                "{level:?}: decompose_rz must leave no Rz behind"
            );
            let round = observer
                .0
                .lock()
                .unwrap()
                .expect("Rz must reach zero at some round");
            assert!(
                round > 1,
                "{level:?}: Rz synthesis must wait for the pre-synthesis sweeps \
                 to converge, but Rz was gone by round {round}"
            );
        }
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
