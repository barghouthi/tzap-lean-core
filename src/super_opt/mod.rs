//! Peephole superoptimization over anchored circuit windows.
//!
//! The pass makes one forward scan over the circuit, carves out small
//! *windows* — causally connected groups of gates on a few qubits — computes
//! each window's unitary matrix, and asks a precomputed synthesis table
//! (`table.rs`) whether the same unitary is reachable with fewer gates. Where
//! it is, the window is replaced. Because replacement is by matrix
//! equivalence rather than by syntactic rule, any identity the table can
//! express is discovered without ever being written down.
//!
//! # Windows
//!
//! Every gate *anchors* a window: the connected component of that gate among
//! all gates observed since it, connectivity meaning "shares a qubit". As the
//! scan advances, each new gate extends every window that touches one of its
//! qubits. Two invariants make this cheap and exhaustive:
//!
//! - A window always holds the *full* connected component of its anchor over
//!   the scanned region: gates on a window qubit between the anchor and the
//!   scan head are all members, so per-qubit gate history only needs to be
//!   consulted when a gate bridges a **new** qubit into the window
//!   (`expand_component_closure`). Such a bridge can retroactively pull in
//!   an entire previously unrelated component.
//! - Unrelated gates in between are simply absent, so a window is a
//!   *subsequence* of the circuit, not a contiguous slice. Rewriting it in
//!   place is still sound because every skipped gate commutes past the
//!   window: it shares no qubit with any member between anchor and head.
//!
//! A window dies when it exceeds `max_qubits` or `window_gates`, when Rz,
//! measurement, or reset touches one of its qubits (Rz is outside SuperOpt's
//! exact Clifford+T matrix domain; measurement/reset are non-unitary), or when
//! one of its gates is claimed by a selected rewrite. Each window is analyzed
//! after every extension, so every intermediate size is considered, not just
//! the final one.
//!
//! # Rewrites
//!
//! Windows are looked up as they grow; the first strictly smaller equivalent
//! claims its gates greedily in scan order (`RewriteSet`), later windows
//! overlapping a claimed gate are discarded, and all selected rewrites are
//! applied in one reconstruction pass at the end.
//!
//! # Caching
//!
//! Three layers keep repeated work off the hot path:
//!
//! 1. The synthesis table is built once per configuration and shared
//!    process-wide (`table::shared_synthesis_table`), and persisted to disk
//!    (under `~/.tzap/superopt-tables/`, one file per distinct config) so
//!    later processes load it instead of rebuilding it.
//! 2. The matrix store (`MatrixStore`) interns each canonical window shape
//!    with its matrix and synthesis outcome — including the negative one —
//!    and is carried across runs of a pass instance, so later fixpoint
//!    sweeps replay recurring shapes as hash hits.
//! 3. Incremental mode ([`SuperOpt::incremental`]) diffs each input against
//!    the instance's previous input and only anchors windows near the
//!    changes; everything else was analyzed before and selected nothing
//!    (`incremental.rs`).

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use smallvec::{SmallVec, smallvec};

use crate::circuit::{Circuit, Gate, Qubit};
use crate::pass::Pass;

/// Inline storage for a window's qubit support (bounded by `max_qubits`, at most
/// four in practice) and its gate indices (bounded by `window_gates`), so the
/// per-gate window bookkeeping stays off the heap.
type QubitVec = SmallVec<[Qubit; 4]>;
type IndexVec = SmallVec<[usize; 8]>;

mod config;
mod error;
mod incremental;
mod matrix;
mod matrix_cache;
mod synthesis_arena;
mod table;

pub use config::SuperOptTableConfig;
pub use error::SuperOptError;

use matrix::UnitaryMatrix;
use matrix_cache::{
    CachedMatrix, CompactKey, MatrixStore, append_compact_gate_key, compact_normalized_key,
};
use table::{UnitaryCircuitTable, shared_synthesis_table};

/// Whether a synthesis table matching `config` is already cached on disk —
/// a hint for callers wanting to report whether the next `SuperOpt::new`
/// call will be a fast cache load or a fresh, slow build. Purely
/// informational: `SuperOpt::new` re-validates independently, so this is
/// never load-bearing for correctness.
pub fn table_is_cached(config: SuperOptTableConfig) -> bool {
    table::disk_cache_exists(config)
}

/// Size in bytes of the on-disk synthesis-table cache for `config`, if one
/// exists — a reporting aid alongside `table_is_cached`, never load-bearing
/// for correctness.
pub fn table_cache_size_bytes(config: SuperOptTableConfig) -> Option<u64> {
    table::disk_cache_size_bytes(config)
}

/// Matrix and location information for one completed anchored window.
#[derive(Clone, Debug)]
pub struct SuperOptWindow {
    /// Gate positions in chronological order; unrelated intervening gates are absent.
    pub gate_indices: Vec<usize>,
    /// Sorted physical qubits corresponding to the matrix's local qubit order.
    pub qubits: Vec<Qubit>,
    /// Shared when another canonical gate sequence has the same matrix construction.
    pub matrix: Arc<UnitaryMatrix>,
}

/// One selected semantics-preserving peephole rewrite, in input coordinates.
#[derive(Clone, Debug)]
pub struct SuperOptRewrite {
    /// Indices, into the input circuit, of the gates this rewrite replaces.
    pub gate_indices: Vec<usize>,
    /// Replacement gates on the original circuit's physical qubits.
    pub replacement: Vec<Gate>,
}

/// Results and matrix-cache statistics from [`SuperOpt::run`].
#[derive(Clone, Debug)]
pub struct SuperOptResult {
    /// Input circuit with a non-overlapping set of strictly smaller rewrites applied.
    pub circuit: Circuit,
    /// Completed windows and their matrices; empty when built with
    /// [`SuperOpt::without_subcircuits`].
    pub subcircuits: Vec<SuperOptWindow>,
    /// All selected rewrites, including identity removals with empty replacements.
    pub rewrites: Vec<SuperOptRewrite>,
    /// Reused matrices for completed closed components.
    pub cache_hits: usize,
    /// Completed components with previously unseen canonical gate sequences.
    pub cache_misses: usize,
}

/// Configuration for the connected anchored-window analysis.
#[derive(Clone, Debug)]
pub struct SuperOpt {
    /// Maximum number of distinct qubits in a tracked window.
    pub max_qubits: usize,
    /// Maximum number of connected gates in a reported window.
    pub window_gates: usize,
    collect_subcircuits: bool,
    incremental: bool,
    synthesis_table: Option<Arc<UnitaryCircuitTable>>,
    /// Matrix cache carried across runs of this pass instance (and its
    /// clones), so repeated fixpoint sweeps skip re-deriving recurring window
    /// shapes. Reuse returns exactly what a cold run would recompute; see
    /// `MatrixStore`. `Rc<RefCell<_>>`, not `Arc<Mutex<_>>`: a `SuperOpt`
    /// instance (and any clones sharing this cache) is meant to stay on one
    /// thread — parallel callers construct one fresh instance per worker
    /// rather than sharing or cloning one across threads — so this is never
    /// actually touched from more than one thread at a time; `Pass` doesn't
    /// require `Sync` for exactly this reason.
    store: Rc<RefCell<MatrixStore>>,
    /// The input the previous run saw, diffed against the next input to
    /// bound where new windows can anchor when `incremental` is set.
    prev_input: Rc<RefCell<Option<Circuit>>>,
}

#[derive(Debug)]
struct ActiveWindow {
    gate_indices: IndexVec,
    qubits: QubitVec,
    // Boxed: `ActiveWindow` is moved in and out of `active` on every touched
    // window for every gate processed (the hottest loop in `run`), so keeping
    // `CompactKey`'s fixed-size array behind a pointer keeps that move O(1)
    // instead of copying the whole array each time.
    compact_key: Option<Box<CompactKey>>,
    // Tracked incrementally by `expand_component_closure` (the only place an
    // Rz gate can enter `gate_indices`, via a bridged-in qubit's history), so
    // `analyze_window` can reject an Rz window in O(1) instead of rescanning
    // the whole (monotonically growing) gate list on every touch.
    contains_rz: bool,
    // Anchor order: the number of windows created before this one. Slot
    // indices in `active` get recycled (see `WindowArena`), so a slot index is
    // no longer a proxy for age — but rewrite selection is greedy in anchor
    // order, so the per-gate touched-window list must still be processed
    // oldest-first. This is the key it sorts by.
    seq: u64,
}

/// Slot storage for the live windows of one scan.
///
/// Nearly every gate anchors a window, but a window dies within
/// `window_gates` gates of its anchor, so only a few dozen are ever live at
/// once (measured on `benchmarks/cobble/ols-ridge.qasm` at `-O3`: 35–68 live,
/// against 536k anchored). Indexing slots by a monotonically increasing
/// counter therefore grew `active` to one 144-byte slot per gate — 77 MB,
/// reallocated and page-faulted on every fixpoint sweep — to hold a working
/// set of a few kilobytes. Retiring a window returns its slot to `free`, so
/// the arena instead stays at high-water-mark size.
///
/// Slot indices are consequently *not* anchor order; `ActiveWindow::seq` is.
#[derive(Debug, Default)]
struct WindowArena {
    slots: Vec<Option<ActiveWindow>>,
    free: Vec<usize>,
    /// Stamped with `gate_index + 1` when a slot is added to the per-gate
    /// touched list, to dedup it without sorting. 0 means "not yet touched".
    touch_stamp: Vec<usize>,
    next_seq: u64,
}

impl WindowArena {
    /// Take the window out of `slot`, which must be live.
    fn take(&mut self, slot: usize) -> ActiveWindow {
        self.slots[slot]
            .take()
            .expect("qubit index only contains live windows")
    }

    fn put_back(&mut self, slot: usize, window: ActiveWindow) {
        self.slots[slot] = Some(window);
    }

    fn seq_of(&self, slot: usize) -> u64 {
        self.slots[slot]
            .as_ref()
            .expect("qubit index only contains live windows")
            .seq
    }

    /// The qubit support of the window in `slot`, which must be live.
    fn qubits(&self, slot: usize) -> &[Qubit] {
        &self.slots[slot]
            .as_ref()
            .expect("qubit index only contains live windows")
            .qubits
    }

    /// The next anchor order value, consumed when building an `ActiveWindow`.
    fn next_seq(&mut self) -> u64 {
        self.next_seq += 1;
        self.next_seq - 1
    }

    /// Store `window` in a recycled slot when one is free, else in a new one.
    fn insert(&mut self, window: ActiveWindow) -> usize {
        match self.free.pop() {
            Some(slot) => {
                self.slots[slot] = Some(window);
                slot
            }
            None => {
                self.slots.push(Some(window));
                self.touch_stamp.push(0);
                self.slots.len() - 1
            }
        }
    }

    /// Retire the window in `slot`: drop it from the per-qubit index (skipping
    /// `exclude`, qubits a just-attempted expansion inserted but never
    /// registered) and return the slot for reuse.
    ///
    /// The window must already have been `take`n out of the slot.
    fn retire(
        &mut self,
        slot: usize,
        qubits: &[Qubit],
        exclude: &[Qubit],
        windows_by_qubit: &mut [Vec<usize>],
    ) {
        unregister_window(slot, qubits, exclude, windows_by_qubit);
        // Clear the stamp so a future tenant of this slot can never inherit a
        // touch recorded against the previous one.
        self.touch_stamp[slot] = 0;
        self.free.push(slot);
    }
}

impl SuperOpt {
    /// An optimizing pass: windows are checked against a synthesis table
    /// (built on first use per `table_config`, then shared process-wide) and
    /// rewritten when a smaller equivalent exists.
    pub fn new(
        max_qubits: usize,
        window_gates: usize,
        table_config: SuperOptTableConfig,
    ) -> Result<Self, SuperOptError> {
        Ok(Self::analyzer(max_qubits, window_gates)
            .with_synthesis_table(shared_synthesis_table(table_config)?))
    }

    /// An analysis-only instance: windows and their matrices are reported in
    /// `result.subcircuits`, but with no synthesis table nothing is rewritten.
    pub fn analyzer(max_qubits: usize, window_gates: usize) -> Self {
        Self {
            max_qubits,
            window_gates,
            collect_subcircuits: true,
            incremental: false,
            synthesis_table: None,
            store: Rc::default(),
            prev_input: Rc::default(),
        }
    }

    fn with_synthesis_table(mut self, table: Arc<UnitaryCircuitTable>) -> Self {
        self.synthesis_table = Some(table);
        self
    }

    /// Anchor windows only near gates that changed since the previous run's
    /// input, skipping regions whose windows were already analyzed and
    /// selected nothing. The output is identical to a full sweep as long as
    /// successive runs see successive versions of the same circuit (a
    /// sequential fixpoint driver); do not combine with parallel chunking,
    /// which feeds one instance interleaved unrelated circuits, or with
    /// subcircuit collection, which would come back incomplete.
    pub fn incremental(mut self) -> Self {
        self.incremental = true;
        self
    }

    /// Skip accumulating per-window [`SuperOptWindow`] diagnostics.
    ///
    /// Rewrites still apply; only `result.subcircuits` stays empty. Large
    /// circuits emit millions of windows, so optimization-only callers should
    /// opt out of retaining them.
    pub const fn without_subcircuits(mut self) -> Self {
        self.collect_subcircuits = false;
        self
    }

    /// Run one forward scan while maintaining one closed unitary component
    /// per anchor (see the module documentation for the algorithm).
    ///
    /// For every gate, in order: (1) windows touching a measurement or reset
    /// die; (2) every live window touching the gate is extended, re-closed,
    /// and analyzed; (3) the gate anchors a fresh window of its own.
    pub fn run(&self, circuit: &Circuit) -> Result<SuperOptResult, SuperOptError> {
        if self.window_gates == 0 {
            return Err(SuperOptError::ZeroWindowGates);
        }
        validate_circuit(circuit)?;

        let frontier = self.take_anchor_frontier(circuit);

        // Scan state: `arena` owns the live windows, recycling slots as they
        // die; `windows_by_qubit` inverts it so a gate finds the windows it
        // touches without scanning them all; `gates_by_qubit` is the full
        // per-qubit gate history that window closure consults.
        let mut arena = WindowArena::default();
        let mut windows_by_qubit: Vec<Vec<usize>> = vec![Vec::new(); circuit.num_qubits];
        let mut gates_by_qubit: Vec<Vec<usize>> = vec![Vec::new(); circuit.num_qubits];
        // Take the persistent store for the duration of this run; an early
        // error drops it, which only costs the next run a cold start.
        let mut store = MatrixStore::take_from(&self.store);
        let mut subcircuits = Vec::new();
        let mut rewrites = RewriteSet::new(circuit.gates.len());
        let mut touched_windows = Vec::new();

        for (gate_index, gate) in circuit.gates.iter().enumerate() {
            let gate_qubits = unique_qubits(gate);

            // Collect the windows this gate touches, deduped by slot via
            // `touch_stamp` (a window registered on two of the gate's qubits
            // appears in both lists) and ordered by anchor age, which is what
            // greedy rewrite selection consumes.
            touched_windows.clear();
            let stamp = gate_index + 1;
            for &qubit in &gate_qubits {
                for &slot in &windows_by_qubit[qubit] {
                    if arena.touch_stamp[slot] != stamp {
                        arena.touch_stamp[slot] = stamp;
                        touched_windows.push((arena.seq_of(slot), slot));
                    }
                }
                gates_by_qubit[qubit].push(gate_index);
            }
            // Sorting `(seq, slot)` pairs, rather than slots by a `seq_of` key
            // closure: `sort_unstable_by_key` re-evaluates its key on every
            // comparison, which would put a bounds-checked load and an
            // `Option` unwrap inside the sort's inner loop.
            touched_windows.sort_unstable();

            // Rz is outside the exact Clifford+T matrix domain; measurement
            // and reset are non-unitary. All three terminate windows touching
            // their qubit. Keep the gate in per-qubit history so a disjoint
            // window cannot later bridge across this barrier.
            if matches!(gate, Gate::rz(..) | Gate::measure { .. } | Gate::reset(_)) {
                for &(_, window_id) in &touched_windows {
                    let window = arena.take(window_id);
                    arena.retire(window_id, &window.qubits, &[], &mut windows_by_qubit);
                }
                continue;
            }

            for &(_, window_id) in &touched_windows {
                let mut window = arena.take(window_id);
                if rewrites.is_claimed(gate_index) || rewrites.claims_any(&window.gate_indices) {
                    arena.retire(window_id, &window.qubits, &[], &mut windows_by_qubit);
                    continue;
                }
                // `added_qubits` were inserted into `window.qubits` but never
                // registered, so unregistration must skip them; the remaining
                // qubits are exactly the set this window was registered on.
                let (within_bounds, added_qubits) = expand_component_closure(
                    circuit,
                    &mut window,
                    gate_index,
                    &gate_qubits,
                    &gates_by_qubit,
                    self.max_qubits,
                    self.window_gates,
                );
                if !within_bounds {
                    arena.retire(
                        window_id,
                        &window.qubits,
                        &added_qubits,
                        &mut windows_by_qubit,
                    );
                    continue;
                }

                // Keep the window's cache key current: appending one gate is
                // O(1), but a bridged-in qubit renumbers the support-local
                // encoding of every member, so the key must be rebuilt.
                if added_qubits.is_empty() {
                    append_compact_gate_key(&mut window.compact_key, gate, &window.qubits);
                } else {
                    window.compact_key =
                        compact_normalized_key(circuit, &window.gate_indices, &window.qubits)
                            .map(Box::new);
                }

                let at_gate_limit = window.gate_indices.len() == self.window_gates;
                let selected = self.analyze_window(
                    circuit,
                    &window,
                    &mut store,
                    &mut rewrites,
                    &mut subcircuits,
                )?;

                if at_gate_limit || selected {
                    arena.retire(
                        window_id,
                        &window.qubits,
                        &added_qubits,
                        &mut windows_by_qubit,
                    );
                } else {
                    for &qubit in &added_qubits {
                        windows_by_qubit[qubit].push(window_id);
                    }
                    arena.put_back(window_id, window);
                }
            }

            // The current gate anchors a new one-gate closed component.
            if frontier.as_ref().is_none_or(|f| f[gate_index])
                && gate_qubits.len() <= self.max_qubits
                && !rewrites.is_claimed(gate_index)
            {
                let window = ActiveWindow {
                    gate_indices: smallvec![gate_index],
                    compact_key: compact_normalized_key(circuit, &[gate_index], &gate_qubits)
                        .map(Box::new),
                    qubits: gate_qubits,
                    // The barrier check above already sent Rz/measure/reset
                    // gates to `continue` before this anchor point is reached.
                    contains_rz: false,
                    seq: arena.next_seq(),
                };
                // A single non-identity Clifford+T gate cannot be rewritten to
                // the empty circuit. Analyze it only when diagnostics were
                // requested; Rz windows are rejected inside `analyze_window`.
                if self.collect_subcircuits {
                    self.analyze_window(
                        circuit,
                        &window,
                        &mut store,
                        &mut rewrites,
                        &mut subcircuits,
                    )?;
                }

                if self.window_gates > 1 && !rewrites.is_claimed(gate_index) {
                    let window_id = arena.insert(window);
                    for &qubit in arena.qubits(window_id) {
                        windows_by_qubit[qubit].push(window_id);
                    }
                }
            }
        }

        subcircuits.sort_by(|left, right| left.gate_indices.cmp(&right.gate_indices));
        let (optimized, rewrites) = rewrites.apply(circuit);
        let (cache_hits, cache_misses) = (store.hits, store.misses);
        store.store_back(&self.store);
        Ok(SuperOptResult {
            circuit: optimized,
            subcircuits,
            rewrites,
            cache_hits,
            cache_misses,
        })
    }

    /// In incremental mode, the bitmap of gates allowed to anchor a window
    /// (`None` anchors everywhere); also remembers this input for the next
    /// run's diff. See [`incremental::anchor_frontier`].
    fn take_anchor_frontier(&self, circuit: &Circuit) -> Option<Vec<bool>> {
        if !self.incremental {
            return None;
        }
        let mut prev = self.prev_input.borrow_mut();
        let frontier = incremental::anchor_frontier(circuit, prev.as_ref(), self.window_gates);
        *prev = Some(circuit.clone());
        frontier
    }

    /// Resolve one window emission: intern its matrix and synthesis outcome
    /// in the store, offer the outcome to the rewrite selection, and record
    /// the window when diagnostics are collected. Returns whether a rewrite
    /// was selected.
    fn analyze_window(
        &self,
        circuit: &Circuit,
        window: &ActiveWindow,
        store: &mut MatrixStore,
        rewrites: &mut RewriteSet,
        subcircuits: &mut Vec<SuperOptWindow>,
    ) -> Result<bool, SuperOptError> {
        // Unspill the SmallVecs once; this runs per emitted window.
        let gate_indices: &[usize] = &window.gate_indices;
        let qubits: &[Qubit] = &window.qubits;
        // Exact SuperOpt matrices represent Clifford+T only. Never construct
        // a matrix or accept a rewrite for a window containing Rz; phase
        // folding/decomposition is responsible for those rotations.
        // `contains_rz` is tracked incrementally by `expand_component_closure`,
        // so this is O(1) rather than a rescan of the (monotonically growing)
        // gate list on every touch.
        if window.contains_rz {
            return Ok(false);
        }
        let Some(cached) = store.lookup(
            circuit,
            gate_indices,
            qubits,
            window.compact_key.as_deref(),
            self.synthesis_table.as_deref(),
        )?
        else {
            // The exact i8 numerator bound was exceeded. Leaving this window
            // untouched is conservative and preserves rewrite soundness.
            return Ok(false);
        };
        let selected = rewrites.consider(cached, gate_indices, qubits);
        if self.collect_subcircuits {
            subcircuits.push(SuperOptWindow {
                gate_indices: gate_indices.to_vec(),
                qubits: qubits.to_vec(),
                matrix: Arc::clone(&cached.matrix),
            });
        }
        Ok(selected)
    }
}

impl Pass for SuperOpt {
    fn name(&self) -> &str {
        "SuperOpt"
    }

    fn run(&self, circuit: &Circuit) -> Circuit {
        match SuperOpt::run(self, circuit) {
            Ok(result) => result.circuit,
            Err(error) => panic!("SuperOpt failed: {error}"),
        }
    }
}

/// Reject gates whose qubit operands fall outside the circuit, so the scan
/// can index per-qubit state unchecked.
fn validate_circuit(circuit: &Circuit) -> Result<(), SuperOptError> {
    for (gate_index, gate) in circuit.gates.iter().enumerate() {
        for qubit in unique_qubits(gate) {
            if qubit >= circuit.num_qubits {
                return Err(SuperOptError::InvalidQubit {
                    gate_index,
                    qubit,
                    num_qubits: circuit.num_qubits,
                });
            }
        }
    }
    Ok(())
}

/// Remove `window_id` from the per-qubit index for each of `qubits` that is not
/// in `exclude`. The excluded qubits are ones a just-attempted expansion
/// inserted into the window but never registered, so they must be skipped.
fn unregister_window(
    window_id: usize,
    qubits: &[Qubit],
    exclude: &[Qubit],
    windows_by_qubit: &mut [Vec<usize>],
) {
    for &qubit in qubits {
        if exclude.contains(&qubit) {
            continue;
        }
        let live = &mut windows_by_qubit[qubit];
        let position = live
            .iter()
            .position(|&live_id| live_id == window_id)
            .expect("window is registered on each of its qubits");
        live.swap_remove(position);
    }
}

/// Extend `window` with `current_gate` and re-close it, scanning only the
/// qubits this step newly introduces.
///
/// The window already holds the connected closure of its anchor over earlier
/// gates, and every gate touching a window qubit expands the window when it is
/// processed, so all history on qubits already in the window is present. Only a
/// gate that bridges in a *new* qubit requires scanning, so the BFS queue is
/// seeded with new qubits alone rather than the whole support.
///
/// Returns whether the window stayed within `max_gates` and `max_qubits`, and
/// the qubits inserted into `window.qubits` by this call (on both paths), none
/// of which have been registered yet.
fn expand_component_closure(
    circuit: &Circuit,
    window: &mut ActiveWindow,
    current_gate: usize,
    current_qubits: &[Qubit],
    gates_by_qubit: &[Vec<usize>],
    max_qubits: usize,
    max_gates: usize,
) -> (bool, QubitVec) {
    /// Admit `qubit` into the sorted support if absent, recording it in
    /// `added` and queueing it for a history scan. False when the support
    /// grows past `max_qubits`.
    fn admit(
        window: &mut ActiveWindow,
        added: &mut QubitVec,
        pending: &mut QubitVec,
        qubit: Qubit,
        max_qubits: usize,
    ) -> bool {
        if let Err(position) = window.qubits.binary_search(&qubit) {
            window.qubits.insert(position, qubit);
            added.push(qubit);
            pending.push(qubit);
            return window.qubits.len() <= max_qubits;
        }
        true
    }

    let mut added = QubitVec::new();
    let mut pending = QubitVec::new();

    let anchor = window.gate_indices[0];
    window.gate_indices.push(current_gate);
    if window.gate_indices.len() > max_gates {
        return (false, added);
    }

    for &qubit in current_qubits {
        if !admit(window, &mut added, &mut pending, qubit, max_qubits) {
            return (false, added);
        }
    }

    while let Some(qubit) = pending.pop() {
        let history = &gates_by_qubit[qubit];
        let start = history.partition_point(|&gate_index| gate_index < anchor);
        for &gate_index in &history[start..] {
            if gate_index > current_gate {
                break;
            }
            if matches!(
                circuit.gates[gate_index],
                Gate::measure { .. } | Gate::reset(_)
            ) {
                return (false, added);
            }
            let Err(position) = window.gate_indices.binary_search(&gate_index) else {
                continue;
            };
            window.gate_indices.insert(position, gate_index);
            if matches!(circuit.gates[gate_index], Gate::rz(..)) {
                window.contains_rz = true;
            }
            if window.gate_indices.len() > max_gates {
                return (false, added);
            }

            for gate_qubit in unique_qubits(&circuit.gates[gate_index]) {
                if !admit(window, &mut added, &mut pending, gate_qubit, max_qubits) {
                    return (false, added);
                }
            }
        }
    }

    (true, added)
}

/// Greedy, non-overlapping rewrite selection over the input's gate positions.
///
/// The first window offered with a strictly smaller replacement claims all
/// its gates; anything overlapping a claimed gate is refused afterwards, so
/// selected rewrites never conflict and [`RewriteSet::apply`] can splice them
/// all in a single reconstruction pass.
struct RewriteSet {
    claimed: Vec<bool>,
    /// Index into `selected` for the rewrite anchored at each gate position.
    anchored: Vec<Option<usize>>,
    selected: Vec<SuperOptRewrite>,
}

impl RewriteSet {
    fn new(gate_count: usize) -> Self {
        Self {
            claimed: vec![false; gate_count],
            anchored: vec![None; gate_count],
            selected: Vec::new(),
        }
    }

    fn is_claimed(&self, gate_index: usize) -> bool {
        self.claimed[gate_index]
    }

    fn claims_any(&self, gate_indices: &[usize]) -> bool {
        gate_indices.iter().any(|&index| self.claimed[index])
    }

    /// Claim this window's rewrite if it has a strictly smaller replacement
    /// and overlaps nothing already claimed. Returns whether it was selected.
    ///
    /// The replacement is stored on the window's *physical* qubits: the
    /// synthesized circuit uses support-local qubits `0..n`, and `qubits[q]`
    /// is exactly where local qubit `q` lives in the input circuit.
    fn consider(
        &mut self,
        cached: &CachedMatrix,
        gate_indices: &[usize],
        qubits: &[Qubit],
    ) -> bool {
        if self.claims_any(gate_indices) {
            return false;
        }
        let Some(local) = cached.synthesized_replacement.as_ref() else {
            return false;
        };
        if local.len() >= gate_indices.len() {
            return false;
        }

        let replacement: Vec<_> = local
            .iter()
            .map(|gate| gate.map_qubits(|q| qubits[q]))
            .collect();
        for &index in gate_indices {
            self.claimed[index] = true;
        }
        self.anchored[gate_indices[0]] = Some(self.selected.len());
        self.selected.push(SuperOptRewrite {
            gate_indices: gate_indices.to_vec(),
            replacement,
        });
        true
    }

    /// Rebuild the circuit with every selected rewrite spliced in: each
    /// replacement is emitted at its window's anchor position, claimed gates
    /// are dropped, and everything else is copied through unchanged. Sound
    /// because a window's members all commute past the unclaimed gates
    /// between them (see the module documentation).
    fn apply(self, circuit: &Circuit) -> (Circuit, Vec<SuperOptRewrite>) {
        let mut optimized = Circuit::with_cbits(circuit.num_qubits, circuit.num_cbits);
        for (index, gate) in circuit.gates.iter().enumerate() {
            if let Some(rewrite) = self.anchored[index] {
                for gate in &self.selected[rewrite].replacement {
                    optimized.apply(gate.clone());
                }
            }
            if !self.claimed[index] {
                optimized.apply(gate.clone());
            }
        }
        (optimized, self.selected)
    }
}

/// A gate's qubit operands, sorted and deduplicated — the window code relies
/// on supports being sorted sets.
fn unique_qubits(gate: &Gate) -> QubitVec {
    let mut qubits: QubitVec = match gate {
        Gate::x(q)
        | Gate::h(q)
        | Gate::s(q)
        | Gate::sdg(q)
        | Gate::z(q)
        | Gate::t(q)
        | Gate::tdg(q)
        | Gate::rz(_, q)
        | Gate::reset(q) => smallvec![*q],
        Gate::cnot { control, target } | Gate::cz { control, target } => {
            smallvec![*control, *target]
        }
        Gate::ccx {
            control1,
            control2,
            target,
        }
        | Gate::ccz {
            control1,
            control2,
            target,
        } => smallvec![*control1, *control2, *target],
        Gate::measure { qubit, .. } => smallvec![*qubit],
    };
    qubits.sort_unstable();
    qubits.dedup();
    qubits
}

#[cfg(test)]
mod tests;
