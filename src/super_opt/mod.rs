//! SuperOpt peephole optimization via anchored subcircuit matrices.
//!
//! Every gate starts one window. A window contains the full connected component
//! of its anchor among the gates observed since that anchor. Unrelated gates are
//! skipped, but shared per-qubit history lets a later bridge pull an entire
//! previously disconnected component into the window retroactively. Completed
//! windows are looked up in a bounded synthesis table and replaced when the
//! table has a smaller equivalent circuit.

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
mod matrix;
mod matrix_cache;
mod synthesis_arena;
mod table;

pub use config::SuperOptTableConfig;
pub use error::SuperOptError;
pub use matrix::{Complex64, UnitaryMatrix};

use matrix_cache::{
    CachedMatrix, MatrixStore, append_compact_gate_key, compact_normalized_key,
    has_lone_arbitrary_rz,
};
use table::{UnitaryCircuitTable, shared_synthesis_table};

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
    pub gate_indices: Vec<usize>,
    /// Replacement gates on the original circuit's physical qubits.
    pub replacement: Vec<Gate>,
}

/// Results and matrix-cache statistics from [`SuperOpt::run`].
#[derive(Clone, Debug)]
pub struct SuperOptResult {
    /// Input circuit with a non-overlapping set of strictly smaller rewrites applied.
    pub circuit: Circuit,
    pub subcircuits: Vec<SuperOptWindow>,
    /// Gate positions of rewrites whose table representative is the empty circuit.
    pub removed_subcircuits: Vec<Vec<usize>>,
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
    synthesis_table: Option<Arc<UnitaryCircuitTable>>,
}

#[derive(Debug)]
struct ActiveWindow {
    gate_indices: IndexVec,
    qubits: QubitVec,
    compact_key: Option<u128>,
}

impl SuperOpt {
    pub fn new(
        max_qubits: usize,
        window_gates: usize,
        table_config: SuperOptTableConfig,
    ) -> Result<Self, SuperOptError> {
        Ok(Self::analyzer(max_qubits, window_gates)
            .with_synthesis_table(shared_synthesis_table(table_config)?))
    }

    pub const fn analyzer(max_qubits: usize, window_gates: usize) -> Self {
        Self {
            max_qubits,
            window_gates,
            collect_subcircuits: true,
            synthesis_table: None,
        }
    }

    fn with_synthesis_table(mut self, table: Arc<UnitaryCircuitTable>) -> Self {
        self.synthesis_table = Some(table);
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

    pub fn name(&self) -> &str {
        "SuperOpt"
    }

    /// Run one forward scan while maintaining one closed unitary component per
    /// anchor. Measurement and reset terminate windows on their qubits.
    pub fn run(&self, circuit: &Circuit) -> Result<SuperOptResult, SuperOptError> {
        if self.window_gates == 0 {
            return Err(SuperOptError::ZeroWindowGates);
        }
        validate_circuit(circuit)?;

        let mut active: Vec<Option<ActiveWindow>> = Vec::with_capacity(circuit.gates.len());
        let mut windows_by_qubit: Vec<Vec<usize>> = vec![Vec::new(); circuit.num_qubits];
        let mut gates_by_qubit: Vec<Vec<usize>> = vec![Vec::new(); circuit.num_qubits];
        let mut store = MatrixStore::default();
        let mut subcircuits = Vec::new();
        let mut rewrites = RewriteSet::new(circuit.gates.len());
        let mut touched_windows = Vec::new();

        for (gate_index, gate) in circuit.gates.iter().enumerate() {
            let gate_qubits = unique_qubits(gate);

            touched_windows.clear();
            for &qubit in &gate_qubits {
                touched_windows.extend_from_slice(&windows_by_qubit[qubit]);
                gates_by_qubit[qubit].push(gate_index);
            }
            touched_windows.sort_unstable();
            touched_windows.dedup();

            // Measurement and reset terminate every unitary window touching
            // their qubit. Keep the gate in the per-qubit history so a window
            // on a disjoint qubit cannot later bridge across this barrier.
            if matches!(gate, Gate::measure { .. } | Gate::reset(_)) {
                for &window_id in &touched_windows {
                    let window = active[window_id]
                        .take()
                        .expect("qubit index only contains live windows");
                    unregister_window(window_id, &window.qubits, &[], &mut windows_by_qubit);
                }
                continue;
            }

            for &window_id in &touched_windows {
                let mut window = active[window_id]
                    .take()
                    .expect("qubit index only contains live windows");
                if rewrites.is_claimed(gate_index) || rewrites.claims_any(&window.gate_indices) {
                    unregister_window(window_id, &window.qubits, &[], &mut windows_by_qubit);
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
                    unregister_window(
                        window_id,
                        &window.qubits,
                        &added_qubits,
                        &mut windows_by_qubit,
                    );
                    continue;
                }

                if added_qubits.is_empty() {
                    window.compact_key = window
                        .compact_key
                        .and_then(|key| append_compact_gate_key(key, gate, &window.qubits));
                } else {
                    window.compact_key =
                        compact_normalized_key(circuit, &window.gate_indices, &window.qubits);
                }

                let at_gate_limit = window.gate_indices.len() == self.window_gates;
                let selected = self.analyze_window(
                    circuit,
                    &window.gate_indices,
                    &window.qubits,
                    window.compact_key,
                    &mut store,
                    &mut rewrites,
                    &mut subcircuits,
                )?;

                if at_gate_limit || selected {
                    unregister_window(
                        window_id,
                        &window.qubits,
                        &added_qubits,
                        &mut windows_by_qubit,
                    );
                } else {
                    for &qubit in &added_qubits {
                        windows_by_qubit[qubit].push(window_id);
                    }
                    active[window_id] = Some(window);
                }
            }

            // The current gate anchors a new one-gate closed component.
            if gate_qubits.len() <= self.max_qubits && !rewrites.is_claimed(gate_index) {
                let indices: IndexVec = smallvec![gate_index];
                let compact_key = compact_normalized_key(circuit, &indices, &gate_qubits);
                // A single non-identity gate can only be rewritten to the empty
                // circuit, which requires its matrix to be identity up to phase.
                // Only `rz` can be that (rz(0)); every other library gate never
                // is, so its lookup can never yield a rewrite. Skip it unless we
                // must collect the window's diagnostics.
                if self.collect_subcircuits || matches!(gate, Gate::rz(..)) {
                    self.analyze_window(
                        circuit,
                        &indices,
                        &gate_qubits,
                        compact_key,
                        &mut store,
                        &mut rewrites,
                        &mut subcircuits,
                    )?;
                }

                if self.window_gates > 1 && !rewrites.is_claimed(gate_index) {
                    let window_id = active.len();
                    for &qubit in &gate_qubits {
                        windows_by_qubit[qubit].push(window_id);
                    }
                    active.push(Some(ActiveWindow {
                        gate_indices: indices,
                        qubits: gate_qubits,
                        compact_key,
                    }));
                }
            }
        }

        subcircuits.sort_by(|left, right| left.gate_indices.cmp(&right.gate_indices));
        let (optimized, removed_subcircuits, rewrites) = rewrites.apply(circuit);
        Ok(SuperOptResult {
            circuit: optimized,
            subcircuits,
            removed_subcircuits,
            rewrites,
            cache_hits: store.hits,
            cache_misses: store.misses,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn analyze_window(
        &self,
        circuit: &Circuit,
        gate_indices: &[usize],
        qubits: &[Qubit],
        compact_key: Option<u128>,
        store: &mut MatrixStore,
        rewrites: &mut RewriteSet,
        subcircuits: &mut Vec<SuperOptWindow>,
    ) -> Result<bool, SuperOptError> {
        if !self.collect_subcircuits
            && self.synthesis_table.is_some()
            && has_lone_arbitrary_rz(circuit, gate_indices)
        {
            return Ok(false);
        }
        let cached = store.lookup(
            circuit,
            gate_indices,
            qubits,
            compact_key,
            self.synthesis_table.as_deref(),
        )?;
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
        SuperOpt::name(self)
    }

    fn run(&self, circuit: &Circuit) -> Circuit {
        match SuperOpt::run(self, circuit) {
            Ok(result) => result.circuit,
            Err(error) => panic!("SuperOpt failed: {error}"),
        }
    }
}

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
    let mut added = QubitVec::new();
    let mut pending = QubitVec::new();

    let anchor = window.gate_indices[0];
    window.gate_indices.push(current_gate);
    if window.gate_indices.len() > max_gates {
        return (false, added);
    }

    for &qubit in current_qubits {
        if let Err(position) = window.qubits.binary_search(&qubit) {
            window.qubits.insert(position, qubit);
            added.push(qubit);
            pending.push(qubit);
            if window.qubits.len() > max_qubits {
                return (false, added);
            }
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
            if window.gate_indices.len() > max_gates {
                return (false, added);
            }

            for gate_qubit in unique_qubits(&circuit.gates[gate_index]) {
                if let Err(position) = window.qubits.binary_search(&gate_qubit) {
                    window.qubits.insert(position, gate_qubit);
                    added.push(gate_qubit);
                    pending.push(gate_qubit);
                    if window.qubits.len() > max_qubits {
                        return (false, added);
                    }
                }
            }
        }
    }

    (true, added)
}

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
            .map(|gate| map_gate_to_physical(gate, qubits))
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

    fn apply(self, circuit: &Circuit) -> (Circuit, Vec<Vec<usize>>, Vec<SuperOptRewrite>) {
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
        let mut removed: Vec<_> = self
            .selected
            .iter()
            .filter(|rewrite| rewrite.replacement.is_empty())
            .map(|rewrite| rewrite.gate_indices.clone())
            .collect();
        removed.sort();
        (optimized, removed, self.selected)
    }
}

fn map_gate_to_physical(gate: &Gate, qubits: &[Qubit]) -> Gate {
    let physical = |q: Qubit| qubits[q];
    match gate {
        Gate::x(q) => Gate::x(physical(*q)),
        Gate::h(q) => Gate::h(physical(*q)),
        Gate::s(q) => Gate::s(physical(*q)),
        Gate::sdg(q) => Gate::sdg(physical(*q)),
        Gate::z(q) => Gate::z(physical(*q)),
        Gate::t(q) => Gate::t(physical(*q)),
        Gate::tdg(q) => Gate::tdg(physical(*q)),
        Gate::rz(theta, q) => Gate::rz(*theta, physical(*q)),
        Gate::cnot { control, target } => Gate::cnot {
            control: physical(*control),
            target: physical(*target),
        },
        Gate::cz { control, target } => Gate::cz {
            control: physical(*control),
            target: physical(*target),
        },
        Gate::ccx {
            control1,
            control2,
            target,
        } => Gate::ccx {
            control1: physical(*control1),
            control2: physical(*control2),
            target: physical(*target),
        },
        Gate::measure { .. } | Gate::reset(_) => unreachable!("library is unitary"),
    }
}

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
        } => smallvec![*control1, *control2, *target],
        Gate::measure { qubit, .. } => smallvec![*qubit],
    };
    qubits.sort_unstable();
    qubits.dedup();
    qubits
}

#[cfg(test)]
mod tests;
