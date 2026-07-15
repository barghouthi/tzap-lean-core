//! The bounded Clifford+T synthesis table: breadth-first enumeration of
//! library-gate circuits keyed by unitary fingerprint, plus the process-wide
//! cache that shares built tables across passes.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};

use rayon::prelude::*;

use crate::circuit::Gate;

use super::matrix::{UnitaryFingerprint, UnitaryMatrix, unitary_fingerprint};
use super::synthesis_arena::WidthTable;
use super::{SuperOptError, SuperOptTableConfig};

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum LibraryGate {
    X(u8),
    H(u8),
    S(u8),
    Sdg(u8),
    Z(u8),
    T(u8),
    Tdg(u8),
    Cnot(u8, u8),
    Cz(u8, u8),
    // Deliberately no Ccx: SuperOpt must not introduce Toffolis (see
    // `library_gates`), so the library cannot even represent one.
}

impl LibraryGate {
    pub(super) fn to_gate(self) -> Gate {
        match self {
            Self::X(q) => Gate::x(q.into()),
            Self::H(q) => Gate::h(q.into()),
            Self::S(q) => Gate::s(q.into()),
            Self::Sdg(q) => Gate::sdg(q.into()),
            Self::Z(q) => Gate::z(q.into()),
            Self::T(q) => Gate::t(q.into()),
            Self::Tdg(q) => Gate::tdg(q.into()),
            Self::Cnot(control, target) => Gate::cnot {
                control: control.into(),
                target: target.into(),
            },
            Self::Cz(control, target) => Gate::cz {
                control: control.into(),
                target: target.into(),
            },
        }
    }

    pub(super) fn qubits(self) -> [Option<u8>; 2] {
        match self {
            Self::X(q)
            | Self::H(q)
            | Self::S(q)
            | Self::Sdg(q)
            | Self::Z(q)
            | Self::T(q)
            | Self::Tdg(q) => [Some(q), None],
            Self::Cnot(left, right) | Self::Cz(left, right) => [Some(left), Some(right)],
        }
    }

    pub(super) fn is_disjoint(self, other: Self) -> bool {
        let left = self.qubits();
        let right = other.qubits();
        left.into_iter()
            .flatten()
            .all(|qubit| !right.contains(&Some(qubit)))
    }

    pub(super) fn is_inverse_of(self, other: Self) -> bool {
        match (self, other) {
            (Self::S(q), Self::Sdg(r))
            | (Self::Sdg(q), Self::S(r))
            | (Self::T(q), Self::Tdg(r))
            | (Self::Tdg(q), Self::T(r)) => q == r,
            _ => {
                self == other
                    && matches!(
                        self,
                        Self::X(_) | Self::H(_) | Self::Z(_) | Self::Cnot(..) | Self::Cz(..)
                    )
            }
        }
    }
}

/// Breadth-first map from a unitary fingerprint to the smallest circuit found.
#[derive(Clone, Debug)]
pub(super) struct UnitaryCircuitTable {
    // Only `entries` serves lookups; the rest is bookkeeping read by tests.
    entries: Vec<WidthTable>,
    #[cfg_attr(not(test), allow(dead_code))]
    saturated: Vec<bool>,
    #[cfg_attr(not(test), allow(dead_code))]
    completed_depth: Vec<usize>,
}

impl UnitaryCircuitTable {
    pub(super) fn build(config: SuperOptTableConfig) -> Result<Self, SuperOptError> {
        if !(1..=4).contains(&config.max_qubits) {
            return Err(SuperOptError::InvalidTableConfig {
                reason: format!("max_qubits must be in 1..=4, got {}", config.max_qubits),
            });
        }
        if config.max_entries_per_qubit == 0 {
            return Err(SuperOptError::InvalidTableConfig {
                reason: "max_entries_per_qubit must be greater than zero".to_owned(),
            });
        }

        let mut entries = vec![WidthTable::default(); config.max_qubits + 1];
        let mut saturated = vec![false; config.max_qubits + 1];
        let mut completed_depth = vec![0; config.max_qubits + 1];
        for num_qubits in 1..=config.max_qubits {
            let identity = UnitaryMatrix::identity(num_qubits)?;
            entries[num_qubits] = WidthTable::with_identity(unitary_fingerprint(&identity));
            let gates = library_gates(num_qubits);
            let support: Vec<_> = (0..num_qubits).collect();
            let mut frontier = vec![(0, identity)];

            // Parents per parallel batch: enough candidates to spread across
            // threads while a batch's survivor list stays small in memory.
            let batch_parents = (65_536 / gates.len()).max(1);

            'depths: for depth in 1..=config.max_gates {
                // Accepted children this layer as (frontier position, node, gate).
                let mut accepted = Vec::new();
                for (batch_index, batch) in frontier.chunks(batch_parents).enumerate() {
                    // Matrix products and fingerprints dominate the build, so
                    // candidates are generated in parallel against a read-only
                    // view of the table. Survivors are then inserted serially
                    // in enumeration order, which keeps the table (and the
                    // exact saturation point) identical to a sequential build;
                    // candidates already present at batch start would have been
                    // skipped by the sequential scan too, so pre-filtering them
                    // in the parallel phase changes nothing.
                    let table = &entries[num_qubits];
                    let batch_survivors: Vec<Vec<(LibraryGate, UnitaryFingerprint)>> = batch
                        .par_iter()
                        .map(|(parent, base)| {
                            let last = table.nodes[*parent].gate;
                            let mut scratch = base.clone();
                            let mut survivors = Vec::new();
                            for &gate in &gates {
                                if let Some(last) = last
                                    && (last.is_inverse_of(gate)
                                        || (last.is_disjoint(gate) && gate < last))
                                {
                                    continue;
                                }
                                scratch.copy_from(base);
                                scratch.apply_gate_left(&gate.to_gate(), &support);
                                let fingerprint = unitary_fingerprint(&scratch);
                                if !table.contains_key(&fingerprint) {
                                    survivors.push((gate, fingerprint));
                                }
                            }
                            survivors
                        })
                        .collect();

                    let table = &mut entries[num_qubits];
                    for (offset, survivors) in batch_survivors.into_iter().enumerate() {
                        let position = batch_index * batch_parents + offset;
                        let parent = frontier[position].0;
                        for (gate, fingerprint) in survivors {
                            if table.contains_key(&fingerprint) {
                                continue;
                            }
                            if table.len() >= config.max_entries_per_qubit {
                                saturated[num_qubits] = true;
                                break 'depths;
                            }
                            let node = table.insert_child(fingerprint, parent, gate);
                            accepted.push((position, node, gate));
                        }
                    }
                }
                completed_depth[num_qubits] = depth;
                if accepted.is_empty() {
                    break;
                }
                // Re-deriving each child from its parent repeats one gate
                // application per accepted node, in exchange for never holding
                // matrices for the (mostly duplicate) rejected candidates.
                let next_frontier = accepted
                    .into_par_iter()
                    .map(|(position, node, gate)| {
                        let mut matrix = frontier[position].1.clone();
                        matrix.apply_gate_left(&gate.to_gate(), &support);
                        (node, matrix)
                    })
                    .collect();
                frontier = next_frontier;
            }
        }

        Ok(Self {
            entries,
            saturated,
            completed_depth,
        })
    }

    #[cfg(test)]
    pub(super) fn entry_count(&self, num_qubits: usize) -> usize {
        self.entries.get(num_qubits).map_or(0, WidthTable::len)
    }

    #[cfg(test)]
    pub(super) fn is_saturated(&self, num_qubits: usize) -> bool {
        self.saturated.get(num_qubits).copied().unwrap_or(false)
    }

    /// Largest gate count whose entire breadth-first layer was enumerated.
    #[cfg(test)]
    pub(super) fn completed_depth(&self, num_qubits: usize) -> usize {
        self.completed_depth.get(num_qubits).copied().unwrap_or(0)
    }

    pub(super) fn synthesize(&self, matrix: &UnitaryMatrix) -> Option<Vec<Gate>> {
        let table = self.entries.get(matrix.num_qubits())?;
        let node = table.node_for(&unitary_fingerprint(matrix))?;
        let circuit = table.circuit(node);
        // The fingerprint is a lossy, rounded hash. This comparison is the
        // release-mode collision guard that makes accepting a rewrite sound;
        // it is not a redundant post-rewrite audit.
        let candidate = library_circuit_matrix(matrix.num_qubits(), &circuit).ok()?;
        matrix
            .equivalent_up_to_global_phase(&candidate)
            .then(|| circuit.into_iter().map(LibraryGate::to_gate).collect())
    }
}

type SharedTable = Result<Arc<UnitaryCircuitTable>, SuperOptError>;
type TableCache = HashMap<SuperOptTableConfig, SharedTable>;

pub(super) fn shared_synthesis_table(config: SuperOptTableConfig) -> SharedTable {
    static TABLES: OnceLock<Mutex<TableCache>> = OnceLock::new();

    let tables = TABLES.get_or_init(|| Mutex::new(HashMap::new()));
    let mut tables = tables
        .lock()
        .expect("SuperOpt synthesis-table cache mutex was poisoned");
    if let Some(table) = tables.get(&config) {
        return table.clone();
    }

    let table = UnitaryCircuitTable::build(config).map(Arc::new);
    tables.insert(config, table.clone());
    table
}

pub(super) fn library_circuit_matrix(
    num_qubits: usize,
    circuit: &[LibraryGate],
) -> Result<UnitaryMatrix, SuperOptError> {
    let support: Vec<_> = (0..num_qubits).collect();
    let mut matrix = UnitaryMatrix::identity(num_qubits)?;
    for &gate in circuit {
        matrix.apply_gate_left(&gate.to_gate(), &support);
    }
    Ok(matrix)
}

pub(super) fn library_gates(num_qubits: usize) -> Vec<LibraryGate> {
    let mut gates = Vec::new();
    for q in 0..num_qubits as u8 {
        gates.extend([
            LibraryGate::X(q),
            LibraryGate::H(q),
            LibraryGate::S(q),
            LibraryGate::Sdg(q),
            LibraryGate::Z(q),
            LibraryGate::T(q),
            LibraryGate::Tdg(q),
        ]);
    }
    for control in 0..num_qubits as u8 {
        for target in 0..num_qubits as u8 {
            if control != target {
                gates.push(LibraryGate::Cnot(control, target));
            }
        }
    }
    for left in 0..num_qubits as u8 {
        for right in left + 1..num_qubits as u8 {
            gates.push(LibraryGate::Cz(left, right));
        }
    }
    // Toffoli is deliberately excluded: SuperOpt must never rewrite a window into
    // a circuit containing a Toffoli, since the pipeline decomposes Toffolis (a
    // single CCX costs ~7 T once lowered). Input Toffolis are still simplified —
    // their windows resolve to Clifford+T table representatives — but never
    // introduced.
    gates
}
