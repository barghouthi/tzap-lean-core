use rustc_hash::FxHashMap;

use super::{LibraryGate, UnitaryFingerprint};

#[derive(Clone, Copy, Debug)]
pub(super) struct CircuitNode {
    pub(super) parent: Option<usize>,
    pub(super) gate: Option<LibraryGate>,
}

/// One synthesis-table width stored as a prefix-sharing circuit arena.
#[derive(Clone, Debug, Default)]
pub(super) struct WidthTable {
    pub(super) fingerprints: FxHashMap<UnitaryFingerprint, usize>,
    pub(super) nodes: Vec<CircuitNode>,
}

impl WidthTable {
    pub(super) fn with_identity(fingerprint: UnitaryFingerprint) -> Self {
        let mut table = Self::default();
        table.nodes.push(CircuitNode {
            parent: None,
            gate: None,
        });
        table.fingerprints.insert(fingerprint, 0);
        table
    }

    #[cfg(test)]
    pub(super) fn with_capacity(capacity: usize) -> Self {
        Self {
            fingerprints: FxHashMap::with_capacity_and_hasher(capacity, Default::default()),
            nodes: Vec::with_capacity(capacity),
        }
    }

    pub(super) fn len(&self) -> usize {
        self.fingerprints.len()
    }

    pub(super) fn contains_key(&self, fingerprint: &UnitaryFingerprint) -> bool {
        self.fingerprints.contains_key(fingerprint)
    }

    pub(super) fn node_for(&self, fingerprint: &UnitaryFingerprint) -> Option<usize> {
        self.fingerprints.get(fingerprint).copied()
    }

    pub(super) fn insert_child(
        &mut self,
        fingerprint: UnitaryFingerprint,
        parent: usize,
        gate: LibraryGate,
    ) -> usize {
        let node = self.nodes.len();
        self.nodes.push(CircuitNode {
            parent: Some(parent),
            gate: Some(gate),
        });
        self.fingerprints.insert(fingerprint, node);
        node
    }

    #[cfg(test)]
    pub(super) fn insert_circuit(
        &mut self,
        fingerprint: UnitaryFingerprint,
        circuit: &[LibraryGate],
    ) -> Option<usize> {
        if self.fingerprints.contains_key(&fingerprint) {
            return None;
        }
        let mut parent = None;
        for &gate in circuit {
            let node = self.nodes.len();
            self.nodes.push(CircuitNode {
                parent,
                gate: Some(gate),
            });
            parent = Some(node);
        }
        let node = parent.unwrap_or_else(|| {
            let node = self.nodes.len();
            self.nodes.push(CircuitNode {
                parent: None,
                gate: None,
            });
            node
        });
        self.fingerprints.insert(fingerprint, node);
        Some(node)
    }

    pub(super) fn circuit(&self, mut node: usize) -> Vec<LibraryGate> {
        let mut circuit = Vec::new();
        loop {
            let entry = self.nodes[node];
            if let Some(gate) = entry.gate {
                circuit.push(gate);
            }
            let Some(parent) = entry.parent else {
                break;
            };
            node = parent;
        }
        circuit.reverse();
        circuit
    }
}
