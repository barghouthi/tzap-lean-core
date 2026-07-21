/// Bounds for breadth-first enumeration of the peephole synthesis database.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SuperOptTableConfig {
    /// Maximum distinct qubits in a table entry.
    pub max_qubits: usize,
    /// Maximum gates in a table entry. A table entry only ever replaces a
    /// window strictly larger than itself, so this never needs to exceed
    /// `window_gates - 1` for a given [`crate::super_opt::SuperOpt`].
    pub max_gates: usize,
    /// Enumeration stops independently at this many distinct unitaries per width.
    pub max_entries_per_qubit: usize,
}

impl Default for SuperOptTableConfig {
    fn default() -> Self {
        Self::new(3, 8, 200_000)
    }
}

impl SuperOptTableConfig {
    /// See the field docs for the meaning of each bound.
    pub const fn new(max_qubits: usize, max_gates: usize, max_entries_per_qubit: usize) -> Self {
        Self {
            max_qubits,
            max_gates,
            max_entries_per_qubit,
        }
    }
}
