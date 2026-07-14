/// Bounds for breadth-first enumeration of the peephole synthesis database.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SuperOptTableConfig {
    pub max_qubits: usize,
    pub max_gates: usize,
    /// Enumeration stops independently at this many distinct unitaries per width.
    pub max_entries_per_qubit: usize,
}

impl Default for SuperOptTableConfig {
    fn default() -> Self {
        Self::new(4, 8, 1_000_000)
    }
}

impl SuperOptTableConfig {
    pub const fn new(max_qubits: usize, max_gates: usize, max_entries_per_qubit: usize) -> Self {
        Self {
            max_qubits,
            max_gates,
            max_entries_per_qubit,
        }
    }
}
