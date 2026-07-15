use std::fmt;

use crate::circuit::Qubit;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SuperOptError {
    ZeroWindowGates,
    InvalidTableConfig {
        reason: String,
    },
    InvalidQubit {
        gate_index: usize,
        qubit: Qubit,
        num_qubits: usize,
    },
    MatrixTooLarge {
        num_qubits: usize,
    },
}

impl fmt::Display for SuperOptError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroWindowGates => write!(f, "window_gates must be greater than zero"),
            Self::InvalidTableConfig { reason } => {
                write!(f, "invalid SuperOpt table config: {reason}")
            }
            Self::InvalidQubit {
                gate_index,
                qubit,
                num_qubits,
            } => write!(
                f,
                "gate {gate_index} references qubit {qubit}, but the circuit has {num_qubits} qubits"
            ),
            Self::MatrixTooLarge { num_qubits } => {
                write!(f, "a dense matrix for {num_qubits} qubits is too large")
            }
        }
    }
}

impl std::error::Error for SuperOptError {}
