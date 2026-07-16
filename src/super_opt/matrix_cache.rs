use std::sync::Arc;

use rustc_hash::FxHashMap;

use crate::circuit::{Circuit, Gate, Qubit};

use super::SuperOptError;
use super::matrix::UnitaryMatrix;
use super::table::UnitaryCircuitTable;

#[derive(Clone, Debug)]
pub(super) struct CachedMatrix {
    pub(super) matrix: Arc<UnitaryMatrix>,
    pub(super) synthesized_replacement: Option<Vec<Gate>>,
}

/// Interned canonical-window matrices. Lookups reuse one scratch key and
/// return a borrowed entry, so the per-emission hot path never allocates on a
/// cache hit.
#[derive(Default)]
pub(super) struct MatrixStore {
    // FxHash: this is probed once per emitted window (millions of times on
    // large circuits), and the keys are short gate sequences where SipHash's
    // per-lookup overhead dominates.
    cache: FxHashMap<Box<[NormalizedGate]>, usize>,
    compact_cache: FxHashMap<u128, usize>,
    entries: Vec<CachedMatrix>,
    scratch: Vec<NormalizedGate>,
    pub(super) hits: usize,
    pub(super) misses: usize,
}

impl MatrixStore {
    pub(super) fn lookup(
        &mut self,
        circuit: &Circuit,
        gate_indices: &[usize],
        qubits: &[Qubit],
        compact_key: Option<u128>,
        table: Option<&UnitaryCircuitTable>,
    ) -> Result<&CachedMatrix, SuperOptError> {
        if let Some(key) = compact_key {
            if let Some(&entry_index) = self.compact_cache.get(&key) {
                self.hits += 1;
                return Ok(&self.entries[entry_index]);
            }
        } else {
            normalized_gate_key(circuit, gate_indices, qubits, &mut self.scratch);
            if let Some(&entry_index) = self.cache.get(self.scratch.as_slice()) {
                self.hits += 1;
                return Ok(&self.entries[entry_index]);
            }
        }

        self.misses += 1;
        let mut matrix = UnitaryMatrix::identity(qubits.len())?;
        for &gate_index in gate_indices {
            matrix.apply_gate_left(&circuit.gates[gate_index], qubits);
        }
        let synthesized_replacement = table.and_then(|table| table.synthesize(&matrix));
        let entry_index = self.entries.len();
        self.entries.push(CachedMatrix {
            synthesized_replacement,
            matrix: Arc::new(matrix),
        });
        if let Some(key) = compact_key {
            self.compact_cache.insert(key, entry_index);
        } else {
            self.cache
                .insert(self.scratch.as_slice().into(), entry_index);
        }
        Ok(&self.entries[entry_index])
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
enum NormalizedGate {
    X(usize),
    H(usize),
    S(usize),
    Sdg(usize),
    Z(usize),
    T(usize),
    Tdg(usize),
    Rz(u64, usize),
    Cnot(usize, usize),
    Cz(usize, usize),
    Ccx(usize, usize, usize),
}

const COMPACT_KEY_LENGTH_BITS: usize = 4;
const COMPACT_GATE_BITS: usize = 12;
const COMPACT_KEY_MAX_GATES: usize =
    (u128::BITS as usize - COMPACT_KEY_LENGTH_BITS) / COMPACT_GATE_BITS;

/// Exact packed normalized key for the common Clifford+T window. Four bits
/// hold the gate count and each gate uses twelve bits, fitting ten gates in a
/// `u128`. Windows containing `rz` use the general key representation below.
pub(super) fn compact_normalized_key(
    circuit: &Circuit,
    gate_indices: &[usize],
    support: &[Qubit],
) -> Option<u128> {
    let mut key = 0;
    for &gate_index in gate_indices {
        key = append_compact_gate_key(key, &circuit.gates[gate_index], support)?;
    }
    Some(key)
}

pub(super) fn append_compact_gate_key(key: u128, gate: &Gate, support: &[Qubit]) -> Option<u128> {
    let length_mask = (1u128 << COMPACT_KEY_LENGTH_BITS) - 1;
    let length = (key & length_mask) as usize;
    if length >= COMPACT_KEY_MAX_GATES {
        return None;
    }
    let encoded = u128::from(compact_gate(gate, support)?);
    let shift = COMPACT_KEY_LENGTH_BITS + length * COMPACT_GATE_BITS;
    Some((key & !length_mask) | (encoded << shift) | (length + 1) as u128)
}

fn compact_gate(gate: &Gate, support: &[Qubit]) -> Option<u16> {
    // Operand positions use two bits each. Wider analyzer-only windows must use
    // the general normalized key instead of silently aliasing local qubits.
    if support.len() > 4 {
        return None;
    }
    let local = |q| {
        support
            .binary_search(&q)
            .expect("window qubit is in support") as u16
    };
    let encode = |tag: u16, first: u16, second: u16, third: u16| {
        tag | (first << 4) | (second << 6) | (third << 8)
    };
    Some(match gate {
        Gate::x(q) => encode(0, local(*q), 0, 0),
        Gate::h(q) => encode(1, local(*q), 0, 0),
        Gate::s(q) => encode(2, local(*q), 0, 0),
        Gate::sdg(q) => encode(3, local(*q), 0, 0),
        Gate::z(q) => encode(4, local(*q), 0, 0),
        Gate::t(q) => encode(5, local(*q), 0, 0),
        Gate::tdg(q) => encode(6, local(*q), 0, 0),
        Gate::cnot { control, target } => encode(7, local(*control), local(*target), 0),
        Gate::cz { control, target } => encode(8, local(*control), local(*target), 0),
        Gate::ccx {
            control1,
            control2,
            target,
        } => encode(9, local(*control1), local(*control2), local(*target)),
        Gate::rz(..) => return None,
        Gate::measure { .. } | Gate::reset(_) => {
            unreachable!("measurement and reset are window barriers")
        }
    })
}

pub(super) fn has_lone_arbitrary_rz(circuit: &Circuit, gate_indices: &[usize]) -> bool {
    let mut arbitrary_rotations = 0;
    for &gate_index in gate_indices {
        if let Gate::rz(theta, _) = circuit.gates[gate_index]
            && !rz_is_clifford_t(theta)
        {
            arbitrary_rotations += 1;
            if arbitrary_rotations > 1 {
                return false;
            }
        }
    }
    arbitrary_rotations == 1
}

fn rz_is_clifford_t(theta: f64) -> bool {
    const ANGLE_TOLERANCE: f64 = 4e-10;
    let step = std::f64::consts::FRAC_PI_4;
    let nearest = (theta / step).round() * step;
    (theta - nearest).abs() <= ANGLE_TOLERANCE
}

fn normalized_gate_key(
    circuit: &Circuit,
    gate_indices: &[usize],
    support: &[Qubit],
    key: &mut Vec<NormalizedGate>,
) {
    let local = |q| {
        support
            .binary_search(&q)
            .expect("window qubit is in support")
    };
    key.clear();
    key.extend(
        gate_indices
            .iter()
            .map(|&gate_index| match &circuit.gates[gate_index] {
                Gate::x(q) => NormalizedGate::X(local(*q)),
                Gate::h(q) => NormalizedGate::H(local(*q)),
                Gate::s(q) => NormalizedGate::S(local(*q)),
                Gate::sdg(q) => NormalizedGate::Sdg(local(*q)),
                Gate::z(q) => NormalizedGate::Z(local(*q)),
                Gate::t(q) => NormalizedGate::T(local(*q)),
                Gate::tdg(q) => NormalizedGate::Tdg(local(*q)),
                Gate::rz(theta, q) => NormalizedGate::Rz(theta.to_bits(), local(*q)),
                Gate::cnot { control, target } => {
                    NormalizedGate::Cnot(local(*control), local(*target))
                }
                Gate::cz { control, target } => NormalizedGate::Cz(local(*control), local(*target)),
                Gate::ccx {
                    control1,
                    control2,
                    target,
                } => NormalizedGate::Ccx(local(*control1), local(*control2), local(*target)),
                Gate::measure { .. } | Gate::reset(_) => {
                    unreachable!("measurement and reset are window barriers")
                }
            }),
    );
}
