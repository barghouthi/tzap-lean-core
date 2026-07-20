//! Dense unitary matrices for window semantics: complex arithmetic, gate
//! application kernels, phase-canonical fingerprints, and equivalence up to
//! global phase.

use crate::circuit::{Gate, Qubit};

use super::SuperOptError;

pub(super) const IDENTITY_TOLERANCE: f64 = 1e-10;

/// A double-precision complex number used by [`UnitaryMatrix`].
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Complex64 {
    pub re: f64,
    pub im: f64,
}

impl Complex64 {
    pub const ZERO: Self = Self { re: 0.0, im: 0.0 };
    pub const ONE: Self = Self { re: 1.0, im: 0.0 };

    pub const fn new(re: f64, im: f64) -> Self {
        Self { re, im }
    }

    fn polar(radius: f64, angle: f64) -> Self {
        Self::new(radius * angle.cos(), radius * angle.sin())
    }

    pub fn norm_sqr(self) -> f64 {
        self.re * self.re + self.im * self.im
    }

    fn conj(self) -> Self {
        Self::new(self.re, -self.im)
    }
}

impl std::ops::Add for Complex64 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.re + rhs.re, self.im + rhs.im)
    }
}

impl std::ops::Mul for Complex64 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(
            self.re * rhs.re - self.im * rhs.im,
            self.re * rhs.im + self.im * rhs.re,
        )
    }
}

impl std::ops::Mul<f64> for Complex64 {
    type Output = Self;

    fn mul(self, rhs: f64) -> Self::Output {
        Self::new(self.re * rhs, self.im * rhs)
    }
}

/// A dense `2^n` by `2^n` unitary matrix in row-major order.
///
/// Qubit zero is the most significant basis-state bit.
#[derive(Clone, Debug)]
pub struct UnitaryMatrix {
    num_qubits: usize,
    dim: usize,
    data: Vec<Complex64>,
}

impl UnitaryMatrix {
    pub(super) fn identity(num_qubits: usize) -> Result<Self, SuperOptError> {
        // dim * dim entries must fit in usize.
        if num_qubits >= usize::BITS as usize / 2 {
            return Err(SuperOptError::MatrixTooLarge { num_qubits });
        }
        let dim = 1 << num_qubits;
        let mut data = vec![Complex64::ZERO; dim * dim];
        for i in 0..dim {
            data[i * dim + i] = Complex64::ONE;
        }
        Ok(Self {
            num_qubits,
            dim,
            data,
        })
    }

    pub fn num_qubits(&self) -> usize {
        self.num_qubits
    }

    pub fn get(&self, row: usize, column: usize) -> Complex64 {
        self.data[row * self.dim + column]
    }

    pub fn as_slice(&self) -> &[Complex64] {
        &self.data
    }

    pub(super) fn equivalent_up_to_global_phase(&self, other: &Self) -> bool {
        if self.num_qubits != other.num_qubits {
            return false;
        }
        let Some(left_phase) = canonical_phase(self) else {
            return false;
        };
        let Some(right_phase) = canonical_phase(other) else {
            return false;
        };
        self.data.iter().zip(&other.data).all(|(&left, &right)| {
            let left = left * left_phase;
            let right = right * right_phase;
            let delta = Complex64::new(left.re - right.re, left.im - right.im);
            delta.norm_sqr() <= IDENTITY_TOLERANCE * IDENTITY_TOLERANCE
        })
    }

    /// Copy `source` into `self`, reusing the existing allocation.
    pub(super) fn copy_from(&mut self, source: &Self) {
        self.num_qubits = source.num_qubits;
        self.dim = source.dim;
        if self.data.len() == source.data.len() {
            self.data.copy_from_slice(&source.data);
        } else {
            self.data.clone_from(&source.data);
        }
    }

    /// Disjoint mutable views of rows `row0` and `row1`, requiring `row0 < row1`.
    fn row_pair_mut(&mut self, row0: usize, row1: usize) -> (&mut [Complex64], &mut [Complex64]) {
        let dim = self.dim;
        let (head, tail) = self.data.split_at_mut(row1 * dim);
        (&mut head[row0 * dim..(row0 + 1) * dim], &mut tail[..dim])
    }

    fn apply_single_left(&mut self, gate: [[Complex64; 2]; 2], bit: usize) {
        for row0 in 0..self.dim {
            if row0 & bit != 0 {
                continue;
            }
            let (top, bottom) = self.row_pair_mut(row0, row0 | bit);
            for (a, b) in top.iter_mut().zip(bottom) {
                let (x, y) = (*a, *b);
                *a = gate[0][0] * x + gate[0][1] * y;
                *b = gate[1][0] * x + gate[1][1] * y;
            }
        }
    }

    /// X on `target_bit`, controlled on every bit of `control_mask` being set:
    /// swaps each row pair that differs only in the target bit.
    fn apply_controlled_x_left(&mut self, control_mask: usize, target_bit: usize) {
        for row0 in 0..self.dim {
            if row0 & control_mask == control_mask && row0 & target_bit == 0 {
                let (top, bottom) = self.row_pair_mut(row0, row0 | target_bit);
                top.swap_with_slice(bottom);
            }
        }
    }

    /// Negate every row whose basis state has all bits of `mask` set (CZ for a
    /// two-bit mask, CCZ for three).
    fn apply_phase_flip_left(&mut self, mask: usize) {
        let minus_one = Complex64::new(-1.0, 0.0);
        for row in 0..self.dim {
            if row & mask == mask {
                for value in &mut self.data[row * self.dim..(row + 1) * self.dim] {
                    *value = minus_one * *value;
                }
            }
        }
    }

    pub(super) fn apply_gate_left(&mut self, gate: &Gate, support: &[Qubit]) {
        let bit = |q: &Qubit| {
            let local = support.binary_search(q).expect("gate qubit is in support");
            qubit_bit(self.num_qubits, local)
        };
        match gate {
            Gate::x(q) => self.apply_controlled_x_left(0, bit(q)),
            Gate::h(q) => self.apply_single_left(gate_h(), bit(q)),
            Gate::s(q) => self.apply_single_left(gate_s(), bit(q)),
            Gate::sdg(q) => self.apply_single_left(gate_sdg(), bit(q)),
            Gate::z(q) => self.apply_phase_flip_left(bit(q)),
            Gate::t(q) => self.apply_single_left(gate_t(), bit(q)),
            Gate::tdg(q) => self.apply_single_left(gate_tdg(), bit(q)),
            Gate::rz(theta, q) => self.apply_single_left(gate_rz(*theta), bit(q)),
            Gate::cnot { control, target } => {
                self.apply_controlled_x_left(bit(control), bit(target))
            }
            Gate::cz { control, target } => self.apply_phase_flip_left(bit(control) | bit(target)),
            Gate::ccx {
                control1,
                control2,
                target,
            } => self.apply_controlled_x_left(bit(control1) | bit(control2), bit(target)),
            Gate::ccz {
                control1,
                control2,
                target,
            } => self.apply_phase_flip_left(bit(control1) | bit(control2) | bit(target)),
            Gate::measure { .. } | Gate::reset(_) => {
                unreachable!("measurement and reset are window barriers")
            }
        }
    }
}

/// The unit phase that rotates the matrix's first non-negligible entry onto
/// the positive real axis. Multiplying by it cancels any global phase, so
/// phase-equivalent matrices canonicalize to (numerically) the same data.
fn canonical_phase(matrix: &UnitaryMatrix) -> Option<Complex64> {
    matrix.data.iter().find_map(|&entry| {
        let norm = entry.norm_sqr().sqrt();
        (norm > IDENTITY_TOLERANCE).then(|| entry.conj() * (1.0 / norm))
    })
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub(super) struct UnitaryFingerprint {
    first: u64,
    second: u64,
}

impl UnitaryFingerprint {
    /// Raw form for on-disk table persistence; round-trips exactly.
    pub(super) fn to_bits(self) -> (u64, u64) {
        (self.first, self.second)
    }

    pub(super) fn from_bits(first: u64, second: u64) -> Self {
        Self { first, second }
    }
}

/// A 128-bit hash of the phase-canonicalized, coarsely rounded entries:
/// global-phase invariant and drift tolerant, but lossy — equal fingerprints
/// must be confirmed by [`UnitaryMatrix::equivalent_up_to_global_phase`]
/// before acting on them.
pub(super) fn unitary_fingerprint(matrix: &UnitaryMatrix) -> UnitaryFingerprint {
    const SCALE: f64 = 1e9;
    let phase = canonical_phase(matrix).unwrap_or(Complex64::ONE);
    let mut first = 0xcbf2_9ce4_8422_2325u64;
    let mut second = 0x9e37_79b9_7f4a_7c15u64;
    for &entry in &matrix.data {
        let normalized = entry * phase;
        for word in [
            (normalized.re * SCALE).round() as i64 as u64,
            (normalized.im * SCALE).round() as i64 as u64,
        ] {
            first ^= word;
            first = first.wrapping_mul(0x0000_0100_0000_01b3);
            second ^= word.wrapping_add(0x517c_c1b7_2722_0a95);
            second = second.rotate_left(27).wrapping_mul(0x94d0_49bb_1331_11eb);
        }
    }
    UnitaryFingerprint { first, second }
}

fn qubit_bit(num_qubits: usize, position: usize) -> usize {
    1usize << (num_qubits - 1 - position)
}

fn gate_h() -> [[Complex64; 2]; 2] {
    let value = std::f64::consts::FRAC_1_SQRT_2;
    let positive = Complex64::new(value, 0.0);
    let negative = Complex64::new(-value, 0.0);
    [[positive, positive], [positive, negative]]
}

fn gate_s() -> [[Complex64; 2]; 2] {
    [
        [Complex64::ONE, Complex64::ZERO],
        [Complex64::ZERO, Complex64::new(0.0, 1.0)],
    ]
}

fn gate_sdg() -> [[Complex64; 2]; 2] {
    [
        [Complex64::ONE, Complex64::ZERO],
        [Complex64::ZERO, Complex64::new(0.0, -1.0)],
    ]
}

fn gate_t() -> [[Complex64; 2]; 2] {
    [
        [Complex64::ONE, Complex64::ZERO],
        [
            Complex64::ZERO,
            Complex64::polar(1.0, std::f64::consts::FRAC_PI_4),
        ],
    ]
}

fn gate_tdg() -> [[Complex64; 2]; 2] {
    [
        [Complex64::ONE, Complex64::ZERO],
        [
            Complex64::ZERO,
            Complex64::polar(1.0, -std::f64::consts::FRAC_PI_4),
        ],
    ]
}

fn gate_rz(theta: f64) -> [[Complex64; 2]; 2] {
    [
        [Complex64::polar(1.0, -theta / 2.0), Complex64::ZERO],
        [Complex64::ZERO, Complex64::polar(1.0, theta / 2.0)],
    ]
}
