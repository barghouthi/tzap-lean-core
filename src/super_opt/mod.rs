//! SuperOpt peephole optimization via anchored subcircuit matrices.
//!
//! Every gate starts one window. A window contains the full connected component
//! of its anchor among the gates observed since that anchor. Unrelated gates are
//! skipped, but shared per-qubit history lets a later bridge pull an entire
//! previously disconnected component into the window retroactively. Completed
//! windows are looked up in a bounded synthesis table and replaced when the
//! table has a smaller equivalent circuit.

use std::collections::HashMap;
#[cfg(test)]
use std::io::Read;
#[cfg(test)]
use std::io::Write;
#[cfg(test)]
use std::path::Path;
use std::sync::{Arc, Mutex, OnceLock};

use crate::circuit::{Circuit, Gate, Qubit, qubits_of};
use crate::pass::Pass;

mod config;
mod error;

pub use config::SuperOptTableConfig;
pub use error::SuperOptError;

const IDENTITY_TOLERANCE: f64 = 1e-10;

/// A double-precision complex number used by [`UnitaryMatrix`].
#[derive(Clone, Copy, Debug, Default, PartialEq)]
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
#[derive(Clone, Debug, PartialEq)]
pub struct UnitaryMatrix {
    num_qubits: usize,
    dim: usize,
    data: Vec<Complex64>,
}

impl UnitaryMatrix {
    fn identity(num_qubits: usize) -> Result<Self, SuperOptError> {
        let dim = 1usize
            .checked_shl(num_qubits.try_into().unwrap_or(u32::MAX))
            .ok_or(SuperOptError::MatrixTooLarge { num_qubits })?;
        let len = dim
            .checked_mul(dim)
            .ok_or(SuperOptError::MatrixTooLarge { num_qubits })?;
        let mut data = vec![Complex64::ZERO; len];
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

    pub fn dimension(&self) -> usize {
        self.dim
    }

    pub fn get(&self, row: usize, column: usize) -> Complex64 {
        self.data[row * self.dim + column]
    }

    pub fn as_slice(&self) -> &[Complex64] {
        &self.data
    }

    fn equivalent_up_to_global_phase(&self, other: &Self, tolerance: f64) -> bool {
        if self.num_qubits != other.num_qubits {
            return false;
        }
        let Some(left_phase) = canonical_phase(self, tolerance) else {
            return false;
        };
        let Some(right_phase) = canonical_phase(other, tolerance) else {
            return false;
        };
        self.data.iter().zip(&other.data).all(|(&left, &right)| {
            let left = left * left_phase;
            let right = right * right_phase;
            let delta = Complex64::new(left.re - right.re, left.im - right.im);
            delta.norm_sqr() <= tolerance * tolerance
        })
    }

    fn set(&mut self, row: usize, column: usize, value: Complex64) {
        self.data[row * self.dim + column] = value;
    }

    fn apply_single_left(&mut self, gate: [[Complex64; 2]; 2], q: usize) {
        let bit = qubit_bit(self.num_qubits, q);
        for column in 0..self.dim {
            for row0 in 0..self.dim {
                if row0 & bit != 0 {
                    continue;
                }
                let row1 = row0 | bit;
                let a = self.get(row0, column);
                let b = self.get(row1, column);
                self.set(row0, column, gate[0][0] * a + gate[0][1] * b);
                self.set(row1, column, gate[1][0] * a + gate[1][1] * b);
            }
        }
    }

    fn apply_cnot_left(&mut self, control: usize, target: usize) {
        let control_bit = qubit_bit(self.num_qubits, control);
        let target_bit = qubit_bit(self.num_qubits, target);
        for column in 0..self.dim {
            for row0 in 0..self.dim {
                if row0 & control_bit != 0 && row0 & target_bit == 0 {
                    let row1 = row0 | target_bit;
                    let a = self.get(row0, column);
                    let b = self.get(row1, column);
                    self.set(row0, column, b);
                    self.set(row1, column, a);
                }
            }
        }
    }

    fn apply_cz_left(&mut self, control: usize, target: usize) {
        let control_bit = qubit_bit(self.num_qubits, control);
        let target_bit = qubit_bit(self.num_qubits, target);
        let minus_one = Complex64::new(-1.0, 0.0);
        for row in 0..self.dim {
            if row & control_bit != 0 && row & target_bit != 0 {
                for column in 0..self.dim {
                    self.set(row, column, minus_one * self.get(row, column));
                }
            }
        }
    }

    fn apply_ccx_left(&mut self, control1: usize, control2: usize, target: usize) {
        let control1_bit = qubit_bit(self.num_qubits, control1);
        let control2_bit = qubit_bit(self.num_qubits, control2);
        let target_bit = qubit_bit(self.num_qubits, target);
        for column in 0..self.dim {
            for row0 in 0..self.dim {
                if row0 & control1_bit != 0 && row0 & control2_bit != 0 && row0 & target_bit == 0 {
                    let row1 = row0 | target_bit;
                    let a = self.get(row0, column);
                    let b = self.get(row1, column);
                    self.set(row0, column, b);
                    self.set(row1, column, a);
                }
            }
        }
    }

    fn apply_gate_left(&mut self, gate: &Gate, support: &[Qubit]) {
        let local = |q| support.binary_search(&q).expect("gate qubit is in support");
        match gate {
            Gate::x(q) => self.apply_single_left(gate_x(), local(*q)),
            Gate::h(q) => self.apply_single_left(gate_h(), local(*q)),
            Gate::s(q) => self.apply_single_left(gate_s(), local(*q)),
            Gate::sdg(q) => self.apply_single_left(gate_sdg(), local(*q)),
            Gate::z(q) => self.apply_single_left(gate_z(), local(*q)),
            Gate::t(q) => self.apply_single_left(gate_t(), local(*q)),
            Gate::tdg(q) => self.apply_single_left(gate_tdg(), local(*q)),
            Gate::rz(theta, q) => self.apply_single_left(gate_rz(*theta), local(*q)),
            Gate::cnot { control, target } => {
                self.apply_cnot_left(local(*control), local(*target));
            }
            Gate::cz { control, target } => {
                self.apply_cz_left(local(*control), local(*target));
            }
            Gate::ccx {
                control1,
                control2,
                target,
            } => self.apply_ccx_left(local(*control1), local(*control2), local(*target)),
            Gate::measure { .. } | Gate::reset(_) => unreachable!("validated as unitary"),
        }
    }
}

fn canonical_phase(matrix: &UnitaryMatrix, tolerance: f64) -> Option<Complex64> {
    matrix.data.iter().find_map(|&entry| {
        let norm = entry.norm_sqr().sqrt();
        (norm > tolerance).then(|| entry.conj() * (1.0 / norm))
    })
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
struct UnitaryFingerprint {
    first: u64,
    second: u64,
}

fn unitary_fingerprint(matrix: &UnitaryMatrix) -> UnitaryFingerprint {
    const SCALE: f64 = 1e9;
    let phase = canonical_phase(matrix, IDENTITY_TOLERANCE).unwrap_or(Complex64::ONE);
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

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum LibraryGate {
    X(u8),
    H(u8),
    S(u8),
    Sdg(u8),
    Z(u8),
    T(u8),
    Tdg(u8),
    Cnot(u8, u8),
    Cz(u8, u8),
    Ccx(u8, u8, u8),
}

impl LibraryGate {
    fn to_gate(self) -> Gate {
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
            Self::Ccx(control1, control2, target) => Gate::ccx {
                control1: control1.into(),
                control2: control2.into(),
                target: target.into(),
            },
        }
    }

    fn qubits(self) -> [Option<u8>; 3] {
        match self {
            Self::X(q)
            | Self::H(q)
            | Self::S(q)
            | Self::Sdg(q)
            | Self::Z(q)
            | Self::T(q)
            | Self::Tdg(q) => [Some(q), None, None],
            Self::Cnot(left, right) | Self::Cz(left, right) => [Some(left), Some(right), None],
            Self::Ccx(first, second, third) => [Some(first), Some(second), Some(third)],
        }
    }

    fn is_disjoint(self, other: Self) -> bool {
        let left = self.qubits();
        let right = other.qubits();
        left.into_iter()
            .flatten()
            .all(|qubit| !right.contains(&Some(qubit)))
    }

    fn is_inverse_of(self, other: Self) -> bool {
        match (self, other) {
            (Self::S(q), Self::Sdg(r))
            | (Self::Sdg(q), Self::S(r))
            | (Self::T(q), Self::Tdg(r))
            | (Self::Tdg(q), Self::T(r)) => q == r,
            _ => {
                self == other
                    && matches!(
                        self,
                        Self::X(_)
                            | Self::H(_)
                            | Self::Z(_)
                            | Self::Cnot(..)
                            | Self::Cz(..)
                            | Self::Ccx(..)
                    )
            }
        }
    }

    #[cfg(test)]
    fn encode(self) -> [u8; 4] {
        match self {
            Self::X(q) => [0, q, u8::MAX, u8::MAX],
            Self::H(q) => [1, q, u8::MAX, u8::MAX],
            Self::S(q) => [2, q, u8::MAX, u8::MAX],
            Self::Sdg(q) => [3, q, u8::MAX, u8::MAX],
            Self::Z(q) => [4, q, u8::MAX, u8::MAX],
            Self::T(q) => [5, q, u8::MAX, u8::MAX],
            Self::Tdg(q) => [6, q, u8::MAX, u8::MAX],
            Self::Cnot(control, target) => [7, control, target, u8::MAX],
            Self::Cz(control, target) => [8, control, target, u8::MAX],
            Self::Ccx(control1, control2, target) => [9, control1, control2, target],
        }
    }

    #[cfg(test)]
    fn decode(encoded: [u8; 4], num_qubits: usize) -> Result<Self, SuperOptError> {
        let [tag, first, second, third] = encoded;
        let gate = match tag {
            0 => Self::X(first),
            1 => Self::H(first),
            2 => Self::S(first),
            3 => Self::Sdg(first),
            4 => Self::Z(first),
            5 => Self::T(first),
            6 => Self::Tdg(first),
            7 => Self::Cnot(first, second),
            8 => Self::Cz(first, second),
            9 => Self::Ccx(first, second, third),
            _ => return Err(invalid_table_file(format!("unknown gate tag {tag}"))),
        };
        let qubits: Vec<_> = gate.qubits().into_iter().flatten().collect();
        if qubits.iter().any(|&qubit| qubit as usize >= num_qubits) {
            return Err(invalid_table_file(format!(
                "gate {gate:?} is outside a {num_qubits}-qubit table"
            )));
        }
        let valid_operands = match gate {
            Self::Cnot(control, target) => control != target,
            Self::Cz(left, right) => left < right,
            Self::Ccx(control1, control2, target) => {
                control1 < control2 && control1 != target && control2 != target
            }
            _ => true,
        };
        if !valid_operands {
            return Err(invalid_table_file(format!(
                "gate {gate:?} has invalid operands"
            )));
        }
        Ok(gate)
    }
}

/// Breadth-first map from a unitary fingerprint to the smallest circuit found.
#[derive(Clone, Debug)]
struct UnitaryCircuitTable {
    #[cfg(test)]
    config: SuperOptTableConfig,
    entries: Vec<HashMap<UnitaryFingerprint, Box<[LibraryGate]>>>,
    #[cfg(test)]
    saturated: Vec<bool>,
    #[cfg(test)]
    completed_depth: Vec<usize>,
}

impl UnitaryCircuitTable {
    #[cfg(test)]
    const FILE_MAGIC: [u8; 8] = *b"TZUCTBL1";

    fn build(config: SuperOptTableConfig) -> Result<Self, SuperOptError> {
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

        let mut entries = vec![HashMap::new(); config.max_qubits + 1];
        let mut saturated = vec![false; config.max_qubits + 1];
        let mut completed_depth = vec![0; config.max_qubits + 1];
        for num_qubits in 1..=config.max_qubits {
            let identity = UnitaryMatrix::identity(num_qubits)?;
            entries[num_qubits].insert(
                unitary_fingerprint(&identity),
                Vec::new().into_boxed_slice(),
            );
            let gates = library_gates(num_qubits);
            let support: Vec<_> = (0..num_qubits).collect();
            let mut frontier: Vec<Box<[LibraryGate]>> = vec![Vec::new().into_boxed_slice()];

            'depths: for depth in 1..=config.max_gates {
                let mut next_frontier = Vec::new();
                for circuit in frontier {
                    let base = library_circuit_matrix(num_qubits, &circuit)?;
                    for &gate in &gates {
                        if let Some(&last) = circuit.last()
                            && (last.is_inverse_of(gate) || (last.is_disjoint(gate) && gate < last))
                        {
                            continue;
                        }

                        let mut matrix = base.clone();
                        matrix.apply_gate_left(&gate.to_gate(), &support);
                        let fingerprint = unitary_fingerprint(&matrix);
                        if entries[num_qubits].contains_key(&fingerprint) {
                            continue;
                        }

                        if entries[num_qubits].len() >= config.max_entries_per_qubit {
                            saturated[num_qubits] = true;
                            break 'depths;
                        }
                        let mut candidate = circuit.to_vec();
                        candidate.push(gate);
                        let candidate = candidate.into_boxed_slice();
                        entries[num_qubits].insert(fingerprint, candidate.clone());
                        next_frontier.push(candidate);
                    }
                }
                if next_frontier.is_empty() {
                    completed_depth[num_qubits] = depth;
                    break;
                }
                completed_depth[num_qubits] = depth;
                frontier = next_frontier;
            }
        }

        Ok(Self {
            #[cfg(test)]
            config,
            entries,
            #[cfg(test)]
            saturated,
            #[cfg(test)]
            completed_depth,
        })
    }

    #[cfg(test)]
    fn entry_count(&self, num_qubits: usize) -> usize {
        self.entries.get(num_qubits).map_or(0, HashMap::len)
    }

    #[cfg(test)]
    fn is_saturated(&self, num_qubits: usize) -> bool {
        self.saturated.get(num_qubits).copied().unwrap_or(false)
    }

    #[cfg(test)]
    fn max_gates(&self) -> usize {
        self.config.max_gates
    }

    /// Largest gate count whose entire breadth-first layer was enumerated.
    #[cfg(test)]
    fn completed_depth(&self, num_qubits: usize) -> usize {
        self.completed_depth.get(num_qubits).copied().unwrap_or(0)
    }

    fn synthesize(&self, matrix: &UnitaryMatrix) -> Option<Vec<Gate>> {
        let circuit = self
            .entries
            .get(matrix.num_qubits())?
            .get(&unitary_fingerprint(matrix))?;
        let candidate = library_circuit_matrix(matrix.num_qubits(), circuit).ok()?;
        matrix
            .equivalent_up_to_global_phase(&candidate, IDENTITY_TOLERANCE)
            .then(|| circuit.iter().map(|gate| gate.to_gate()).collect())
    }

    /// Serialize this table in a deterministic compact binary format.
    ///
    /// The file is written to a sibling temporary path and atomically renamed
    /// after it has been flushed, so an interrupted save does not replace an
    /// existing table with a partial file.
    #[cfg(test)]
    fn save(&self, path: impl AsRef<Path>) -> Result<(), SuperOptError> {
        let path = path.as_ref();
        if let Some(parent) = path.parent()
            && !parent.as_os_str().is_empty()
        {
            std::fs::create_dir_all(parent).map_err(|error| table_io_error("create", error))?;
        }
        let temporary =
            path.with_extension(match path.extension().and_then(|value| value.to_str()) {
                Some(extension) => format!("{extension}.tmp"),
                None => "tmp".to_owned(),
            });
        let file =
            std::fs::File::create(&temporary).map_err(|error| table_io_error("create", error))?;
        let mut writer = std::io::BufWriter::new(file);
        self.write_to(&mut writer)?;
        writer
            .flush()
            .map_err(|error| table_io_error("flush", error))?;
        writer
            .get_ref()
            .sync_all()
            .map_err(|error| table_io_error("sync", error))?;
        drop(writer);
        std::fs::rename(&temporary, path).map_err(|error| table_io_error("rename", error))?;
        Ok(())
    }

    /// Load a table previously written by [`Self::save`].
    #[cfg(test)]
    fn load(path: impl AsRef<Path>) -> Result<Self, SuperOptError> {
        let file = std::fs::File::open(path).map_err(|error| table_io_error("open", error))?;
        Self::read_from(&mut std::io::BufReader::new(file))
    }

    #[cfg(test)]
    fn write_to(&self, writer: &mut impl Write) -> Result<(), SuperOptError> {
        writer
            .write_all(&Self::FILE_MAGIC)
            .map_err(|error| table_io_error("write", error))?;
        write_u64(writer, self.config.max_qubits as u64)?;
        write_u64(writer, self.config.max_gates as u64)?;
        write_u64(writer, self.config.max_entries_per_qubit as u64)?;

        for num_qubits in 1..=self.config.max_qubits {
            writer
                .write_all(&[num_qubits as u8, u8::from(self.saturated[num_qubits])])
                .map_err(|error| table_io_error("write", error))?;
            write_u64(writer, self.completed_depth[num_qubits] as u64)?;
            write_u64(writer, self.entries[num_qubits].len() as u64)?;

            let mut ordered: Vec<_> = self.entries[num_qubits].iter().collect();
            ordered
                .sort_unstable_by_key(|(fingerprint, _)| (fingerprint.first, fingerprint.second));
            for (fingerprint, circuit) in ordered {
                write_u64(writer, fingerprint.first)?;
                write_u64(writer, fingerprint.second)?;
                write_u64(writer, circuit.len() as u64)?;
                for &gate in circuit.iter() {
                    writer
                        .write_all(&gate.encode())
                        .map_err(|error| table_io_error("write", error))?;
                }
            }
        }
        Ok(())
    }

    #[cfg(test)]
    fn read_from(reader: &mut impl Read) -> Result<Self, SuperOptError> {
        let mut magic = [0; 8];
        read_exact(reader, &mut magic)?;
        if magic != Self::FILE_MAGIC {
            return Err(invalid_table_file("invalid magic or unsupported version"));
        }

        let config = SuperOptTableConfig {
            max_qubits: read_usize(reader, "max_qubits")?,
            max_gates: read_usize(reader, "max_gates")?,
            max_entries_per_qubit: read_usize(reader, "max_entries_per_qubit")?,
        };
        if config.max_qubits == 0 || config.max_qubits > 4 {
            return Err(invalid_table_file(format!(
                "invalid qubit bound {}",
                config.max_qubits
            )));
        }
        if config.max_entries_per_qubit == 0 {
            return Err(invalid_table_file("zero entry bound"));
        }

        let mut entries = vec![HashMap::new(); config.max_qubits + 1];
        let mut saturated = vec![false; config.max_qubits + 1];
        let mut completed_depth = vec![0; config.max_qubits + 1];
        for num_qubits in 1..=config.max_qubits {
            let mut header = [0; 2];
            read_exact(reader, &mut header)?;
            if header[0] as usize != num_qubits || header[1] > 1 {
                return Err(invalid_table_file(format!(
                    "invalid width header {:?} for {num_qubits} qubits",
                    header
                )));
            }
            saturated[num_qubits] = header[1] == 1;
            completed_depth[num_qubits] = read_usize(reader, "completed_depth")?;
            if completed_depth[num_qubits] > config.max_gates {
                return Err(invalid_table_file("completed depth exceeds gate bound"));
            }
            let entry_count = read_usize(reader, "entry_count")?;
            if entry_count > config.max_entries_per_qubit {
                return Err(invalid_table_file("entry count exceeds configured bound"));
            }
            entries[num_qubits] = HashMap::with_capacity(entry_count.min(1_000_000));

            for _ in 0..entry_count {
                let fingerprint = UnitaryFingerprint {
                    first: read_u64(reader)?,
                    second: read_u64(reader)?,
                };
                let gate_count = read_usize(reader, "gate_count")?;
                if gate_count > config.max_gates {
                    return Err(invalid_table_file("circuit exceeds gate bound"));
                }
                let mut circuit = Vec::with_capacity(gate_count);
                for _ in 0..gate_count {
                    let mut encoded = [0; 4];
                    read_exact(reader, &mut encoded)?;
                    circuit.push(LibraryGate::decode(encoded, num_qubits)?);
                }
                if entries[num_qubits]
                    .insert(fingerprint, circuit.into_boxed_slice())
                    .is_some()
                {
                    return Err(invalid_table_file("duplicate unitary fingerprint"));
                }
            }

            let identity = UnitaryMatrix::identity(num_qubits)?;
            if !entries[num_qubits].contains_key(&unitary_fingerprint(&identity)) {
                return Err(invalid_table_file(format!(
                    "{num_qubits}-qubit table is missing identity"
                )));
            }
        }

        let mut trailing = [0; 1];
        match reader.read(&mut trailing) {
            Ok(0) => {}
            Ok(_) => return Err(invalid_table_file("trailing bytes after table")),
            Err(error) => return Err(table_io_error("read", error)),
        }

        Ok(Self {
            #[cfg(test)]
            config,
            entries,
            #[cfg(test)]
            saturated,
            #[cfg(test)]
            completed_depth,
        })
    }
}

type SharedTable = Result<Arc<UnitaryCircuitTable>, SuperOptError>;
type TableCache = HashMap<SuperOptTableConfig, SharedTable>;

fn shared_synthesis_table(config: SuperOptTableConfig) -> SharedTable {
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

#[cfg(test)]
fn write_u64(writer: &mut impl Write, value: u64) -> Result<(), SuperOptError> {
    writer
        .write_all(&value.to_le_bytes())
        .map_err(|error| table_io_error("write", error))
}

#[cfg(test)]
fn read_u64(reader: &mut impl Read) -> Result<u64, SuperOptError> {
    let mut bytes = [0; 8];
    read_exact(reader, &mut bytes)?;
    Ok(u64::from_le_bytes(bytes))
}

#[cfg(test)]
fn read_usize(reader: &mut impl Read, field: &'static str) -> Result<usize, SuperOptError> {
    usize::try_from(read_u64(reader)?)
        .map_err(|_| invalid_table_file(format!("{field} does not fit usize")))
}

#[cfg(test)]
fn read_exact(reader: &mut impl Read, bytes: &mut [u8]) -> Result<(), SuperOptError> {
    reader
        .read_exact(bytes)
        .map_err(|error| table_io_error("read", error))
}

#[cfg(test)]
fn table_io_error(operation: &'static str, error: std::io::Error) -> SuperOptError {
    SuperOptError::TableIo {
        operation,
        message: error.to_string(),
    }
}

#[cfg(test)]
fn invalid_table_file(reason: impl Into<String>) -> SuperOptError {
    SuperOptError::InvalidTableFile {
        reason: reason.into(),
    }
}

fn library_circuit_matrix(
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

fn library_gates(num_qubits: usize) -> Vec<LibraryGate> {
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
    for target in 0..num_qubits as u8 {
        for first in 0..num_qubits as u8 {
            for second in first + 1..num_qubits as u8 {
                if first != target && second != target {
                    gates.push(LibraryGate::Ccx(first, second, target));
                }
            }
        }
    }
    gates
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
    pub gate_indices: Vec<usize>,
    /// Replacement gates on the original circuit's physical qubits.
    pub replacement: Vec<Gate>,
}

/// Results and matrix-cache statistics from [`SuperOptPass::run`].
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
pub struct SuperOptPass {
    /// Maximum number of distinct qubits in a tracked window.
    pub max_qubits: usize,
    /// Maximum number of connected gates in a reported window.
    pub window_gates: usize,
    collect_subcircuits: bool,
    synthesis_table: Option<Arc<UnitaryCircuitTable>>,
}

#[derive(Debug)]
struct ActiveWindow {
    gate_indices: Vec<usize>,
    qubits: Vec<Qubit>,
}

#[derive(Clone, Debug)]
struct CachedMatrix {
    matrix: Arc<UnitaryMatrix>,
    synthesized_replacement: Option<Vec<Gate>>,
}

impl SuperOptPass {
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

    /// Run one forward scan while maintaining one closed component per anchor.
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
        // Reused across every window expansion so the common append-only path
        // allocates nothing: `added` collects qubits this step introduced,
        // `pending` is the BFS queue over only those new qubits.
        let mut added_qubits: Vec<Qubit> = Vec::new();
        let mut pending_qubits: Vec<Qubit> = Vec::new();

        for (gate_index, gate) in circuit.gates.iter().enumerate() {
            let gate_qubits = unique_qubits(gate);

            touched_windows.clear();
            for &qubit in &gate_qubits {
                touched_windows.extend_from_slice(&windows_by_qubit[qubit]);
                gates_by_qubit[qubit].push(gate_index);
            }
            touched_windows.sort_unstable();
            touched_windows.dedup();

            for &window_id in &touched_windows {
                let mut window = active[window_id]
                    .take()
                    .expect("qubit index only contains live windows");
                let within_bounds = expand_component_closure(
                    circuit,
                    &mut window,
                    gate_index,
                    &gate_qubits,
                    &gates_by_qubit,
                    self.max_qubits,
                    self.window_gates,
                    &mut added_qubits,
                    &mut pending_qubits,
                );
                // `added_qubits` were inserted into `window.qubits` but never
                // registered, so unregistration must skip them; the remaining
                // qubits are exactly the set this window was registered on.
                if !within_bounds {
                    unregister_window(
                        window_id,
                        &window.qubits,
                        &added_qubits,
                        &mut windows_by_qubit,
                    );
                    continue;
                }

                let at_gate_limit = window.gate_indices.len() == self.window_gates;
                if at_gate_limit {
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
                }

                self.analyze_window(
                    circuit,
                    &window.gate_indices,
                    &window.qubits,
                    &mut store,
                    &mut rewrites,
                    &mut subcircuits,
                )?;

                if !at_gate_limit {
                    active[window_id] = Some(window);
                }
            }

            // The current gate anchors a new one-gate closed component.
            if gate_qubits.len() <= self.max_qubits {
                let indices = vec![gate_index];
                self.analyze_window(
                    circuit,
                    &indices,
                    &gate_qubits,
                    &mut store,
                    &mut rewrites,
                    &mut subcircuits,
                )?;

                if self.window_gates > 1 {
                    let window_id = active.len();
                    for &qubit in &gate_qubits {
                        windows_by_qubit[qubit].push(window_id);
                    }
                    active.push(Some(ActiveWindow {
                        gate_indices: indices,
                        qubits: gate_qubits,
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

    fn analyze_window(
        &self,
        circuit: &Circuit,
        gate_indices: &[usize],
        qubits: &[Qubit],
        store: &mut MatrixStore,
        rewrites: &mut RewriteSet,
        subcircuits: &mut Vec<SuperOptWindow>,
    ) -> Result<(), SuperOptError> {
        let cached = store.lookup(
            circuit,
            gate_indices,
            qubits,
            self.synthesis_table.as_deref(),
        )?;
        rewrites.consider(cached, gate_indices, qubits);
        if self.collect_subcircuits {
            subcircuits.push(SuperOptWindow {
                gate_indices: gate_indices.to_vec(),
                qubits: qubits.to_vec(),
                matrix: Arc::clone(&cached.matrix),
            });
        }
        Ok(())
    }
}

impl Pass for SuperOptPass {
    fn name(&self) -> &str {
        SuperOptPass::name(self)
    }

    fn run(&self, circuit: &Circuit) -> Circuit {
        SuperOptPass::run(self, circuit)
            .expect("SuperOptPass requires a valid unitary circuit")
            .circuit
    }
}

fn validate_circuit(circuit: &Circuit) -> Result<(), SuperOptError> {
    for (gate_index, gate) in circuit.gates.iter().enumerate() {
        if matches!(gate, Gate::measure { .. } | Gate::reset(_)) {
            return Err(SuperOptError::NonUnitaryGate { gate_index });
        }
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
/// gate that bridges in a *new* qubit requires scanning, so `pending` is seeded
/// with new qubits alone rather than the whole support. Returns `false` when the
/// window would exceed `max_gates` or `max_qubits`; `added` always lists exactly
/// the qubits inserted this call (even on the `false` path), none of which have
/// been registered yet.
#[allow(clippy::too_many_arguments)]
fn expand_component_closure(
    circuit: &Circuit,
    window: &mut ActiveWindow,
    current_gate: usize,
    current_qubits: &[Qubit],
    gates_by_qubit: &[Vec<usize>],
    max_qubits: usize,
    max_gates: usize,
    added: &mut Vec<Qubit>,
    pending: &mut Vec<Qubit>,
) -> bool {
    added.clear();
    pending.clear();

    let anchor = window.gate_indices[0];
    window.gate_indices.push(current_gate);
    if window.gate_indices.len() > max_gates {
        return false;
    }

    for &qubit in current_qubits {
        if let Err(position) = window.qubits.binary_search(&qubit) {
            window.qubits.insert(position, qubit);
            added.push(qubit);
            pending.push(qubit);
            if window.qubits.len() > max_qubits {
                return false;
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
            let Err(position) = window.gate_indices.binary_search(&gate_index) else {
                continue;
            };
            window.gate_indices.insert(position, gate_index);
            if window.gate_indices.len() > max_gates {
                return false;
            }

            for gate_qubit in unique_qubits(&circuit.gates[gate_index]) {
                if let Err(position) = window.qubits.binary_search(&gate_qubit) {
                    window.qubits.insert(position, gate_qubit);
                    added.push(gate_qubit);
                    pending.push(gate_qubit);
                    if window.qubits.len() > max_qubits {
                        return false;
                    }
                }
            }
        }
    }

    true
}

struct RewriteSet {
    claimed: Vec<bool>,
    replacements: Vec<Option<Vec<Gate>>>,
    removed: Vec<Vec<usize>>,
    selected: Vec<SuperOptRewrite>,
}

impl RewriteSet {
    fn new(gate_count: usize) -> Self {
        Self {
            claimed: vec![false; gate_count],
            replacements: vec![None; gate_count],
            removed: Vec::new(),
            selected: Vec::new(),
        }
    }

    fn consider(&mut self, cached: &CachedMatrix, gate_indices: &[usize], qubits: &[Qubit]) {
        if gate_indices.iter().any(|&index| self.claimed[index]) {
            return;
        }
        let Some(local) = cached.synthesized_replacement.as_ref() else {
            return;
        };
        if local.len() >= gate_indices.len() {
            return;
        }

        let replacement: Vec<_> = local
            .iter()
            .map(|gate| map_gate_to_physical(gate, qubits))
            .collect();
        for &index in gate_indices {
            self.claimed[index] = true;
        }
        self.replacements[gate_indices[0]] = Some(replacement.clone());
        if replacement.is_empty() {
            self.removed.push(gate_indices.to_vec());
        }
        self.selected.push(SuperOptRewrite {
            gate_indices: gate_indices.to_vec(),
            replacement,
        });
    }

    fn apply(mut self, circuit: &Circuit) -> (Circuit, Vec<Vec<usize>>, Vec<SuperOptRewrite>) {
        let mut optimized = Circuit::with_cbits(circuit.num_qubits, circuit.num_cbits);
        for (index, gate) in circuit.gates.iter().enumerate() {
            if let Some(replacement) = self.replacements[index].take() {
                for gate in replacement {
                    optimized.apply(gate);
                }
            }
            if !self.claimed[index] {
                optimized.apply(gate.clone());
            }
        }
        self.removed.sort();
        (optimized, self.removed, self.selected)
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

/// Interned canonical-window matrices. Lookups reuse one scratch key and
/// return a borrowed entry, so the per-emission hot path never allocates on a
/// cache hit.
#[derive(Default)]
struct MatrixStore {
    cache: HashMap<Box<[NormalizedGate]>, usize>,
    entries: Vec<CachedMatrix>,
    scratch: Vec<NormalizedGate>,
    hits: usize,
    misses: usize,
}

impl MatrixStore {
    fn lookup(
        &mut self,
        circuit: &Circuit,
        gate_indices: &[usize],
        qubits: &[Qubit],
        table: Option<&UnitaryCircuitTable>,
    ) -> Result<&CachedMatrix, SuperOptError> {
        normalized_gate_key(circuit, gate_indices, qubits, &mut self.scratch);
        if let Some(&entry_index) = self.cache.get(self.scratch.as_slice()) {
            self.hits += 1;
            return Ok(&self.entries[entry_index]);
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
        self.cache
            .insert(self.scratch.as_slice().into(), entry_index);
        Ok(&self.entries[entry_index])
    }
}

fn unique_qubits(gate: &Gate) -> Vec<Qubit> {
    let mut qubits = qubits_of(gate);
    qubits.sort_unstable();
    qubits.dedup();
    qubits
}

#[cfg(test)]
fn union_qubits(left: &[Qubit], right: &[Qubit]) -> Vec<Qubit> {
    let mut union = Vec::with_capacity(left.len() + right.len());
    union.extend_from_slice(left);
    union.extend_from_slice(right);
    union.sort_unstable();
    union.dedup();
    union
}

fn qubit_bit(num_qubits: usize, position: usize) -> usize {
    1usize << (num_qubits - 1 - position)
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
                Gate::measure { .. } | Gate::reset(_) => unreachable!("validated as unitary"),
            }),
    );
}

fn gate_x() -> [[Complex64; 2]; 2] {
    [
        [Complex64::ZERO, Complex64::ONE],
        [Complex64::ONE, Complex64::ZERO],
    ]
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

fn gate_z() -> [[Complex64; 2]; 2] {
    [
        [Complex64::ONE, Complex64::ZERO],
        [Complex64::ZERO, Complex64::new(-1.0, 0.0)],
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

#[cfg(test)]
mod tests;
