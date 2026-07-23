//! The bounded Clifford+T synthesis table: breadth-first enumeration of
//! library-gate circuits keyed by unitary fingerprint, plus the process-wide
//! cache that shares built tables across passes.
//!
//! For each width the enumeration grows circuits one gate at a time, layer
//! by layer, recording each unitary the first time it appears. Because
//! layers are visited in gate-count order, the first circuit to reach a
//! unitary is a smallest one — so a table hit *is* the synthesis answer, no
//! search needed at lookup time. Two prunes keep the frontier tractable
//! without losing any unitary: a child never follows its parent's inverse
//! (the product would revisit the grandparent's unitary), and among
//! qubit-disjoint neighbors only the canonically ordered interleaving is
//! expanded (the swapped one has the same product).

use std::collections::HashMap;
use std::io::{self, Read, Write};
use std::sync::{Arc, Mutex, OnceLock};

use rayon::prelude::*;

use crate::circuit::Gate;

use super::matrix::{UnitaryFingerprint, UnitaryMatrix, unitary_fingerprint};
use super::synthesis_arena::WidthTable;
use super::{SuperOptError, SuperOptTableConfig};

/// On-disk table cache format identifier and version. Bump
/// `CACHE_FORMAT_VERSION` whenever the byte layout below changes; a mismatch
/// (or a missing/corrupt file) simply falls back to rebuilding, never to a
/// misread table.
///
/// The crate version is checked too (see `CACHE_CRATE_VERSION`), separately
/// from the byte layout: table *construction* (pruning rules, the library
/// gate set, etc.) can change between releases without touching how a table
/// is serialized, and such a change must still invalidate old caches even
/// though `CACHE_FORMAT_VERSION` didn't move. Tying invalidation to the crate
/// version means that never has to be caught by hand — every release gets a
/// fresh cache namespace for free.
const CACHE_MAGIC: &[u8; 4] = b"TZS1";
// Version 2 introduced exact cyclotomic fingerprints, version 3 the compact
// i8 coefficient bound, and version 4 stores 64-bit rather than 128-bit keys.
const CACHE_FORMAT_VERSION: u32 = 4;
const CACHE_CRATE_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Reads and validates a cache file's header — magic, format version, and
/// config fields — against `config`. Shared by `read_from_disk` (which
/// continues on to read the table body) and `disk_cache_exists` (which only
/// needs to know the header matches).
fn read_cache_header(input: &mut impl Read, config: SuperOptTableConfig) -> io::Result<()> {
    let invalid = |msg: &str| io::Error::new(io::ErrorKind::InvalidData, msg.to_owned());

    let mut magic = [0u8; 4];
    input.read_exact(&mut magic)?;
    if magic != *CACHE_MAGIC {
        return Err(invalid("not a SuperOpt table cache file"));
    }
    let mut version_buf = [0u8; 4];
    input.read_exact(&mut version_buf)?;
    if u32::from_le_bytes(version_buf) != CACHE_FORMAT_VERSION {
        return Err(invalid("cache format version mismatch"));
    }

    let mut crate_version_len = [0u8; 1];
    input.read_exact(&mut crate_version_len)?;
    let mut crate_version_buf = vec![0u8; crate_version_len[0] as usize];
    input.read_exact(&mut crate_version_buf)?;
    if crate_version_buf != CACHE_CRATE_VERSION.as_bytes() {
        return Err(invalid("cache crate version mismatch"));
    }

    let mut qubits_buf = [0u8; 4];
    input.read_exact(&mut qubits_buf)?;
    let mut gates_buf = [0u8; 4];
    input.read_exact(&mut gates_buf)?;
    let mut entries_buf = [0u8; 8];
    input.read_exact(&mut entries_buf)?;
    let stored_config = (
        u32::from_le_bytes(qubits_buf) as usize,
        u32::from_le_bytes(gates_buf) as usize,
        u64::from_le_bytes(entries_buf) as usize,
    );
    if stored_config
        != (
            config.max_qubits,
            config.max_gates,
            config.max_entries_per_qubit,
        )
    {
        return Err(invalid("cache config mismatch"));
    }
    Ok(())
}

/// The gate set the table enumerates: Clifford+T over table-local qubits.
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
    // Deliberately no Ccx or Cz: SuperOpt must not introduce gates outside
    // the H/X/Z/S/T/CX emission basis (see `library_gates`), so the library
    // cannot even represent them. Windows *containing* such gates are still
    // matched and simplified — their unitaries come from the input gates.
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
            Self::Cnot(left, right) => [Some(left), Some(right)],
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
                    && matches!(self, Self::X(_) | Self::H(_) | Self::Z(_) | Self::Cnot(..))
            }
        }
    }

    /// Fixed 3-byte encoding for on-disk table persistence: a tag byte plus
    /// up to two qubit-index operands (unused operands are zero).
    pub(super) fn to_bytes(self) -> [u8; 3] {
        match self {
            Self::X(q) => [0, q, 0],
            Self::H(q) => [1, q, 0],
            Self::S(q) => [2, q, 0],
            Self::Sdg(q) => [3, q, 0],
            Self::Z(q) => [4, q, 0],
            Self::T(q) => [5, q, 0],
            Self::Tdg(q) => [6, q, 0],
            Self::Cnot(control, target) => [7, control, target],
        }
    }

    pub(super) fn from_bytes(bytes: [u8; 3]) -> Option<Self> {
        let [tag, a, b] = bytes;
        Some(match tag {
            0 => Self::X(a),
            1 => Self::H(a),
            2 => Self::S(a),
            3 => Self::Sdg(a),
            4 => Self::Z(a),
            5 => Self::T(a),
            6 => Self::Tdg(a),
            7 => Self::Cnot(a, b),
            _ => return None,
        })
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
        if !(1..=5).contains(&config.max_qubits) {
            return Err(SuperOptError::InvalidTableConfig {
                reason: format!("max_qubits must be in 1..=5, got {}", config.max_qubits),
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
                                if scratch.apply_gate_left(&gate.to_gate(), &support).is_err() {
                                    continue;
                                }
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
                        matrix
                            .apply_gate_left(&gate.to_gate(), &support)
                            .expect("an accepted table child remains representable");
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

    /// Write this table to `path` for reuse by a later process, tagged with
    /// `config` so a mismatched config on read is rejected rather than
    /// silently misinterpreted. Written to a sibling temp file and renamed
    /// into place, so a reader never observes a partially written cache file
    /// (concurrent writers each rename their own complete file; last one
    /// wins, which is fine since every writer for the same `config` builds
    /// byte-identical content).
    pub(super) fn write_to_disk(
        &self,
        path: &std::path::Path,
        config: SuperOptTableConfig,
    ) -> io::Result<()> {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let tmp_path = path.with_extension("tmp");
        {
            let file = std::fs::File::create(&tmp_path)?;
            let mut out = io::BufWriter::new(file);
            out.write_all(CACHE_MAGIC)?;
            out.write_all(&CACHE_FORMAT_VERSION.to_le_bytes())?;
            out.write_all(&[CACHE_CRATE_VERSION.len() as u8])?;
            out.write_all(CACHE_CRATE_VERSION.as_bytes())?;
            out.write_all(&(config.max_qubits as u32).to_le_bytes())?;
            out.write_all(&(config.max_gates as u32).to_le_bytes())?;
            out.write_all(&(config.max_entries_per_qubit as u64).to_le_bytes())?;
            out.write_all(&(self.entries.len() as u32).to_le_bytes())?;
            for width_table in &self.entries {
                width_table.write_to(&mut out)?;
            }
            for &saturated in &self.saturated {
                out.write_all(&[u8::from(saturated)])?;
            }
            for &depth in &self.completed_depth {
                out.write_all(&(depth as u32).to_le_bytes())?;
            }
        }
        std::fs::rename(&tmp_path, path)
    }

    /// Read a table previously written by `write_to_disk`, rejecting it
    /// (with an `io::Error`) unless its header matches `config` exactly and
    /// the format version is one this build understands. Any error here —
    /// missing file, truncated write, config mismatch, version bump — should
    /// be treated by the caller as "no usable cache", not as a hard failure.
    pub(super) fn read_from_disk(
        path: &std::path::Path,
        config: SuperOptTableConfig,
    ) -> io::Result<Self> {
        let file = std::fs::File::open(path)?;
        let mut input = io::BufReader::new(file);
        read_cache_header(&mut input, config)?;

        let mut width_count_buf = [0u8; 4];
        input.read_exact(&mut width_count_buf)?;
        let width_count = u32::from_le_bytes(width_count_buf) as usize;

        let mut entries = Vec::with_capacity(width_count);
        for _ in 0..width_count {
            entries.push(WidthTable::read_from(&mut input)?);
        }
        let mut saturated = Vec::with_capacity(width_count);
        for _ in 0..width_count {
            let mut byte = [0u8; 1];
            input.read_exact(&mut byte)?;
            saturated.push(byte[0] != 0);
        }
        let mut completed_depth = Vec::with_capacity(width_count);
        for _ in 0..width_count {
            let mut depth_buf = [0u8; 4];
            input.read_exact(&mut depth_buf)?;
            completed_depth.push(u32::from_le_bytes(depth_buf) as usize);
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

    /// Test seam for exercising the release-mode fingerprint collision guard.
    #[cfg(test)]
    pub(super) fn inject_fingerprint_alias(
        &mut self,
        query: &UnitaryMatrix,
        wrong_candidate: &UnitaryMatrix,
    ) {
        assert_eq!(query.num_qubits(), wrong_candidate.num_qubits());
        let width = query.num_qubits();
        let candidate = self.entries[width]
            .node_for(&unitary_fingerprint(wrong_candidate))
            .expect("wrong candidate is present in the test table");
        self.entries[width].insert_fingerprint_alias(unitary_fingerprint(query), candidate);
    }

    /// A smallest known library circuit implementing `matrix` up to global
    /// phase, on local qubits `0..matrix.num_qubits()`.
    pub(super) fn synthesize(&self, matrix: &UnitaryMatrix) -> Option<Vec<Gate>> {
        let table = self.entries.get(matrix.num_qubits())?;
        let node = table.node_for(&unitary_fingerprint(matrix))?;
        let circuit = table.circuit(node);
        // A fingerprint is still a finite hash of the exact matrix. This
        // exact comparison is the release-mode collision guard that makes
        // accepting a rewrite sound; it is not a redundant post-rewrite audit.
        let candidate = library_circuit_matrix(matrix.num_qubits(), &circuit)
            .ok()
            .flatten()?;
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

    let table = build_or_load_from_disk(config).map(Arc::new);
    tables.insert(config, table.clone());
    table
}

/// Directory holding on-disk synthesis-table caches. `None` when `$HOME`
/// isn't set, in which case callers just skip disk caching entirely — it is
/// always a pure speed optimization, never required for correctness.
fn cache_dir() -> Option<std::path::PathBuf> {
    let home = std::env::var_os("HOME")?;
    let mut dir = std::path::PathBuf::from(home);
    dir.push(".tzap");
    dir.push("superopt-tables");
    Some(dir)
}

/// One file per distinct `config`, since different bounds produce different
/// tables; the format version and crate version are in the name too so a
/// bump of either can't collide with (and doesn't need to explicitly
/// invalidate) old files — they're simply never looked up again and can be
/// cleaned up manually.
pub(super) fn cache_file_path(config: SuperOptTableConfig) -> Option<std::path::PathBuf> {
    let mut path = cache_dir()?;
    path.push(format!(
        "q{}_g{}_e{}.v{CACHE_FORMAT_VERSION}.tzap{CACHE_CRATE_VERSION}.bin",
        config.max_qubits, config.max_gates, config.max_entries_per_qubit
    ));
    Some(path)
}

/// Whether a valid on-disk cache for `config` already exists, checked by
/// reading just the header (magic, format version, config fields) rather
/// than the full table body. Purely informational — for callers wanting to
/// report whether a `SuperOpt::new` call is about to do a fast cache load or
/// a slow fresh build. `build_or_load_from_disk` is the sole source of truth
/// and re-validates independently, so a wrong answer here (e.g. a race with
/// another process writing the same file) can never cause a bad load, only
/// a misleading message.
pub(super) fn disk_cache_exists(config: SuperOptTableConfig) -> bool {
    let Some(path) = cache_file_path(config) else {
        return false;
    };
    let Ok(file) = std::fs::File::open(&path) else {
        return false;
    };
    read_cache_header(&mut io::BufReader::new(file), config).is_ok()
}

/// Size in bytes of the on-disk cache file for `config`, if a valid one
/// exists — a reporting aid alongside `disk_cache_exists`, never
/// load-bearing for correctness.
pub(super) fn disk_cache_size_bytes(config: SuperOptTableConfig) -> Option<u64> {
    if !disk_cache_exists(config) {
        return None;
    }
    let path = cache_file_path(config)?;
    std::fs::metadata(&path).ok().map(|metadata| metadata.len())
}

/// Load a matching table from disk if one exists, else build it and (on a
/// best-effort basis) write it back for the next process to reuse. A disk
/// read/write failure of any kind — missing file, corrupt content, a
/// read-only cache directory — is swallowed here: it can only make this run
/// as slow as a cold run would have been anyway, never wrong.
fn build_or_load_from_disk(
    config: SuperOptTableConfig,
) -> Result<UnitaryCircuitTable, SuperOptError> {
    let path = cache_file_path(config);
    if let Some(path) = &path
        && let Ok(table) = UnitaryCircuitTable::read_from_disk(path, config)
    {
        return Ok(table);
    }

    let table = UnitaryCircuitTable::build(config)?;
    if let Some(path) = &path {
        let _ = table.write_to_disk(path, config);
    }
    Ok(table)
}

/// Build a library circuit's exact matrix. The outer `Result` reports an
/// unusably large dense matrix; `Ok(None)` means its coefficients exceeded the
/// bounded i8 representation and the candidate must be skipped.
pub(super) fn library_circuit_matrix(
    num_qubits: usize,
    circuit: &[LibraryGate],
) -> Result<Option<UnitaryMatrix>, SuperOptError> {
    let support: Vec<_> = (0..num_qubits).collect();
    let mut matrix = UnitaryMatrix::identity(num_qubits)?;
    for &gate in circuit {
        if matrix.apply_gate_left(&gate.to_gate(), &support).is_err() {
            return Ok(None);
        }
    }
    Ok(Some(matrix))
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
    // Toffoli and CZ are deliberately excluded, so SuperOpt never rewrites a
    // window into a circuit containing them: a Toffoli costs ~7 T once the
    // pipeline lowers it, and CZ would take the output outside the
    // H/X/Z/S/T/CX emission basis. Input Toffolis and CZs are still
    // simplified — their windows resolve to table representatives — but such
    // gates are never introduced.
    gates
}
