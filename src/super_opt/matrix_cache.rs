//! Canonical window keys and the interned matrix store.
//!
//! Two windows with the same gate kinds in the same order, acting on the
//! same *support-local* qubit positions, have the same unitary — regardless
//! of which physical qubits or circuit positions they sit on. Keying on that
//! canonical shape lets one matrix construction and one synthesis-table
//! probe serve every recurrence of a shape, across the whole circuit and
//! across runs.
//!
//! Keys come in two forms: a fixed-size, non-allocating [`CompactKey`] fast
//! path covering the common case (at most [`COMPACT_KEY_MAX_GATES`] gates on
//! at most four qubits), and a general, heap-allocated [`NormalizedGate`]
//! sequence for wider or longer Clifford+T windows.

use std::cell::RefCell;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use rustc_hash::FxHashMap;

use crate::circuit::{Circuit, Gate, Qubit};

use super::SuperOptError;
use super::matrix::UnitaryMatrix;
use super::table::UnitaryCircuitTable;

/// Everything the pass knows about one canonical window shape: its unitary,
/// and the smallest support-local replacement the synthesis table offered
/// (`None` caches the negative outcome, so misses are never retried).
#[derive(Clone, Debug)]
pub(super) struct CachedMatrix {
    pub(super) matrix: Arc<UnitaryMatrix>,
    pub(super) synthesized_replacement: Option<Vec<Gate>>,
}

/// Interned canonical-window matrices. Lookups reuse one scratch key and
/// return a borrowed entry, so the per-emission hot path never allocates on a
/// cache hit.
///
/// Both key forms use support-local qubit indices and each entry is resolved
/// against the pass instance's fixed synthesis table, so entries are valid for
/// any window with the same shape — including windows in a different circuit.
/// That is what makes carrying the store across runs of one pass instance
/// sound (see [`MatrixStore::take_from`]).
#[derive(Debug, Default)]
pub(super) struct MatrixStore {
    // FxHash: this is probed once per emitted window (millions of times on
    // large circuits), and the keys are short gate sequences where SipHash's
    // per-lookup overhead dominates.
    cache: FxHashMap<Box<[NormalizedGate]>, usize>,
    compact_cache: FxHashMap<CompactKey, usize>,
    entries: Vec<CachedMatrix>,
    scratch: Vec<NormalizedGate>,
    pub(super) hits: usize,
    pub(super) misses: usize,
}

impl MatrixStore {
    /// Take the persistent store out of `slot` for one run, leaving the slot
    /// empty. The hit/miss counters describe a single run and are reset here.
    pub(super) fn take_from(slot: &RefCell<MatrixStore>) -> MatrixStore {
        let mut store = std::mem::take(&mut *slot.borrow_mut());
        store.hits = 0;
        store.misses = 0;
        store
    }

    /// Return the store to `slot` so the pass's next run starts warm. If two
    /// clones of the same pass instance (sharing this `Rc`) both ran and are
    /// now returning their store, the one with more interned entries wins
    /// and the other is simply dropped — clones only ever run one at a time
    /// on the single thread they're confined to, so this is an ordering
    /// choice, not a data race.
    pub(super) fn store_back(self, slot: &RefCell<MatrixStore>) {
        let mut guard = slot.borrow_mut();
        if guard.entries.len() < self.entries.len() {
            *guard = self;
        }
    }

    pub(super) fn lookup(
        &mut self,
        circuit: &Circuit,
        gate_indices: &[usize],
        qubits: &[Qubit],
        compact_key: Option<&CompactKey>,
        table: Option<&UnitaryCircuitTable>,
    ) -> Result<Option<&CachedMatrix>, SuperOptError> {
        if let Some(key) = compact_key {
            if let Some(&entry_index) = self.compact_cache.get(key) {
                self.hits += 1;
                return Ok(Some(&self.entries[entry_index]));
            }
        } else {
            normalized_gate_key(circuit, gate_indices, qubits, &mut self.scratch);
            if let Some(&entry_index) = self.cache.get(self.scratch.as_slice()) {
                self.hits += 1;
                return Ok(Some(&self.entries[entry_index]));
            }
        }

        self.misses += 1;
        let mut matrix = UnitaryMatrix::identity(qubits.len())?;
        for &gate_index in gate_indices {
            if matrix
                .apply_gate_left(&circuit.gates[gate_index], qubits)
                .is_err()
            {
                return Ok(None);
            }
        }
        let synthesized_replacement = table.and_then(|table| table.synthesize(&matrix));
        let entry_index = self.entries.len();
        self.entries.push(CachedMatrix {
            synthesized_replacement,
            matrix: Arc::new(matrix),
        });
        if let Some(key) = compact_key {
            self.compact_cache.insert(*key, entry_index);
        } else {
            self.cache
                .insert(self.scratch.as_slice().into(), entry_index);
        }
        Ok(Some(&self.entries[entry_index]))
    }
}

/// One gate of a general canonical key on support-local qubit positions. The
/// fallback when the packed `u128` form below cannot represent the window.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
enum NormalizedGate {
    X(usize),
    H(usize),
    S(usize),
    Sdg(usize),
    Z(usize),
    T(usize),
    Tdg(usize),
    Cnot(usize, usize),
    Cz(usize, usize),
    Ccx(usize, usize, usize),
    Ccz(usize, usize, usize),
}

/// Longest window the fixed-size compact key can represent without falling
/// back to the heap-allocated general key. Comfortably covers `-Osuper`'s
/// `window_gates=40` (see `main.rs`), with headroom for the hidden
/// `--superopt-window-gates` experimentation flag.
pub(super) const COMPACT_KEY_MAX_GATES: usize = 64;

/// Exact non-allocating normalized key for the common Clifford+T window: one
/// `u16` gate code (see `compact_gate`) per slot, with only the first `len`
/// slots meaningful. Hashing and equality look at just that prefix (see the
/// trait impls below), so cost tracks the window's actual length rather than
/// the array's fixed capacity.
#[derive(Clone, Copy, Debug)]
pub(super) struct CompactKey {
    len: u8,
    gates: [u16; COMPACT_KEY_MAX_GATES],
}

impl CompactKey {
    const EMPTY: Self = Self {
        len: 0,
        gates: [0; COMPACT_KEY_MAX_GATES],
    };

    fn as_slice(&self) -> &[u16] {
        &self.gates[..usize::from(self.len)]
    }

    /// Append one gate's code in place. Returns `false` (leaving `self`
    /// unchanged) if the window would exceed `COMPACT_KEY_MAX_GATES` gates or
    /// the gate/support isn't compactly encodable; the caller then falls back
    /// to the general key.
    fn try_push(&mut self, gate: &Gate, support: &[Qubit]) -> bool {
        let len = usize::from(self.len);
        if len >= COMPACT_KEY_MAX_GATES {
            return false;
        }
        let Some(code) = compact_gate(gate, support) else {
            return false;
        };
        self.gates[len] = code;
        self.len = (len + 1) as u8;
        true
    }
}

impl PartialEq for CompactKey {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl Eq for CompactKey {}

impl Hash for CompactKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

pub(super) fn compact_normalized_key(
    circuit: &Circuit,
    gate_indices: &[usize],
    support: &[Qubit],
) -> Option<CompactKey> {
    let mut key = CompactKey::EMPTY;
    for &gate_index in gate_indices {
        if !key.try_push(&circuit.gates[gate_index], support) {
            return None;
        }
    }
    Some(key)
}

/// Append one gate to `key` in place — no `CompactKey` is ever copied, since
/// growing an active window's key is the hot path (once per live window per
/// gate processed). Falls back to `None` (forcing the general key on the
/// next lookup) exactly when [`CompactKey::try_push`] would have.
pub(super) fn append_compact_gate_key(
    key: &mut Option<Box<CompactKey>>,
    gate: &Gate,
    support: &[Qubit],
) {
    if let Some(inner) = key
        && !inner.try_push(gate, support)
    {
        *key = None;
    }
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
        Gate::ccz {
            control1,
            control2,
            target,
        } => encode(10, local(*control1), local(*control2), local(*target)),
        Gate::rz(..) => return None,
        Gate::measure { .. } | Gate::reset(_) => {
            unreachable!("measurement and reset are window barriers")
        }
    })
}

/// Write the window's general canonical key into `key` (reused scratch, so
/// the hot path allocates nothing on a hit).
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
                Gate::rz(..) => unreachable!("Rz gates are SuperOpt window barriers"),
                Gate::cnot { control, target } => {
                    NormalizedGate::Cnot(local(*control), local(*target))
                }
                Gate::cz { control, target } => NormalizedGate::Cz(local(*control), local(*target)),
                Gate::ccx {
                    control1,
                    control2,
                    target,
                } => NormalizedGate::Ccx(local(*control1), local(*control2), local(*target)),
                Gate::ccz {
                    control1,
                    control2,
                    target,
                } => NormalizedGate::Ccz(local(*control1), local(*control2), local(*target)),
                Gate::measure { .. } | Gate::reset(_) => {
                    unreachable!("measurement and reset are SuperOpt window barriers")
                }
            }),
    );
}
