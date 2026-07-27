import Tzap.Circuit

/-!
# Symbolic Parity Analysis

The abstract domain of the paper's static analysis. The analysis tracks, for each qubit, a
Boolean *affine parity* — an xor of variables plus an optional constant — over ℕ-indexed
variables. Variables `0, …, n-1` stand for the circuit's input bits; each Hadamard allocates a
fresh variable for its (unconstrained) output bit.

Contents:

* `Parity` — syntax of affine expressions (`const`, `var`, `xor`) with evaluation `Parity.eval`
  under a valuation `Nat → Bool`, and the well-formedness predicate `Parity.Bounded`.
* `State n` — the abstract state: one parity per qubit plus the next-fresh-variable counter;
  `initial n` assigns variable `q` to qubit `q`.
* `step` — the four transfer functions: `CNOT` xors the control's parity into the target's,
  `X` flips a parity, `H` overwrites the target with a fresh variable, and `Rz` is the identity
  (rotations are diagonal, so they never change which basis states are related).
* `analyzeFrom` / `analyze` — folding `step` over a circuit; `analyzeFrom` is generalized over
  the start state because the algorithm proofs re-run the analysis from mid-circuit states.
* `Consistent` — the concretization relation tying a symbolic state to a concrete basis state
  under a valuation; it is the invariant threaded through the soundness proof
  (`Soundness.analyzeFrom_sound`) and the merge-soundness lemma (`Algorithm.mergeInto_sound`).

Boundedness (`State.Bounded`, `step_bounded`, `analyze_bounded`) guarantees each qubit's parity
only mentions already-allocated variables — needed so that valuations can be extended at
Hadamards without disturbing earlier parities (`Parity.eval_eq_of_agree`), and so the
randomized analysis knows how many variables to draw hashes for.
-/

namespace Tzap.Symbolic

/-- Syntax of affine Boolean parities. `xor` is interpreted over `𝔽₂`; a parity thus denotes an
affine function `𝔽₂^ℕ → 𝔽₂` of its variables. Variables below `n` are circuit inputs; higher
ones are allocated at Hadamards. Canonical normal forms live in `Tzap/Affine.lean`. -/
inductive Parity where
  | const (b : Bool)
  | var (id : Nat)
  | xor (left right : Parity)
deriving DecidableEq, Repr

namespace Parity

/-- Evaluate a parity under a valuation of its variables, with `xor` as Boolean `!=`. -/
def eval (valuation : Nat → Bool) : Parity → Bool
  | .const b => b
  | .var id => valuation id
  | .xor p q => (eval valuation p) != (eval valuation q)

/-- Negate a parity by xoring with `true` — the abstract effect of the `X` gate. -/
def flip (p : Parity) : Parity := .xor p (.const true)

/-- Every variable occurring in `p` has identifier below `bound`. Parities bounded by the
current fresh counter are insensitive to how a valuation is extended at later Hadamards
(see `eval_eq_of_agree`). -/
def Bounded (bound : Nat) : Parity → Prop
  | .const _ => True
  | .var id => id < bound
  | .xor p q => Bounded bound p ∧ Bounded bound q

/-- Constants evaluate to themselves. -/
@[simp] theorem eval_const (v) (b) : eval v (.const b) = b := rfl
/-- Variables evaluate to their valuation. -/
@[simp] theorem eval_var (v) (i) : eval v (.var i) = v i := rfl
/-- `xor` evaluates to Boolean inequality of the sides. -/
@[simp] theorem eval_xor (v) (p q) :
    eval v (.xor p q) = (eval v p != eval v q) := rfl

/-- A parity bounded by `k` only reads variables below `k`, so any two valuations agreeing
below `k` evaluate it identically. This is what lets the soundness proof extend a valuation
with a fresh value at each Hadamard without changing the meaning of existing parities. -/
theorem eval_eq_of_agree {p : Parity} {k : Nat} {v w : Nat → Bool}
    (hp : p.Bounded k) (hvw : ∀ i, i < k → v i = w i) :
    p.eval v = p.eval w := by
  induction p with
  | const b => rfl
  | var i => exact hvw i hp
  | xor p q ihp ihq =>
      simp only [Bounded] at hp
      simp [eval, ihp hp.1, ihq hp.2]

/-- Boundedness is monotone in the bound: raising the fresh counter keeps parities bounded. -/
theorem bounded_mono {p : Parity} {k k' : Nat} (h : p.Bounded k) (hkk : k ≤ k') :
    p.Bounded k' := by
  induction p with
  | const => trivial
  | var i => exact Nat.lt_of_lt_of_le h hkk
  | xor p q ihp ihq => exact ⟨ihp h.1, ihq h.2⟩

end Parity

/-- Symbolic values of all qubits plus the next globally fresh variable. This is the abstract
state of the analysis: `qubit q` is the affine parity currently held by wire `q`, and
`nextFresh` counts the variables allocated so far (inputs plus Hadamard outputs). -/
structure State (n : Nat) where
  qubit : Fin n → Parity
  nextFresh : Nat

/-- Well-formedness of a symbolic state: every qubit's parity mentions only already-allocated
variables (identifiers below `nextFresh`). Preserved by every transfer function
(`step_bounded`); the soundness and algorithm proofs assume it of their start states. -/
def State.Bounded {n} (s : State n) : Prop :=
  ∀ q, (s.qubit q).Bounded s.nextFresh

/-- Initial qubits receive distinct variables `v₀, …, vₙ₋₁`, one per input bit;
the fresh counter starts at `n`. -/
def initial (n : Nat) : State n where
  qubit q := .var q.val
  nextFresh := n

/-- The initial state is well-formed: each qubit `q` holds `var q` with `q < n = nextFresh`. -/
theorem initial_bounded (n : Nat) : (initial n).Bounded := by
  intro q
  exact q.isLt

/-- The four abstract transfer functions from the paper, mirroring the classical action of each
gate on basis states (`Semantics.gate_ne_zero_shape`):
* `CNOT c t` xors the control's parity into the target's (`b t != b c` concretely);
* `X t` flips the target's parity;
* `H t` forgets the target — its output is a fresh, unconstrained variable;
* `Rz` is the identity: rotations are diagonal and never change basis states.
Soundness of each case against the exact semantics is
`Soundness.step_preserves_consistency` / `analyzeFrom_sound`. -/
def step {n : Nat} (s : State n) : Gate n → State n
  | .cnot c t =>
      { s with qubit := fun q => if q = t then .xor (s.qubit t) (s.qubit c) else s.qubit q }
  | .x t =>
      { s with qubit := fun q => if q = t then (s.qubit t).flip else s.qubit q }
  | .hadamard t =>
      { qubit := fun q => if q = t then .var s.nextFresh else s.qubit q
        nextFresh := s.nextFresh + 1 }
  | .rz _ _ => s

/-- Run the analysis over a circuit from an arbitrary starting state, folding `step` left to
right. Generalizing over the start state (rather than fixing `initial`) is what lets the
soundness induction (`Soundness.analyzeFrom_sound`) and the algorithm proofs restart the
analysis at any point mid-circuit. -/
def analyzeFrom {n : Nat} : State n → Circuit n → State n
  | s, [] => s
  | s, g :: gs => analyzeFrom (step s g) gs

/-- The paper's analysis: run `analyzeFrom` starting from the `initial` state, where each qubit
holds its own input variable. -/
def analyze {n : Nat} (C : Circuit n) : State n :=
  analyzeFrom (initial n) C

/-- Analysis distributes over append: analyzing `C ++ D` is analyzing `D` from the state after
`C`. Used to relate the analysis at a merge site to the analysis of the full circuit. -/
theorem analyzeFrom_append {n} (s : State n) (C D : Circuit n) :
    analyzeFrom s (C ++ D) = analyzeFrom (analyzeFrom s C) D := by
  induction C generalizing s with
  | nil => rfl
  | cons g C ih => exact ih (step s g)

/-- Specialization of `analyzeFrom_append` to the initial state. -/
theorem analyze_append {n} (C D : Circuit n) :
    analyze (C ++ D) = analyzeFrom (analyze C) D :=
  analyzeFrom_append (initial n) C D

/-- Each transfer function preserves well-formedness: `CNOT`/`X` combine existing bounded
parities, `H` allocates exactly the next variable while bumping the bound, and `Rz` does
nothing. -/
theorem step_bounded {n} (s : State n) (g : Gate n) (hs : s.Bounded) :
    (step s g).Bounded := by
  intro q
  cases g with
  | cnot c t =>
      simp only [step]
      split
      · exact ⟨hs t, hs c⟩
      · exact hs q
  | x t =>
      simp only [step, Parity.flip]
      split
      · exact ⟨hs t, trivial⟩
      · exact hs q
  | hadamard t =>
      simp only [step]
      split
      · exact Nat.lt_succ_self _
      · exact Parity.bounded_mono (hs q) (Nat.le_add_right _ 1)
  | rz θ t => exact hs q

/-- Well-formedness is an invariant of the whole analysis, from any well-formed start state. -/
theorem analyzeFrom_bounded {n} (s : State n) (C : Circuit n) (hs : s.Bounded) :
    (analyzeFrom s C).Bounded := by
  induction C generalizing s with
  | nil => exact hs
  | cons g C ih => exact ih (step s g) (step_bounded s g hs)

/-- The state produced by `analyze` is always well-formed; in particular `nextFresh` bounds all
variables, which sizes the sample space of the randomized analysis (`Tzap/Randomized.lean`). -/
theorem analyze_bounded {n} (C : Circuit n) : (analyze C).Bounded :=
  analyzeFrom_bounded (initial n) C (initial_bounded n)

/-- A concrete basis state is described by a symbolic state under `valuation`: every qubit's
parity evaluates to that qubit's actual bit. This is the concretization relation of the
abstract interpretation — the invariant established by the soundness theorem
(`Soundness.symbolic_soundness`: every supported transition is `Consistent` for some valuation)
and threaded through the merge argument via `Algorithm.step_preserves_consistency`. -/
def Consistent {n} (s : State n) (valuation : Nat → Bool) (b : Basis n) : Prop :=
  ∀ q, (s.qubit q).eval valuation = b q

end Tzap.Symbolic
