import Tzap.Semantics
import Tzap.Symbolic

/-! # Soundness of the symbolic parity analysis

This file proves the appendix soundness theorem of the paper: the symbolic
parity analysis of `Tzap.Symbolic` is a sound abstraction of the exact
complex-amplitude semantics of `Tzap.Semantics`.

The key notion (defined in `Tzap.Symbolic`) is `Consistent s v b`: under the
valuation `v : Nat → Bool` of the symbolic variables, the parity expression
`s.qubit q` evaluates to the concrete bit `b q` for every qubit `q`. The
analysis is sound in the sense that every *supported* transition of the
semantics — every input/output basis-state pair with nonzero amplitude — is
witnessed by some valuation consistent with the analysis result.

Structure of the proof:

* `step_preserves_consistency` — the one-gate case split: each of the four
  transfer functions matches the corresponding gate semantics. Only the
  Hadamard case extends the valuation, and only at the fresh variable.
* `analyzeFrom_sound` — the induction over the circuit, generalized to an
  arbitrary well-formed (bounded) starting state; this generality is reused
  by the algorithm proofs in `Tzap.Algorithm`.
* `symbolic_soundness` — the theorem specialized to the initial state, where
  the witness valuation agrees with the input bits on the initial variables.
* `parity_equality_sound` — the consequence the optimizer relies on: any
  input/output parity equality claimed by the analysis holds on every
  supported transition.

Valuations are total functions `Nat → Bool`; `AgreeBelow k v w` says `v` and
`w` agree on all variables `< k`, i.e. on everything allocated so far.
-/

namespace Tzap.Soundness

open Symbolic

/-- Two valuations agree on all variables already allocated below `k`. -/
def AgreeBelow (k : Nat) (v w : Nat → Bool) : Prop :=
  ∀ i, i < k → v i = w i

/-- `AgreeBelow` is reflexive: every valuation agrees with itself below any bound. -/
theorem AgreeBelow.refl (k : Nat) (v : Nat → Bool) : AgreeBelow k v v := by
  intro i hi
  rfl

/-- Update the valuation `v` at the single variable `fresh` to `value`, leaving
all other variables unchanged. Used in the Hadamard case to record the bit the
gate nondeterministically produced at the freshly allocated variable. -/
def setFresh (v : Nat → Bool) (fresh : Nat) (value : Bool) : Nat → Bool :=
  fun i => if i = fresh then value else v i

/-- Reading `setFresh v k b` at the updated variable `k` returns the new value `b`. -/
@[simp] theorem setFresh_same (v) (k) (b) : setFresh v k b k = b := by
  simp [setFresh]

/-- Updating at variable `k` does not disturb any variable below `k`: the old
and new valuations agree on all previously allocated variables. -/
theorem setFresh_below (v) (k) (b) : AgreeBelow k v (setFresh v k b) := by
  intro i hi
  simp [setFresh, Nat.ne_of_lt hi]

/-- The fresh-variable counter never decreases across a transfer-function step:
`CNOT`, `X`, `Rz` leave it unchanged and Hadamard increments it. -/
theorem step_nextFresh_mono {n} (s : State n) (g : Gate n) :
    s.nextFresh ≤ (Symbolic.step s g).nextFresh := by
  cases g <;> simp [Symbolic.step]

/-!
## MAIN THEOREM: step_preserves_consistency

**Statement.** Fix a bounded symbolic state `s` (every parity mentions only
variables below `s.nextFresh`) and a valuation `v` consistent with `s` on the
input basis state `b`. If the gate `g` has nonzero amplitude from `b` to `b'`
(`Semantics.gate g b b' ≠ 0`), then there is a valuation `w` consistent with
the stepped symbolic state `Symbolic.step s g` on the output `b'`, and `w`
agrees with `v` on all variables below `s.nextFresh`. In other words, any
concrete gate transition the semantics supports is matched by the symbolic
transfer function, and the witness valuation is only ever extended at the one
fresh variable allocated by a Hadamard (all other gates keep `v` unchanged).

**Significance.** This is the per-gate case split of the appendix soundness
proof; it is the induction step used by both `analyzeFrom_sound` below and
the algorithm correctness proofs in `Tzap.Algorithm`.
-/

/--
The appendix's gate case split. A supported concrete gate transition can be
matched by the symbolic transfer function. At Hadamard, the witness valuation
is extended only at the freshly allocated variable; for `CNOT`, `X`, and `Rz`
the valuation `v` itself already witnesses the stepped state.
-/
theorem step_preserves_consistency {n} (s : State n) (g : Gate n)
    (v : Nat → Bool) (b b' : Basis n)
    (hbounded : s.Bounded) (hconsistent : Consistent s v b)
    (hsupport : Semantics.gate g b b' ≠ 0) :
    ∃ w, Consistent (Symbolic.step s g) w b' ∧
      AgreeBelow s.nextFresh v w := by
  have hshape := Semantics.gate_ne_zero_shape hsupport
  cases g with
  | cnot c t =>
      rw [hshape]
      refine ⟨v, ?_, AgreeBelow.refl _ _⟩
      intro q
      by_cases hqt : q = t
      · subst q
        simp [Symbolic.step, hconsistent t, hconsistent c,
          Basis.cnot]
      · simp [Symbolic.step, hqt, hconsistent q, Basis.cnot]
  | x t =>
      rw [hshape]
      refine ⟨v, ?_, AgreeBelow.refl _ _⟩
      intro q
      by_cases hqt : q = t
      · subst q
        simp [Symbolic.step, Parity.flip, Parity.eval, hconsistent t,
          Basis.flip]
      · simp [Symbolic.step, hqt, hconsistent q, Basis.flip]
  | rz θ t =>
      rw [hshape]
      exact ⟨v, hconsistent, AgreeBelow.refl _ _⟩
  | hadamard t =>
      let w := setFresh v s.nextFresh (b' t)
      refine ⟨w, ?_, setFresh_below _ _ _⟩
      intro q
      by_cases hqt : q = t
      · subst q
        simp [Symbolic.step, w]
      · simp only [Symbolic.step, hqt, ↓reduceIte]
        calc
          (s.qubit q).eval w = (s.qubit q).eval v :=
            Parity.eval_eq_of_agree (hbounded q) (fun i hi =>
              (setFresh_below v s.nextFresh (b' t) i hi).symm)
          _ = b q := hconsistent q
          _ = b' q := (hshape q hqt).symm

/-!
## MAIN THEOREM: analyzeFrom_sound

**Statement.** Run the analysis over an arbitrary circuit `C` starting from
any bounded symbolic state `s`, with a valuation `v` consistent with `s` on
the input basis state `x`. If the whole circuit has nonzero amplitude from
`x` to `z`, then some valuation `w` is consistent with the analysis result
`Symbolic.analyzeFrom s C` on the output `z`, and `w` agrees with `v` on all
variables that existed on entry (those below `s.nextFresh`). So the witness
only fixes the fresh variables allocated by the Hadamards inside `C`.

**Significance.** This is the circuit-level induction of the soundness proof,
deliberately generalized from the initial state to any well-formed state so
that the algorithm proofs in `Tzap.Algorithm` can invoke it mid-circuit.
-/

/--
Inductive form of symbolic soundness, generalized to an arbitrary already
well-formed symbolic state. The returned valuation preserves every variable
that existed on entry. Proved by induction on the circuit, chaining
`step_preserves_consistency` at each gate and transitivity of `AgreeBelow`.
-/
theorem analyzeFrom_sound {n} (C : Circuit n) (s : State n)
    (v : Nat → Bool) (x z : Basis n)
    (hbounded : s.Bounded) (hconsistent : Consistent s v x)
    (hsupport : Semantics.circuit C x z ≠ 0) :
    ∃ w, Consistent (Symbolic.analyzeFrom s C) w z ∧
      AgreeBelow s.nextFresh v w := by
  induction C generalizing s v x with
  | nil =>
      have hxz : x = z := by
        by_contra hne
        apply hsupport
        simp [Semantics.circuit, WeightedRelation.id, hne]
      subst z
      exact ⟨v, hconsistent, AgreeBelow.refl _ _⟩
  | cons g C ih =>
      rcases Semantics.nonzero_cons_witness hsupport with ⟨y, hgate, htail⟩
      rcases step_preserves_consistency s g v x y hbounded hconsistent hgate with
        ⟨v₁, hv₁, hagree₁⟩
      rcases ih (Symbolic.step s g) v₁ y
        (Symbolic.step_bounded s g hbounded) hv₁ htail with
        ⟨w, hw, hagree₂⟩
      refine ⟨w, hw, ?_⟩
      intro i hi
      exact (hagree₁ i hi).trans
        (hagree₂ i (Nat.lt_of_lt_of_le hi (step_nextFresh_mono s g)))

/-- The canonical valuation for an input basis state `x`: variable `i < n`
carries the input bit `x i`, and all other variables are `false`. This is the
valuation the initial symbolic state (`qubit q = var q`) is consistent with. -/
def inputValuation {n} (x : Basis n) : Nat → Bool :=
  fun i => if h : i < n then x ⟨i, h⟩ else false

/-- The base case of soundness: the initial symbolic state (qubit `q` maps to
`var q`) is consistent with `inputValuation x` on the input basis state `x`. -/
theorem initial_consistent {n} (x : Basis n) :
    Consistent (Symbolic.initial n) (inputValuation x) x := by
  intro q
  simp [Symbolic.initial, inputValuation, q.isLt]

/-!
## MAIN THEOREM: symbolic_soundness

**Statement.** For any circuit `C` and any input/output pair of basis states
`x, x'` with nonzero complex amplitude (`Semantics.circuit C x x' ≠ 0`),
there is a single valuation of the symbolic variables that (i) is consistent
with the final analysis result `Symbolic.analyze C` on the output `x'` — the
parity of every qubit evaluates to the corresponding output bit — and (ii)
assigns to each initial variable `q < n` exactly the input bit `x q`. Thus
every transition the semantics supports is realized in the abstract domain.

**Significance.** This is the appendix soundness theorem of the paper; it
turns claims of the parity analysis into facts about supported transitions,
and directly yields `parity_equality_sound` below.
-/

/--
Soundness of the symbolic analysis (the appendix theorem): every input/output
pair with nonzero complex amplitude is represented by one valuation of the
initial variables and fresh Hadamard variables. Instantiates
`analyzeFrom_sound` at the initial state with `inputValuation x`.
-/
theorem symbolic_soundness {n} (C : Circuit n) (x x' : Basis n)
    (hsupport : Semantics.circuit C x x' ≠ 0) :
    ∃ valuation,
      Consistent (Symbolic.analyze C) valuation x' ∧
      (∀ q : Fin n, valuation q.val = x q) := by
  rcases analyzeFrom_sound C (Symbolic.initial n) (inputValuation x) x x'
    (Symbolic.initial_bounded n) (initial_consistent x) hsupport with
    ⟨valuation, hout, hagree⟩
  refine ⟨valuation, hout, ?_⟩
  intro q
  rw [← hagree q.val q.isLt]
  simp [inputValuation, q.isLt]

/-!
## MAIN THEOREM: parity_equality_sound

**Statement.** Suppose the analysis claims that the parity of qubit `q` in the
initial state (the bare variable `var q`, i.e. the input bit at `q`) is
syntactically equal to the parity of qubit `q'` in the final analysis result
of circuit `C`. Then on every supported transition — every input `x` and
output `x'` with `Semantics.circuit C x x' ≠ 0` — the concrete bits agree:
`x q = x' q'`. The abstract equality is a true semantic equality.

**Significance.** This is exactly the fact the phase-folding rewrite needs:
it discharges the side `Condition` of `PhaseFolding.phase_folding`, licensing
the merging of two `Rz` rotations whose parities the analysis identifies.
-/

/--
Every equality claimed between an input parity and an output parity is a true
equality on every supported transition of the weighted semantics. Follows by
evaluating both sides of the claimed equality under the witness valuation
provided by `symbolic_soundness`.
-/
theorem parity_equality_sound {n} (C : Circuit n) (q q' : Fin n)
    (heq : (Symbolic.initial n).qubit q = (Symbolic.analyze C).qubit q')
    (x x' : Basis n) (hsupport : Semantics.circuit C x x' ≠ 0) :
    x q = x' q' := by
  rcases symbolic_soundness C x x' hsupport with ⟨valuation, hout, hin⟩
  calc
    x q = valuation q.val := (hin q).symm
    _ = ((Symbolic.initial n).qubit q).eval valuation := rfl
    _ = ((Symbolic.analyze C).qubit q').eval valuation := by rw [heq]
    _ = x' q' := hout q'

end Tzap.Soundness
