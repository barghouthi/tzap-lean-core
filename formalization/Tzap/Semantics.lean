import Mathlib.Analysis.Complex.Exponential
import Tzap.WeightedRelation
import Tzap.Circuit

/-!
# Exact Circuit Semantics

The exact complex semantics of gates and circuits, as weighted relations on basis states.

* `gate g : WeightedRelation (Basis n) (Basis n)` gives each gate its matrix in the
  computational basis: `Rz θ = diag(1, e^{iθ})` (via `phase`), Hadamard with `±1/√2`
  coefficients (via `hadCoeff`), and `X`/`CNOT` as basis-state permutations using
  `Basis.flip` / `Basis.cnot`.
* `circuit C` composes the gate matrices head-first; `circuit_append` shows this is a monoid
  homomorphism from list append to `WeightedRelation.comp`, the splitting tool used by the
  phase-folding rewrite and the algorithm correctness proofs.

Key algebraic facts used downstream:

* `phase_add` — `Rz` phases with equal parity bits multiply to the phase of the summed angle;
  this single identity is *why* merging two rotations (`PhaseFolding.phase_folding`,
  `Algorithm.mergeInto_sound`) preserves semantics.
* `gate_ne_zero_shape` — every nonzero gate entry has a constrained output shape; combined
  with `nonzero_cons_witness` this lets the
  soundness proof (`Tzap/Soundness.lean`) analyse exactly the transitions a circuit supports.
-/

namespace Tzap.Semantics

open Complex

noncomputable section

/-- The paper's convention `Rz θ = diag(1, exp(iθ))`: the phase factor an `Rz θ` gate applies
when its target bit is `b` — `e^{iθ}` if `b = true`, `1` otherwise. The whole phase-folding
argument rests on `phase_add` below. -/
def phase (θ : ℝ) (b : Bool) : ℂ :=
  if b then Complex.exp (Complex.I * (θ : ℂ)) else 1

/-- The computational-basis coefficient of the Hadamard gate on its target qubit:
`-1/√2` when input and output bits are both `1`, and `1/√2` otherwise —
i.e. the entries of `(1/√2) · [[1, 1], [1, -1]]`. -/
def hadCoeff (input output : Bool) : ℂ :=
  (if input && output then -1 else 1) / (Real.sqrt 2 : ℂ)

/-- Exact complex weighted-relation semantics of one gate, entrywise in the computational basis:
`Rz` is diagonal with entries `phase θ`; `X` and `CNOT` are permutation matrices given by
`Basis.flip` and `Basis.cnot`; Hadamard is supported on pairs of states agreeing away from the
target, with coefficient `hadCoeff` at the target. -/
def gate {n : Nat} (g : Gate n) : WeightedRelation (Basis n) (Basis n) :=
  fun b b' => match g with
    | .rz θ q => if b' = b then phase θ (b q) else 0
    | .x q => if b' = Basis.flip b q then 1 else 0
    | .cnot c t => if b' = Basis.cnot b c t then 1 else 0
    | .hadamard q =>
        if ∀ r, r ≠ q → b' r = b r then hadCoeff (b q) (b' q) else 0

/-- Exact circuit semantics; list order is execution order. The empty circuit is the identity
matrix and `g :: gs` composes the matrix of `g` before that of `gs`. -/
def circuit {n : Nat} : Circuit n → WeightedRelation (Basis n) (Basis n)
  | [] => WeightedRelation.id
  | g :: gs => WeightedRelation.comp (gate g) (circuit gs)

/-- `Rz` angles add on equal parity bits: `phase θ b * phase φ b = phase (θ + φ) b`. This is the
algebraic heart of phase folding — if two rotations see the same parity bit on every supported
transition, their product equals a single rotation by the summed angle. Used directly in
`PhaseFolding.phase_folding` and `Algorithm.mergeInto_sound`. -/
theorem phase_add (θ φ : ℝ) (b : Bool) :
    phase θ b * phase φ b = phase (θ + φ) b := by
  cases b <;> simp [phase, Complex.exp_add, mul_add]

/-- A nonzero gate amplitude forces the output state's shape: `Rz` fixes the state, `X` and
`CNOT` produce the corresponding classical update, and Hadamard changes at most its target.
This is the exact-semantics counterpart of the symbolic transfer function `Symbolic.step`;
the soundness induction (`Soundness.analyzeFrom_sound`) matches on this shape case by case. -/
theorem gate_ne_zero_shape {n} {g : Gate n} {b b' : Basis n}
    (h : gate g b b' ≠ 0) :
    match g with
    | .rz _ _ => b' = b
    | .x q => b' = Basis.flip b q
    | .cnot c t => b' = Basis.cnot b c t
    | .hadamard q => ∀ r, r ≠ q → b' r = b r := by
  cases g with
  | cnot c t =>
      simp only [gate] at h
      split at h
      next heq => exact heq
      next => simp at h
  | hadamard q =>
      simp only [gate] at h
      split at h
      next heq => exact heq
      next => simp at h
  | x q =>
      simp only [gate] at h
      split at h
      next heq => exact heq
      next => simp at h
  | rz θ q =>
      simp only [gate] at h
      split at h
      next heq => exact heq
      next => simp at h

/-- Nonzero total amplitude guarantees at least one nonzero-amplitude path: if `circuit (g :: C)`
has nonzero amplitude from `x` to `z`, some intermediate state `y` is reached from `x` by `g` and
carried to `z` by `C`, both with nonzero amplitude. Specializes
`WeightedRelation.comp_ne_zero_witness`; iterated, it is the step case of the soundness
induction in `Tzap/Soundness.lean`. -/
theorem nonzero_cons_witness {n} {g : Gate n} {C : Circuit n} {x z : Basis n}
    (h : circuit (g :: C) x z ≠ 0) :
    ∃ y, gate g x y ≠ 0 ∧ circuit C y z ≠ 0 :=
  WeightedRelation.comp_ne_zero_witness _ _ h

/-- Circuit semantics turns list append into matrix composition:
`⟦C ++ D⟧ = ⟦C⟧ ; ⟦D⟧`. This is the splitting tool that lets the phase-folding proof and
`Algorithm.fold_correct` cut a circuit at the rotation sites being merged and reason about the
pieces independently. -/
theorem circuit_append {n} (C D : Circuit n) :
    circuit (C ++ D) = WeightedRelation.comp (circuit C) (circuit D) := by
  induction C with
  | nil => simp [circuit]
  | cons g C ih =>
      simp only [List.cons_append, circuit]
      rw [ih, WeightedRelation.comp_assoc]

/-- Prepending an `Rz` gate just scales every amplitude out of `x` by `phase θ (x q)`, since `Rz`
is diagonal. This closed form is how the merge-soundness argument (`Algorithm.mergeInto_sound`)
tracks the forwarded angle through the rest of the circuit. -/
theorem rz_cons_apply {n} (θ : ℝ) (q : Fin n) (C : Circuit n) (x z : Basis n) :
    circuit (.rz θ q :: C) x z = phase θ (x q) * circuit C x z := by
  simp [circuit, WeightedRelation.comp, gate]

end
end Tzap.Semantics
