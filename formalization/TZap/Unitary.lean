import Mathlib.Data.Matrix.Mul
import TZap.Semantics

/-!
# Dense Unitary Semantics

This file gives the formal circuit syntax a general dense-matrix semantics. Matrices use rows as
output basis states and columns as input basis states, and a gate is applied on the left of the
accumulated matrix. Consequently the head-first circuit `g :: C` denotes
`unitary C * unitaryGate g`.

The gate entries use exactly the same convention as `Semantics`, including
`Rz θ = diag (1, exp (iθ))`. The main theorem `unitary_agrees` therefore establishes literal
equality with the weighted-relation semantics after accounting for the opposite index order.
-/

namespace TZap.Unitary

noncomputable section

/-- A dense `2^n × 2^n` complex matrix indexed directly by computational basis states.
As in SuperOpt, the first index is the output (row) and the second is the input (column). -/
abbrev UnitaryMatrix (n : Nat) := Matrix (Basis n) (Basis n) ℂ

/-- A gate's dense matrix, defined independently entry-by-entry using the formalization's
weighted-relation `Rz` convention. -/
def unitaryGate {n : Nat} (g : Gate n) : UnitaryMatrix n :=
  fun output input => match g with
    | .rz θ q => if output = input then Semantics.phase θ (input q) else 0
    | .x q => if output = Basis.flip input q then 1 else 0
    | .cnot c t => if output = Basis.cnot input c t then 1 else 0
    | .hadamard q =>
        if ∀ r, r ≠ q → output r = input r
        then Semantics.hadCoeff (input q) (output q)
        else 0

/-- Dense unitary semantics. Starting at the identity and processing gates
head-first by left multiplication yields the recursion `unitary C * unitaryGate g`. -/
def unitary {n : Nat} : Circuit n → UnitaryMatrix n
  | [] => 1
  | g :: C => unitary C * unitaryGate g

/-- View a row-output/column-input matrix as an input/output weighted relation. -/
def asWeightedRelation {n : Nat} (U : UnitaryMatrix n) :
    WeightedRelation (Basis n) (Basis n) :=
  fun input output => U output input

/-- Entrywise bridge for one gate, accounting for the swapped matrix indices. -/
@[simp] theorem unitaryGate_apply {n : Nat} (g : Gate n) (output input : Basis n) :
    unitaryGate g output input = Semantics.gate g input output := by
  cases g <;> rfl

/-- The `Rz` case is the weighted-relation rotation `diag (1, exp (iθ))`. -/
theorem unitaryGate_rz_apply {n : Nat} (θ : ℝ) (q : Fin n)
    (output input : Basis n) :
    unitaryGate (.rz θ q) output input =
      if output = input then Semantics.phase θ (input q) else 0 := rfl

/-- Exact entrywise correspondence between the dense unitary matrix and the existing
weighted-relation semantics. The matrix is the transpose of the relation. -/
theorem unitary_apply_eq_semantics {n : Nat} (C : Circuit n)
    (output input : Basis n) :
    unitary C output input = Semantics.circuit C input output := by
  induction C generalizing output input with
  | nil => simp [unitary, Semantics.circuit, Matrix.one_apply,
      WeightedRelation.id, eq_comm]
  | cons g C ih =>
      simp only [unitary, Matrix.mul_apply, unitaryGate_apply, Semantics.circuit,
        WeightedRelation.comp]
      apply Finset.sum_congr rfl
      intro middle _
      rw [ih]
      ring

/-- Main semantic-equivalence theorem: after swapping the matrix indices, the unitary
semantics is literally equal to the weighted-relation semantics of every formal circuit. -/
theorem unitary_agrees {n : Nat} (C : Circuit n) :
    asWeightedRelation (unitary C) = Semantics.circuit C := by
  funext input output
  exact unitary_apply_eq_semantics C output input

/-- The same correspondence stated as equality of weighted relations. -/
theorem asWeightedRelation_unitary {n : Nat} (C : Circuit n) :
    asWeightedRelation (unitary C) = Semantics.circuit C :=
  unitary_agrees C

end
end TZap.Unitary
