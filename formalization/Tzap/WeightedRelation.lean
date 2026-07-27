import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Contrapose

/-!
# Complex-Weighted Relations

This file defines the semantic universe of the whole development: *weighted relations*
`WeightedRelation α β = α → β → ℂ`, i.e. complex matrices indexed by (typically finite) types.
Quantum gates and circuits over `n` qubits denote weighted relations on the computational basis
`Basis n = Fin n → Bool` (see `Tzap/Semantics.lean`); the entry `r x y` is the amplitude of the
transition from input basis state `x` to output basis state `y`.

We provide the identity relation `id`, matrix composition `comp` (summing amplitudes over the
intermediate basis, i.e. ordinary matrix multiplication in diagrammatic order), and the monoid
laws `comp_assoc` and `id_comp`. Circuit equivalence in `Tzap/PhaseFolding.lean` is
*equality* of weighted relations, so these laws underlie every semantic rewriting step.

The key supporting lemma is `comp_ne_zero_witness`: a nonzero composite amplitude admits an
intermediate point with nonzero amplitudes on both legs. Iterated over a circuit (via
`Semantics.nonzero_cons_witness`), it extracts a nonzero-amplitude *path* through the circuit —
the engine of the symbolic-analysis soundness proof in `Tzap/Soundness.lean`.
-/

namespace Tzap

noncomputable section

/-- A complex-weighted relation (matrix) from `α` to `β`: the entry `r x y : ℂ` is the amplitude
attached to the pair `(x, y)`. Gates and circuits denote weighted relations on basis states, and
circuit equivalence is equality of weighted relations. -/
abbrev WeightedRelation (α : Type u) (β : Type v) := α → β → ℂ

namespace WeightedRelation

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The identity weighted relation (the identity matrix): amplitude `1` on the diagonal and `0`
elsewhere. It is the semantics of the empty circuit. -/
def id [DecidableEq α] : WeightedRelation α α :=
  fun x y => if x = y then 1 else 0

/-- Matrix composition, summing amplitudes over the intermediate basis:
`(comp r s) x z = ∑ y, r x y * s y z`. Note the diagrammatic order — `r` acts first — matching
the head-first execution order of circuits. -/
def comp [Fintype β] (r : WeightedRelation α β) (s : WeightedRelation β γ) :
    WeightedRelation α γ :=
  fun x z => ∑ y, r x y * s y z

/-- A nonzero finite sum has a nonzero summand: if the composite amplitude `comp r s x z` is
nonzero, some intermediate point `y` has nonzero amplitude on both legs. Iterating this along a
circuit (see `Semantics.nonzero_cons_witness`) turns "nonzero total amplitude" into a concrete
nonzero-amplitude path, which drives the induction in the soundness proof
(`Soundness.analyzeFrom_sound`). -/
theorem comp_ne_zero_witness [Fintype β]
    (r : WeightedRelation α β) (s : WeightedRelation β γ)
    {x : α} {z : γ} (h : comp r s x z ≠ 0) :
    ∃ y, r x y ≠ 0 ∧ s y z ≠ 0 := by
  classical
  contrapose! h
  rw [comp]
  apply Finset.sum_eq_zero
  intro y _
  rcases eq_or_ne (r x y) 0 with hr | hr
  · simp [hr]
  · simp [h y hr]

/-- Composition of weighted relations is associative (associativity of matrix multiplication).
Together with `circuit_append`, this lets circuit semantics be re-bracketed freely, which the
phase-folding proof (`PhaseFolding.phase_folding`) and the algorithm correctness proof use to
isolate the two rotation sites being merged. -/
theorem comp_assoc [Fintype α] [Fintype β] [Fintype γ]
    {δ : Type x} (r : WeightedRelation α β) (s : WeightedRelation β γ)
    (t : WeightedRelation γ δ) :
    comp (comp r s) t = comp r (comp s t) := by
  funext x z
  simp only [comp, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [← Fintype.sum_prod_type'
    (fun (x' : γ) (y : β) => r x y * (s y x' * t x' z))]
  rw [← Fintype.sum_prod_type_right'
    (fun (x' : γ) (y : β) => r x y * (s y x' * t x' z))]

/-- `id` is a left identity for composition: prepending the empty circuit changes nothing. -/
@[simp] theorem id_comp [Fintype α] [DecidableEq α]
    (r : WeightedRelation α β) : comp id r = r := by
  funext x z
  simp only [comp, id, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

end WeightedRelation
end
end Tzap
