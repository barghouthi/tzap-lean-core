import Mathlib.Probability.Distributions.Uniform
import Mathlib.GroupTheory.Index

/-!
# Uniform finite probability via Mathlib PMFs

Every random experiment in this development has a finite sample space.  We use
Mathlib's `PMF.uniformOfFintype` directly, and interpret events through its
associated outer measure.  The only project-specific result needed here is
equidistribution of the fibers of a surjective additive homomorphism; Mathlib's
uniform-PMF cardinality theorem then turns equal fiber sizes into exact event
probabilities in `ℝ≥0∞`.

This fiber theorem is the group-theoretic engine behind the `2⁻ᵏ` collision
bound in `Collision.lean`.  Optimizer-wide bounds use Mathlib's outer-measure
finite-union inequality rather than a custom probability or union-bound API.
-/

namespace TZap.FiniteProbability

noncomputable section

open scoped ENNReal

/-- Every fiber of a surjective homomorphism between finite additive groups has
probability `|B|⁻¹` under Mathlib's uniform PMF on the domain. -/
theorem uniform_fiber_of_surjective
    {A : Type u} {B : Type v} [AddGroup A] [Fintype A]
    [AddGroup B] [Fintype B] [DecidableEq B]
    (f : A →+ B) (hf : Function.Surjective f) (y : B) :
    (PMF.uniformOfFintype A).toOuterMeasure {x | f x = y} =
      (Fintype.card B : ℝ≥0∞) ⁻¹ := by
  classical
  let fiberCard := (Finset.univ.filter fun x : A => f x = y).card
  have hfib (b : B) :
      (Finset.univ.filter fun x : A => f x = b).card = fiberCard := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf b) (hf y)
  have hcard : Fintype.card A = Fintype.card B * fiberCard := by
    calc
      Fintype.card A = ∑ b ∈ (Finset.univ : Finset B),
          (Finset.univ.filter fun x : A => f x = b).card := by
            rw [← Finset.card_univ]
            exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      _ = ∑ _b ∈ (Finset.univ : Finset B), fiberCard := by
            apply Finset.sum_congr rfl
            intro b _
            exact hfib b
      _ = Fintype.card B * fiberCard := by simp
  have hfiber_pos : 0 < fiberCard := by
    rcases hf y with ⟨x, hx⟩
    apply Finset.card_pos.mpr
    exact ⟨x, by simp [hx]⟩
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [Fintype.card_subtype]
  change (fiberCard : ℝ≥0∞) / Fintype.card A =
    (Fintype.card B : ℝ≥0∞)⁻¹
  rw [hcard, Nat.cast_mul, ENNReal.div_eq_inv_mul]
  have hBtop : (Fintype.card B : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hFtop : (fiberCard : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hFzero : (fiberCard : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hfiber_pos
  rw [ENNReal.mul_inv (Or.inr hFtop) (Or.inl hBtop)]
  rw [mul_assoc, ENNReal.inv_mul_cancel hFzero hFtop, mul_one]

end
end TZap.FiniteProbability
