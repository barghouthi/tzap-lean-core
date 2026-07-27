import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.LinearCombination
import Tzap.Randomized
import Tzap.FiniteProbability

/-!
# The hash-collision bound

The randomized analysis (`Tzap.Randomized`) hashes each affine parity into `k` bits.
Its only failure mode is a *collision*: two parities with distinct canonical normal
forms (`Affine.Form`) hashing to the same `k`-bit string. This file proves that a
collision happens with probability at most `2⁻ᵏ` (`affine_collision_bound`).

Setup. The sample space is `Sample m k = Fin m → BitString k`: one uniform `k`-bit
draw per variable, for the finitely many (`m`) variables the analysis allocates.
`liftSample` extends a sample to a full draw stream (zero beyond `m`), and
`output p sample` is the hash of a form `p` under the sample.

Proof shape. Write `output p = p.constant + linearMap p.coefficients` — a constant
plus an 𝔽₂-linear function of the sample (`output_eq_constant_add_linear`). Then
`output p = output q` iff the linear map of the *difference* `d = p - q` sends the
sample into one specific fiber (`output_eq_iff_linear_eq`). If `p ≠ q` either `d` has a
nonzero coefficient — then `linearMap d.coefficients` is surjective onto `BitString k`
and every fiber has probability exactly `1/2ᵏ` by
`FiniteProbability.uniform_fiber_of_surjective` — or `d` is a nonzero constant and no
collision is possible at all (for `k > 0`).

Downstream, `RandomizedSoundness.lean` and `RandomizedAlgorithm.lean` combine this
per-pair bound with the union bound to control the whole optimizer.
-/


namespace Tzap.Collision

open Tzap.Affine
open Tzap.Randomized
open Tzap.FiniteProbability

noncomputable section

open scoped ENNReal

/-! ## The sample space -/

/-- The finite collection of independent random draws used by a circuit: one `k`-bit
string for each of the `m` variables the analysis allocates. This finite function type
is the uniform sample space used by Mathlib's `PMF.uniformOfFintype`. -/
abbrev Sample (m k : Nat) := Fin m → BitString k

/-- Extend a finite sample to a full draw stream (`Draws k`) by zero outside the
allocated variable range. Bounded forms never look past `m`, so this padding is
invisible to them (`sum_liftSample_eq`); it is also how `RandomizedAlgorithm.lean`
feeds a sampled `Sample` into the stream-based analysis of `Randomized.lean`. -/
def liftSample {m k : Nat} (sample : Sample m k) : Draws k :=
  fun i => if h : i < m then sample ⟨i, h⟩ else 0

/-- Evaluate a canonical affine parity into a sampled bitstring: the hash of the form
`p` under the sample, i.e. `Affine.eval` applied per hash coordinate to the lifted
draws. This is `Randomized.evalBits` composed with `normalize`, restated on `Form`s so
the collision event is a statement about normal forms. -/
def output {m k : Nat} (p : Form) (sample : Sample m k) : BitString k :=
  fun j => Affine.eval (fun i => liftSample sample i j) p

/-! ## Reduction to a linear map on the sample -/

/-- For a form bounded by `m`, the `Finsupp` sum over its support equals the finite sum
over all of `Fin m` (extra indices contribute zero coefficients, and `liftSample` agrees
with the sample below `m`). Converts hashing from a support-indexed sum into a sum over
the fixed index type `Fin m`, the shape needed to package it as `linearMap`. -/
theorem sum_liftSample_eq {m k : Nat} (p : Form) (hp : Affine.Bounded m p)
    (sample : Sample m k) (j : Fin k) :
    p.coefficients.sum (fun i coefficient => coefficient * liftSample sample i j) =
      ∑ i : Fin m, p.coefficients i.val * sample i j := by
  rw [Finsupp.sum_of_support_subset p.coefficients
    (s := Finset.range m) (fun i hi => Finset.mem_range.mpr (hp i hi))]
  · calc
      (∑ i ∈ Finset.range m,
          p.coefficients i * liftSample sample i j) =
          ∑ i : Fin m, p.coefficients i.val * liftSample sample i.val j :=
            (Fin.sum_univ_eq_sum_range
              (fun i => p.coefficients i * liftSample sample i j) m).symm
      _ = ∑ i : Fin m, p.coefficients i.val * sample i j := by
            apply Finset.sum_congr rfl
            intro i _
            simp [liftSample, i.isLt]
  · intro i _
    simp

/-- The linear part of affine evaluation on all `k` coordinates, packaged as an additive
group homomorphism `Sample m k →+ BitString k` (everything is an 𝔽₂-vector space, so
additivity is 𝔽₂-linearity). The hom structure is exactly what
`FiniteProbability.uniform_fiber_of_surjective` needs to equidistribute its fibers. -/
def linearMap (coefficients : Nat →₀ F₂) (m k : Nat) :
    Sample m k →+ BitString k where
  toFun sample := fun j => ∑ i : Fin m, coefficients i.val * sample i j
  map_zero' := by
    funext j
    simp
  map_add' left right := by
    funext j
    simp [mul_add, Finset.sum_add_distrib]

/-- Affine decomposition of hashing: for a bounded form, `output p` is the constant of
`p` plus the linear map of its coefficients applied to the sample. Separates the
sample-independent part from the linear part, enabling the fiber argument. -/
theorem output_eq_constant_add_linear {m k : Nat} (p : Form) (hp : Affine.Bounded m p)
    (sample : Sample m k) :
    output p sample = fun j => p.constant + linearMap p.coefficients m k sample j := by
  funext j
  change p.constant +
      p.coefficients.sum (fun i coefficient => coefficient * liftSample sample i j) =
    p.constant + ∑ i : Fin m, p.coefficients i.val * sample i j
  rw [sum_liftSample_eq p hp sample j]

/-- Surjectivity of the linear part: if some coefficient below `m` is nonzero (a
"pivot"), then `linearMap` hits every target bitstring — concentrate the desired target
on the pivot variable and set all other draws to zero (over `𝔽₂` the nonzero
coefficient is `1`). This is the hypothesis feeding `uniform_fiber_of_surjective`
in the main bound. -/
theorem linearMap_surjective_of_coeff_ne_zero {m k : Nat} (coefficients : Nat →₀ F₂)
    {pivot : Fin m} (hpivot : coefficients pivot.val ≠ 0) :
    Function.Surjective (linearMap coefficients m k) := by
  intro target
  let sample : Sample m k := fun i j =>
    if i = pivot then (coefficients pivot.val)⁻¹ * target j else 0
  refine ⟨sample, ?_⟩
  funext j
  change (∑ i : Fin m, coefficients i.val * sample i j) = target j
  rw [Finset.sum_eq_single pivot]
  · simp only [sample, if_pos]
    have hone : coefficients pivot.val = (1 : F₂) := by
      apply (ZMod.val_eq_one (by norm_num) _).mp
      have hvne : (coefficients pivot.val).val ≠ 0 := by
        intro hv
        exact hpivot ((ZMod.val_eq_zero _).mp hv)
      have hvlt := ZMod.val_lt (coefficients pivot.val)
      omega
    simp [hone]
  · intro i _ hne
    simp [sample, hne]
  · simp

/-- Boundedness is preserved by subtraction of forms: the difference `p - q` mentions no
variable that neither `p` nor `q` mentions. Needed because the collision argument works
with the difference form `d = p - q`. -/
theorem sub_bounded {m : Nat} {p q : Form} (hp : Affine.Bounded m p)
    (hq : Affine.Bounded m q) : Affine.Bounded m (p - q) := by
  intro i hi
  simp only [sub_coefficients, Finsupp.mem_support_iff,
    Finsupp.sub_apply] at hi ⊢
  by_cases hpi : p.coefficients i = 0
  · have hqi : q.coefficients i ≠ 0 := by
      intro hq0
      simp [hpi, hq0] at hi
    exact hq i (Finsupp.mem_support_iff.mpr hqi)
  · exact hp i (Finsupp.mem_support_iff.mpr hpi)

/-- `linearMap` is linear in the coefficient vector as well: the map of a difference of
forms is the pointwise difference of the maps. Used to rewrite the collision event in
terms of the single difference form. -/
theorem linearMap_sub (p q : Form) (m k : Nat) (sample : Sample m k) :
    linearMap (p - q).coefficients m k sample =
      linearMap p.coefficients m k sample - linearMap q.coefficients m k sample := by
  funext j
  simp [linearMap, Finset.sum_sub_distrib, sub_mul]

/-- The key reformulation: `p` and `q` hash equal on a sample iff the linear map of the
difference `p - q` sends the sample to the constant bitstring `-(p - q).constant`.
Collision is thus exactly membership in ONE fiber of a fixed linear map, which the
fiber-uniformity theorem then measures. -/
theorem output_eq_iff_linear_eq {m k : Nat} {p q : Form}
    (hp : Affine.Bounded m p) (hq : Affine.Bounded m q) (sample : Sample m k) :
    output p sample = output q sample ↔
      linearMap (p - q).coefficients m k sample = fun _ => -(p - q).constant := by
  rw [output_eq_constant_add_linear p hp, output_eq_constant_add_linear q hq]
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    change p.constant + linearMap p.coefficients m k sample j =
      q.constant + linearMap q.coefficients m k sample j at hj
    rw [linearMap_sub]
    change linearMap p.coefficients m k sample j -
      linearMap q.coefficients m k sample j = -(p.constant - q.constant)
    linear_combination hj
  · intro h
    funext j
    have hj := congrFun h j
    rw [linearMap_sub] at hj
    change linearMap p.coefficients m k sample j -
      linearMap q.coefficients m k sample j = -(p.constant - q.constant) at hj
    change p.constant + linearMap p.coefficients m k sample j =
      q.constant + linearMap q.coefficients m k sample j
    linear_combination hj

/-! ## Counting the codomain -/

/-- There are `2^k` bitstrings of length `k`. -/
theorem card_bitString (k : Nat) : Fintype.card (BitString k) = 2 ^ k := by
  simp [BitString, ZMod.card]

/-- In `ℝ≥0∞`, the inverse cardinality of `k`-bit strings is `2⁻ᵏ`. -/
theorem inv_card_bitString (k : Nat) :
    (Fintype.card (BitString k) : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞)⁻¹) ^ k := by
  rw [card_bitString]
  push_cast
  exact ENNReal.inv_pow

/-!
## MAIN THEOREM: the collision bound

**Statement.** Let `p` and `q` be two DISTINCT canonical affine parities (`Form`s) whose
variables all lie below `m`. Draw a uniformly random sample — one independent `k`-bit
string per variable in `Fin m`. Then the probability that `p` and `q` hash to the same
`k`-bit string is at most `(1/2)^k`. The proof rewrites collision as the event that the
𝔽₂-linear map of the difference `d = p - q` lands in one fixed fiber: if `d` has a
nonzero coefficient the map is surjective and each fiber has probability exactly `2⁻ᵏ`
(`uniform_fiber_of_surjective`); if `d` is a nonzero constant, `p` and `q` never collide
(for `k = 0` the trivial bound `≤ 1` applies).

**Significance.** This is the paper's per-pair hashing guarantee: `k`-bit hashes
distinguish semantically distinct parities except with probability `2⁻ᵏ`. Summed over
the `t²` pairs of parities the optimizer compares (via the union bound), it yields the
`t² · 2⁻ᵏ` end-to-end failure probability of the randomized Algorithm 1.
-/

/--
Two distinct affine parities collide under uniform `k`-bit evaluation with
probability at most `2⁻ᵏ`.
-/
theorem affine_collision_bound {m k : Nat} (p q : Form)
    (hp : Affine.Bounded m p) (hq : Affine.Bounded m q) (hne : p ≠ q) :
    (PMF.uniformOfFintype (Sample m k)).toOuterMeasure
        {sample | output p sample = output q sample} ≤
      ((2 : ℝ≥0∞)⁻¹) ^ k := by
  by_cases hk : k = 0
  · subst k
    calc
      (PMF.uniformOfFintype (Sample m 0)).toOuterMeasure
          {sample | output p sample = output q sample} ≤
          (PMF.uniformOfFintype (Sample m 0)).toOuterMeasure Set.univ :=
        (PMF.uniformOfFintype (Sample m 0)).toOuterMeasure.mono (Set.subset_univ _)
      _ = 1 := (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)
      _ = ((2 : ℝ≥0∞)⁻¹) ^ 0 := by simp
  let d := p - q
  have hdBounded : Affine.Bounded m d := sub_bounded hp hq
  by_cases hlinear : d.coefficients = 0
  · have hconstant : d.constant ≠ 0 := by
      intro hc
      apply hne
      apply Form.ext
      · exact sub_eq_zero.mp (by simpa [d] using hc)
      · exact sub_eq_zero.mp (by simpa [d] using hlinear)
    have hno (sample : Sample m k) : output p sample ≠ output q sample := by
      intro heq
      have hlin := (output_eq_iff_linear_eq hp hq sample).mp heq
      have j : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
      have hj := congrFun hlin j
      have hz : linearMap d.coefficients m k sample j = 0 := by
        simp [hlinear, linearMap]
      rw [hz] at hj
      exact hconstant (neg_eq_zero.mp hj.symm)
    have hevent : {sample : Sample m k | output p sample = output q sample} = ∅ := by
      ext sample
      simp [hno sample]
    rw [hevent]
    simp
  · have hsupp : d.coefficients.support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr hlinear
    obtain ⟨i, hiSupport⟩ := hsupp
    have hi : d.coefficients i ≠ 0 := Finsupp.mem_support_iff.mp hiSupport
    let pivot : Fin m := ⟨i, hdBounded i hiSupport⟩
    have hpivot : d.coefficients pivot.val ≠ 0 := hi
    have hsurj : Function.Surjective (linearMap d.coefficients m k) :=
      linearMap_surjective_of_coeff_ne_zero d.coefficients hpivot
    have hevent :
        {sample : Sample m k | output p sample = output q sample} =
          {sample | linearMap d.coefficients m k sample = fun _ => -d.constant} := by
      ext sample
      simpa [d] using output_eq_iff_linear_eq hp hq sample
    rw [hevent, uniform_fiber_of_surjective _ hsurj, inv_card_bitString]

end
end Tzap.Collision
