import TZap.RandomizedAlgorithm

/-! # Tightness of the randomized Algorithm 1 bound

The `C(t, 2) * 2^-k` failure bound of `randomized_fold_correct` is attained
already when `t = 2`.  Take two rotations with a nontrivial first angle on
different input wires.  Their symbolic parities are the distinct variables
`v0` and `v1`, whose independent uniform `k`-bit hashes agree with probability
exactly `2^-k`.  On precisely those samples the randomized optimizer merges
the rotations across the two wires, producing a non-equivalent circuit.
-/

namespace TZap.RandomizedAlgorithm

open TZap.Randomized TZap.Collision TZap.FiniteProbability
open scoped ENNReal

noncomputable section

/-- The two-rotation witness.  The hypothesis used below only asks that `theta`
have a nontrivial phase, so `theta = Real.pi` is one concrete choice. -/
def tightCircuit (theta : Real) : Circuit 2 :=
  [.rz theta 0, .rz 0 1]

/-- With arbitrary draws, the optimizer merges exactly when the hashes of the
two input variables agree. -/
theorem foldR_tightCircuit_draws {k : Nat} (draws : Draws k) (theta : Real) :
    foldR draws (tightCircuit theta) =
      if draws 0 = draws 1 then [.rz theta 1] else tightCircuit theta := by
  by_cases h : draws 0 = draws 1
  · have hs : draws (1 : Fin 2).val = draws (0 : Fin 2).val := by
      simpa using h.symm
    simp only [foldR, foldFromR, mergeIntoR, tightCircuit, Randomized.initial,
      Option.map_none]
    rw [if_pos hs]
    simp [mergeIntoR, foldFromR, h]
  · have hs : draws (1 : Fin 2).val ≠ draws (0 : Fin 2).val := by
      simpa using fun heq => h heq.symm
    simp only [foldR, foldFromR, mergeIntoR, tightCircuit, Randomized.initial,
      Option.map_none]
    rw [if_neg hs]
    simp [h]

/-- The sampled version of `foldR_tightCircuit_draws`. -/
theorem foldR_tightCircuit {k : Nat} (sample : Sample 2 k) (theta : Real) :
    foldR (liftSample sample) (tightCircuit theta) =
      if sample 0 = sample 1 then [.rz theta 1] else tightCircuit theta := by
  rw [foldR_tightCircuit_draws]
  simp [liftSample]

/-- Moving a nontrivial rotation from wire zero to wire one is not semantics
preserving. -/
theorem tightCircuit_bad_merge_not_equivalent (theta : Real)
    (htheta : Semantics.phase theta true ≠ 1) :
    ¬ PhaseFolding.Equivalent ([.rz theta 1] : Circuit 2) (tightCircuit theta) := by
  intro heq
  let b : Basis 2 := fun q => q == (0 : Fin 2)
  have hentry := congrFun (congrFun heq b) b
  apply htheta
  simpa [tightCircuit, Semantics.rz_cons_apply, Semantics.circuit,
    WeightedRelation.comp, WeightedRelation.id, Semantics.gate,
    Semantics.phase, b] using hentry.symm

/-- The angle `pi` satisfies the witness's nontrivial-phase hypothesis. -/
theorem phase_pi_true_ne_one : Semantics.phase Real.pi true ≠ 1 := by
  simp only [Semantics.phase, if_true]
  rw [mul_comm]
  rw [Complex.exp_pi_mul_I]
  norm_num

/-- For the witness circuit, semantic failure is exactly equality of the two
sampled hashes. -/
theorem tightCircuit_failure_iff {k : Nat} (sample : Sample 2 k) (theta : Real)
    (htheta : Semantics.phase theta true ≠ 1) :
    (¬ PhaseFolding.Equivalent
        (foldR (liftSample sample) (tightCircuit theta)) (tightCircuit theta)) ↔
      sample 0 = sample 1 := by
  rw [foldR_tightCircuit]
  by_cases h : sample 0 = sample 1
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => tightCircuit_bad_merge_not_equivalent theta htheta⟩
  · rw [if_neg h]
    exact ⟨fun hbad => (hbad rfl).elim, fun heq => (h heq).elim⟩

/-- Two independent uniform `k`-bit strings agree with probability exactly
`2^-k`. -/
theorem two_hashes_equal_probability {k : Nat} :
    (PMF.uniformOfFintype (Sample 2 k)).toOuterMeasure
        {sample | sample 0 = sample 1} = ((2 : ℝ≥0∞)⁻¹) ^ k := by
  let difference : Sample 2 k →+ BitString k :=
    { toFun := fun sample => sample 0 - sample 1
      map_zero' := by ext j; simp
      map_add' := by
        intro left right
        ext j
        simp only [Pi.add_apply, Pi.sub_apply]
        abel }
  have hsurjective : Function.Surjective difference := by
    intro target
    let sample : Sample 2 k := fun i => if i = 0 then target else 0
    refine ⟨sample, ?_⟩
    ext j
    simp [difference, sample]
  have hevent : {sample : Sample 2 k | sample 0 = sample 1} =
      {sample | difference sample = 0} := by
    ext sample
    simp [difference, sub_eq_zero]
  rw [hevent, uniform_fiber_of_surjective difference hsurjective,
    Collision.inv_card_bitString]

/-- The end-to-end randomized Algorithm 1 bound is tight: this two-rotation
circuit fails with probability exactly `2^-k`, which equals
`C(2, 2) * 2^-k`. -/
theorem randomized_fold_correct_tight {k : Nat} (theta : Real)
    (htheta : Semantics.phase theta true ≠ 1) :
    (PMF.uniformOfFintype
        (Sample (Symbolic.analyze (tightCircuit theta)).nextFresh k)).toOuterMeasure
        {sample |
          ¬ PhaseFolding.Equivalent
            (foldR (liftSample sample) (tightCircuit theta)) (tightCircuit theta)} =
      (((rzParities (tightCircuit theta)).length.choose 2 : Nat) : ENNReal) *
        ((2 : ℝ≥0∞)⁻¹) ^ k := by
  have hnext : (Symbolic.analyze (tightCircuit theta)).nextFresh = 2 := by
    rfl
  have hlength : (rzParities (tightCircuit theta)).length = 2 := by
    rfl
  rw [hnext, hlength]
  simp only [Nat.choose_self, Nat.cast_one, one_mul]
  rw [show {sample : Sample 2 k |
      ¬ PhaseFolding.Equivalent
        (foldR (liftSample sample) (tightCircuit theta)) (tightCircuit theta)} =
      {sample | sample 0 = sample 1} by
        ext sample
        exact tightCircuit_failure_iff sample theta htheta]
  exact two_hashes_equal_probability

/-- A fully concrete tight example: `Rz pi` on wire zero followed by `Rz 0`
on wire one. -/
theorem randomized_fold_correct_tight_pi {k : Nat} :
    (PMF.uniformOfFintype
        (Sample (Symbolic.analyze (tightCircuit Real.pi)).nextFresh k)).toOuterMeasure
        {sample |
          ¬ PhaseFolding.Equivalent
            (foldR (liftSample sample) (tightCircuit Real.pi))
            (tightCircuit Real.pi)} =
      (((rzParities (tightCircuit Real.pi)).length.choose 2 : Nat) : ℝ≥0∞) *
        ((2 : ℝ≥0∞)⁻¹) ^ k :=
  randomized_fold_correct_tight Real.pi phase_pi_true_ne_one

end
end TZap.RandomizedAlgorithm
