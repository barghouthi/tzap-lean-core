import TZap.PhaseFolding
import TZap.RandomizedSoundness

/-! # Randomized phase folding: the per-merge guarantee

This file gives the probabilistic guarantee for a *single* phase-folding
rewrite decided by the randomized analysis.  The rewrite in question merges
two rotations,

  `pre ; Rz θ q ; middle ; Rz φ q' ; suffix  ⟶  pre ; middle ; Rz (θ+φ) q' ; suffix`,

which the exact theorem `PhaseFolding.phase_folding` justifies whenever the
side `Condition pre middle q q'` holds (the parity at the first rotation site
equals the parity at the second on all reachable states).

Two directions are established:

* **Symbolic suffices** (`symbolic_establishes_condition`): if the canonical
  affine parities computed by the exact symbolic analysis agree at the two
  sites, the semantic side condition holds — so the exact algorithm's merges
  are always justified.
* **Randomized errors are rare** (`false_condition_probability`,
  `randomized_phase_folding`): when the side condition *fails*, the two
  canonical parities must be distinct, hence their `k`-bit hashes agree with
  probability at most `2⁻ᵏ` by the collision bound.  Consequently accepting a
  semantically wrong merge has probability at most `2⁻ᵏ`, and the dichotomy
  `randomized_phase_folding_dichotomy` follows.

As everywhere in this development, probability is the outer-measure event mass
of Mathlib's uniform PMF on the finite sample space
`Sample (analyze (pre ++ middle)).nextFresh k`, valued in `ℝ≥0∞`.
-/

namespace TZap.RandomizedPhaseFolding

open TZap.Symbolic
open TZap.Affine
open TZap.Randomized
open TZap.Collision
open TZap.FiniteProbability
open TZap.PhaseFolding

noncomputable section

open scoped ENNReal

/-!
## MAIN THEOREM: Symbolic equality establishes the side condition

**Statement.** Suppose the exact symbolic analysis assigns qubit `q` after
`pre` and qubit `q'` after `pre ++ middle` parities with the same canonical
affine normal form.  Then the semantic side condition
`PhaseFolding.Condition pre middle q q'` holds: on every pair of transitions
with nonzero amplitude through `pre` and then `middle`, the intermediate bit
at `q` equals the final bit at `q'`.  This is a deterministic statement — no
probability is involved.

**Significance.** It shows the parity comparison performed by Algorithm 1 is
a sound test for the phase-folding precondition, so every merge the *exact*
algorithm performs is justified by `PhaseFolding.phase_folding`.  Its
contrapositive drives the probabilistic bounds below.
-/

/-- Symbolic equality at the two rotation sites proves the paper's side
condition.  The proof runs the exact soundness theorem through `pre` and then
`middle`, obtaining a valuation realizing both transitions, and evaluates the
equal normal forms under it. -/
theorem symbolic_establishes_condition {n} (pre middle : Circuit n) (q q' : Fin n)
    (heq : Affine.normalize ((Symbolic.analyze pre).qubit q) =
      Affine.normalize ((Symbolic.analyze (pre ++ middle)).qubit q')) :
    PhaseFolding.Condition pre middle q q' := by
  intro x₀ x x' hpre hmiddle
  rcases Soundness.analyzeFrom_sound pre (Symbolic.initial n)
      (Soundness.inputValuation x₀) x₀ x
      (Symbolic.initial_bounded n) (Soundness.initial_consistent x₀) hpre with
    ⟨valuation, hx, _⟩
  rcases Soundness.analyzeFrom_sound middle (Symbolic.analyze pre)
      valuation x x' (Symbolic.analyze_bounded pre) hx hmiddle with
    ⟨valuation', hx', hagree⟩
  have heval : ((Symbolic.analyze pre).qubit q).eval valuation' =
      ((Symbolic.analyze (pre ++ middle)).qubit q').eval valuation' := by
    apply Affine.bit_injective
    rw [← Affine.normalize_eval, ← Affine.normalize_eval, heq]
  calc
    x q = ((Symbolic.analyze pre).qubit q).eval valuation := (hx q).symm
    _ = ((Symbolic.analyze pre).qubit q).eval valuation' :=
      Parity.eval_eq_of_agree (Symbolic.analyze_bounded pre q) hagree
    _ = ((Symbolic.analyze (pre ++ middle)).qubit q').eval valuation' := heval
    _ = ((Symbolic.analyzeFrom (Symbolic.analyze pre) middle).qubit q').eval valuation' := by
      rw [Symbolic.analyze_append]
    _ = x' q' := hx' q'

/-- Failure of the side condition yields distinct symbolic parities at the
sites — the contrapositive of `symbolic_establishes_condition`, in the form
needed to invoke the collision bound. -/
theorem condition_failure_implies_normalize_ne {n} (pre middle : Circuit n)
    (q q' : Fin n) (hfail : ¬PhaseFolding.Condition pre middle q q') :
    Affine.normalize ((Symbolic.analyze pre).qubit q) ≠
      Affine.normalize ((Symbolic.analyze (pre ++ middle)).qubit q') := by
  contrapose! hfail
  exact symbolic_establishes_condition pre middle q q' hfail

/-! ## Boundedness of the two site parities

The collision bound requires both affine forms to mention only variables below
the size `m` of the sample space, here `(analyze (pre ++ middle)).nextFresh`.
-/

/-- The parity at the first rotation site (after `pre`) is bounded by the
final counter of the *whole* prefix `pre ++ middle`, since the counter only
grows. -/
theorem site_input_bounded {n} (pre middle : Circuit n) (q : Fin n) :
    Affine.Bounded (Symbolic.analyze (pre ++ middle)).nextFresh
      (Affine.normalize ((Symbolic.analyze pre).qubit q)) := by
  apply Affine.normalize_bounded
  apply Parity.bounded_mono (Symbolic.analyze_bounded pre q)
  rw [Symbolic.analyze_append]
  exact RandomizedSoundness.analyzeFrom_nextFresh_mono (Symbolic.analyze pre) middle

/-- The parity at the second rotation site (after `pre ++ middle`) is bounded
by that circuit's own final counter. -/
theorem site_output_bounded {n} (pre middle : Circuit n) (q' : Fin n) :
    Affine.Bounded (Symbolic.analyze (pre ++ middle)).nextFresh
      (Affine.normalize ((Symbolic.analyze (pre ++ middle)).qubit q')) :=
  Affine.normalize_bounded (Symbolic.analyze_bounded (pre ++ middle) q')

/-- For every fixed sample, the randomized analysis judging the two rotation
sites equal is exactly a hash collision between the two canonical affine
forms — the event to which the collision bound applies. -/
theorem site_random_event_iff_affine_event {n k} (pre middle : Circuit n)
    (q q' : Fin n)
    (sample : Sample (Symbolic.analyze (pre ++ middle)).nextFresh k) :
    (Randomized.analyze (liftSample sample) pre).qubit q =
        (Randomized.analyze (liftSample sample) (pre ++ middle)).qubit q' ↔
      Collision.output (Affine.normalize ((Symbolic.analyze pre).qubit q)) sample =
        Collision.output
          (Affine.normalize ((Symbolic.analyze (pre ++ middle)).qubit q')) sample := by
  rw [Randomized.analyze_qubit_eq_evalBits, Randomized.analyze_qubit_eq_evalBits]
  rfl

/-!
## MAIN THEOREM: A false side condition is rarely accepted

**Statement.** Suppose the semantic side condition
`PhaseFolding.Condition pre middle q q'` is *false*.  Then the probability —
over a uniformly random sample assigning `k`-bit strings to the symbolic
variables of `pre ++ middle` — that the randomized analysis nevertheless
assigns the two rotation sites equal hashes is at most `(1/2)^k`.

**Significance.** This is the quantitative heart of the per-merge guarantee:
a failed condition forces distinct canonical parities
(`condition_failure_implies_normalize_ne`), and distinct affine forms collide
with probability at most `2⁻ᵏ`.
-/

/-- If the phase-folding condition is false, randomized acceptance is rare:
the two hashes agree with probability at most `2⁻ᵏ`. -/
theorem false_condition_probability {n k} (pre middle : Circuit n) (q q' : Fin n)
    (hfail : ¬PhaseFolding.Condition pre middle q q') :
    (PMF.uniformOfFintype
        (Sample (Symbolic.analyze (pre ++ middle)).nextFresh k)).toOuterMeasure
        {sample |
          (Randomized.analyze (liftSample sample) pre).qubit q =
            (Randomized.analyze (liftSample sample) (pre ++ middle)).qubit q'} ≤
      ((2 : ℝ≥0∞)⁻¹) ^ k := by
  let p := Affine.normalize ((Symbolic.analyze pre).qubit q)
  let p' := Affine.normalize ((Symbolic.analyze (pre ++ middle)).qubit q')
  have hevent :
      {sample : Sample (Symbolic.analyze (pre ++ middle)).nextFresh k |
        (Randomized.analyze (liftSample sample) pre).qubit q =
          (Randomized.analyze (liftSample sample) (pre ++ middle)).qubit q'} =
      {sample | Collision.output p sample = Collision.output p' sample} := by
    ext sample
    exact site_random_event_iff_affine_event pre middle q q' sample
  rw [hevent]
  exact affine_collision_bound p p'
    (site_input_bounded pre middle q) (site_output_bounded pre middle q')
    (condition_failure_implies_normalize_ne pre middle q q' hfail)

/-!
## MAIN THEOREM: Randomized phase folding

**Statement.** Fix circuits `pre`, `middle`, `suffix`, angles `θ`, `φ`, and
qubits `q`, `q'`, and suppose the merged circuit
`pre ; middle ; Rz (θ+φ) q' ; suffix` is *not* equivalent (as a weighted
relation) to the original `pre ; Rz θ q ; middle ; Rz φ q' ; suffix`.  Then
the probability — over the uniform sample of `k`-bit strings for the symbolic
variables of `pre ++ middle` — that the randomized analysis accepts the merge
(i.e., gives the two rotation sites equal hashes) is at most `(1/2)^k`.

**Significance.** This is the paper's per-merge guarantee for the hash-based
analysis: a semantically wrong rewrite is accepted with probability at most
`2⁻ᵏ`.  It combines the exact phase-folding theorem (non-equivalence forces
the side condition to fail) with `false_condition_probability`.
-/

/--
End-to-end randomized phase-folding soundness: the probability that the
analysis accepts a merge whose transformed circuit is not equivalent to the
original is at most `2⁻ᵏ`.
-/
theorem randomized_phase_folding {n k} (pre middle suffix : Circuit n)
    (θ φ : ℝ) (q q' : Fin n)
    (hnotEquivalent : ¬PhaseFolding.Equivalent
      (PhaseFolding.leftCircuit pre middle suffix θ φ q q')
      (PhaseFolding.rightCircuit pre middle suffix θ φ q')) :
    (PMF.uniformOfFintype
        (Sample (Symbolic.analyze (pre ++ middle)).nextFresh k)).toOuterMeasure
        {sample |
          (Randomized.analyze (liftSample sample) pre).qubit q =
            (Randomized.analyze (liftSample sample) (pre ++ middle)).qubit q'} ≤
      ((2 : ℝ≥0∞)⁻¹) ^ k := by
  have hfail : ¬PhaseFolding.Condition pre middle q q' := by
    intro hcondition
    exact hnotEquivalent
      (PhaseFolding.phase_folding pre middle suffix θ φ q q' hcondition)
  exact false_condition_probability (k := k) pre middle q q' hfail

/-!
## MAIN THEOREM: The phase-folding dichotomy

**Statement.** For any single candidate merge, at least one of the following
holds: (i) the rewritten circuit is exactly equivalent to the original, so
performing the merge is harmless; or (ii) the probability, over the uniform
`k`-bit sample, that the randomized analysis accepts the merge is at most
`(1/2)^k`.

**Significance.** This is the "either correct or rare" phrasing of the
per-merge guarantee: whenever the randomized optimizer acts, it is either
right, or it was unlucky on an event of probability at most `2⁻ᵏ`.
-/

/-- Either folding is correct, or randomized acceptance has probability at
most `2⁻ᵏ`.  Immediate case split on equivalence, using
`randomized_phase_folding` in the negative case. -/
theorem randomized_phase_folding_dichotomy {n k} (pre middle suffix : Circuit n)
    (θ φ : ℝ) (q q' : Fin n) :
    PhaseFolding.Equivalent
      (PhaseFolding.leftCircuit pre middle suffix θ φ q q')
      (PhaseFolding.rightCircuit pre middle suffix θ φ q') ∨
    (PMF.uniformOfFintype
        (Sample (Symbolic.analyze (pre ++ middle)).nextFresh k)).toOuterMeasure
        {sample |
          (Randomized.analyze (liftSample sample) pre).qubit q =
            (Randomized.analyze (liftSample sample) (pre ++ middle)).qubit q'} ≤
      ((2 : ℝ≥0∞)⁻¹) ^ k := by
  classical
  by_cases h : PhaseFolding.Equivalent
      (PhaseFolding.leftCircuit pre middle suffix θ φ q q')
      (PhaseFolding.rightCircuit pre middle suffix θ φ q')
  · exact Or.inl h
  · exact Or.inr (randomized_phase_folding pre middle suffix θ φ q q' h)

end
end TZap.RandomizedPhaseFolding
