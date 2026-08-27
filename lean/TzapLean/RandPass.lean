import Mathlib.Probability.ProbabilityMassFunction.Constructions
import TzapLean.Pass

/-!
# Randomized Passes

`Pass` demands unconditional correctness, which a randomized optimizer cannot sign: fixing a
seed fixes the transformation, and no fixed seed can be right on *every* circuit. A pass
whose parities are `k`-bit random tags is already defeated by a circuit on `k+1` wires,
which has more distinct parities than there are tags.

So the primitive here is `RandPass`: a transformation together with a distribution on its
seed and a *bound on the probability that its output is wrong*.

```
correct : ∀ c, c.Wf → Pr_{s ← dist c} [ ⟦run c s⟧ ≠ ⟦c⟧ ] ≤ error c
```

A deterministic pass is the `error = 0` case, with a one-point seed: `Pass.toRand` turns any
`Pass` into a `RandPass` whose failure event is literally empty. Nothing about the existing
`CancelGates` and `CnotMin` proofs changes; they are reused verbatim.

Composition is where the design pays off. `RandPass.comp` draws the second pass's seed
*after* seeing the first pass's output — `PMF.bind`, so the seed space of the composite is a
sigma type and no independence argument is needed. The error adds:

```
error (comp p q) c = p.error c + ⨆ s, q.error (p.run c s)
```

and a pipeline of deterministic passes collapses to `0`, recovering `Pass.correct_runAll`.
Note that the bound needs no independence *between* the two failure events — it is a union
bound, which holds regardless.
-/

namespace TzapLean

open scoped ENNReal

noncomputable section

/-- An optimization pass that may consult randomness, carrying a bound on how often its
output can fail to denote the same channel as its input. -/
structure RandPass where
  /-- The pass's name. -/
  name : String
  /-- The randomness the pass consumes, as a function of the circuit it is given. -/
  Seed : Circuit → Type
  /-- The distribution the seed is drawn from (`PMF.uniformOfFintype` in practice). -/
  dist : (c : Circuit) → PMF (Seed c)
  /-- The transformation, for a given seed. -/
  run : (c : Circuit) → Seed c → Circuit
  /-- The failure probability this pass is allowed. -/
  error : Circuit → ℝ≥0∞
  /-- Passes never change the number of qubits. -/
  numQubits_run : ∀ c s, (run c s).numQubits = c.numQubits
  /-- Passes never change the number of classical bits. -/
  numCbits_run : ∀ c s, (run c s).numCbits = c.numCbits
  /-- Passes preserve well-formedness, whatever the seed. -/
  wf_run : ∀ c s, c.Wf → (run c s).Wf
  /-- **The correctness obligation**: the output denotes the same channel as the input,
  except on a set of seeds of probability at most `error c`. -/
  correct : ∀ c, c.Wf →
    (dist c).toOuterMeasure
        {s | ¬ Equivalent c.numQubits c.numCbits (run c s).gates c.gates} ≤ error c

namespace RandPass

/-- The failure event of a pass on a circuit. -/
def failure (p : RandPass) (c : Circuit) : Set (p.Seed c) :=
  {s | ¬ Equivalent c.numQubits c.numCbits (p.run c s).gates c.gates}

/-! ## Deterministic passes are the `error = 0` case -/

/-- Any `Pass` is a `RandPass` that ignores its seed and never fails. -/
def _root_.TzapLean.Pass.toRand (p : Pass) : RandPass where
  name := p.name
  Seed := fun _ => Unit
  dist := fun _ => PMF.pure ()
  run := fun c _ => p.run c
  error := fun _ => 0
  numQubits_run c _ := p.numQubits_run c
  numCbits_run c _ := p.numCbits_run c
  wf_run c _ hc := p.wf_run c hc
  correct c hc := by
    have hempty : {s : Unit | ¬ Equivalent c.numQubits c.numCbits (p.run c).gates c.gates} = ∅ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact p.correct c hc
    rw [hempty]
    simp

@[simp] theorem toRand_error (p : Pass) (c : Circuit) : (Pass.toRand p).error c = 0 := rfl

@[simp] theorem toRand_run (p : Pass) (c : Circuit) (s : Unit) :
    (Pass.toRand p).run c s = p.run c := rfl

/-- The identity pass. -/
def id : RandPass where
  name := "id"
  Seed := fun _ => Unit
  dist := fun _ => PMF.pure ()
  run := fun c _ => c
  error := fun _ => 0
  numQubits_run _ _ := rfl
  numCbits_run _ _ := rfl
  wf_run _ _ hc := hc
  correct c _ := by
    have hempty : {s : Unit | ¬ Equivalent c.numQubits c.numCbits c.gates c.gates} = ∅ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Equivalent.refl _ _ _
    rw [hempty]
    simp

/-- **Zero error collapses to deterministic correctness.** A `RandPass` with `error c = 0` is
right on *every* seed its distribution can produce — the `Pass` notion, recovered from the
randomized one rather than sitting beside it. -/
theorem correct_of_error_eq_zero (p : RandPass) (c : Circuit) (hc : c.Wf)
    (h : p.error c = 0) {s : p.Seed c} (hs : s ∈ (p.dist c).support) :
    Equivalent c.numQubits c.numCbits (p.run c s).gates c.gates := by
  have hzero : (p.dist c).toOuterMeasure (p.failure c) = 0 :=
    le_antisymm (le_of_le_of_eq (p.correct c hc) h) (by simp)
  have hdisj := (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mp hzero
  by_contra hne
  exact (Set.disjoint_left.mp hdisj hs) hne

/-! ## Composition -/

/-- Run `p`, then `q` on its output, drawing `q`'s seed after seeing that output. -/
def comp (p q : RandPass) : RandPass where
  name := q.name ++ " ∘ " ++ p.name
  Seed := fun c => Σ s : p.Seed c, q.Seed (p.run c s)
  dist := fun c => (p.dist c).bind fun s =>
    (q.dist (p.run c s)).map (fun s₂ => (⟨s, s₂⟩ : Σ s : p.Seed c, q.Seed (p.run c s)))
  run := fun c s => q.run (p.run c s.1) s.2
  error := fun c => p.error c + ⨆ s : p.Seed c, q.error (p.run c s)
  numQubits_run c s := by
    rw [q.numQubits_run, p.numQubits_run]
  numCbits_run c s := by
    rw [q.numCbits_run, p.numCbits_run]
  wf_run c s hc := q.wf_run _ _ (p.wf_run c s.1 hc)
  correct c hc := by
    set E : ℝ≥0∞ := ⨆ s : p.Seed c, q.error (p.run c s) with hE
    set F : Set (Σ s : p.Seed c, q.Seed (p.run c s)) :=
      {s | ¬ Equivalent c.numQubits c.numCbits
        (q.run (p.run c s.1) s.2).gates c.gates} with hF
    -- the inner measure, for a fixed first-stage seed
    have hinner : ∀ s : p.Seed c,
        (q.dist (p.run c s)).toOuterMeasure
            ((fun s₂ => (⟨s, s₂⟩ : Σ s : p.Seed c, q.Seed (p.run c s))) ⁻¹' F) ≤
          Set.indicator (p.failure c) (fun _ => (1 : ℝ≥0∞)) s + E := by
      intro s
      by_cases hgood : Equivalent c.numQubits c.numCbits (p.run c s).gates c.gates
      · -- `p` succeeded here, so any final failure is a failure of `q`
        have hsub : (fun s₂ => (⟨s, s₂⟩ : Σ s : p.Seed c, q.Seed (p.run c s))) ⁻¹' F ⊆
            q.failure (p.run c s) := by
          intro s₂ hs₂
          simp only [hF, Set.mem_preimage, Set.mem_setOf_eq] at hs₂
          intro hq
          refine hs₂ ?_
          have hq' : Equivalent c.numQubits c.numCbits
              (q.run (p.run c s) s₂).gates (p.run c s).gates := by
            rw [p.numQubits_run, p.numCbits_run] at hq
            exact hq
          exact Equivalent.trans hq' hgood
        calc (q.dist (p.run c s)).toOuterMeasure
              ((fun s₂ => (⟨s, s₂⟩ : Σ s : p.Seed c, q.Seed (p.run c s))) ⁻¹' F)
            ≤ (q.dist (p.run c s)).toOuterMeasure (q.failure (p.run c s)) :=
              (q.dist (p.run c s)).toOuterMeasure_mono (by
                intro x hx; exact hsub hx.1)
          _ ≤ q.error (p.run c s) := q.correct _ (p.wf_run c s hc)
          _ ≤ E := le_iSup (fun s => q.error (p.run c s)) s
          _ ≤ Set.indicator (p.failure c) (fun _ => (1 : ℝ≥0∞)) s + E := le_add_self
      · -- `p` already failed here; bound the inner probability by one
        have hone : Set.indicator (p.failure c) (fun _ => (1 : ℝ≥0∞)) s = 1 := by
          rw [Set.indicator_of_mem]
          exact hgood
        rw [hone]
        refine le_add_right ?_
        calc (q.dist (p.run c s)).toOuterMeasure _
            ≤ (q.dist (p.run c s)).toOuterMeasure Set.univ :=
              (q.dist (p.run c s)).toOuterMeasure_mono (by intro x _; exact Set.mem_univ x)
          _ = 1 := by rw [PMF.toOuterMeasure_apply]; simpa using (q.dist (p.run c s)).tsum_coe
    calc ((p.dist c).bind fun s =>
            (q.dist (p.run c s)).map
              (fun s₂ => (⟨s, s₂⟩ : Σ s : p.Seed c, q.Seed (p.run c s)))).toOuterMeasure F
        = ∑' s, (p.dist c) s *
            ((q.dist (p.run c s)).map
              (fun s₂ => (⟨s, s₂⟩ : Σ s : p.Seed c, q.Seed (p.run c s)))).toOuterMeasure F := by
          rw [PMF.toOuterMeasure_bind_apply]
      _ = ∑' s, (p.dist c) s * (q.dist (p.run c s)).toOuterMeasure
            ((fun s₂ => (⟨s, s₂⟩ : Σ s : p.Seed c, q.Seed (p.run c s))) ⁻¹' F) := by
          refine tsum_congr fun s => ?_
          rw [PMF.toOuterMeasure_map_apply]
      _ ≤ ∑' s, (p.dist c) s *
            (Set.indicator (p.failure c) (fun _ => (1 : ℝ≥0∞)) s + E) := by
          refine ENNReal.tsum_le_tsum fun s => ?_
          exact mul_le_mul_left' (hinner s) _
      _ = (∑' s, (p.dist c) s * Set.indicator (p.failure c) (fun _ => (1 : ℝ≥0∞)) s) +
            (∑' s, (p.dist c) s * E) := by
          rw [← ENNReal.tsum_add]
          exact tsum_congr fun s => by ring
      _ = (p.dist c).toOuterMeasure (p.failure c) + E := by
          have h1 : (∑' s, (p.dist c) s * Set.indicator (p.failure c) (fun _ => (1 : ℝ≥0∞)) s)
              = (p.dist c).toOuterMeasure (p.failure c) := by
            rw [PMF.toOuterMeasure_apply]
            refine tsum_congr fun s => ?_
            by_cases hs : s ∈ p.failure c <;> simp [Set.indicator_apply, hs]
          have h2 : (∑' _s : p.Seed c, (p.dist c) _s * E) = E := by
            rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
          rw [h1, h2]
      _ ≤ p.error c + E := add_le_add (p.correct c hc) le_rfl

/-- A pipeline, run left to right: the head runs first, on the original circuit. -/
def pipeline : List RandPass → RandPass
  | [] => RandPass.id
  | p :: ps => p.comp (pipeline ps)

@[simp] theorem pipeline_nil : pipeline [] = RandPass.id := rfl

@[simp] theorem pipeline_cons (p : RandPass) (ps : List RandPass) :
    pipeline (p :: ps) = p.comp (pipeline ps) := rfl

/-- **A pipeline of deterministic passes has error zero** — the `Pass` world, recovered. -/
theorem pipeline_error_eq_zero (ps : List Pass) (c : Circuit) :
    (pipeline (ps.map Pass.toRand)).error c = 0 := by
  induction ps generalizing c with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons, pipeline_cons, comp, Pass.toRand, toRand_error]
      simp [ih]

end RandPass

end
end TzapLean
