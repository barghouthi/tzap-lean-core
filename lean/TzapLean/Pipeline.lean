import TzapLean.RandPass
import TzapLean.CnotMinProof
import TzapLean.PhaseFoldRand
import TzapLean.SuperOptProof

/-!
# tzap's Pipeline, in the Randomized World

The two passes proved here are deterministic, so they enter `RandPass` at `error = 0` with a
one-point seed. `pipeline_error` shows a pipeline of them still carries error `0`, and
`pipeline_correct` turns that back into the unconditional statement — nothing was given up
by moving to the randomized structure.

`foldPipeline` then slots the randomized pass in: phase folding's `C(L,2)·2⁻ᵏ` is the only
term that survives, since the deterministic passes around it contribute `0`.
-/

namespace TzapLean

open scoped ENNReal

noncomputable section

/-- `CancelGates` as a zero-error randomized pass. -/
def CancelGatesR : RandPass := Pass.toRand CancelGates

/-- `CnotMin` as a zero-error randomized pass. -/
def CnotMinR : RandPass := Pass.toRand CnotMin

/-- `SuperOpt` as a zero-error randomized pass: it verifies each rewrite by exact matrix
comparison, so despite the search inside it there is nothing probabilistic about it. -/
def SuperOptR (cfg : SuperOptConfig) (tbl : SynthTable) : RandPass :=
  Pass.toRand (SuperOpt cfg tbl)

/-- tzap's deterministic pipeline, expressed in the randomized world. -/
def detPipeline : RandPass := RandPass.pipeline [CancelGatesR, CnotMinR]

/-- The deterministic pipeline with superoptimization at the end. -/
def detPipelineSO (cfg : SuperOptConfig) (tbl : SynthTable) : RandPass :=
  RandPass.pipeline [CancelGatesR, CnotMinR, SuperOptR cfg tbl]

@[simp] theorem CancelGatesR_error (c : Circuit) : CancelGatesR.error c = 0 := rfl
@[simp] theorem CnotMinR_error (c : Circuit) : CnotMinR.error c = 0 := rfl

/-- Superoptimization keeps the pipeline exact. -/
theorem detPipelineSO_error (cfg : SuperOptConfig) (tbl : SynthTable) (c : Circuit) :
    (detPipelineSO cfg tbl).error c = 0 :=
  RandPass.pipeline_error_eq_zero [CancelGates, CnotMin, SuperOpt cfg tbl] c

theorem detPipelineSO_correct (cfg : SuperOptConfig) (tbl : SynthTable) (c : Circuit)
    (hc : c.Wf) {s : (detPipelineSO cfg tbl).Seed c}
    (hs : s ∈ ((detPipelineSO cfg tbl).dist c).support) :
    Equivalent c.numQubits c.numCbits ((detPipelineSO cfg tbl).run c s).gates c.gates :=
  RandPass.correct_of_error_eq_zero _ c hc (detPipelineSO_error cfg tbl c) hs

/-- The pipeline's failure probability is zero. -/
theorem detPipeline_error (c : Circuit) : detPipeline.error c = 0 :=
  RandPass.pipeline_error_eq_zero [CancelGates, CnotMin] c

/-- …and therefore every run of it is exactly correct. -/
theorem detPipeline_correct (c : Circuit) (hc : c.Wf) {s : detPipeline.Seed c}
    (hs : s ∈ (detPipeline.dist c).support) :
    Equivalent c.numQubits c.numCbits (detPipeline.run c s).gates c.gates :=
  RandPass.correct_of_error_eq_zero detPipeline c hc (detPipeline_error c) hs

/-! ## With phase folding in the pipeline -/

/-- tzap's pipeline with phase folding in front of the deterministic passes. -/
def foldPipeline (k : Nat) : RandPass :=
  RandPass.pipeline [PhaseFoldRand k, CancelGatesR, CnotMinR]

/-- **The whole pipeline's failure bound is phase folding's.** Everything else is exact, so
the union bound over the pipeline collapses to the single randomized term. -/
theorem foldPipeline_error (k : Nat) (c : Circuit) :
    (foldPipeline k).error c =
      ((relevantForms c).length.choose 2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ k := by
  simp only [foldPipeline, RandPass.pipeline_cons, RandPass.pipeline_nil, RandPass.comp,
    PhaseFoldRand_error]
  simp [RandPass.id, CancelGatesR, CnotMinR, Pass.toRand]

/-- What the pipeline computes: phase folding first, on the seed's first component, then the
two deterministic passes. -/
theorem foldPipeline_correct (k : Nat) (c : Circuit) (hc : c.Wf)
    (s : (foldPipeline k).Seed c) :
    (foldPipeline k).run c s = CnotMin.run (CancelGates.run (phaseFold (liftSample s.1) c)) :=
  rfl

end
end TzapLean
