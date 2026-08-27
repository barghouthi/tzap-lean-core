import TzapLean.PhaseFoldProof
import TzapLean.RandPass

/-!
# `PhaseFoldRand` as a `RandPass`

Everything is in place: `phaseFoldGates_correct` says the pass is right whenever its tags are
faithful, and `collides_probability_le` says unfaithful tags are unlikely. Putting the two
together gives the obligation `RandPass` demands,

```
Pr_{s ← uniform} [ ⟦phaseFold s c⟧ ≠ ⟦c⟧ ]  ≤  C(L, 2) · 2⁻ᵏ
```

where `L` is the number of parities (and complements) this circuit makes the pass compare —
at most `2·(n·(|gates|+1) + 1)`. The seed is drawn once per circuit: one uniform `k`-bit tag
per variable, `Sample (varBound c) k`, which is exactly what `phaseFoldIO` draws at runtime.
-/

namespace TzapLean

open scoped ENNReal

open Form

/-! ## Well-formedness is preserved -/

theorem emitRotation_wf (q : Qubit) (a : ℚ) : ∀ g ∈ emitRotation q a, g.Wf := by
  by_cases h0 : BlockState.angleMod a = 0
  · rw [emitRotation_eq_nil h0]; simp
  · cases hcl : classifyQuarterPi (BlockState.angleMod a) with
    | some j =>
        rw [emitRotation_eq_diagRun h0 hcl]
        match j with
        | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => intro g hg; fin_cases hg <;> trivial
        | (i + 8) => intro g hg; simp [diagRun] at hg
    | none =>
        rw [emitRotation_eq_rz h0 hcl]
        intro g hg
        rw [List.mem_singleton.1 hg]
        trivial

theorem emitAll_wf {gs : List Gate} (h : ∀ g ∈ gs, g.Wf) : ∀ g ∈ emitAll gs, g.Wf := by
  induction gs with
  | nil => intro g hg; simp [emitAll] at hg
  | cons x gs ih =>
      intro g hg
      rw [emitAll] at hg
      rcases List.mem_append.1 hg with hg | hg
      · cases hrot : rotAngle x with
        | some p =>
            obtain ⟨a, q⟩ := p
            rw [hrot] at hg
            exact emitRotation_wf q a g hg
        | none =>
            rw [hrot] at hg
            rw [List.mem_singleton.1 hg]
            exact h x (by simp)
      · exact ih (fun y hy => h y (by simp [hy])) g hg

theorem foldFrom_wf {k : Nat} (wdraws : Nat → Tag) (targets : Array Bool) :
    ∀ (N : Nat) (gs : List Gate), gs.length ≤ N → ∀ (at_ : Nat) (ts : TState k),
      (∀ g ∈ gs, g.Wf) → ∀ g ∈ foldFrom wdraws targets ts at_ gs, g.Wf := by
  intro N
  induction N with
  | zero =>
      intro gs hgs at_ ts _ g hg
      rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hgs)] at hg
      simp at hg
  | succ N ih =>
      intro gs hlen at_ ts hwf
      cases gs with
      | nil => intro g hg; simp at hg
      | cons x gs =>
          have hlenN : gs.length ≤ N := by
            simp only [List.length_cons] at hlen
            omega
          have keep : foldFrom wdraws targets ts at_ (x :: gs)
                = x :: foldFrom wdraws targets (ts.step wdraws x) (at_ + 1) gs →
              ∀ g ∈ foldFrom wdraws targets ts at_ (x :: gs), g.Wf := by
            intro heq g hg
            rw [heq] at hg
            rcases List.mem_cons.1 hg with rfl | hg
            · exact hwf g (by simp)
            · exact ih gs hlenN _ _ (fun y hy => hwf y (by simp [hy])) g hg
          cases hrot : rotAngle x with
          | none => exact keep (foldFrom_cons_none hrot)
          | some p =>
              obtain ⟨θ, q⟩ := p
              by_cases hsel : targets[at_]?.getD true = true
              case neg => exact keep (foldFrom_cons_keep hrot (Or.inl (by simpa using hsel)))
              case pos =>
              cases hm : mergeInto wdraws ts (ts.tagOf q) θ gs with
              | none => exact keep (foldFrom_cons_keep hrot (Or.inr hm))
              | some gs' =>
                  obtain ⟨M, rest, g', φ, q', sign, hgseq, hgs'eq, -, -, -⟩ :=
                    mergeInto_spec wdraws (ts.tagOf q) θ gs gs' ts hm
                  have hlen'' : gs'.length ≤ N := by
                    have := mergeInto_length wdraws (ts.tagOf q) θ gs gs' ts hm
                    omega
                  have hwf' : ∀ y ∈ gs', y.Wf := by
                    intro y hy
                    rw [hgs'eq] at hy
                    rcases List.mem_append.1 hy with hy | hy
                    · exact hwf y (by rw [hgseq]; simp [hy])
                    · rcases List.mem_cons.1 hy with rfl | hy
                      · trivial
                      · exact hwf y (by rw [hgseq]; simp [hy])
                  intro g hg
                  rw [foldFrom_cons_merge hrot hsel hm] at hg
                  exact ih gs' hlen'' (at_ + 1) ts hwf' g hg

theorem phaseFoldGates_wf {k n : Nat} (wdraws : Nat → Tag) {gs : List Gate}
    (h : ∀ g ∈ gs, g.Wf) : ∀ g ∈ phaseFoldGates k wdraws n gs, g.Wf :=
  emitAll_wf (foldFrom_wf (k := k) wdraws _ gs.length gs le_rfl 0 _ h)

/-! ## The compared parities are bounded -/

theorem fresh_steps_le (st : AState) (gs : List Gate) :
    (st.steps gs).fresh ≤ st.fresh + gs.length := by
  induction gs generalizing st with
  | nil => simp
  | cons g gs ih =>
      have hstep : (st.step g).fresh ≤ st.fresh + 1 := by cases g <;> simp [AState.step]
      have := ih (st.step g)
      simp only [AState.steps_cons, List.length_cons]
      omega

theorem bounded_formsOf {n : Nat} {st : AState} (hst : st.Bounded) {m : Nat}
    (h : st.fresh ≤ m) : ∀ p ∈ formsOf n st, Form.Bounded m p := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact Form.bounded_const _ false
  · rcases List.mem_map.1 hp with ⟨q, -, rfl⟩
    exact Form.bounded_mono h (hst q)

theorem bounded_visited {n : Nat} : ∀ (gs : List Gate) (st : AState), st.Bounded →
    ∀ {m : Nat}, st.fresh + gs.length ≤ m → ∀ p ∈ visited n st gs, Form.Bounded m p := by
  intro gs
  induction gs with
  | nil =>
      intro st hst m h p hp
      exact bounded_formsOf hst (by simpa using h) p hp
  | cons g gs ih =>
      intro st hst m h p hp
      have hstep : (st.step g).fresh ≤ st.fresh + 1 := by cases g <;> simp [AState.step]
      rcases List.mem_append.1 hp with hp | hp
      · refine bounded_formsOf hst ?_ p hp
        simp only [List.length_cons] at h
        omega
      · refine ih (st.step g) (AState.bounded_step hst g) ?_ p hp
        simp only [List.length_cons] at h
        omega

/-- The forms one run of the pass can compare. -/
noncomputable def relevantForms (c : Circuit) : List Form :=
  relevant c.numQubits (AState.initial c.numQubits) c.gates

theorem bounded_relevantForms (c : Circuit) :
    ∀ p ∈ relevantForms c, Form.Bounded (varBound c) p := by
  intro p hp
  have hbase : ∀ r ∈ visited c.numQubits (AState.initial c.numQubits) c.gates,
      Form.Bounded (varBound c) r := by
    refine bounded_visited c.gates (AState.initial c.numQubits) (AState.bounded_initial _) ?_
    simp [varBound, AState.initial]
  rcases List.mem_append.1 hp with hp | hp
  · exact hbase p hp
  · rcases List.mem_map.1 hp with ⟨r, hr, rfl⟩
    exact Form.bounded_flip (hbase r hr)

/-! ## Faithful, unless the tags collide -/

theorem faithful_of_not_collides {m k : Nat} {ps : List Form} {sample : Sample m k}
    (h : ¬ Collides ps sample) : Faithful (liftSample sample) ps := by
  intro p hp q hq hpq
  by_contra hne
  exact h ⟨p, hp, q, hq, hne, hpq⟩

/-! ## The pass -/

noncomputable section

/-- **Phase folding, as a randomized pass.** The seed is one uniform `k`-bit tag per
variable; the failure probability is the chance that two of the parities this circuit makes
the pass compare hash alike. -/
def PhaseFoldRand (k : Nat) : RandPass where
  name := "Phase folding"
  Seed := fun c => Sample (varBound c) k
  dist := fun _ => PMF.uniformOfFintype _
  run := fun c s => phaseFold k (wordsOf k (liftSample s)) c
  error := fun c => ((relevantForms c).length.choose 2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ k
  numQubits_run _ _ := rfl
  numCbits_run _ _ := rfl
  wf_run c s hc := phaseFoldGates_wf (wordsOf k (liftSample s)) hc
  correct c hc := by
    refine le_trans ((PMF.uniformOfFintype (Sample (varBound c) k)).toOuterMeasure_mono ?_)
      (collides_probability_le (relevantForms c) (bounded_relevantForms c))
    intro s hs
    by_contra hcol
    exact hs.1 (phaseFoldGates_correct (wordToBits_wordsOf k (liftSample s)) c.gates hc
      (faithful_of_not_collides hcol))

@[simp] theorem PhaseFoldRand_run (k : Nat) (c : Circuit) (s : (PhaseFoldRand k).Seed c) :
    (PhaseFoldRand k).run c s = phaseFold k (wordsOf k (liftSample s)) c := rfl

/-- The failure bound in closed form: with `t` compared parities the pass is wrong with
probability at most `C(t,2)·2⁻ᵏ`, so doubling the tag width squares the odds against it. -/
theorem PhaseFoldRand_error (k : Nat) (c : Circuit) :
    (PhaseFoldRand k).error c =
      ((relevantForms c).length.choose 2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ k := rfl

end

end TzapLean
