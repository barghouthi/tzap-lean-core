import TzapLean.SuperOpt

/-!
# `SuperOpt`: correctness

The pass proposes a rewrite by search and then *verifies* it, so nothing about the search
enters the proof. What the verification establishes, and what this file turns into a `Pass`:

* `trySynth_correct` — a replacement that passes `accepts` denotes the window's unitary up to
  global phase, hence is equivalent to it. This is where `Locality.equivalent_of_local_smul`
  earns its keep: the matrices compared are the window's own, on its own wires.
* `tryWindow_correct` — carrying `WinOk` along the scan: the window's support stays distinct
  and in range, its members live on it, and no skipped gate touches it. The last invariant is
  what lets a window be a subsequence rather than a slice — every skipped gate commutes past
  every member.
-/

namespace TzapLean

open ExactMat

/-! ## Small facts about the scan's bookkeeping -/

theorem touches_false {S : List Qubit} {g : Gate} (h : touches S g = false) :
    ∀ q ∈ g.qubitsOf, q ∉ S := by
  intro q hq hmem
  rw [touches, List.any_eq_false] at h
  exact absurd (List.contains_iff_mem.2 hmem) (by simpa using h q hq)

theorem mem_widen : ∀ (l S : List Qubit) {q : Qubit}, q ∈ widen S l → q ∈ S ∨ q ∈ l := by
  intro l
  induction l with
  | nil => intro S q h; exact Or.inl h
  | cons a as ih =>
      intro S q h
      rw [widen] at h
      rcases ih _ h with h' | h'
      · by_cases hc : S.contains a = true
        · rw [if_pos hc] at h'; exact Or.inl h'
        · rw [if_neg hc] at h'
          rcases List.mem_append.1 h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (by simp [List.mem_singleton.1 h''])
      · exact Or.inr (by simp [h'])

theorem subset_widen : ∀ (l S : List Qubit) {q : Qubit}, q ∈ S → q ∈ widen S l := by
  intro l
  induction l with
  | nil => intro S q h; exact h
  | cons a as ih =>
      intro S q h
      rw [widen]
      refine ih _ ?_
      by_cases hc : S.contains a = true
      · rw [if_pos hc]; exact h
      · rw [if_neg hc]; exact List.mem_append.2 (Or.inl h)

theorem mem_widen_of_mem : ∀ (l S : List Qubit) {q : Qubit}, q ∈ l → q ∈ widen S l := by
  intro l
  induction l with
  | nil => intro S q h; simp at h
  | cons a as ih =>
      intro S q h
      rw [widen]
      rcases List.mem_cons.1 h with rfl | h'
      · refine subset_widen _ _ ?_
        by_cases hc : S.contains q = true
        · rw [if_pos hc]; exact List.contains_iff_mem.1 hc
        · rw [if_neg hc]; exact List.mem_append.2 (Or.inr (by simp))
      · exact ih _ h'

theorem nodup_widen : ∀ (l S : List Qubit), S.Nodup → (widen S l).Nodup := by
  intro l
  induction l with
  | nil => intro S hnd; exact hnd
  | cons a as ih =>
      intro S hnd
      rw [widen]
      refine ih _ ?_
      by_cases hc : S.contains a = true
      · rw [if_pos hc]; exact hnd
      · rw [if_neg hc]
        refine List.Nodup.append hnd (by simp) ?_
        intro x hx hy
        rw [List.mem_singleton.1 hy] at hx
        exact hc (List.contains_iff_mem.2 hx)

theorem qubitsOf_nodup {g : Gate} (h : g.Wf) : g.qubitsOf.Nodup := by
  cases g <;> simp_all [Gate.Wf, Gate.qubitsOf]

theorem isWindowGate_isUnitary {g : Gate} (h : isWindowGate g = true) : g.isUnitary = true := by
  cases g <;> simp_all [isWindowGate, Gate.isUnitary, Gate.isMeasurement]

/-! ## Localizing and globalizing preserve well-formedness -/

theorem Wf_mapQubits {f : Qubit → Qubit} {g : Gate} (hwf : g.Wf)
    (hinj : ∀ q ∈ g.qubitsOf, ∀ r ∈ g.qubitsOf, f q = f r → q = r) : (mapQubits f g).Wf := by
  cases g <;>
    simp_all [mapQubits, Gate.Wf, Gate.qubitsOf] <;>
    tauto

theorem localIdxD_inj {S : List Qubit} {q r : Qubit} (hq : q ∈ S) (hr : r ∈ S)
    (h : localIdxD S q = localIdxD S r) : q = r := by
  obtain ⟨i, hi, hdi⟩ := exists_localIdx hq
  obtain ⟨j, hj, hdj⟩ := exists_localIdx hr
  rw [hdi, hdj] at h
  subst h
  exact (localIdx_getD hi).symm.trans (localIdx_getD hj)

theorem getD_inj {S : List Qubit} (hnd : S.Nodup) {i j : Nat} (hi : i < S.length)
    (hj : j < S.length) (h : S.getD i 0 = S.getD j 0) : i = j := by
  have h1 := localIdx_getD_self hnd hi
  have h2 := localIdx_getD_self hnd hj
  rw [h, h2] at h1
  exact (Option.some.injEq _ _ ▸ h1).symm

/-! ## What `accepts` establishes -/

theorem applyGate_isUnitary {n : Nat} {g : Gate} {M M' : ExactMat n}
    (h : applyGate g M = some M') : g.isUnitary = true := by
  cases g <;> simp_all [applyGate, Gate.isUnitary, Gate.isMeasurement]

theorem matrixOfFrom_isUnitary {n : Nat} : ∀ (gs : List Gate) {M M' : ExactMat n},
    matrixOfFrom M gs = some M' → ∀ g ∈ gs, g.isUnitary = true := by
  intro gs
  induction gs with
  | nil => intro M M' _ g hg; simp at hg
  | cons a as ih =>
      intro M M' h g hg
      rw [matrixOfFrom] at h
      cases ha : applyGate a M with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some M₁ =>
          rw [ha, Option.bind_some] at h
          rcases List.mem_cons.1 hg with rfl | hg
          · exact applyGate_isUnitary ha
          · exact ih h g hg

theorem matrixOf_isUnitary {n : Nat} {gs : List Gate} {M : ExactMat n}
    (h : matrixOf n gs = some M) : ∀ g ∈ gs, g.isUnitary = true :=
  matrixOfFrom_isUnitary gs h

theorem accepts_spec {k : Nat} {target : ExactMat k} {cand : List Gate}
    (h : accepts target cand = true) :
    (∀ g ∈ cand, ∀ q ∈ g.qubitsOf, q < k) ∧ (∀ g ∈ cand, g.Wf) ∧
      ∃ N p, matrixOf k cand = some N ∧ phaseMatch target N.normalize = some p := by
  rw [accepts, Bool.and_eq_true] at h
  obtain ⟨hall, hmat⟩ := h
  rw [List.all_eq_true] at hall
  refine ⟨fun g hg q hq => ?_, fun g hg => ?_, ?_⟩
  · have := hall g hg
    rw [Bool.and_eq_true, List.all_eq_true] at this
    exact of_decide_eq_true (this.1 q hq)
  · have := hall g hg
    rw [Bool.and_eq_true] at this
    exact of_decide_eq_true this.2
  · cases hN : matrixOf k cand with
    | none => rw [hN] at hmat; exact absurd hmat (by simp)
    | some N =>
        rw [hN] at hmat
        simp only at hmat
        cases hp : phaseMatch target N.normalize with
        | none => rw [hp] at hmat; exact absurd hmat (by simp)
        | some p => exact ⟨N, p, rfl, hp⟩

/-! ## A verified replacement is equivalent to its window -/

theorem trySynth_correct {n m : Nat} {tbl : SynthTable} {w : Win} {repl : List Gate}
    (hnd : w.support.Nodup) (hrange : ∀ q ∈ w.support, q < n)
    (hsub : ∀ g ∈ w.members, ∀ q ∈ g.qubitsOf, q ∈ w.support)
    (hwf : ∀ g ∈ w.members, g.Wf)
    (h : trySynth tbl w = some repl) :
    Equivalent n m repl w.members ∧ (∀ g ∈ repl, g.Wf) ∧
      (∀ g ∈ repl, ∀ q ∈ g.qubitsOf, q ∈ w.support) := by
  set S := w.support with hS
  set k := S.length with hk
  rw [trySynth] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i M hM
      split at h
      · exact absurd h (by simp)
      · rename_i cand _
        split at h
        · rename_i hok
          rw [Bool.and_eq_true] at hok
          obtain ⟨hacc, -⟩ := hok
          rw [Option.some.injEq] at h
          subst h
          obtain ⟨hqb, hwfc, N, p, hN, hp⟩ := accepts_spec hacc
          -- the localized window is well-formed
          have hwfl : ∀ g ∈ localizeGates S w.members, g.Wf := by
            intro g hg
            rcases List.mem_map.1 hg with ⟨g', hg', rfl⟩
            refine Wf_mapQubits (hwf g' hg') ?_
            intro q hq r hr hqr
            exact localIdxD_inj (hsub g' hg' q hq) (hsub g' hg' r hr) hqr
          -- the replacement's gates
          have hround : ∀ g ∈ cand, localizeGate S (globalizeGate S g) = g := by
            intro g hg
            refine mapQubits_comp ?_
            intro q hq
            exact localIdxD_eq (localIdx_getD_self hnd (hqb g hg q hq))
          have hlocal : localizeGates S (cand.map (globalizeGate S)) = cand := by
            rw [localizeGates, List.map_map]
            refine Eq.trans (List.map_congr_left ?_) (List.map_id cand)
            intro g hg
            exact hround g hg
          have hreplsub : ∀ g ∈ cand.map (globalizeGate S), ∀ q ∈ g.qubitsOf, q ∈ S := by
            intro g hg q hq
            rcases List.mem_map.1 hg with ⟨g', hg', rfl⟩
            rw [globalizeGate, qubitsOf_mapQubits] at hq
            rcases List.mem_map.1 hq with ⟨i, hi, rfl⟩
            exact getD_mem (hqb g' hg' i hi)
          have hreplwf : ∀ g ∈ cand.map (globalizeGate S), g.Wf := by
            intro g hg
            rcases List.mem_map.1 hg with ⟨g', hg', rfl⟩
            refine Wf_mapQubits (hwfc g' hg') ?_
            intro q hq r hr hqr
            exact getD_inj hnd (hqb g' hg' q hq) (hqb g' hg' r hr) hqr
          -- both sides are unitary gate lists
          have hcandu : ∀ g ∈ cand, g.isUnitary = true := matrixOf_isUnitary hN
          have hreplu : ∀ g ∈ cand.map (globalizeGate S), g.isUnitary = true := by
            intro g hg
            rcases List.mem_map.1 hg with ⟨g', hg', rfl⟩
            rw [globalizeGate, isUnitary_mapQubits]
            exact hcandu g' hg'
          have hmemu : ∀ g ∈ w.members, g.isUnitary = true := by
            intro g hg
            have := matrixOf_isUnitary hM (localizeGate S g) (List.mem_map.2 ⟨g, hg, rfl⟩)
            rwa [localizeGate, isUnitary_mapQubits] at this
          -- the matrices agree up to a global phase
          have h1 : N.interp = unitary k cand := matrixOf_sound hwfc hN
          have h2 : M.interp = unitary k (localizeGates S w.members) := matrixOf_sound hwfl hM
          have h3 : (N.normalize).interp = ω ^ p • (M.normalize).interp := phaseMatch_sound hp
          rw [interp_normalize, interp_normalize, h1, h2] at h3
          refine ⟨?_, hreplwf, hreplsub⟩
          exact equivalent_of_local_smul hnd hrange hsub hreplsub hmemu hreplu (ω ^ p)
            (omega_pow_unit p) (by rw [hlocal]; exact h3)
        · exact absurd h (by simp)

/-! ## The scan's invariant -/

/-- What the scan maintains about a window: its support is a set of real wires, its members
live on it, and **no skipped gate touches it** — the last is what makes a window a legitimate
subsequence, since every skipped gate then commutes past every member. -/
structure WinOk (n m : Nat) (w : Win) : Prop where
  /-- The support lists distinct wires. -/
  nodup : w.support.Nodup
  /-- All of them are wires of the register. -/
  range : ∀ q ∈ w.support, q < n
  /-- Members live on the support. -/
  sub : ∀ g ∈ w.members, ∀ q ∈ g.qubitsOf, q ∈ w.support
  /-- Members are well-formed… -/
  wf : ∀ g ∈ w.members, g.Wf
  /-- …and unitary. -/
  unit : ∀ g ∈ w.members, g.isUnitary = true
  /-- Skipped gates are well-formed. -/
  wfsk : ∀ g ∈ w.skipped, g.Wf
  /-- No skipped gate touches the support. -/
  disj : ∀ g ∈ w.skipped, ∀ q ∈ g.qubitsOf, q ∉ w.support
  /-- Pulling the members to the front of the span is meaning-preserving. -/
  equiv : Equivalent n m (w.members ++ w.skipped) w.consumed

theorem disjoint_of_notMem {g g' : Gate} (h : ∀ q ∈ g.qubitsOf, q ∉ g'.qubitsOf) :
    Wires.Disjoint g.support g'.support := by
  intro q hq
  rcases hq' : g'.support q with _ | _
  · rfl
  · exact absurd ((Gate.support_iff g' q).1 (by simp [hq'])) (h q ((Gate.support_iff g q).1 hq))

theorem tryWindow_correct {n m : Nat} {cfg : SuperOptConfig} {tbl : SynthTable} :
    ∀ (rest : List Gate) (w : Win) (out : List Gate), WinOk n m w → (∀ g ∈ rest, g.Wf) →
      tryWindow cfg tbl n w rest = some out →
      Equivalent n m out (w.consumed ++ rest) ∧ (∀ g ∈ out, g.Wf) := by
  intro rest
  induction rest with
  | nil => intro w out _ _ h; rw [tryWindow] at h; exact absurd h (by simp)
  | cons g rest ih =>
      intro w out hok hwfr h
      rw [tryWindow] at h
      split at h
      · -- the gate touches the window
        rename_i htouch
        split at h
        · rename_i hchecks
          -- unpack the guard
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
            List.any_eq_false] at hchecks
          obtain ⟨⟨⟨⟨⟨hwin, hrangeg⟩, hwfg⟩, -⟩, -⟩, hskip⟩ := hchecks
          have hrangeg' : ∀ q ∈ g.qubitsOf, q < n := hrangeg
          have hu : g.isUnitary = true := isWindowGate_isUnitary hwin
          set sup := widen w.support g.qubitsOf with hsup
          -- the skipped gates still miss the widened support
          have hdisj' : ∀ s ∈ w.skipped, ∀ q ∈ s.qubitsOf, q ∉ sup := by
            intro s hs
            exact touches_false (by simpa using hskip s hs)
          have hok' : WinOk n m ⟨sup, w.members ++ [g], w.skipped, w.consumed ++ [g]⟩ := by
            refine ⟨nodup_widen _ _ hok.nodup, ?_, ?_, ?_, ?_, hok.wfsk, hdisj', ?_⟩
            · intro q hq
              rcases mem_widen _ _ hq with hq' | hq'
              · exact hok.range q hq'
              · exact hrangeg' q hq'
            · intro x hx q hq
              rcases List.mem_append.1 hx with hx | hx
              · exact subset_widen _ _ (hok.sub x hx q hq)
              · rw [List.mem_singleton.1 hx] at hq
                exact mem_widen_of_mem _ _ hq
            · intro x hx
              rcases List.mem_append.1 hx with hx | hx
              · exact hok.wf x hx
              · rw [List.mem_singleton.1 hx]; exact hwfg
            · intro x hx
              rcases List.mem_append.1 hx with hx | hx
              · exact hok.unit x hx
              · rw [List.mem_singleton.1 hx]; exact hu
            · -- the new member moves to the front of the skipped block
              have hgd : ∀ s ∈ w.skipped, Wires.Disjoint g.support s.support := by
                intro s hs
                refine disjoint_of_notMem ?_
                intro q hq hq'
                exact hdisj' s hs q hq' (mem_widen_of_mem _ _ hq)
              have e1 : Equivalent n m ((w.members ++ w.skipped) ++ [g]) (w.consumed ++ [g]) :=
                Equivalent.append_right [g] hok.equiv
              have e2 : Equivalent n m ((w.members ++ [g]) ++ w.skipped)
                  ((w.members ++ w.skipped) ++ [g]) := by
                have := Equivalent.append_left (n := n) (m := m) w.members
                  (Equivalent.move_back hu w.skipped hgd)
                simpa using this
              exact e2.trans e1
          split at h
          · -- a rewrite was found
            rename_i repl hsynth
            rw [Option.some.injEq] at h
            subst h
            obtain ⟨heq, hwfrepl, -⟩ :=
              trySynth_correct (m := m) hok'.nodup hok'.range hok'.sub hok'.wf hsynth
            constructor
            · have e1 : Equivalent n m (repl ++ w.skipped) ((w.members ++ [g]) ++ w.skipped) :=
                Equivalent.append_right w.skipped heq
              have e2 : Equivalent n m (repl ++ w.skipped) (w.consumed ++ [g]) :=
                e1.trans hok'.equiv
              have := Equivalent.append_right (n := n) (m := m) rest e2
              simpa using this
            · intro x hx
              rcases List.mem_append.1 hx with hx | hx
              · rcases List.mem_append.1 hx with hx | hx
                · exact hwfrepl x hx
                · exact hok.wfsk x hx
              · exact hwfr x (by simp [hx])
          · -- keep scanning
            obtain ⟨heq, hwfout⟩ :=
              ih ⟨sup, w.members ++ [g], w.skipped, w.consumed ++ [g]⟩ out hok'
                (fun x hx => hwfr x (by simp [hx])) h
            exact ⟨by simpa using heq, hwfout⟩
        · exact absurd h (by simp)
      · -- the gate misses the window: skip it
        rename_i htouch
        have hmiss : ∀ q ∈ g.qubitsOf, q ∉ w.support := touches_false (by simpa using htouch)
        have hok' : WinOk n m ⟨w.support, w.members, w.skipped ++ [g], w.consumed ++ [g]⟩ := by
          refine ⟨hok.nodup, hok.range, hok.sub, hok.wf, hok.unit, ?_, ?_, ?_⟩
          · intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact hok.wfsk x hx
            · rw [List.mem_singleton.1 hx]; exact hwfr g (by simp)
          · intro x hx q hq
            rcases List.mem_append.1 hx with hx | hx
            · exact hok.disj x hx q hq
            · rw [List.mem_singleton.1 hx] at hq
              exact hmiss q hq
          · have := Equivalent.append_right (n := n) (m := m) [g] hok.equiv
            simpa using this
        obtain ⟨heq, hwfout⟩ :=
          ih ⟨w.support, w.members, w.skipped ++ [g], w.consumed ++ [g]⟩ out hok'
            (fun x hx => hwfr x (by simp [hx])) h
        exact ⟨by simpa using heq, hwfout⟩

/-! ## The pass -/

theorem rewriteOnce_correct {n m : Nat} {cfg : SuperOptConfig} {tbl : SynthTable} :
    ∀ (gs out : List Gate), (∀ g ∈ gs, g.Wf) → rewriteOnce cfg tbl n gs = some out →
      Equivalent n m out gs ∧ (∀ g ∈ out, g.Wf) := by
  intro gs
  induction gs with
  | nil => intro out _ h; rw [rewriteOnce] at h; exact absurd h (by simp)
  | cons g rest ih =>
      intro out hwf h
      rw [rewriteOnce] at h
      split at h
      · rename_i hguard
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hguard
        obtain ⟨⟨⟨hwin, -⟩, hrangeg⟩, hwfg⟩ := hguard
        split at h
        · rename_i outw hw
          rw [Option.some.injEq] at h
          subst h
          have hok : WinOk n m (Win.start g) := by
            refine ⟨qubitsOf_nodup hwfg, hrangeg, ?_, ?_, ?_, by simp [Win.start], by
              simp [Win.start], ?_⟩
            · intro x hx q hq
              rw [List.mem_singleton.1 hx] at hq
              exact hq
            · intro x hx; rw [List.mem_singleton.1 hx]; exact hwfg
            · intro x hx
              rw [List.mem_singleton.1 hx]
              exact isWindowGate_isUnitary hwin
            · simpa [Win.start] using Equivalent.refl n m [g]
          obtain ⟨heq, hwfout⟩ :=
            tryWindow_correct rest (Win.start g) outw hok (fun x hx => hwf x (by simp [hx])) hw
          exact ⟨by simpa [Win.start] using heq, hwfout⟩
        · rcases Option.map_eq_some_iff.1 h with ⟨out', hout', rfl⟩
          obtain ⟨heq, hwfout⟩ := ih out' (fun x hx => hwf x (by simp [hx])) hout'
          refine ⟨by simpa using Equivalent.append_left [g] heq, ?_⟩
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hwf x (by simp)
          · exact hwfout x hx
      · rcases Option.map_eq_some_iff.1 h with ⟨out', hout', rfl⟩
        obtain ⟨heq, hwfout⟩ := ih out' (fun x hx => hwf x (by simp [hx])) hout'
        refine ⟨by simpa using Equivalent.append_left [g] heq, ?_⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hwf x (by simp)
        · exact hwfout x hx

theorem superOptAux_correct {n m : Nat} {cfg : SuperOptConfig} {tbl : SynthTable} :
    ∀ (fuel : Nat) (gs : List Gate), (∀ g ∈ gs, g.Wf) →
      Equivalent n m (superOptAux cfg tbl n fuel gs) gs ∧
        (∀ g ∈ superOptAux cfg tbl n fuel gs, g.Wf) := by
  intro fuel
  induction fuel with
  | zero => intro gs hwf; exact ⟨Equivalent.refl n m gs, hwf⟩
  | succ fuel ih =>
      intro gs hwf
      rw [superOptAux]
      split
      · rename_i gs' hstep
        obtain ⟨heq, hwf'⟩ := rewriteOnce_correct (m := m) gs gs' hwf hstep
        obtain ⟨heq', hwf''⟩ := ih gs' hwf'
        exact ⟨heq'.trans heq, hwf''⟩
      · exact ⟨Equivalent.refl n m gs, hwf⟩

/-- **Superoptimization preserves meaning.** -/
theorem superOptGates_correct {n m : Nat} (cfg : SuperOptConfig) (tbl : SynthTable)
    (gs : List Gate) (hwf : ∀ g ∈ gs, g.Wf) :
    Equivalent n m (superOptGates cfg tbl n gs) gs :=
  (superOptAux_correct gs.length gs hwf).1

theorem superOptGates_wf {n : Nat} (cfg : SuperOptConfig) (tbl : SynthTable) (gs : List Gate)
    (hwf : ∀ g ∈ gs, g.Wf) : ∀ g ∈ superOptGates cfg tbl n gs, g.Wf :=
  (superOptAux_correct (n := n) (m := 0) gs.length gs hwf).2

/-- `SuperOpt`, as a `Pass`: the rewrite is decided by exact matrix comparison, so the proof
obligation is discharged by the check the pass already runs. -/
def SuperOpt (cfg : SuperOptConfig) (tbl : SynthTable) : Pass where
  name := "Superoptimization"
  run := superOpt cfg tbl
  numQubits_run _ := rfl
  numCbits_run _ := rfl
  wf_run c hc := superOptGates_wf cfg tbl c.gates hc
  correct c hc := superOptGates_correct cfg tbl c.gates hc

@[simp] theorem SuperOpt_run (cfg : SuperOptConfig) (tbl : SynthTable) (c : Circuit) :
    (SuperOpt cfg tbl).run c = superOpt cfg tbl c := rfl

end TzapLean
