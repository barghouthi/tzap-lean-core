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

/-- The filter only ever skips work: a replacement it returns is one `trySynth` returned. -/
theorem trySynthFiltered_eq {tbl : SynthTable} {fm : Option FlatMat} {w : Win} {repl : List Gate}
    (h : trySynthFiltered tbl fm w = some repl) : trySynth tbl w = some repl := by
  rw [trySynthFiltered] at h
  split at h
  · exact h
  · exact absurd h (by simp)

/-! ## A verified replacement is equivalent to its window -/

theorem trySynth_correct {n m : Nat} {tbl : SynthTable} {w : Win} {repl : List Gate}
    (hnd : w.support.Nodup) (hrange : ∀ q ∈ w.support, q < n)
    (hsub : ∀ g ∈ w.members, ∀ q ∈ g.qubitsOf, q ∈ w.support)
    (hwf : ∀ g ∈ w.members, g.Wf)
    (h : trySynth tbl w = some repl) :
    Equivalent n m repl w.members ∧ (∀ g ∈ repl, g.Wf) ∧
      (∀ g ∈ repl, ∀ q ∈ g.qubitsOf, q ∈ w.support) ∧
      (∀ g ∈ repl, g.isUnitary = true) := by
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
          refine ⟨?_, hreplwf, hreplsub, hreplu⟩
          exact equivalent_of_local_smul hnd hrange hsub hreplsub hmemu hreplu (ω ^ p)
            (omega_pow_unit p) (by rw [hlocal]; exact h3)
        · exact absurd h (by simp)

theorem disjoint_of_notMem {g g' : Gate} (h : ∀ q ∈ g.qubitsOf, q ∉ g'.qubitsOf) :
    Wires.Disjoint g.support g'.support := by
  intro q hq
  rcases hq' : g'.support q with _ | _
  · rfl
  · exact absurd ((Gate.support_iff g' q).1 (by simp [hq'])) (h q ((Gate.support_iff g q).1 hq))

/-! ## What closing the window does

`closeSpan` is the one step that moves gates from one side of the window's partition to the
other, so it is the one step that has to be shown to keep the invariant. Four facts do it: the
span's gates are untouched, the support only grows, the members' wires stay inside it, and —
the point of iterating to a fixpoint — when a sweep reports no change, *every* remaining
skipped gate misses the support.

`absorbPass` is order-agnostic, so these are stated for the stored span (most recent first)
and used on it directly. -/

/-- Absorbing changes flags, not gates. -/
theorem absorbPass_gates : ∀ (span : Span) (S : List Qubit),
    spanGates (absorbPass S span).2.1 = spanGates span := by
  intro span
  induction span with
  | nil => intro S; rfl
  | cons p rest ih =>
      obtain ⟨g, b⟩ := p
      intro S
      cases b with
      | true => rw [absorbPass_true]; simp only [spanGates_cons]; rw [ih]
      | false =>
          rcases h : touches S g with _ | _
          · rw [absorbPass_false_miss rest h]; simp only [spanGates_cons]; rw [ih]
          · rw [absorbPass_false_touch rest h]; simp only [spanGates_cons]; rw [ih]

/-- The support only grows. -/
theorem absorbPass_support : ∀ (span : Span) (S : List Qubit) {q : Qubit},
    q ∈ S → q ∈ (absorbPass S span).1 := by
  intro span
  induction span with
  | nil => intro S q h; exact h
  | cons p rest ih =>
      obtain ⟨g, b⟩ := p
      intro S q hq
      cases b with
      | true => rw [absorbPass_true]; exact ih S hq
      | false =>
          rcases h : touches S g with _ | _
          · rw [absorbPass_false_miss rest h]; exact ih S hq
          · rw [absorbPass_false_touch rest h]
            exact ih _ (subset_widen _ _ hq)

/-- Every wire it adds comes from a gate it absorbed — which is a member afterwards. That is
what lets the bounds check, which vets the members, stand in for a check on the wires. -/
theorem absorbPass_support_src : ∀ (span : Span) (S : List Qubit) {q : Qubit},
    q ∈ (absorbPass S span).1 →
      q ∈ S ∨ ∃ x ∈ spanMembers (absorbPass S span).2.1, q ∈ x.qubitsOf := by
  intro span
  induction span with
  | nil => intro S q h; exact Or.inl h
  | cons p rest ih =>
      obtain ⟨g, b⟩ := p
      intro S q hq
      cases b with
      | true =>
          rw [absorbPass_true] at hq ⊢
          rcases ih S hq with h' | ⟨x, hx, hqx⟩
          · exact Or.inl h'
          · exact Or.inr ⟨x, by simp [hx], hqx⟩
      | false =>
          rcases h : touches S g with _ | _
          · rw [absorbPass_false_miss rest h] at hq ⊢
            rcases ih S hq with h' | ⟨x, hx, hqx⟩
            · exact Or.inl h'
            · exact Or.inr ⟨x, by simpa using hx, hqx⟩
          · rw [absorbPass_false_touch rest h] at hq ⊢
            rcases ih _ hq with hw | ⟨x, hx, hqx⟩
            · rcases mem_widen _ _ hw with h' | h'
              · exact Or.inl h'
              · exact Or.inr ⟨g, by simp, h'⟩
            · exact Or.inr ⟨x, by simp [hx], hqx⟩

/-- Distinctness survives. -/
theorem absorbPass_nodup : ∀ (span : Span) (S : List Qubit),
    S.Nodup → (absorbPass S span).1.Nodup := by
  intro span
  induction span with
  | nil => intro S h; exact h
  | cons p rest ih =>
      obtain ⟨g, b⟩ := p
      intro S hnd
      cases b with
      | true => rw [absorbPass_true]; exact ih S hnd
      | false =>
          rcases h : touches S g with _ | _
          · rw [absorbPass_false_miss rest h]; exact ih S hnd
          · rw [absorbPass_false_touch rest h]; exact ih _ (nodup_widen _ _ hnd)

/-- Members stay on the support. -/
theorem absorbPass_sub : ∀ (span : Span) (S : List Qubit),
    (∀ x ∈ spanMembers span, ∀ q ∈ x.qubitsOf, q ∈ S) →
      ∀ x ∈ spanMembers (absorbPass S span).2.1, ∀ q ∈ x.qubitsOf,
        q ∈ (absorbPass S span).1 := by
  intro span
  induction span with
  | nil => intro S _ x hx; simp at hx
  | cons p rest ih =>
      obtain ⟨g, b⟩ := p
      intro S hsub
      cases b with
      | true =>
          rw [absorbPass_true]
          simp only [spanMembers_cons_true]
          intro x hx q hq
          rcases List.mem_cons.1 hx with rfl | hx
          · exact absorbPass_support rest S (hsub x (by simp) q hq)
          · exact ih S (fun y hy => hsub y (by simp [hy])) x hx q hq
      | false =>
          rcases h : touches S g with _ | _
          · rw [absorbPass_false_miss rest h]
            simp only [spanMembers_cons_false]
            exact ih S (fun y hy => hsub y (by simpa using hy))
          · rw [absorbPass_false_touch rest h]
            simp only [spanMembers_cons_true]
            intro x hx q hq
            rcases List.mem_cons.1 hx with rfl | hx
            · exact absorbPass_support rest _ (mem_widen_of_mem _ _ hq)
            · refine ih _ (fun y hy q' hq' => ?_) x hx q hq
              exact subset_widen _ _ (hsub y (by simpa using hy) q' hq')

/-- Members stay members. -/
theorem absorbPass_members : ∀ (span : Span) (S : List Qubit),
    ∀ x ∈ spanMembers span, x ∈ spanMembers (absorbPass S span).2.1 := by
  intro span
  induction span with
  | nil => intro S x hx; exact hx
  | cons p rest ih =>
      obtain ⟨g, b⟩ := p
      intro S x hx
      cases b with
      | true =>
          rw [absorbPass_true]
          simp only [spanMembers_cons_true] at hx ⊢
          rcases List.mem_cons.1 hx with rfl | hx
          · simp
          · exact List.mem_cons_of_mem _ (ih S x hx)
      | false =>
          simp only [spanMembers_cons_false] at hx
          rcases h : touches S g with _ | _
          · rw [absorbPass_false_miss rest h]
            simp only [spanMembers_cons_false]
            exact ih S x hx
          · rw [absorbPass_false_touch rest h]
            simp only [spanMembers_cons_true]
            exact List.mem_cons_of_mem _ (ih _ x hx)

/-- Gates only move from skipped to member. -/
theorem absorbPass_skipped : ∀ (span : Span) (S : List Qubit),
    ∀ x ∈ spanSkipped (absorbPass S span).2.1, x ∈ spanSkipped span := by
  intro span
  induction span with
  | nil => intro S x hx; exact hx
  | cons p rest ih =>
      obtain ⟨g, b⟩ := p
      intro S x hx
      cases b with
      | true =>
          rw [absorbPass_true] at hx
          simp only [spanSkipped_cons_true] at hx ⊢
          exact ih S x hx
      | false =>
          rcases h : touches S g with _ | _
          · rw [absorbPass_false_miss rest h] at hx
            simp only [spanSkipped_cons_false] at hx ⊢
            rcases List.mem_cons.1 hx with rfl | hx
            · simp
            · exact List.mem_cons_of_mem _ (ih S x hx)
          · rw [absorbPass_false_touch rest h] at hx
            simp only [spanSkipped_cons_true] at hx
            simp only [spanSkipped_cons_false]
            exact List.mem_cons_of_mem _ (ih _ x hx)

/-- **A sweep that reports no change is a closed window.** Nothing moved, so the support never
widened during it, so the check every skipped gate failed was against the final support. -/
theorem absorbPass_stable : ∀ (span : Span) (S : List Qubit),
    (absorbPass S span).2.2 = false →
      (absorbPass S span).1 = S ∧ (absorbPass S span).2.1 = span ∧
        ∀ x ∈ spanSkipped span, touches S x = false := by
  intro span
  induction span with
  | nil =>
      intro S _
      refine ⟨rfl, rfl, ?_⟩
      intro x hx
      exact absurd hx (by simp)
  | cons p rest ih =>
      obtain ⟨g, b⟩ := p
      intro S hch
      cases b with
      | true =>
          rw [absorbPass_true] at hch ⊢
          obtain ⟨h1, h2, h3⟩ := ih S hch
          refine ⟨h1, ?_, ?_⟩
          · simp only [h2]
          · simpa using h3
      | false =>
          rcases h : touches S g with _ | _
          · rw [absorbPass_false_miss rest h] at hch ⊢
            obtain ⟨h1, h2, h3⟩ := ih S hch
            refine ⟨h1, by simp only [h2], ?_⟩
            intro x hx
            simp only [spanSkipped_cons_false] at hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact h
            · exact h3 x hx
          · rw [absorbPass_false_touch rest h] at hch
            exact absurd hch (by simp)

/-- What closing a window guarantees, as one object: the span's gates are untouched, the
support grew from the wires of that span, and the result is *closed* — every gate still on the
skipped side misses the support. -/
structure CloseOk (S S' : List Qubit) (span span' : Span) : Prop where
  /-- Flags changed; gates did not. -/
  gates : spanGates span' = spanGates span
  /-- The support only grew. -/
  grow : ∀ q ∈ S, q ∈ S'
  /-- …and only by wires of gates it absorbed, which are members afterwards. -/
  src : ∀ q ∈ S', q ∈ S ∨ ∃ x ∈ spanMembers span', q ∈ x.qubitsOf
  /-- Members stay members. -/
  members : ∀ x ∈ spanMembers span, x ∈ spanMembers span'
  /-- Distinctness survives. -/
  nodup : S.Nodup → S'.Nodup
  /-- Members stay on the support. -/
  sub : (∀ x ∈ spanMembers span, ∀ q ∈ x.qubitsOf, q ∈ S) →
        ∀ x ∈ spanMembers span', ∀ q ∈ x.qubitsOf, q ∈ S'
  /-- Gates only move from skipped to member. -/
  skipped : ∀ x ∈ spanSkipped span', x ∈ spanSkipped span

theorem CloseOk.trans {S S₁ S' : List Qubit} {span span₁ span' : Span}
    (h : CloseOk S S₁ span span₁) (h' : CloseOk S₁ S' span₁ span') : CloseOk S S' span span' where
  gates := h'.gates.trans h.gates
  grow q hq := h'.grow q (h.grow q hq)
  src q hq := by
    rcases h'.src q hq with hq' | ⟨x, hx, hqx⟩
    · rcases h.src q hq' with hq'' | ⟨y, hy, hqy⟩
      · exact Or.inl hq''
      · exact Or.inr ⟨y, h'.members y hy, hqy⟩
    · exact Or.inr ⟨x, hx, hqx⟩
  members x hx := h'.members x (h.members x hx)
  nodup hnd := h'.nodup (h.nodup hnd)
  sub hs := h'.sub (h.sub hs)
  skipped x hx := h.skipped x (h'.skipped x hx)

/-- One sweep, packaged. Being *closed* is not among these: only a sweep that reports no
change gives that, which is what iterating buys and `closeSpan_spec` records separately. -/
theorem absorbPass_closeOk (S : List Qubit) (span : Span) :
    CloseOk S (absorbPass S span).1 span (absorbPass S span).2.1 where
  gates := absorbPass_gates span S
  grow _ hq := absorbPass_support span S hq
  src _ hq := absorbPass_support_src span S hq
  members := absorbPass_members span S
  nodup := absorbPass_nodup span S
  sub := absorbPass_sub span S
  skipped := absorbPass_skipped span S

/-- **What `closeSpan` returns is a closed window**: a sequence of sweeps, and the last of
them reported nothing left to move. -/
theorem closeSpan_spec : ∀ (fuel : Nat) (S : List Qubit) (span : Span) {S' : List Qubit}
    {span' : Span}, closeSpan fuel S span = some (S', span') →
      CloseOk S S' span span' ∧ ∀ x ∈ spanSkipped span', touches S' x = false := by
  intro fuel
  induction fuel with
  | zero => intro S span S' span' h; rw [closeSpan] at h; exact absurd h (by simp)
  | succ fuel ih =>
      intro S span S' span' h
      rw [closeSpan] at h
      split at h
      · obtain ⟨hok, hcl⟩ := ih _ _ h
        exact ⟨(absorbPass_closeOk S span).trans hok, hcl⟩
      · rename_i hstable
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2, h3⟩ := absorbPass_stable span S (by simpa using hstable)
        refine ⟨absorbPass_closeOk S span, ?_⟩
        intro x hx
        rw [h1]
        exact h3 x (h2 ▸ hx)

/-! ## The scan's invariant -/

/-- What the scan maintains about a window: its support is a set of real wires, its members
live on it, and **no skipped gate touches it** — the last is what makes a window a legitimate
subsequence, since every skipped gate then commutes past every member. -/
structure WinOk (n m : Nat) (w : Win) : Prop where
  /-- The support lists distinct wires. -/
  nodup : w.support.Nodup
  /-- All of them are wires of the register. -/
  range : ∀ q ∈ w.support, q < n
  /-- The memoized member list is the span's. -/
  memEq : w.members = spanMembers w.span
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

/-! ### Pulling the members to the front

The window is a *partition* of its span: members, which live on the support, and skipped
gates, which miss it entirely. Every skipped gate therefore commutes with every member, and
the span can be rewritten as its members followed by its skipped gates. This is the one fact
about a window the rewrite consumes, and it is a theorem about the invariant rather than
something the scan has to carry along and re-establish at every step — which matters now that
a step can move gates from one side of the partition to the other. -/

/-- **A window's span is its members followed by its skipped gates.** -/
theorem equivalent_span {n m : Nat} (S : List Qubit) :
    ∀ (span : Span),
      (∀ p ∈ span, p.2 = true → (∀ q ∈ p.1.qubitsOf, q ∈ S) ∧ p.1.isUnitary = true) →
      (∀ p ∈ span, p.2 = false → ∀ q ∈ p.1.qubitsOf, q ∉ S) →
      Equivalent n m (spanMembers span ++ spanSkipped span) (spanGates span) := by
  intro span
  induction span with
  | nil => intro _ _; exact Equivalent.refl _ _ _
  | cons p rest ih =>
      intro hmem hsk
      obtain ⟨g, b⟩ := p
      have ihr := ih (fun q hq => hmem q (by simp [hq])) (fun q hq => hsk q (by simp [hq]))
      have hprop : ∀ x ∈ spanMembers rest,
          (∀ q ∈ x.qubitsOf, q ∈ S) ∧ x.isUnitary = true := fun x hx =>
        hmem (x, true) (List.mem_cons_of_mem _ (mem_spanMembers_iff.1 hx)) rfl
      cases b with
      | true =>
          -- a member stays at the front of both sides
          simp only [spanMembers_cons_true, spanSkipped_cons_true, spanGates_cons,
            List.cons_append]
          exact Equivalent.append_left [g] ihr
      | false =>
          -- a skipped gate has to travel back past the members, which it misses entirely
          have hmove : Equivalent n m (spanMembers rest ++ [g]) ([g] ++ spanMembers rest) :=
            Equivalent.append_comm _ _ (fun x hx => (hprop x hx).2) (fun x hx y hy => by
              rw [List.mem_singleton.1 hy]
              refine disjoint_of_notMem ?_
              intro q hq hq'
              exact hsk (g, false) (by simp) rfl q hq' ((hprop x hx).1 q hq))
          simp only [spanMembers_cons_false, spanSkipped_cons_false, spanGates_cons]
          have step₁ : Equivalent n m (spanMembers rest ++ g :: spanSkipped rest)
              (([g] ++ spanMembers rest) ++ spanSkipped rest) := by
            have := Equivalent.append_right (n := n) (m := m) (spanSkipped rest) hmove
            simpa using this
          refine Equivalent.trans step₁ ?_
          simpa using Equivalent.append_left [g] ihr

/-- **The window's rewrite target, in the order the rewrite emits it.** -/
theorem WinOk.equiv {n m : Nat} {w : Win} (h : WinOk n m w) :
    Equivalent n m (w.members ++ w.skipped) w.consumed := by
  rw [h.memEq]
  refine equivalent_span (n := n) (m := m) w.support w.span ?_ ?_
  · intro p hp hpt
    obtain ⟨x, b⟩ := p
    cases b with
    | false => exact absurd hpt (by simp)
    | true =>
        have hx : x ∈ spanMembers w.span :=
          mem_spanMembers_iff.2 hp
        exact ⟨fun q hq => h.sub x (h.memEq ▸ hx) q hq, h.unit x (h.memEq ▸ hx)⟩
  · intro p hp hpf
    obtain ⟨x, b⟩ := p
    cases b with
    | true => exact absurd hpf (by simp)
    | false =>
        have hx : x ∈ w.skipped := List.mem_filterMap.2 ⟨(x, false), hp, rfl⟩
        exact h.disj x hx

theorem acceptWindow_spec {cfg : SuperOptConfig} {n : Nat} {sup : List Qubit}
    {members : List Gate} {revSpan : Span} {w' : Win}
    (h : acceptWindow cfg n sup members revSpan = some w') :
    w' = ⟨sup, members, revSpan⟩ ∧ membersOk n members = true := by
  rw [acceptWindow] at h
  split at h
  · rename_i hb
    simp only [Option.some.injEq] at h
    simp only [Bool.and_eq_true] at hb
    exact ⟨h.symm, hb.2⟩
  · exact absurd h (by simp)

/-- **Growing a window keeps its invariant.**

Closing over a new wire is the one step that moves gates between the two sides of the
partition, so it is the one step that has to be shown safe. It is, and cheaply: the closure
only ever absorbs, so every wire it adds belongs to a gate that is a *member* afterwards — and
the members are exactly what `acceptWindow` then vets. What is left on the skipped side misses
the support because the last sweep reported nothing to move. -/
theorem growWindow_spec {n m : Nat} {cfg : SuperOptConfig} {w w' : Win} {g : Gate}
    (hok : WinOk n m w) (h : growWindow cfg n w g = some w') :
    WinOk n m w' ∧ w'.consumed = w.consumed ++ [g] := by
  rw [growWindow] at h
  rcases hclose : closeSpan (w.revSpan.length + 2) (widen w.support g.qubitsOf)
      ((g, true) :: w.revSpan) with _ | ⟨sup, revSpan⟩
  · rw [hclose] at h; exact absurd h (by simp)
  rw [hclose] at h
  simp only [Option.bind_some] at h
  obtain ⟨rfl, hmok⟩ := acceptWindow_spec h
  obtain ⟨hco, hclosed⟩ := closeSpan_spec _ _ _ hclose
  -- what `acceptWindow` vetted, unpacked once
  have hmemOk : ∀ x ∈ spanMembers revSpan.reverse,
      isWindowGate x = true ∧ (∀ q ∈ x.qubitsOf, q < n) ∧ x.Wf := by
    intro x hx
    have hall := (List.all_eq_true.1 hmok) x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hall
    exact ⟨hall.1.1, fun q hq => hall.1.2 q hq, hall.2⟩
  have hmemRev : ∀ x, x ∈ spanMembers revSpan ↔ x ∈ spanMembers revSpan.reverse :=
    fun _ => mem_spanMembers_reverse.symm
  -- every old member, and `g` itself, sits on the widened support
  have hsubIn : ∀ x ∈ spanMembers ((g, true) :: w.revSpan), ∀ q ∈ x.qubitsOf,
      q ∈ widen w.support g.qubitsOf := by
    intro x hx q hq
    simp only [spanMembers_cons_true] at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact mem_widen_of_mem _ _ hq
    · refine subset_widen _ _ (hok.sub x ?_ q hq)
      rw [hok.memEq, Win.span]
      exact mem_spanMembers_reverse.2 hx
  refine ⟨⟨hco.nodup (nodup_widen _ _ hok.nodup), ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- every support wire is a wire of the register
    intro q hq
    rcases hco.src q hq with hq' | ⟨x, hx, hqx⟩
    · rcases mem_widen _ _ hq' with h' | h'
      · exact hok.range q h'
      · exact (hmemOk g ((hmemRev g).1 (hco.members g (by simp)))).2.1 q h'
    · exact (hmemOk x ((hmemRev x).1 hx)).2.1 q hqx
  · -- members live on the support
    intro x hx q hq
    exact hco.sub hsubIn x ((hmemRev x).2 hx) q hq
  · exact fun x hx => (hmemOk x hx).2.2
  · exact fun x hx => isWindowGate_isUnitary (hmemOk x hx).1
  · -- skipped gates were skipped before, so they came from the circuit
    intro x hx
    have hx' := hco.skipped x (mem_spanSkipped_reverse.1 hx)
    simp only [spanSkipped_cons_true] at hx'
    exact hok.wfsk x (mem_spanSkipped_reverse.2 hx')
  · -- …and none of them touches the support: the last sweep found nothing to move
    intro x hx
    exact touches_false (hclosed x (mem_spanSkipped_reverse.1 hx))
  · -- the consumed span gained exactly `g`
    show spanGates (Win.span ⟨sup, spanMembers revSpan.reverse, revSpan⟩) = w.consumed ++ [g]
    simp only [Win.span, spanGates_reverse, hco.gates, spanGates_cons, List.reverse_cons]
    simp [Win.consumed, Win.span]

theorem tryWindow_correct {n m : Nat} {cfg : SuperOptConfig} {tbl : SynthTable} :
    ∀ (rest : List Gate) (fm : Option FlatMat) (w : Win) (cnt : Nat)
      (repl sk tail : List Gate) (k : Nat), WinOk n m w →
      (∀ g ∈ rest, g.Wf) → tryWindow cfg tbl n fm w cnt rest = some (repl, sk, tail, k) →
      Equivalent n m (repl ++ sk ++ tail) (w.consumed ++ rest) ∧
        (∀ g ∈ repl, g.Wf) ∧ (∀ g ∈ sk, g.Wf) ∧ (∀ g ∈ tail, g.Wf) := by
  intro rest
  induction rest with
  | nil => intro fm w cnt repl sk tail k _ _ h; rw [tryWindow] at h; exact absurd h (by simp)
  | cons g rest ih =>
      intro fm w cnt repl sk tail k hok hwfr h
      rw [tryWindow] at h
      split at h
      · -- the gate touches the window: grow it
        split at h
        · exact absurd h (by simp)
        · rename_i w' hgrow
          obtain ⟨hok', hcons⟩ := growWindow_spec hok hgrow
          dsimp only at h
          split at h
          · -- a rewrite was found; the tail is what is left of `rest`
            rename_i repl₀ hsynth
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hr, hs, ht, -⟩ := h
            subst hr; subst hs; subst ht
            obtain ⟨heq, hwfrepl, -, -⟩ :=
              trySynth_correct (m := m) hok'.nodup hok'.range hok'.sub hok'.wf
                (trySynthFiltered_eq hsynth)
            refine ⟨?_, hwfrepl, hok'.wfsk, fun x hx => hwfr x (by simp [hx])⟩
            have e1 : Equivalent n m (repl₀ ++ w'.skipped) (w'.members ++ w'.skipped) :=
              Equivalent.append_right w'.skipped heq
            have e2 : Equivalent n m (repl₀ ++ w'.skipped) (w.consumed ++ [g]) :=
              e1.trans (hcons ▸ hok'.equiv)
            have := Equivalent.append_right (n := n) (m := m) rest e2
            simpa using this
          · -- keep scanning
            obtain ⟨heq, h1, h2, h3⟩ :=
              ih _ w' _ repl sk tail k hok' (fun x hx => hwfr x (by simp [hx])) h
            refine ⟨?_, h1, h2, h3⟩
            rw [hcons] at heq
            simpa using heq
      · -- the gate misses the window: skip it
        rename_i htouch
        have hmiss : ∀ q ∈ g.qubitsOf, q ∉ w.support := touches_false (by simpa using htouch)
        have hspan : (Win.mk w.support w.members ((g, false) :: w.revSpan)).span
            = w.span ++ [(g, false)] := by simp [Win.span]
        have hsk : (Win.mk w.support w.members ((g, false) :: w.revSpan)).skipped
            = w.skipped ++ [g] := by simp [Win.skipped, hspan]
        have hok' : WinOk n m ⟨w.support, w.members, (g, false) :: w.revSpan⟩ := by
          refine ⟨hok.nodup, hok.range, ?_, hok.sub, hok.wf, hok.unit, ?_, ?_⟩
          · rw [hspan]; simpa using hok.memEq
          · intro x hx
            rw [hsk] at hx
            rcases List.mem_append.1 hx with hx' | hx'
            · exact hok.wfsk x hx'
            · rw [List.mem_singleton.1 hx']; exact hwfr g (by simp)
          · intro x hx
            rw [hsk] at hx
            rcases List.mem_append.1 hx with hx' | hx'
            · exact hok.disj x hx'
            · rw [List.mem_singleton.1 hx']; exact hmiss
        obtain ⟨heq, h1, h2, h3⟩ :=
          ih _ ⟨w.support, w.members, (g, false) :: w.revSpan⟩ _ repl sk tail k hok'
            (fun x hx => hwfr x (by simp [hx])) h
        refine ⟨?_, h1, h2, h3⟩
        have hcons : (Win.mk w.support w.members ((g, false) :: w.revSpan)).consumed
            = w.consumed ++ [g] := by simp [Win.consumed, hspan]
        rw [hcons] at heq
        simpa using heq

/-! ## The pass -/

theorem sweep_correct {n m : Nat} {cfg : SuperOptConfig} {tbl : SynthTable}
    (arr : Array Gate) (tracks : Array (Array Nat)) :
    ∀ (fuel at_ : Nat) (gs : List Gate), (∀ g ∈ gs, g.Wf) →
      Equivalent n m (sweepOnce cfg tbl n arr tracks fuel at_ gs) gs ∧
        (∀ g ∈ sweepOnce cfg tbl n arr tracks fuel at_ gs, g.Wf) := by
  intro fuel
  induction fuel with
  | zero => intro at_ gs hwf; exact ⟨Equivalent.refl n m gs, hwf⟩
  | succ fuel ih =>
      intro at_ gs hwf
      cases gs with
      | nil => exact ⟨Equivalent.refl n m [], by simp [sweepOnce]⟩
      | cons g rest =>
          have keep : ∀ k : Nat,
              Equivalent n m (g :: sweepOnce cfg tbl n arr tracks fuel k rest) (g :: rest) ∧
              (∀ x ∈ g :: sweepOnce cfg tbl n arr tracks fuel k rest, x.Wf) := by
            intro k
            obtain ⟨heq, hwf'⟩ := ih k rest (fun x hx => hwf x (by simp [hx]))
            refine ⟨by simpa using Equivalent.append_left [g] heq, ?_⟩
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact hwf x (by simp)
            · exact hwf' x hx
          rw [sweepOnce]
          split
          · rename_i hanchor
            simp only [canAnchor, Bool.and_eq_true, decide_eq_true_eq,
              List.all_eq_true] at hanchor
            obtain ⟨⟨⟨⟨hwin, -⟩, hrangeg⟩, hwfg⟩, -⟩ := hanchor
            split
            · rename_i repl sk tail consumed hw
              -- the window's own invariant, at the anchor
              have hok : WinOk n m (Win.start g) := by
                refine ⟨qubitsOf_nodup hwfg, hrangeg, rfl, ?_, ?_, ?_, by simp, by simp⟩
                · intro x hx q hq
                  rw [List.mem_singleton.1 hx] at hq
                  exact hq
                · intro x hx; rw [List.mem_singleton.1 hx]; exact hwfg
                · intro x hx
                  rw [List.mem_singleton.1 hx]
                  exact isWindowGate_isUnitary hwin
              obtain ⟨heq, hrepl, hsk, htail⟩ :=
                tryWindow_correct rest _ (Win.start g) 0 repl sk tail consumed hok
                  (fun x hx => hwf x (by simp [hx])) hw
              obtain ⟨heqt, hwft⟩ := ih (at_ + 1 + consumed) tail htail
              refine ⟨?_, ?_⟩
              · -- rewrite here, then whatever the rest of the sweepOnce does
                have hcont : Equivalent n m
                    (repl ++ sk ++ sweepOnce cfg tbl n arr tracks fuel
                      (at_ + 1 + consumed) tail)
                    (repl ++ sk ++ tail) := by
                  have := Equivalent.append_left (n := n) (m := m) sk heqt
                  simpa using Equivalent.append_left (n := n) (m := m) repl this
                exact hcont.trans (by simpa using heq)
              · intro x hx
                rcases List.mem_append.1 hx with hx | hx
                · rcases List.mem_append.1 hx with hx | hx
                  · exact hrepl x hx
                  · exact hsk x hx
                · exact hwft x hx
            · exact keep _
          · exact keep _

/-- **Superoptimization preserves meaning.** -/
theorem superOptGates_correct {n m : Nat} (cfg : SuperOptConfig) (tbl : SynthTable)
    (gs : List Gate) (hwf : ∀ g ∈ gs, g.Wf) :
    Equivalent n m (superOptGates cfg tbl n gs) gs :=
  (sweep_correct (m := m) gs.toArray (buildTracks n gs.toArray) gs.length 0 gs hwf).1

theorem superOptGates_wf {n : Nat} (cfg : SuperOptConfig) (tbl : SynthTable) (gs : List Gate)
    (hwf : ∀ g ∈ gs, g.Wf) : ∀ g ∈ superOptGates cfg tbl n gs, g.Wf :=
  (sweep_correct (n := n) (m := 0) gs.toArray (buildTracks n gs.toArray) gs.length 0 gs hwf).2

/-! ## Operand ranges

`WinOk` carries what the equivalence argument needs; the range argument needs less — in
particular not `equiv` — so it gets its own invariant. The only gates superoptimization
invents are the table's answer for a window, and `trySynth_correct` already says those live
on the window's wires and are unitary. `canAnchor` and the scan's own check keep the window's
wires below `n`, and a unitary gate has no classical operand, so a replacement is in range
without any assumption about what the table contains. -/

/-! ## Operand ranges

`WinOk` carries what the equivalence argument needs; the range argument needs less, but it
needs the same closure reasoning — the ranges of the gates a closure absorbs are exactly what
`acceptWindow` vets — so it reuses `growWindow_spec` rather than re-deriving it, and carries
the skipped gates' ranges alongside. -/

theorem tryWindow_inRange {n m : Nat} {cfg : SuperOptConfig} {tbl : SynthTable} :
    ∀ (rest : List Gate) (fm : Option FlatMat) (w : Win) (cnt : Nat)
      (repl sk tail : List Gate) (k : Nat), WinOk n m w → (∀ g ∈ w.skipped, g.InRange n m) →
      (∀ g ∈ rest, g.Wf) → (∀ g ∈ rest, g.InRange n m) →
      tryWindow cfg tbl n fm w cnt rest = some (repl, sk, tail, k) →
      (∀ g ∈ repl, g.InRange n m) ∧ (∀ g ∈ sk, g.InRange n m) ∧
        (∀ g ∈ tail, g.InRange n m) := by
  intro rest
  induction rest with
  | nil =>
      intro fm w cnt repl sk tail k _ _ _ _ h
      rw [tryWindow] at h; exact absurd h (by simp)
  | cons g rest ih =>
      intro fm w cnt repl sk tail k hok hsk hwfr hin h
      have hgwf : g.Wf := hwfr g (by simp)
      rw [tryWindow] at h
      split at h
      · split at h
        · exact absurd h (by simp)
        · rename_i w' hgrow
          obtain ⟨hok', hcons⟩ := growWindow_spec (m := m) hok hgrow
          -- the skipped gates of the grown window were skipped before
          have hsk' : ∀ x ∈ w'.skipped, x.InRange n m := by
            intro x hx
            rw [growWindow] at hgrow
            rcases hclose : closeSpan (w.revSpan.length + 2) (widen w.support g.qubitsOf)
                ((g, true) :: w.revSpan) with _ | ⟨sup, revSpan⟩
            · rw [hclose] at hgrow; exact absurd hgrow (by simp)
            rw [hclose] at hgrow
            simp only [Option.bind_some] at hgrow
            obtain ⟨rfl, -⟩ := acceptWindow_spec hgrow
            obtain ⟨hco, -⟩ := closeSpan_spec _ _ _ hclose
            have hx' := hco.skipped x (mem_spanSkipped_reverse.1 hx)
            simp only [spanSkipped_cons_true] at hx'
            exact hsk x (mem_spanSkipped_reverse.2 hx')
          dsimp only at h
          split at h
          · rename_i repl₀ hsynth
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hr, hs, ht, -⟩ := h
            subst hr; subst hs; subst ht
            obtain ⟨-, -, hsub', hu'⟩ :=
              trySynth_correct (n := n) (m := m) hok'.nodup hok'.range hok'.sub hok'.wf
                (trySynthFiltered_eq hsynth)
            refine ⟨fun x hx => ⟨fun q hq => hok'.range q (hsub' x hx q hq), fun b hb => ?_⟩,
              hsk', fun x hx => hin x (by simp [hx])⟩
            rw [Gate.cbitsOf_eq_nil_of_isUnitary (hu' x hx)] at hb
            exact absurd hb (by simp)
          · exact ih _ w' _ repl sk tail k hok' hsk' (fun x hx => hwfr x (by simp [hx]))
              (fun x hx => hin x (by simp [hx])) h
      · rename_i htouch
        have hmiss : ∀ q ∈ g.qubitsOf, q ∉ w.support := touches_false (by simpa using htouch)
        have hspan : (Win.mk w.support w.members ((g, false) :: w.revSpan)).skipped
            = w.skipped ++ [g] := by simp [Win.skipped, Win.span]
        have hok' : WinOk n m ⟨w.support, w.members, (g, false) :: w.revSpan⟩ := by
          refine ⟨hok.nodup, hok.range, ?_, hok.sub, hok.wf, hok.unit, ?_, ?_⟩
          · simp only [Win.span, List.reverse_cons, spanMembers_append, spanMembers_cons_false,
              spanMembers_nil, List.append_nil]
            exact hok.memEq
          · intro x hx
            rw [hspan] at hx
            rcases List.mem_append.1 hx with hx' | hx'
            · exact hok.wfsk x hx'
            · rw [List.mem_singleton.1 hx']; exact hgwf
          · intro x hx
            rw [hspan] at hx
            rcases List.mem_append.1 hx with hx' | hx'
            · exact hok.disj x hx'
            · rw [List.mem_singleton.1 hx']; exact hmiss
        refine ih _ ⟨w.support, w.members, (g, false) :: w.revSpan⟩ _ repl sk tail k hok' ?_
          (fun x hx => hwfr x (by simp [hx])) (fun x hx => hin x (by simp [hx])) h
        intro x hx
        rw [hspan] at hx
        rcases List.mem_append.1 hx with hx' | hx'
        · exact hsk x hx'
        · rw [List.mem_singleton.1 hx']; exact hin g (by simp)

theorem sweep_inRange {n m : Nat} {cfg : SuperOptConfig} {tbl : SynthTable}
    (arr : Array Gate) (tracks : Array (Array Nat)) :
    ∀ (fuel at_ : Nat) (gs : List Gate), (∀ g ∈ gs, g.Wf) → (∀ g ∈ gs, g.InRange n m) →
      ∀ g ∈ sweepOnce cfg tbl n arr tracks fuel at_ gs, g.InRange n m := by
  intro fuel
  induction fuel with
  | zero => intro at_ gs _ h; exact h
  | succ fuel ih =>
      intro at_ gs hwf hin
      cases gs with
      | nil => simp [sweepOnce]
      | cons g rest =>
          have keep : ∀ j : Nat, ∀ x ∈ g :: sweepOnce cfg tbl n arr tracks fuel j rest,
              x.InRange n m := by
            intro j x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact hin x (by simp)
            · exact ih j rest (fun y hy => hwf y (by simp [hy]))
                (fun y hy => hin y (by simp [hy])) x hx
          rw [sweepOnce]
          split
          · rename_i hanchor
            simp only [canAnchor, Bool.and_eq_true, decide_eq_true_eq,
              List.all_eq_true] at hanchor
            obtain ⟨⟨⟨⟨hwin, -⟩, hrangeg⟩, hwfg⟩, -⟩ := hanchor
            split
            · rename_i repl sk tail consumed hw
              have hok : WinOk n m (Win.start g) := by
                refine ⟨qubitsOf_nodup hwfg, hrangeg, rfl, ?_, ?_, ?_, by simp, by simp⟩
                · intro x hx q hq
                  rw [List.mem_singleton.1 hx] at hq
                  exact hq
                · intro x hx; rw [List.mem_singleton.1 hx]; exact hwfg
                · intro x hx
                  rw [List.mem_singleton.1 hx]
                  exact isWindowGate_isUnitary hwin
              obtain ⟨h1, h2, h3⟩ :=
                tryWindow_inRange rest _ (Win.start g) 0 repl sk tail consumed hok (by simp)
                  (fun x hx => hwf x (by simp [hx])) (fun x hx => hin x (by simp [hx])) hw
              intro x hx
              rcases List.mem_append.1 hx with hx | hx
              · rcases List.mem_append.1 hx with hx | hx
                · exact h1 x hx
                · exact h2 x hx
              · have htailwf := (tryWindow_correct (m := m) rest _ (Win.start g) 0 repl sk tail
                  consumed hok (fun y hy => hwf y (by simp [hy])) hw).2.2.2
                exact ih (at_ + 1 + consumed) tail htailwf h3 x hx
            · exact keep _
          · exact keep _

/-- **Superoptimization keeps every operand in range.** -/
theorem superOptGates_inRange {n m : Nat} (cfg : SuperOptConfig) (tbl : SynthTable)
    (gs : List Gate) (hwf : ∀ g ∈ gs, g.Wf) (hin : ∀ g ∈ gs, g.InRange n m) :
    ∀ g ∈ superOptGates cfg tbl n gs, g.InRange n m :=
  sweep_inRange (n := n) (m := m) (cfg := cfg) (tbl := tbl)
    gs.toArray (buildTracks n gs.toArray) gs.length 0 gs hwf hin

/-- `SuperOpt`, as a `Pass`: the rewrite is decided by exact matrix comparison, so the proof
obligation is discharged by the check the pass already runs. -/
def SuperOpt (cfg : SuperOptConfig) (tbl : SynthTable) : Pass where
  name := "Superoptimization"
  run := superOpt cfg tbl
  numQubits_run _ := rfl
  numCbits_run _ := rfl
  wf_run c hc := superOptGates_wf cfg tbl c.gates hc
  wellFormed_run c hwf hc := superOptGates_inRange cfg tbl c.gates hwf hc
  flagsOk_run c _ := Circuit.flagsOk_withGates _ _
  correct c hc := superOptGates_correct cfg tbl c.gates hc

@[simp] theorem SuperOpt_run (cfg : SuperOptConfig) (tbl : SynthTable) (c : Circuit) :
    (SuperOpt cfg tbl).run c = superOpt cfg tbl c := rfl

end TzapLean
