import TzapLean.Equivalence

/-!
# Applying a Set of Rewrites at Once

Rust's superoptimizer keeps every live window open as it scans, and selects rewrites greedily
over the *whole* circuit: the first window offered with a strictly shorter replacement claims
its gates, anything overlapping a claimed gate is refused afterwards, and one final pass
splices every selected replacement in at its window's anchor (`RewriteSet::apply`). A window
is a subsequence, not a run, so the gates it claims are scattered — the ones in between belong
to other windows, or to nothing, and stay where they are.

That is a different shape of theorem from "one rewrite, on a prefix of what is left", which is
what a scan that commits its first hit and moves on needs. This file is that theorem.

The trick is to stop talking about indices. A selection is a **tagging**: every gate carries
the rewrite that claims it, or nothing. `applyAll` then emits a rewrite's replacement at the
first gate it claims, drops the others, and copies untagged gates through — a plain structural
recursion, which is what makes `applyAll_correct` a list induction instead of a permutation
argument over positions.

Two conditions make it sound, and both are checked rather than assumed (see
`TzapLean/SuperOptProof.lean`):

* `OnSupp` — a claimed gate lives on its rewrite's wires, and is unitary;
* `Sep` — a gate that some *later* gate's rewrite does not claim misses that rewrite's wires.

`Sep` is what lets a rewrite's scattered gates be gathered at its first one: everything they
cross on the way is disjoint from them. Both survive taking sublists, which is exactly what
the recursion does to the list.
-/

namespace TzapLean

/-- Which rewrite claims a gate, if any. -/
abbrev Claim := Option Nat

/-- A gate together with the rewrite that claims it. -/
abbrev Tagged := Gate × Claim

/-- The gates, forgetting the tags. -/
def untag (xs : List Tagged) : List Gate := xs.map (·.1)

/-- The gates rewrite `w` claims, in order. -/
def claimedBy (w : Nat) (xs : List Tagged) : List Gate :=
  xs.filterMap fun p => if p.2 = some w then some p.1 else none

/-- What is left of `xs` once rewrite `w`'s gates are taken out. -/
def unclaimed (w : Nat) (xs : List Tagged) : List Tagged :=
  xs.filter fun p => p.2 ≠ some w

@[simp] theorem untag_nil : untag [] = [] := rfl
@[simp] theorem untag_cons (p : Tagged) (xs : List Tagged) :
    untag (p :: xs) = p.1 :: untag xs := rfl
@[simp] theorem claimedBy_nil (w : Nat) : claimedBy w [] = [] := rfl
@[simp] theorem unclaimed_nil (w : Nat) : unclaimed w [] = [] := rfl

theorem claimedBy_cons_self (w : Nat) (g : Gate) (xs : List Tagged) :
    claimedBy w ((g, some w) :: xs) = g :: claimedBy w xs := by
  simp [claimedBy]

theorem claimedBy_cons_other {w : Nat} {t : Claim} (g : Gate) (xs : List Tagged)
    (h : t ≠ some w) : claimedBy w ((g, t) :: xs) = claimedBy w xs := by
  simp [claimedBy, h]

theorem unclaimed_cons_self (w : Nat) (g : Gate) (xs : List Tagged) :
    unclaimed w ((g, some w) :: xs) = unclaimed w xs := by
  simp [unclaimed]

theorem unclaimed_cons_other {w : Nat} {t : Claim} (g : Gate) (xs : List Tagged)
    (h : t ≠ some w) : unclaimed w ((g, t) :: xs) = (g, t) :: unclaimed w xs := by
  simp [unclaimed, h]

theorem unclaimed_length_le (w : Nat) (xs : List Tagged) : (unclaimed w xs).length ≤ xs.length :=
  List.length_filter_le _ _

theorem mem_unclaimed {w : Nat} {xs : List Tagged} {p : Tagged} (h : p ∈ unclaimed w xs) :
    p ∈ xs := List.mem_of_mem_filter h

theorem mem_claimedBy {w : Nat} {xs : List Tagged} {g : Gate} (h : g ∈ claimedBy w xs) :
    (g, some w) ∈ xs := by
  rcases List.mem_filterMap.1 h with ⟨⟨y, t⟩, hy, hyg⟩
  by_cases ht : t = some w
  · subst ht
    simp only [if_true, Option.some.injEq, decide_true] at hyg
    exact hyg ▸ hy
  · simp [ht] at hyg

/-! ## The two side conditions -/

/-- A claimed gate lives on its rewrite's wires, and is unitary. -/
def OnSupp (supp : Nat → List Qubit) (xs : List Tagged) : Prop :=
  ∀ p ∈ xs, ∀ w, p.2 = some w → (∀ q ∈ p.1.qubitsOf, q ∈ supp w) ∧ p.1.isUnitary = true

/-- **The separation condition, for one rewrite.** A gate that rewrite `w` does not claim, but
which one of `w`'s gates follows, misses `w`'s wires.

Note where this is used: always on the *tail after a `w`-claim*, so what it says is "everything
between two of `w`'s gates". A gate before `w`'s first claim is never constrained — it is never
crossed, because `w`'s gates only ever move left as far as the first of them. -/
def SepOne (S : List Qubit) (w : Nat) : List Tagged → Prop
  | [] => True
  | p :: rest =>
      (p.2 ≠ some w → (∃ r ∈ rest, r.2 = some w) → ∀ q ∈ p.1.qubitsOf, q ∉ S) ∧
      SepOne S w rest

/-- **The separation condition.** After each claimed gate, `SepOne` for the rewrite that
claimed it. -/
def Sep (supp : Nat → List Qubit) : List Tagged → Prop
  | [] => True
  | p :: rest => (∀ w, p.2 = some w → SepOne (supp w) w rest) ∧ Sep supp rest

theorem Sep.tail {supp : Nat → List Qubit} {p : Tagged} {rest : List Tagged}
    (h : Sep supp (p :: rest)) : Sep supp rest := h.2

theorem OnSupp.tail {supp : Nat → List Qubit} {p : Tagged} {rest : List Tagged}
    (h : OnSupp supp (p :: rest)) : OnSupp supp rest :=
  fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem OnSupp.unclaimed {supp : Nat → List Qubit} {xs : List Tagged} (h : OnSupp supp xs)
    (w : Nat) : OnSupp supp (TzapLean.unclaimed w xs) :=
  fun p hp => h p (mem_unclaimed hp)

/-- Both conditions only ever say less about a shorter list, which is what lets the recursion
drop gates and keep them. -/
theorem SepOne.filter {S : List Qubit} {w : Nat} (q : Tagged → Bool) :
    ∀ {xs : List Tagged}, SepOne S w xs → SepOne S w (xs.filter q)
  | [], _ => trivial
  | p :: rest, h => by
      by_cases hq : q p
      · rw [List.filter_cons_of_pos hq]
        refine ⟨fun hne hex => h.1 hne ?_, SepOne.filter q h.2⟩
        obtain ⟨r, hr, hrw⟩ := hex
        exact ⟨r, List.mem_of_mem_filter hr, hrw⟩
      · rw [List.filter_cons_of_neg (by simpa using hq)]
        exact SepOne.filter q h.2

theorem Sep.filter {supp : Nat → List Qubit} (q : Tagged → Bool) :
    ∀ {xs : List Tagged}, Sep supp xs → Sep supp (xs.filter q)
  | [], _ => trivial
  | p :: rest, h => by
      by_cases hq : q p
      · rw [List.filter_cons_of_pos hq]
        exact ⟨fun w hw => SepOne.filter q (h.1 w hw), Sep.filter q h.2⟩
      · rw [List.filter_cons_of_neg (by simpa using hq)]
        exact Sep.filter q h.2

theorem Sep.unclaimed {supp : Nat → List Qubit} {xs : List Tagged} (h : Sep supp xs) (w : Nat) :
    Sep supp (TzapLean.unclaimed w xs) := Sep.filter _ h

/-- Two gates on disjoint operand lists have disjoint supports. -/
theorem disjoint_of_notMem {g g' : Gate} (h : ∀ q ∈ g.qubitsOf, q ∉ g'.qubitsOf) :
    Wires.Disjoint g.support g'.support := by
  intro q hq
  rcases hq' : g'.support q with _ | _
  · rfl
  · exact absurd ((Gate.support_iff g' q).1 (by simp [hq'])) (h q ((Gate.support_iff g q).1 hq))

/-! ## Gathering one rewrite's gates -/

/-- **A rewrite's gates may be gathered at the first of them.** Everything they cross on the
way is a gate the rewrite does not claim but which a claimed gate follows — and `Sep` says
those miss the rewrite's wires. -/
theorem gather_equiv {n m : Nat} (supp : Nat → List Qubit) (w : Nat) :
    ∀ xs : List Tagged, SepOne (supp w) w xs → OnSupp supp xs →
      Equivalent n m (claimedBy w xs ++ untag (unclaimed w xs)) (untag xs) := by
  intro xs
  induction xs with
  | nil => intro _ _; exact Equivalent.refl _ _ _
  | cons p rest ih =>
      intro hsep hon
      obtain ⟨g, t⟩ := p
      have ihr := ih hsep.2 hon.tail
      by_cases ht : t = some w
      · subst ht
        rw [claimedBy_cons_self, unclaimed_cons_self, untag_cons, List.cons_append]
        exact Equivalent.append_left [g] ihr
      · rw [claimedBy_cons_other _ _ ht, unclaimed_cons_other _ _ ht, untag_cons, untag_cons]
        have hcomm : Equivalent n m (claimedBy w rest ++ [g]) ([g] ++ claimedBy w rest) := by
          have hmem : ∀ x ∈ claimedBy w rest, (x, some w) ∈ rest :=
            fun x hx => mem_claimedBy hx
          have honm : ∀ x ∈ claimedBy w rest,
              (∀ q ∈ x.qubitsOf, q ∈ supp w) ∧ x.isUnitary = true := fun x hx =>
            hon.tail _ (hmem x hx) w rfl
          refine Equivalent.append_comm _ _ (fun x hx => (honm x hx).2) (fun x hx y hy => ?_)
          rw [List.mem_singleton.1 hy]
          refine disjoint_of_notMem ?_
          intro q hq hq'
          exact hsep.1 ht ⟨(x, some w), hmem x hx, rfl⟩ q hq' ((honm x hx).1 q hq)
        have step₁ : Equivalent n m (claimedBy w rest ++ g :: untag (unclaimed w rest))
            (g :: (claimedBy w rest ++ untag (unclaimed w rest))) := by
          have h := Equivalent.append_right (n := n) (m := m) (untag (unclaimed w rest)) hcomm
          simpa using h
        exact step₁.trans (Equivalent.append_left [g] ihr)

/-! ## Applying every rewrite at once -/

@[simp] theorem claimedBy_unclaimed_self (w : Nat) (xs : List Tagged) :
    claimedBy w (unclaimed w xs) = [] := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨g, t⟩ := p
      by_cases ht : t = some w
      · rw [ht, unclaimed_cons_self]; exact ih
      · rw [unclaimed_cons_other _ _ ht, claimedBy_cons_other _ _ ht]; exact ih

theorem claimedBy_unclaimed_other {v w : Nat} (h : v ≠ w) (xs : List Tagged) :
    claimedBy v (unclaimed w xs) = claimedBy v xs := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨g, t⟩ := p
      by_cases ht : t = some w
      · rw [ht, unclaimed_cons_self, ih,
          claimedBy_cons_other _ _ (by simp [Ne.symm h])]
      · rw [unclaimed_cons_other _ _ ht]
        by_cases htv : t = some v
        · rw [htv, claimedBy_cons_self, claimedBy_cons_self, ih]
        · rw [claimedBy_cons_other _ _ htv, claimedBy_cons_other _ _ htv, ih]

/-- Splice every rewrite in: its replacement is emitted at the first gate it claims, the
gates it claims elsewhere are dropped, and everything else is copied through. This is Rust's
`RewriteSet::apply`, with the tagging standing in for its `claimed`/`anchored` arrays. -/
def applyAll (repl : Nat → List Gate) : List Tagged → List Gate
  | [] => []
  | (g, none) :: rest => g :: applyAll repl rest
  | (_, some w) :: rest => repl w ++ applyAll repl (unclaimed w rest)
termination_by xs => xs.length
decreasing_by
  · simp
  · exact Nat.lt_succ_of_le (unclaimed_length_le w rest)

/-- Every gate of the result is either one of the input's or one a replacement supplied. -/
theorem mem_applyAll (repl : Nat → List Gate) :
    ∀ (xs : List Tagged) (g : Gate), g ∈ applyAll repl xs →
      g ∈ untag xs ∨ ∃ w, g ∈ repl w := by
  intro xs
  induction xs using applyAll.induct with
  | case1 => intro g hg; rw [applyAll] at hg; exact absurd hg (by simp)
  | case2 x rest ih =>
      intro g hg
      rw [applyAll] at hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact Or.inl (by simp)
      · rcases ih g hg with h | h
        · exact Or.inl (by simp only [untag_cons, List.mem_cons]; exact Or.inr h)
        · exact Or.inr h
  | case3 x w rest ih =>
      intro g hg
      rw [applyAll] at hg
      rcases List.mem_append.1 hg with h | h
      · exact Or.inr ⟨w, h⟩
      · rcases ih g h with h' | h'
        · refine Or.inl ?_
          simp only [untag, List.mem_map] at h' ⊢
          obtain ⟨q, hq, rfl⟩ := h'
          exact ⟨q, List.mem_cons_of_mem _ (mem_unclaimed hq), rfl⟩
        · exact Or.inr h'

/-- **A set of rewrites, spliced in at once, preserves the circuit.**

Under the two conditions the checker establishes — every claimed gate on its rewrite's wires
and unitary, and every gate a later rewrite does not claim missing that rewrite's wires — the
whole splice is meaning-preserving, however the claimed gates interleave. -/
theorem applyAll_correct {n m : Nat} (supp : Nat → List Qubit) (repl : Nat → List Gate) :
    ∀ xs : List Tagged, Sep supp xs → OnSupp supp xs →
      (∀ w, (∃ p ∈ xs, p.2 = some w) → Equivalent n m (repl w) (claimedBy w xs)) →
      Equivalent n m (applyAll repl xs) (untag xs) := by
  intro xs
  induction xs using applyAll.induct with
  | case1 => intro _ _ _; rw [applyAll]; exact Equivalent.refl _ _ _
  | case2 g rest ih =>
      intro hsep hon hrepl
      rw [applyAll, untag_cons]
      refine Equivalent.append_left [g] (ih hsep.2 hon.tail fun w hw => ?_)
      have hx := hrepl w ⟨_, List.mem_cons_of_mem _ hw.choose_spec.1, hw.choose_spec.2⟩
      rwa [claimedBy_cons_other _ _ (by simp)] at hx
  | case3 g w rest ih =>
      intro hsep hon hrepl
      have hgw : Equivalent n m (repl w) (g :: claimedBy w rest) := by
        have hx := hrepl w ⟨(g, some w), by simp, rfl⟩
        rwa [claimedBy_cons_self] at hx
      have ihr := ih ((hsep.2).unclaimed w) (hon.tail.unclaimed w) (fun v hv => ?_)
      · rw [applyAll, untag_cons]
        have step₁ : Equivalent n m (repl w ++ applyAll repl (unclaimed w rest))
            ((g :: claimedBy w rest) ++ applyAll repl (unclaimed w rest)) :=
          Equivalent.append_right _ hgw
        have step₂ : Equivalent n m ((g :: claimedBy w rest) ++ applyAll repl (unclaimed w rest))
            ((g :: claimedBy w rest) ++ untag (unclaimed w rest)) :=
          Equivalent.append_left _ ihr
        have step₃ : Equivalent n m (g :: (claimedBy w rest ++ untag (unclaimed w rest)))
            (g :: untag rest) :=
          Equivalent.append_left [g] (gather_equiv supp w rest (hsep.1 w rfl) hon.tail)
        exact step₁.trans (step₂.trans (by simpa using step₃))
      · -- a rewrite still present in what is left is not `w`, and claims the same gates
        obtain ⟨q, hq, hqv⟩ := hv
        have hvw : v ≠ w := by
          rintro rfl
          have := (List.of_mem_filter hq)
          simp only [ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not] at this
          exact this hqv
        rw [claimedBy_unclaimed_other hvw]
        have hx := hrepl v ⟨q, List.mem_cons_of_mem _ (mem_unclaimed hq), hqv⟩
        rwa [claimedBy_cons_other _ _ (by simp [Ne.symm hvw])] at hx

/-- Any property of gates that the input and every replacement have, the result has: it is
built from nothing else. Both halves of the structural invariant go through this. -/
theorem applyAll_pred {P : Gate → Prop} (repl : Nat → List Gate) (xs : List Tagged)
    (hin : ∀ g ∈ untag xs, P g) (hr : ∀ w, ∀ g ∈ repl w, P g) :
    ∀ g ∈ applyAll repl xs, P g := by
  intro g hg
  rcases mem_applyAll repl xs g hg with h | ⟨w, h⟩
  · exact hin g h
  · exact hr w g h

/-! ## Deciding the two conditions

The scan that proposes a tagging is unverified, so both conditions are *checked* before the
splice is taken — this is the same certifying arrangement the window search already used, one
level up. Nothing about how a proposal was found is trusted; only that it passes these.

`sepOneB` is one right-to-left pass, carrying whether the rewrite claims anything further
right, so the whole check is linear per rewrite rather than quadratic. `sepB` runs it once per
rewrite rather than once per claimed gate: a later claim's tail is a suffix of the first
claim's, and `SepOne` only ever says less about a suffix. -/

/-- `SepOne`, decided: `.1` is the verdict, `.2` whether `w` claims anything here. -/
def sepOneAux (S : List Qubit) (w : Nat) : List Tagged → Bool × Bool
  | [] => (true, false)
  | (g, t) :: rest =>
      let r := sepOneAux S w rest
      if t = some w then (r.1, true)
      else (r.1 && (!r.2 || g.qubitsOf.all fun q => !S.contains q), r.2)

def sepOneB (S : List Qubit) (w : Nat) (xs : List Tagged) : Bool := (sepOneAux S w xs).1

theorem sepOneAux_seen (S : List Qubit) (w : Nat) :
    ∀ xs : List Tagged, (sepOneAux S w xs).2 = true ↔ ∃ r ∈ xs, r.2 = some w := by
  intro xs
  induction xs with
  | nil => simp [sepOneAux]
  | cons p rest ih =>
      obtain ⟨g, t⟩ := p
      by_cases ht : t = some w
      · simp [sepOneAux, ht]
      · simp only [sepOneAux, if_neg ht]
        rw [ih]
        constructor
        · rintro ⟨r, hr, hrw⟩; exact ⟨r, List.mem_cons_of_mem _ hr, hrw⟩
        · rintro ⟨r, hr, hrw⟩
          rcases List.mem_cons.1 hr with rfl | hr
          · exact absurd hrw ht
          · exact ⟨r, hr, hrw⟩

theorem sepOneB_sound (S : List Qubit) (w : Nat) :
    ∀ xs : List Tagged, sepOneB S w xs = true → SepOne S w xs := by
  intro xs
  induction xs with
  | nil => intro _; trivial
  | cons p rest ih =>
      obtain ⟨g, t⟩ := p
      intro h
      by_cases ht : t = some w
      · refine ⟨fun hne _ => absurd ht hne, ih ?_⟩
        simpa [sepOneB, sepOneAux, ht] using h
      · simp only [sepOneB, sepOneAux, if_neg ht, Bool.and_eq_true] at h
        refine ⟨fun _ hex q hq hmem => ?_, ih (by simpa [sepOneB] using h.1)⟩
        have hseen : (sepOneAux S w rest).2 = true := (sepOneAux_seen S w rest).2 hex
        simp only [hseen, Bool.not_true, Bool.false_or, List.all_eq_true] at h
        have hnc := h.2 q hq
        simp only [Bool.not_eq_true'] at hnc
        rw [List.contains_eq_mem, decide_eq_false_iff_not] at hnc
        exact hnc hmem

/-- `Sep`, decided — `started` records the rewrites already checked. -/
def sepB (supp : Nat → List Qubit) : List Nat → List Tagged → Bool
  | _, [] => true
  | started, (_, none) :: rest => sepB supp started rest
  | started, (_, some w) :: rest =>
      (started.contains w || sepOneB (supp w) w rest) && sepB supp (w :: started) rest

theorem sepB_sound (supp : Nat → List Qubit) :
    ∀ (xs : List Tagged) (started : List Nat),
      (∀ w ∈ started, SepOne (supp w) w xs) → sepB supp started xs = true → Sep supp xs := by
  intro xs
  induction xs with
  | nil => intro _ _ _; trivial
  | cons p rest ih =>
      obtain ⟨g, t⟩ := p
      intro started hst h
      cases t with
      | none =>
          refine ⟨fun w hw => absurd hw (by simp), ?_⟩
          exact ih started (fun w hw => (hst w hw).2) (by simpa [sepB] using h)
      | some w =>
          simp only [sepB, Bool.and_eq_true, Bool.or_eq_true] at h
          have hw : SepOne (supp w) w rest := by
            rcases h.1 with hc | hs
            · exact (hst w (by simpa using hc)).2
            · exact sepOneB_sound _ _ _ hs
          refine ⟨fun v hv => ?_, ih (w :: started) (fun v hv => ?_) h.2⟩
          · exact (Option.some.injEq w v ▸ hv) ▸ hw
          · rcases List.mem_cons.1 hv with rfl | hv
            · exact hw
            · exact (hst v hv).2

/-- `OnSupp`, decided. -/
def onSuppB (supp : Nat → List Qubit) (xs : List Tagged) : Bool :=
  xs.all fun p =>
    match p.2 with
    | none => true
    | some w => p.1.qubitsOf.all (fun q => (supp w).contains q) && p.1.isUnitary

theorem onSuppB_sound {supp : Nat → List Qubit} {xs : List Tagged}
    (h : onSuppB supp xs = true) : OnSupp supp xs := by
  intro p hp w hw
  have := (List.all_eq_true.1 h) p hp
  rw [hw] at this
  simp only [Bool.and_eq_true, List.all_eq_true] at this
  exact ⟨fun q hq => List.mem_of_elem_eq_true (this.1 q hq), this.2⟩

end TzapLean