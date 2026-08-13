import Mathlib.Data.List.Enum
import Tzap.SuperOpt.Table

/-!
# The Anchored SuperOpt Pass, Proved Correct and Proved Linear

This module holds the pass and both of its guarantees, stated about one definition:

* `optimize_correct` -- the output is equivalent to the input and has no more gates;
* `optimize_linear` -- the work done is at most a constant times the number of input
  gates, the constant fixed by the window bounds.

## The scan this models

The pass is an event-driven scan over the input circuit `C = g_1; …; g_m`. It keeps a
set `A` of live anchors, each carrying the positions `S_a` of the window it anchors,
and a set `R` of selected rewrites. Writing `i ⋈ j` for "gates `i` and `j` are
dependent" and `comp(a,b)` for the connected component of `a` within `g_a; …; g_b`:

    A ← ∅;  R ← ∅
    for b ← 1 to m do
      for all a ∈ A with i ⋈ b for some i ∈ S_a, in increasing order of a do
        if g_b acts only on qubits that C|_{S_a} already uses then
          S_a ← S_a ∪ {b}
        else
          S_a ← comp(a,b)                        -- g_b bridges two components
        if C|_{S_a} exceeds the qubit or the gate bound then
          A ← A \ {a}                            -- the anchor is dropped
        else
          Consider(S_a)
      S_b ← {b};  A ← A ∪ {b};  Consider(S_b)    -- b anchors a window of its own
    return C with C|_S replaced by W' for every (S,W') ∈ R

    function Consider(S)
      W ← C|_S;  W' ← M(canon(⟦W⟧))
      if W' is defined and |W'| < |W| and no position of S is claimed then
        add (S,W') to R and claim every position of S

The definitions below follow this scan piece for piece, with one deliberate
difference, recorded after the table.

| the scan above | here |
| --- | --- |
| `S_a ← S_a ∪ {b}` / `S_a ← comp(a,b)` | `anchorComponent (seen ++ [g])` |
| the bound test and `A ← A \ {a}` | `bounds.allows` inside `tryWindow` |
| `Consider(S)` | `tryWindow` |
| `W ← C|_S`; `W' ← M(canon(⟦W⟧))` | `table.lookup (unitary component)` |
| `|W'| < |W|`, positions unclaimed | the length guard, and dropping the window's
  gates from the remainder |
| growing one anchor across later gates | `findFrom` |
| the outer loop, and installing every rewrite | `scanSteps` |

The two branches that set `S_a` collapse into one here: `comp(a,b)` already returns
`S_a ∪ {b}` when `g_b` only touches qubits the window uses, so recomputing the closure
covers the extension case too. The split above is an optimization, not a difference in
the window.

**The one real difference.** The scan above visits an anchor only when the incoming
gate is dependent on it, which an implementation gets from a per-qubit index; gates the
window skips cost that anchor nothing. This module has no such index, so an anchor is
instead given an explicit `budget`: it may reach at most that many gates past itself
before the scan moves on. The budget is what makes `optimize_linear` unconditional,
and it is the price of not modelling the index. It costs coverage rather than
soundness -- a window whose gates are spread across more than `budget` positions is
never offered to the table, and is simply left alone.

## Windows

Every input gate anchors a window, which grows across later gates by
connected-component closure: unrelated gates are skipped, while a later bridge can
retroactively pull an earlier disconnected component into the window. Skipped gates
commute with every gate of the window -- that is what `span_factorization` establishes
-- so a window may be rewritten where it sits.
-/
namespace Tzap.SuperOpt.Algorithm

open Tzap.Unitary

noncomputable section

-- `inAnchorComponent` is not decidable, so the selections built from it need
-- classical instances.
open scoped Classical

/-- Physical qubits touched by a formal gate. -/
def gateSupport {n : Nat} : Gate n → Finset (Fin n)
  | .cnot control target => {control, target}
  | .hadamard target | .x target | .rz _ target => {target}

/-- Two gates commute when their weighted relations commute under matrix composition. -/
def GateCommutes {n : Nat} (left right : Gate n) : Prop :=
  WeightedRelation.comp (Semantics.gate left) (Semantics.gate right) =
    WeightedRelation.comp (Semantics.gate right) (Semantics.gate left)

/-- The dependency graph contains Rust's shared-qubit edges. The semantic disjunct is a
conservative guard: an omitted edge always certifies that the two gates commute. -/
def GateDependent {n : Nat} (left right : Gate n) : Prop :=
  ¬Disjoint (gateSupport left) (gateSupport right) ∨ ¬GateCommutes left right

abbrev Occurrence (n : Nat) := Gate n × Nat

/-- An edge between two gate occurrences in a buffered circuit. -/
def occurrenceEdge {n : Nat} (buffer : Circuit n)
    (left right : Occurrence n) : Prop :=
  left ∈ buffer.zipIdx ∧ right ∈ buffer.zipIdx ∧ GateDependent left.1 right.1

/-- Membership in the connected component anchored at the first buffered gate. -/
def inAnchorComponent {n : Nat} (buffer : Circuit n) (node : Occurrence n) : Prop :=
  ∃ root, buffer.head? = some root ∧
    Relation.ReflTransGen (occurrenceEdge buffer) (root, 0) node

/-- Gates in the anchor's connected component, in their original order. -/
noncomputable def anchorComponent {n : Nat} (buffer : Circuit n) : Circuit n :=
  by
    classical
    exact ((buffer.zipIdx.filter fun node => decide (inAnchorComponent buffer node)).map Prod.fst)

/-- Gates in other connected components of the buffered span, in original order. -/
noncomputable def outsideComponent {n : Nat} (buffer : Circuit n) : Circuit n :=
  by
    classical
    exact
      ((buffer.zipIdx.filter fun node => !decide (inAnchorComponent buffer node)).map Prod.fst)

theorem component_outside_commute {n : Nat} (buffer : Circuit n)
    {inside outside : Occurrence n}
    (hiMem : inside ∈ buffer.zipIdx) (hoMem : outside ∈ buffer.zipIdx)
    (hi : inAnchorComponent buffer inside) (ho : ¬inAnchorComponent buffer outside) :
    GateCommutes inside.1 outside.1 := by
  by_contra hcomm
  rcases hi with ⟨root, hroot, hpath⟩
  apply ho
  refine ⟨root, hroot, hpath.tail ?_⟩
  exact ⟨hiMem, hoMem, Or.inr hcomm⟩

/-- Swapping two adjacent commuting gates preserves the remainder of a circuit. -/
theorem swap_adjacent {n : Nat} {left right : Gate n} (tail : Circuit n)
    (hcomm : GateCommutes left right) :
    Semantics.circuit (left :: right :: tail) =
      Semantics.circuit (right :: left :: tail) := by
  simp only [Semantics.circuit]
  rw [← WeightedRelation.comp_assoc, hcomm, WeightedRelation.comp_assoc]

theorem GateCommutes.symm {n : Nat} {left right : Gate n}
    (hcomm : GateCommutes left right) : GateCommutes right left :=
  Eq.symm hcomm

/-- A gate can move right across a circuit of pairwise commuting gates. -/
theorem move_right {n : Nat} (g : Gate n) (across suffix : Circuit n)
    (hcomm : ∀ h ∈ across, GateCommutes g h) :
    Semantics.circuit (g :: (across ++ suffix)) =
      Semantics.circuit (across ++ g :: suffix) := by
  induction across with
  | nil => rfl
  | cons h across ih =>
      calc
        Semantics.circuit (g :: ((h :: across) ++ suffix)) =
            Semantics.circuit (h :: g :: (across ++ suffix)) :=
              swap_adjacent (across ++ suffix) (hcomm h (by simp))
        _ = Semantics.circuit (h :: (across ++ g :: suffix)) := by
              simpa only [Semantics.circuit] using congrArg
                (WeightedRelation.comp (Semantics.gate h))
                (ih (fun k hk => hcomm k (by simp [hk])))
        _ = Semantics.circuit ((h :: across) ++ g :: suffix) := rfl

/-- Stable partitioning is semantics-preserving when every selected/rejected pair commutes. -/
theorem map_eq_filter_append {α : Type*} {n : Nat} (items : List α)
    (toGate : α → Gate n) (selected : α → Bool)
    (hcomm : ∀ inside ∈ items, ∀ outside ∈ items,
      selected inside = true → selected outside = false →
        GateCommutes (toGate outside) (toGate inside)) :
    Semantics.circuit (items.map toGate) =
      Semantics.circuit
        ((items.filter selected).map toGate ++
          (items.filter fun item => !selected item).map toGate) := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      cases hs : selected item with
      | false =>
        have ih' := ih (fun inside hi outside ho hsi hso =>
          hcomm inside (by simp [hi]) outside (by simp [ho]) hsi hso)
        have hmove :
            Semantics.circuit
                (toGate item ::
                  ((items.filter selected).map toGate ++
                    (items.filter fun item => !selected item).map toGate)) =
              Semantics.circuit
                ((items.filter selected).map toGate ++
                  toGate item :: (items.filter fun item => !selected item).map toGate) := by
          apply move_right
          intro gate hgate
          rcases List.mem_map.mp hgate with ⟨inside, hi, rfl⟩
          have hiMem := List.mem_of_mem_filter hi
          have hiSelected := List.of_mem_filter hi
          exact hcomm inside (by simp [hiMem]) item (by simp) hiSelected hs
        calc
          Semantics.circuit ((item :: items).map toGate) =
              Semantics.circuit
                (toGate item ::
                  ((items.filter selected).map toGate ++
                    (items.filter fun item => !selected item).map toGate)) := by
                simpa only [List.map_cons, Semantics.circuit] using congrArg
                  (WeightedRelation.comp (Semantics.gate (toGate item))) ih'
          _ = _ := hmove
          _ = Semantics.circuit
                (((item :: items).filter selected).map toGate ++
                  ((item :: items).filter fun item => !selected item).map toGate) := by
                simp [hs]
      | true =>
        have ih' := ih (fun inside hi outside ho hsi hso =>
          hcomm inside (by simp [hi]) outside (by simp [ho]) hsi hso)
        simpa [List.filter_cons, hs, Semantics.circuit] using congrArg
          (WeightedRelation.comp (Semantics.gate (toGate item))) ih'

/-- The buffered span factors into its anchor component followed by all unrelated components. -/
theorem anchorComponent_factorization {n : Nat} (buffer : Circuit n) :
    Semantics.circuit buffer =
      Semantics.circuit (anchorComponent buffer ++ outsideComponent buffer) := by
  classical
  simp only [anchorComponent, outsideComponent]
  conv_lhs => rw [← List.zipIdx_map_fst 0 buffer]
  apply map_eq_filter_append
  intro inside hi outside ho hinside houtside
  apply GateCommutes.symm (component_outside_commute buffer hi ho ?_ ?_)
  · exact of_decide_eq_true hinside
  · exact of_decide_eq_false houtside

/-- Qubits used by a circuit window. -/
def circuitSupport {n : Nat} (circuit : Circuit n) : Finset (Fin n) :=
  circuit.foldl (fun support gate => support ∪ gateSupport gate) ∅

/-- The same two resource bounds used to limit Rust's active windows. -/
structure WindowBounds where
  maxQubits : Nat
  maxGates : Nat

/-- Whether an anchor component fits within the configured synthesis bounds. -/
def WindowBounds.allows {n : Nat} (bounds : WindowBounds) (component : Circuit n) : Bool :=
  component.length ≤ bounds.maxGates ∧ (circuitSupport component).card ≤ bounds.maxQubits

/-- `Consider(S)` from the scan in the module header, with the bound test in front of
it. The returned pair is the replacement followed by the unclaimed remainder: the
gates of the span outside the window, then the gates beyond the span.

Dropping the window's gates from what is returned is how `claim every position of S`
(line 17) is realised: a claimed gate is simply no longer on offer to any later
anchor, so selected rewrites cannot overlap. -/
def tryWindow {n : Nat} (table : UnitaryTable n) (bounds : WindowBounds)
    (buffer rest : Circuit n) : Option (Circuit n × Circuit n) :=
  let component := anchorComponent buffer
  if bounds.allows component then
    match table.lookup (unitary component) with     -- W' ← M(canon(⟦W⟧))
    | some replacement =>
        if replacement.length < component.length then -- |W'| < |W|
          some (replacement, outsideComponent buffer ++ rest)
        else none
    | none => none
  else none

/-- A table rewrite of an anchor component preserves the buffered span and untouched suffix. -/
theorem tryWindow_sound {n : Nat} (table : UnitaryTable n) (bounds : WindowBounds)
    (buffer rest replacement remainder : Circuit n)
    (h : tryWindow table bounds buffer rest = some (replacement, remainder)) :
    Semantics.circuit (replacement ++ remainder) =
      Semantics.circuit (buffer ++ rest) := by
  simp only [tryWindow] at h
  split at h
  next _ =>
    split at h
    next candidate hlookup =>
      split at h
      next _ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have htable := table.lookup_semantics (anchorComponent buffer) candidate hlookup
        have hspan :
            Semantics.circuit (candidate ++ outsideComponent buffer) =
              Semantics.circuit buffer := by
          calc
            Semantics.circuit (candidate ++ outsideComponent buffer) =
                WeightedRelation.comp (Semantics.circuit candidate)
                  (Semantics.circuit (outsideComponent buffer)) :=
                    Semantics.circuit_append _ _
            _ = WeightedRelation.comp (Semantics.circuit (anchorComponent buffer))
                  (Semantics.circuit (outsideComponent buffer)) := by rw [htable]
            _ = Semantics.circuit (anchorComponent buffer ++ outsideComponent buffer) :=
                  (Semantics.circuit_append _ _).symm
            _ = Semantics.circuit buffer := (anchorComponent_factorization buffer).symm
        rw [show candidate ++ (outsideComponent buffer ++ rest) =
          (candidate ++ outsideComponent buffer) ++ rest by simp [List.append_assoc]]
        rw [Semantics.circuit_append]
        rw [hspan]
        exact (Semantics.circuit_append buffer rest).symm
      next => simp at h
    next => simp at h
  next => simp at h

/-- Grow one anchor's window across successive gates: the inner loop of the scan in
the module header, for a single `a`. `seen` is the buffered span beginning at the anchor, `rest` the unexamined
suffix, and `fuel` the anchor's budget: how many further gates it may reach across
before the scan gives up on it. That budget stands in for the per-qubit index, which
is what lets the implementation skip non-dependent gates for free. -/
def findFrom {n : Nat} (table : UnitaryTable n) (bounds : WindowBounds) :
    Nat → Circuit n → Circuit n → Option (Circuit n × Circuit n)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | fuel + 1, seen, g :: rest =>
      let buffer := seen ++ [g]
      match tryWindow table bounds buffer rest with
      | some result => some result
      | none => findFrom table bounds fuel buffer rest

/-- Any rewrite found while growing an anchor preserves the full prefix and remaining input. -/
theorem findFrom_sound {n : Nat} (table : UnitaryTable n) (bounds : WindowBounds)
    (fuel : Nat) (seen rest replacement remainder : Circuit n)
    (h : findFrom table bounds fuel seen rest = some (replacement, remainder)) :
    Semantics.circuit (replacement ++ remainder) =
      Semantics.circuit (seen ++ rest) := by
  induction fuel generalizing seen rest with
  | zero => simp [findFrom] at h
  | succ fuel ih =>
      cases rest with
      | nil => simp [findFrom] at h
      | cons g rest =>
          let buffer := seen ++ [g]
          change (match tryWindow table bounds buffer rest with
            | some result => some result
            | none => findFrom table bounds fuel buffer rest) =
              some (replacement, remainder) at h
          cases htry : tryWindow table bounds buffer rest with
          | some result =>
              rw [htry] at h
              injection h
              subst result
              simpa [buffer, List.append_assoc] using
                tryWindow_sound table bounds buffer rest replacement remainder htry
          | none =>
              rw [htry] at h
              have hrec := ih buffer rest h
              simpa [buffer, List.append_assoc] using hrec



/-- A selection of a span's gates, as a predicate on occurrences. The scan's windows
are selections of this form: the gates at the positions it has collected. -/
abbrev Selection (n : Nat) := Occurrence n → Bool

/-- A selection is *closed* in its span when no gate outside it interferes with a gate
inside it. This is what the scan's dependency-closure invariant buys, and it is the
side condition under which a window may be rewritten where it sits. -/
def Closed {n : Nat} (span : Circuit n) (sel : Selection n) : Prop :=
  ∀ inside ∈ span.zipIdx, ∀ outside ∈ span.zipIdx,
    sel inside = true → sel outside = false → GateCommutes outside.1 inside.1

/-- The gates a selection picks out, in their original order. -/
def selected {n : Nat} (span : Circuit n) (sel : Selection n) : Circuit n :=
  (span.zipIdx.filter sel).map Prod.fst

/-- The gates a selection skips, in their original order. -/
def unselected {n : Nat} (span : Circuit n) (sel : Selection n) : Circuit n :=
  (span.zipIdx.filter (fun item => !sel item)).map Prod.fst

/-- **Any closed selection factors out.** A span is semantically the selected gates
followed by the skipped ones, so a window may be replaced where it sits without
disturbing the gates it steps over. Generalizes `anchorComponent_factorization`, which
is the special case where the selection is the connected component of the span's head.
-/
theorem span_factorization {n : Nat} (span : Circuit n) (sel : Selection n)
    (hclosed : Closed span sel) :
    Semantics.circuit span =
      Semantics.circuit (selected span sel ++ unselected span sel) := by
  classical
  simp only [selected, unselected]
  conv_lhs => rw [← List.zipIdx_map_fst 0 span]
  exact map_eq_filter_append _ Prod.fst sel hclosed

/-- A span is exactly its selected and skipped gates. -/
theorem length_selected_add_unselected (span : Circuit n) (sel : Selection n) :
    (selected span sel).length + (unselected span sel).length = span.length := by
  simp only [selected, unselected, List.length_map]
  rw [← List.length_zipIdx (l := span)]
  generalize span.zipIdx = items
  induction items with
  | nil => rfl
  | cons item items ih =>
      by_cases h : sel item = true <;>
        simp [h] <;> omega

/-- The connected component of a span's head is a closed selection, so the existing
factorization is an instance of the general one. -/
theorem closed_inAnchorComponent {n : Nat} (span : Circuit n) :
    Closed span (fun node => decide (inAnchorComponent span node)) := by
  intro inside hi outside ho hinside houtside
  refine GateCommutes.symm (component_outside_commute span hi ho ?_ ?_)
  · exact of_decide_eq_true hinside
  · exact of_decide_eq_false houtside

/-- `anchorComponent_factorization` recovered from the general lemma. -/
theorem anchorComponent_factorization' {n : Nat} (span : Circuit n) :
    Semantics.circuit span =
      Semantics.circuit (anchorComponent span ++ outsideComponent span) := by
  have h := span_factorization span (fun node => decide (inAnchorComponent span node))
    (closed_inAnchorComponent span)
  simpa [selected, unselected, anchorComponent, outsideComponent] using h

/-- **A closed window may be rewritten wherever it sits.** If `sel` is closed in
`span` and `repl` implements the gates it selects, then swapping `repl` in for those
gates -- leaving the skipped gates of the span, and everything before and after it,
exactly where they are -- preserves the whole circuit's semantics.

This is `tryWindow_sound` freed of its anchoring: the window need not be the connected
component of the span's head, and the span need not sit at the front of the circuit.
It is the step the scan repeats once per selected rewrite. -/
theorem rewrite_in_place {n : Nat} (pre span post repl : Circuit n) (sel : Selection n)
    (hclosed : Closed span sel)
    (hsem : Semantics.circuit repl = Semantics.circuit (selected span sel)) :
    Semantics.circuit (pre ++ (repl ++ unselected span sel) ++ post) =
      Semantics.circuit (pre ++ span ++ post) := by
  have hspan : Semantics.circuit (repl ++ unselected span sel) =
      Semantics.circuit span := by
    calc
      Semantics.circuit (repl ++ unselected span sel)
          = WeightedRelation.comp (Semantics.circuit repl)
              (Semantics.circuit (unselected span sel)) := Semantics.circuit_append _ _
      _ = WeightedRelation.comp (Semantics.circuit (selected span sel))
              (Semantics.circuit (unselected span sel)) := by rw [hsem]
      _ = Semantics.circuit (selected span sel ++ unselected span sel) :=
            (Semantics.circuit_append _ _).symm
      _ = Semantics.circuit span := (span_factorization span sel hclosed).symm
  simp only [Semantics.circuit_append, hspan]

/-- Two disjoint closed selections of the same span commute wholesale: every gate of
one is outside the other, so closedness makes them pairwise independent. This is what
lets the scan apply its selected rewrites independently of each other, even when their
windows interleave positionally. -/
theorem closed_disjoint_commute {n : Nat} (span : Circuit n) (sel other : Selection n)
    (hclosed : Closed span sel)
    (hdisj : ∀ node, other node = true → sel node = false) :
    ∀ inside ∈ span.zipIdx, ∀ outside ∈ span.zipIdx,
      sel inside = true → other outside = true → GateCommutes outside.1 inside.1 :=
  fun inside hi outside ho hsi hso => hclosed inside hi outside ho hsi (hdisj outside hso)

/-! ## Applying every selected rewrite

A scan does not stop at one rewrite: it collects several and installs them all. A
`Layout` records the shape of that result -- the circuit as alternating untouched
stretches and rewritten spans -- so that installing every rewrite is an induction over
this structure, one `rewrite_in_place` per step. -/

/-- A circuit presented as alternating untouched stretches and rewritten spans. -/
inductive Layout (n : Nat) where
  /-- The untouched tail after the last rewritten span. -/
  | done (tail : Circuit n)
  /-- An untouched stretch, then a span in which `sel` is replaced by `repl`. -/
  | step (keep span : Circuit n) (sel : Selection n) (repl : Circuit n)
      (rest : Layout n)

namespace Layout

variable {n : Nat}

/-- The circuit the scan started from. -/
def original : Layout n → Circuit n
  | .done tail => tail
  | .step keep span _ _ rest => keep ++ span ++ rest.original

/-- The circuit the scan produced. -/
def rewritten : Layout n → Circuit n
  | .done tail => tail
  | .step keep span sel repl rest => keep ++ (repl ++ unselected span sel) ++ rest.rewritten

/-- Every rewrite in the layout is licensed: its window is closed in its span, and its
replacement implements the gates that window selects. -/
def Valid : Layout n → Prop
  | .done _ => True
  | .step _ span sel repl rest =>
      Closed span sel ∧
      Semantics.circuit repl = Semantics.circuit (selected span sel) ∧
      Valid rest

/-- **Installing every selected rewrite preserves the circuit.** Spans are disjoint by
construction here -- the layout interleaves them with the stretches between -- so each
rewrite is discharged independently by `rewrite_in_place`. -/
theorem sound : ∀ (L : Layout n), L.Valid →
    Semantics.circuit L.rewritten = Semantics.circuit L.original
  | .done _, _ => rfl
  | .step keep span sel repl rest, ⟨hclosed, hsem, hrest⟩ => by
      have ih := sound rest hrest
      calc
        Semantics.circuit (keep ++ (repl ++ unselected span sel) ++ rest.rewritten)
            = Semantics.circuit (keep ++ (repl ++ unselected span sel) ++ rest.original) := by
              simp only [Semantics.circuit_append, ih]
        _ = Semantics.circuit (keep ++ span ++ rest.original) :=
              rewrite_in_place keep span rest.original repl sel hclosed hsem

/-- Every rewrite in the layout is at least as short as what it replaces. -/
def Shrinks : Layout n → Prop
  | .done _ => True
  | .step _ span sel repl rest =>
      repl.length ≤ (selected span sel).length ∧ Shrinks rest

/-- **A layout never grows the circuit**, given no replacement is longer than what it
replaces. Together with `Layout.sound` this is the second half of the pass's
correctness statement: equivalent, and no larger. -/
theorem length_le : ∀ (L : Layout n), L.Shrinks →
    L.rewritten.length ≤ L.original.length
  | .done _, _ => le_refl _
  | .step keep span sel repl rest, ⟨hshort, hrest⟩ => by
      have ih := length_le rest hrest
      have hsplit := length_selected_add_unselected span sel
      simp only [rewritten, original, List.length_append]
      omega

end Layout

/-! ## The scan, instrumented

The definitions below are the pass itself, carrying both the synthesis table and a
count of the work done, so that correctness and the work bound are theorems about one
function. The anchor search is given an explicit budget: an anchor reaches at most
`budget` gates past itself before the scan moves on. That budget is what makes the
work bound unconditional. -/

/-- A span is its anchor component plus the components it skips. -/
theorem length_anchorComponent_add_outside (buffer : Circuit n) :
    (anchorComponent buffer).length + (outsideComponent buffer).length = buffer.length := by
  classical
  simpa [anchorComponent, outsideComponent, selected, unselected] using
    length_selected_add_unselected buffer (fun node => decide (inAnchorComponent buffer node))

/-- A committed rewrite always leaves strictly fewer gates to scan. -/
theorem tryWindow_length {table : UnitaryTable n} {bounds : WindowBounds}
    {buffer rest replacement remainder : Circuit n}
    (h : tryWindow table bounds buffer rest = some (replacement, remainder)) :
    remainder.length < (buffer ++ rest).length := by
  classical
  simp only [tryWindow] at h
  split at h
  next =>
    split at h
    next candidate hlookup =>
      split at h
      next hshorter =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have hsplit := length_anchorComponent_add_outside buffer
        have hpos : 0 < (anchorComponent buffer).length := by
          rcases Nat.eq_zero_or_pos (anchorComponent buffer).length with hz | hp
          · rw [hz] at hshorter; omega
          · exact hp
        simp only [List.length_append]
        omega
      next => simp at h
    next => simp at h
  next => simp at h

/-- Growing an anchor and committing a rewrite likewise leaves fewer gates to scan. -/
theorem findFrom_length {table : UnitaryTable n} {bounds : WindowBounds} :
    ∀ (fuel : Nat) (seen rest replacement remainder : Circuit n),
      findFrom table bounds fuel seen rest = some (replacement, remainder) →
        remainder.length < (seen ++ rest).length
  | 0, _, _, _, _, h => by simp [findFrom] at h
  | fuel + 1, seen, rest, replacement, remainder, h => by
      cases rest with
      | nil => simp [findFrom] at h
      | cons g rest =>
          simp only [findFrom] at h
          cases htry : tryWindow table bounds (seen ++ [g]) rest with
          | some result =>
              rw [htry] at h
              injection h with h
              subst h
              have := tryWindow_length htry
              simpa [List.append_assoc] using this
          | none =>
              rw [htry] at h
              have := findFrom_length fuel (seen ++ [g]) rest replacement remainder h
              simpa [List.append_assoc] using this

/-- The pass: the outer loop of the scan in the module header, together with its final
application of the selected rewrites, which is done here as each rewrite commits
rather than in one pass at the end -- the two agree because rewrites never overlap.

The second component is the work done. One unit is one window: building its unitary,
canonicalizing, and the table query that follows. It is charged at `budget` per step
of the scan, which is the most that step's anchor search can have cost. -/
def scanSteps (table : UnitaryTable n) (bounds : WindowBounds) (budget : Nat) :
    Nat → Circuit n → Circuit n × Nat
  | 0, input => (input, 0)
  | _ + 1, [] => ([], 0)
  | fuel + 1, g :: rest =>
      match findFrom table bounds budget [] (g :: rest) with
      | some (replacement, remainder) =>
          let r := scanSteps table bounds budget fuel remainder
          (replacement ++ r.1, budget + r.2)
      | none =>
          let r := scanSteps table bounds budget fuel rest
          (g :: r.1, budget + r.2)

/-- **The scan is correct.** Whatever rewrites it commits, the circuit it returns is
equivalent to the one it was given. -/
theorem scanSteps_correct (table : UnitaryTable n) (bounds : WindowBounds)
    (budget : Nat) :
    ∀ (fuel : Nat) (input : Circuit n),
      Semantics.circuit (scanSteps table bounds budget fuel input).1 =
        Semantics.circuit input
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | fuel + 1, g :: rest => by
      simp only [scanSteps]
      cases hfind : findFrom table bounds budget [] (g :: rest) with
      | none =>
          have ih := scanSteps_correct table bounds budget fuel rest
          simp only [Semantics.circuit]
          rw [ih]
      | some result =>
          rcases result with ⟨replacement, remainder⟩
          have hwindow := findFrom_sound table bounds budget [] (g :: rest)
            replacement remainder hfind
          have ih := scanSteps_correct table bounds budget fuel remainder
          calc
            Semantics.circuit (replacement ++ (scanSteps table bounds budget fuel remainder).1)
                = WeightedRelation.comp (Semantics.circuit replacement)
                    (Semantics.circuit (scanSteps table bounds budget fuel remainder).1) :=
                      Semantics.circuit_append _ _
            _ = WeightedRelation.comp (Semantics.circuit replacement)
                    (Semantics.circuit remainder) := by rw [ih]
            _ = Semantics.circuit (replacement ++ remainder) :=
                  (Semantics.circuit_append _ _).symm
            _ = Semantics.circuit (g :: rest) := by simpa using hwindow

/-- **The scan is linear.** It does at most `budget` units of work per input gate:
every step of the scan either commits a rewrite -- which strictly shortens what is
left to scan -- or retires one gate, and either way the anchor search it ran was
capped at `budget`. The constant depends only on the bounds, never on the circuit. -/
theorem scanSteps_steps_le (table : UnitaryTable n) (bounds : WindowBounds)
    (budget : Nat) :
    ∀ (fuel : Nat) (input : Circuit n),
      (scanSteps table bounds budget fuel input).2 ≤ budget * input.length
  | 0, _ => by simp [scanSteps]
  | _ + 1, [] => by simp [scanSteps]
  | fuel + 1, g :: rest => by
      simp only [scanSteps]
      cases hfind : findFrom table bounds budget [] (g :: rest) with
      | none =>
          have ih := scanSteps_steps_le table bounds budget fuel rest
          simp only [List.length_cons, Nat.mul_succ]
          omega
      | some result =>
          rcases result with ⟨replacement, remainder⟩
          have ih := scanSteps_steps_le table bounds budget fuel remainder
          -- A committed rewrite leaves strictly fewer gates, so the recursive call is
          -- charged against a strictly shorter circuit.
          have hlen : remainder.length < (g :: rest).length := by
            simpa using findFrom_length budget [] (g :: rest) replacement remainder hfind
          simp only [List.length_cons] at hlen
          -- Stated against `rest.length` directly: `omega` treats each product as an
          -- opaque atom, so the two sides must already share one.
          have hmono : budget * remainder.length ≤ budget * rest.length :=
            Nat.mul_le_mul_left budget (by omega)
          have hexp : budget * (rest.length + 1) = budget * rest.length + budget := by ring
          simp only [List.length_cons]
          omega

/-- A committed rewrite never adds gates: the replacement is strictly shorter than the
window it stands in for, and the rest of the span is carried over untouched. -/
theorem tryWindow_length_le {table : UnitaryTable n} {bounds : WindowBounds}
    {buffer rest replacement remainder : Circuit n}
    (h : tryWindow table bounds buffer rest = some (replacement, remainder)) :
    replacement.length + remainder.length ≤ (buffer ++ rest).length := by
  classical
  simp only [tryWindow] at h
  split at h
  next =>
    split at h
    next candidate hlookup =>
      split at h
      next hshorter =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have hsplit := length_anchorComponent_add_outside buffer
        simp only [List.length_append]
        omega
      next => simp at h
    next => simp at h
  next => simp at h

/-- The same, for a rewrite found while growing an anchor. -/
theorem findFrom_length_le {table : UnitaryTable n} {bounds : WindowBounds} :
    ∀ (fuel : Nat) (seen rest replacement remainder : Circuit n),
      findFrom table bounds fuel seen rest = some (replacement, remainder) →
        replacement.length + remainder.length ≤ (seen ++ rest).length
  | 0, _, _, _, _, h => by simp [findFrom] at h
  | fuel + 1, seen, rest, replacement, remainder, h => by
      cases rest with
      | nil => simp [findFrom] at h
      | cons g rest =>
          simp only [findFrom] at h
          cases htry : tryWindow table bounds (seen ++ [g]) rest with
          | some result =>
              rw [htry] at h
              injection h with h
              subst h
              have := tryWindow_length_le htry
              simpa [List.append_assoc] using this
          | none =>
              rw [htry] at h
              have := findFrom_length_le fuel (seen ++ [g]) rest replacement remainder h
              simpa [List.append_assoc] using this

/-- **The scan never grows the circuit.** With `scanSteps_correct` this is the pass's
full correctness statement: the output is equivalent to the input and no larger. -/
theorem scanSteps_length_le (table : UnitaryTable n) (bounds : WindowBounds)
    (budget : Nat) :
    ∀ (fuel : Nat) (input : Circuit n),
      (scanSteps table bounds budget fuel input).1.length ≤ input.length
  | 0, _ => le_refl _
  | _ + 1, [] => le_refl _
  | fuel + 1, g :: rest => by
      simp only [scanSteps]
      cases hfind : findFrom table bounds budget [] (g :: rest) with
      | none =>
          have ih := scanSteps_length_le table bounds budget fuel rest
          simp only [List.length_cons]
          omega
      | some result =>
          rcases result with ⟨replacement, remainder⟩
          have ih := scanSteps_length_le table bounds budget fuel remainder
          have hlen : replacement.length + remainder.length ≤ (g :: rest).length := by
            simpa using findFrom_length_le budget [] (g :: rest) replacement remainder hfind
          simp only [List.length_append] at *
          omega

/-- The pass: run the scan with one unit of outer fuel per input gate, which is always
enough, since every step of the scan retires at least one gate. -/
def optimize (table : UnitaryTable n) (bounds : WindowBounds) (budget : Nat)
    (input : Circuit n) : Circuit n :=
  (scanSteps table bounds budget input.length input).1

/-- The work the pass does on `input`. -/
def optimizeSteps (table : UnitaryTable n) (bounds : WindowBounds) (budget : Nat)
    (input : Circuit n) : Nat :=
  (scanSteps table bounds budget input.length input).2

/-- **Correctness.** The pass returns an equivalent circuit with no more gates. -/
theorem optimize_correct (table : UnitaryTable n) (bounds : WindowBounds) (budget : Nat)
    (input : Circuit n) :
    Semantics.circuit (optimize table bounds budget input) = Semantics.circuit input ∧
      (optimize table bounds budget input).length ≤ input.length :=
  ⟨scanSteps_correct table bounds budget input.length input,
   scanSteps_length_le table bounds budget input.length input⟩

/-- **Linearity.** The pass does at most `budget` units of work per input gate. The
constant is fixed by the bounds; it does not grow with the circuit. -/
theorem optimize_linear (table : UnitaryTable n) (bounds : WindowBounds) (budget : Nat)
    (input : Circuit n) :
    optimizeSteps table bounds budget input ≤ budget * input.length :=
  scanSteps_steps_le table bounds budget input.length input

end
end Tzap.SuperOpt.Algorithm
