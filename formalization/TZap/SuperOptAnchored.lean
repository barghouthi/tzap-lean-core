import Mathlib.Data.List.Enum
import TZap.SuperOpt

/-!
# Anchored Connected-Window SuperOpt

This module captures the central windowing ideas of the Rust SuperOpt pass. Every input gate is
an anchor. Its window grows across later gates by connected-component closure: unrelated gates
are skipped, while a later bridge can retroactively pull an earlier disconnected component into
the anchor window. The abstract unitary table is queried after every growth step, and accepted
windows are removed from further consideration, so selected rewrites never overlap.

The implementation recomputes each anchor closure from its buffered span instead of maintaining
Rust's optimized per-qubit reverse indices. This changes bookkeeping cost, not the window or
rewrite principle.
-/

namespace TZap.SuperOptAnchored

open TZap.SuperOpt

noncomputable section

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

/-- Query one completed anchor component. The returned pair is the replacement followed by the
unclaimed remainder: gates outside the component, then gates beyond the buffered span. -/
def tryWindow {n : Nat} (table : UnitaryTable n) (bounds : WindowBounds)
    (buffer rest : Circuit n) : Option (Circuit n × Circuit n) :=
  let component := anchorComponent buffer
  if bounds.allows component then
    match table.lookup (unitary component) with
    | some replacement =>
        if replacement.length < component.length then
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

/-- Grow one anchor window across successive gates. `seen` is the buffered span beginning at
the anchor; `rest` is the unexamined suffix. -/
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

/-- Search all bounded connected windows anchored at the first input gate. -/
def findAnchoredRewrite {n : Nat} (table : UnitaryTable n) (bounds : WindowBounds)
    (input : Circuit n) : Option (Circuit n × Circuit n) :=
  findFrom table bounds input.length [] input

theorem findAnchoredRewrite_sound {n : Nat} (table : UnitaryTable n)
    (bounds : WindowBounds) (input replacement remainder : Circuit n)
    (h : findAnchoredRewrite table bounds input = some (replacement, remainder)) :
    Semantics.circuit (replacement ++ remainder) = Semantics.circuit input := by
  simpa [findAnchoredRewrite] using
    findFrom_sound table bounds input.length [] input replacement remainder h

/-- The anchored SuperOpt scan. A successful connected-window rewrite commits its replacement
and recursively scans only the unclaimed gates. If an anchor has no rewrite, that gate is emitted
and the next gate becomes the anchor. -/
def optimizeFuel {n : Nat} (table : UnitaryTable n) (bounds : WindowBounds) :
    Nat → Circuit n → Circuit n
  | 0, input => input
  | _ + 1, [] => []
  | fuel + 1, g :: rest =>
      match findAnchoredRewrite table bounds (g :: rest) with
      | some (replacement, remainder) =>
          replacement ++ optimizeFuel table bounds fuel remainder
      | none => g :: optimizeFuel table bounds fuel rest

theorem optimizeFuel_correct {n : Nat} (table : UnitaryTable n) (bounds : WindowBounds)
    (fuel : Nat) (input : Circuit n) :
    Semantics.circuit (optimizeFuel table bounds fuel input) = Semantics.circuit input := by
  induction fuel generalizing input with
  | zero => rfl
  | succ fuel ih =>
      cases input with
      | nil => rfl
      | cons g rest =>
          simp only [optimizeFuel]
          cases hfind : findAnchoredRewrite table bounds (g :: rest) with
          | none =>
              simp only [Semantics.circuit]
              rw [ih]
          | some result =>
              rcases result with ⟨replacement, remainder⟩
              have hwindow :=
                findAnchoredRewrite_sound table bounds (g :: rest) replacement remainder hfind
              calc
                Semantics.circuit (replacement ++ optimizeFuel table bounds fuel remainder) =
                    WeightedRelation.comp (Semantics.circuit replacement)
                      (Semantics.circuit (optimizeFuel table bounds fuel remainder)) :=
                        Semantics.circuit_append _ _
                _ = WeightedRelation.comp (Semantics.circuit replacement)
                      (Semantics.circuit remainder) := by rw [ih]
                _ = Semantics.circuit (replacement ++ remainder) :=
                      (Semantics.circuit_append _ _).symm
                _ = Semantics.circuit (g :: rest) := hwindow

/-- Run with one unit of fuel per input gate. Replacements are committed, while every recursive
call scans only unclaimed original gates, so this is sufficient for a full forward pass. -/
def optimize {n : Nat} (table : UnitaryTable n) (bounds : WindowBounds)
    (input : Circuit n) : Circuit n :=
  optimizeFuel table bounds input.length input

/-- End-to-end correctness of the anchored connected-window algorithm. -/
theorem optimize_correct {n : Nat} (table : UnitaryTable n) (bounds : WindowBounds)
    (input : Circuit n) :
    Semantics.circuit (optimize table bounds input) = Semantics.circuit input := by
  exact optimizeFuel_correct table bounds input.length input

end
end TZap.SuperOptAnchored
