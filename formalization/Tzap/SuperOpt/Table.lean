import Tzap.Unitary

/-!
# Abstract SuperOpt Synthesis Table

The concrete synthesis table is intentionally abstracted to a partial matrix-to-circuit lookup.
The optimizer uses only its exact semantic soundness contract.
-/

namespace Tzap.SuperOpt

open Tzap.Unitary

noncomputable section

/-- An abstract, possibly partial synthesis table. A successful lookup returns a circuit whose
unitary semantics is exactly the matrix used as the key. -/
structure UnitaryTable (n : Nat) where
  lookup : UnitaryMatrix n → Option (Circuit n)
  sound : ∀ (U : UnitaryMatrix n) (replacement : Circuit n),
    lookup U = some replacement → unitary replacement = U

namespace UnitaryTable

/-- A successful abstract-table lookup preserves weighted-relation semantics. -/
theorem lookup_semantics {n : Nat} (table : UnitaryTable n) (window replacement : Circuit n)
    (h : table.lookup (unitary window) = some replacement) :
    Semantics.circuit replacement = Semantics.circuit window := by
  calc
    Semantics.circuit replacement = asWeightedRelation (unitary replacement) :=
      (unitary_agrees replacement).symm
    _ = asWeightedRelation (unitary window) :=
      congrArg asWeightedRelation (table.sound (unitary window) replacement h)
    _ = Semantics.circuit window := unitary_agrees window

end UnitaryTable

end
end Tzap.SuperOpt
