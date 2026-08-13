import Tzap.SuperOpt.GlobalPhase
import Tzap.SuperOpt.Search
import Tzap.SuperOpt.Table
import Tzap.SuperOpt.Algorithm

/-!
# SuperOpt Formalization

This umbrella module exports the abstract synthesis-table interface, anchored connected-window
algorithm, and its end-to-end correctness theorem. General dense unitary semantics lives in the
top-level `Tzap.Unitary` module.

`Tzap.SuperOpt.GlobalPhase` and `Tzap.SuperOpt.Search` cover table *construction*: the canonical
form that makes two unitaries differing only by a global phase share one table key, and the
bounded length-ordered enumeration whose first-wins insertion makes every stored circuit a
shortest one for its key.

`Tzap.SuperOpt.Algorithm` holds the pass itself, together with both of its
guarantees, proved about one definition: `optimize_correct` (equivalent output, no
larger) and `optimize_linear` (work bounded by a constant times the number of input
gates).
-/
