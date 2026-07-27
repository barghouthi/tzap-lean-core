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
-/
