import TZap.SuperOpt.GlobalPhase
import TZap.SuperOpt.Search
import TZap.SuperOpt.Table
import TZap.SuperOpt.Algorithm

/-!
# SuperOpt Formalization

This umbrella module exports the abstract synthesis-table interface, anchored connected-window
algorithm, and its end-to-end correctness theorem. General dense unitary semantics lives in the
top-level `TZap.Unitary` module.

`TZap.SuperOpt.GlobalPhase` and `TZap.SuperOpt.Search` cover table *construction*: the canonical
form that makes two unitaries differing only by a global phase share one table key, and the
bounded length-ordered enumeration whose first-wins insertion makes every stored circuit a
shortest one for its key.
-/
