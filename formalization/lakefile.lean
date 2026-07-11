import Lake
open Lake DSL

package «tzap-lean» where
  version := v!"0.1.0"

require "leanprover-community" / "mathlib" @ git "v4.30.0"

lean_lib TZap where
  roots := #[`TZap]

@[default_target]
lean_exe tzapCheck where
  root := `Main
