import Tzap.Cyclotomic.Basic
import Tzap.Cyclotomic.Semantics

/-!
# Cyclotomic Representation of Clifford+T Amplitudes

This umbrella module exports the exact number representation used by
`src/super_opt/matrix.rs` — the ring `ℤ[ω][1/√2]` with `ω = exp(iπ/4)` — and the theorem that
every amplitude of a Clifford+T circuit lies in it.
-/
