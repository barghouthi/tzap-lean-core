# tzap-lean

A Lean 4 + Mathlib development of tzap's circuit representation, semantics, and optimizer
passes. Every pass here carries its correctness proof as a *field*: an unverified circuit
transformation is not a `Pass`.

```sh
lake exe cache get   # prebuilt Mathlib
lake build           # library + tests (the `#guard` checks run at build time)
```

## Layers

| File | What it is |
|---|---|
| `TzapLean/Circuit.lean` | The Rust `src/circuit.rs`, declaration for declaration. `rz` angles are rationals in units of `π`. |
| `TzapLean/Semantics.lean` | Density-matrix semantics: gate matrices, classical-quantum states, and the channel `step` — `measure` and `reset` included. Trace preservation for all three gate kinds. |
| `TzapLean/Support.lean` | Locality (`SupportedOn`) and the theorem that operators on disjoint wires commute. |
| `TzapLean/GateAlgebra.lean` | Gate-matrix algebra: products of one-wire gates, permutations and diagonals, the self-inverse squares, and the four Hadamard-reduction identities. |
| `TzapLean/Equivalence.lean` | `Equivalent`: equality of channels. Congruence, commutation, and the fact that global phase is invisible. |
| `TzapLean/Pass.lean` | The `Pass` structure — a transformation *plus* proofs — with composition and pipelines. |
| `TzapLean/RandPass.lean` | `RandPass`: a pass with a seed distribution and a bound on its failure probability. Deterministic passes are the `error = 0` case. |
| `TzapLean/Pipeline.lean` | tzap's pipeline as a `RandPass`: deterministic at error `0`, and with phase folding in front (`foldPipeline`). |
| `TzapLean/Cancel.lean` | `CancelGates`: all three sweeps of `src/cancel.rs`, proved. |
| `TzapLean/CnotMin.lean` | `CnotMin`: the phase-polynomial resynthesis of `src/cnot_min.rs`. |
| `TzapLean/CnotMinProof.lean` | Soundness of that pass's analysis, and the pass itself. |
| `TzapLean/Hash.lean` | 𝔽₂ affine forms, random tags, and the collision bound `C(t,2)·2⁻ᵏ` (uniform PMFs, fibers of a surjective hom, union bound). |
| `TzapLean/Analysis.lean` | The parity analysis over all 14 gates, and its soundness: every nonzero amplitude path is explained by a valuation of the analysis' variables. |
| `TzapLean/Merge.lean` | The merge lemma — when the analysis gives two rotation sites the same parity, the first may be deleted into the second. |
| `TzapLean/PhaseFold.lean` | `PhaseFoldRand`'s algorithm, on Rust-style tags, plus `phaseFoldIO` (the entropy boundary). |
| `TzapLean/PhaseFoldProof.lean` | Tags simulate parities; the fold is correct whenever the tags are faithful. |
| `TzapLean/PhaseFoldRand.lean` | The pass as a `RandPass`, with its failure bound. |
| `TzapLean/Cyclotomic.lean` | `ℤ[ω]`, `ω = e^{iπ/4}`: exact Clifford+T arithmetic, the eight global phases, and division by `√2 = ω − ω³`. |
| `TzapLean/ExactMat.lean` | Exact `2ⁿ × 2ⁿ` matrices over that ring, gate by gate, with `matrixOf_sound`. |
| `TzapLean/Locality.lean` | `pad`: an operator on a few wires is itself ⊗ identity. Products, scalars, and every gate. |
| `TzapLean/SuperOpt.lean` | `SuperOpt`: window scan and verified rewrite. |
| `TzapLean/SuperOptProof.lean` | The window invariant, and the pass. |
| `TzapLean/SemanticsCheck.lean` | Independent validation of the semantics: unitarity of every gate, trace preservation, concrete amplitudes, and the `src/unitary.rs` suite. |
| `TzapLean/Tests.lean` | The Rust test suites of `circuit.rs`, `pass.rs`, `cancel.rs` and `cnot_min.rs`, as `#guard` checks. |
| `TzapLean/PhaseFoldTests.lean` | The `phase_fold_rand.rs` suite: 108 `#guard` checks. |
| `TzapLean/SuperOptTests.lean` | The behavioural half of the `super_opt` suite, as `#guard` checks. |

## The obligation

```lean
structure Pass where
  name : String
  run : Circuit → Circuit
  numQubits_run : ∀ c, (run c).numQubits = c.numQubits
  numCbits_run : ∀ c, (run c).numCbits = c.numCbits
  wf_run : ∀ c, c.Wf → (run c).Wf
  correct : ∀ c, c.Wf → Equivalent c.numQubits c.numCbits (run c).gates c.gates
```

`Pass.comp` and `Pass.runAll` compose that obligation, so any pipeline of passes is correct
by construction (`Pass.correct_runAll`).

### Randomized passes

`Pass.correct` is unconditional, which a randomized optimizer cannot sign: fixing a seed
fixes the transformation, and no fixed seed is right on every circuit (a pass whose parities
are `k`-bit tags is already defeated by a circuit on `k+1` wires). So the general structure
is `RandPass`, which carries the seed's distribution and a bound:

```lean
correct : ∀ c, c.Wf →
  (dist c).toOuterMeasure {s | ¬ Equivalent … (run c s).gates c.gates} ≤ error c
```

`Pass.toRand` embeds any deterministic pass at `error = 0` with a one-point seed — its
failure set is literally empty. `RandPass.comp` draws the second pass's seed *after* seeing
the first pass's output (`PMF.bind`, so the composite seed is a sigma type), and the errors
add; no independence between the failure events is needed, since the bound is a union bound.
`RandPass.correct_of_error_eq_zero` turns error `0` back into unconditional correctness on
every seed, so nothing is lost by working in the randomized structure throughout.

`PMF` is noncomputable, so `RandPass` instances are too. Executability stays where it was:
`cancelGates`, `cnotMinGates` and the `Pass` layer still compute, which is what the `#guard`
suite runs on.

`Circuit.Wf` is "multi-qubit gates have distinct operands" — the class of circuits the QASM
front end produces. It is genuinely needed: `cnot q q` is idempotent, not self-inverse, so
cancelling a pair of them would be unsound.

## Where the randomness lives

`PhaseFoldRand` merges two rotations when their wires carry the same parity, and it decides
that by comparing random `k`-bit tags rather than symbolic parities. So the pass can be
wrong — exactly when two *distinct* parities happen to hash alike — and the proof is
organised to isolate that:

* **`Faithful draws ps`** — on the forms this run compares, equal tags mean equal parities.
  It is the only place randomness appears in the correctness argument.
* **`phaseFoldGates_correct`** — under `Faithful`, the output is equivalent to the input.
  Entirely deterministic: no probability, no measure theory.
* **`collides_probability_le`** — `¬ Faithful` has probability at most `C(t,2)·2⁻ᵏ`, by a
  union bound over pairs, each pair bounded by the fiber of a surjective 𝔽₂-linear map.

Composing the two gives the `RandPass` obligation. Doubling the tag width squares the odds
against the pass; `foldPipeline_error` shows the whole pipeline's bound is this single term,
since everything around it is exact.

The seed *is* the randomness: `Seed c = Sample (varBound c) k`, one uniform `k`-bit tag per
variable, under `PMF.uniformOfFintype`. Nothing is sampled in the proof — the bad set is
measured. The algorithm, in turn, is a pure function of a draw stream `Draws k`, so entropy
enters at exactly one place: `phaseFoldIO` draws a `Sample` from `IO.rand` and pads it into
that stream, which is the same object the theorem quantifies over. (`liftSample` is
noncomputable, living with the `Finsupp` machinery, so the runtime uses `padSample`;
`padSample_eq` records that they are the same function.)

Two representations meet here, as they do in Rust: the pass carries `k`-bit tags and never
mentions a parity, while the proof carries 𝔽₂ affine forms and never mentions a tag. `Sim`
relates them wire by wire, and `sim_step` shows every transfer function keeps them in step.

### What this port does not fold

Rust folds *through* measurement and reset: a computational-basis measurement preserves the
value it measures, and `reset` pins a wire to the constant `0`. Here the lookahead stops at
both, because the merge lemma is stated on unitaries — the segment between the two rotation
sites has to be a matrix. The pass therefore merges strictly less than Rust, never more, and
the ported tests record the difference instead of hiding it. Lifting the restriction means
restating the merge on channels (a diagonal operator does commute with the measurement
projectors, so the result should hold).

## Exact arithmetic, and why locality matters

`SuperOpt` replaces a window of gates whenever a shorter gate list has *the same unitary*, so
it has to decide matrix equality — and two Clifford+T circuits are equal or they are not, with
no tolerance to hide behind. Every entry is

```
    (a + b·ω + c·ω² + d·ω³) / √2 ᵏ ,      ω = e^{iπ/4},  ω⁴ = -1
```

over `ℤ`, one denominator exponent for the whole matrix — Rust's representation, with `i8`
coefficients and an overflow path this port does not need. Hadamard adds and subtracts row
pairs and bumps `k`; phase gates rotate coefficients; controlled-`X` permutes rows. Where Rust
*checks* divisibility by `√2` with a parity test before cancelling a factor, `divSqrt2_spec`
proves that test right.

The second ingredient is locality. A window covers a handful of wires, and its matrix must be
computed on *those*, not on the whole register — otherwise the check is exponential in the
circuit's width rather than the window's. `Locality.lean` supplies

```lean
unitary n gs = pad S (unitary S.length (localizeGates S gs))
```

for a gate list living on wires `S`, with `pad` respecting products and scalars. So a local
matrix identity, up to global phase, lifts to the full register — that is
`equivalent_of_local_smul`, and it is what makes the window check both sound and small.

### What the pass does, and what it does not

`SuperOpt` scans forward, growing a window from each anchor through the gates that share its
wires, and rewrites at the first strictly shorter equivalent. Windows are *subsequences*:
gates in between on unrelated wires — including `measure` and `reset` — are skipped and
re-emitted, which is sound because no skipped gate ever touches the window's support. That
invariant is maintained by re-checking every skipped gate when a new member widens the
support, and it is exactly the hypothesis the proof consumes.

Two deliberate departures from Rust:

* **Search instead of a table.** Rust precomputes shortest circuits per matrix, caches them on
  disk, and looks windows up. This port enumerates candidates shorter than the window and
  tests each, so there is no table to build or persist — at the cost of doing that work per
  window. `maxSearch` caps it, so the Lean pass finds short replacements, not arbitrary ones.
* **Skipped gates move to just after the replacement** rather than staying interleaved. They
  commute with every window gate, so this is invisible.

Neither affects correctness, which rests on the check the pass runs before every rewrite:
nothing about the search enters the proof. The identities in the test file — `h·z·h = x`,
`h·cx·h = cz`, `x·cx·x = x⊗cx`, a `T` commuting through a `CNOT` control — are *discovered*,
not listed.

## Two proof styles

* **`CancelGates` is proved outright.** Each of the three sweeps — self-inverse pair
  cancellation, Hadamard reduction, and `CNOT`/`CZ` cancellation across commuting gates — is
  proved to preserve `denote`, including every entry of the two commutation tables ported
  from `commutes_past_cnot` / `commutes_past_cz`.
* **`CnotMin` and `SuperOpt` are proved *certifying*.** Its Gray-code synthesis is a heuristic whose
  correctness argument is a nontrivial invariant; instead of proving it, the pass re-analyses
  its own output and keeps it only when the (proved-sound) analysis returns the same linear
  map and phase polynomial. Soundness rests on the analysis alone — a bug in the heuristic
  could cost optimization, never correctness. On every ported test the check passes, so the
  output matches the Rust pass gate for gate. `SuperOpt` is the same idea with a wider
  search: its candidate replacements come from an unverified enumeration and are accepted only
  after an exact matrix comparison, so the search may be replaced wholesale — by Rust's
  precomputed table, say — without touching a line of the proof.

## Checking the semantics

`TzapLean/Semantics.lean` is what everything else stands on, so `SemanticsCheck.lean`
attacks it from four directions the pass proofs never exercise:

1. **Unitarity.** `gateUnitary_unitary`: every gate matrix satisfies `UᴴU = 1`. A wrong sign,
   a missing `1/√2` or a swapped control and target cannot survive this. It also discharges
   the hypothesis in the trace results, so `totalTrace_denote` now holds for every
   well-formed circuit unconditionally.
2. **Concrete amplitudes.** `X|0⟩ = |1⟩`; `T` phases the `|1⟩` branch by `e^{+iπ/4}` (not its
   conjugate); `CNOT 0 1` flips wire 1 when wire 0 is set and does nothing when it is clear;
   `bell_state` computes the full density matrix of `H(0);CNOT(0,1)|00⟩`;
   `measure_plus_outcome` gives `1/2` for each outcome of measuring `|+⟩` and
   `measure_kills_coherence` shows the off-diagonal is gone; `reset_one_to_zero`.
   `list_order_is_execution_order` pins that a gate list runs left to right.
3. **The `src/unitary.rs` suite** — 43 of its 50 tests, including the negative ones
   (`not_equiv_h_vs_x`, `hsdgh_is_not_s`, `z_does_not_commute_with_cnot_target`,
   `cnot_no_commute_overlapping`, `four_qubit_cnot_ladder_not_reversible`,
   `cz_does_not_commute_with_x_on_operand`,
   `cz_does_not_commute_with_cnot_targeting_operand`). Those matter: every positive test
   would also pass for a degenerate semantics that equated everything.
   The end of that file lists what is not ported, and why.
4. **Against the Rust implementation.** The matrices `circuit_unitary` prints for `H`, `T`,
   `rz(π/4)`, `CNOT`, `CZ`, `H;CNOT` and `H;Sdg;H` were compared entry by entry with what
   these theorems state — agreeing on both conventions that are easy to get wrong: `rz`'s
   symmetric `diag(e^{-iθ/2}, e^{iθ/2})`, and which operand of `CNOT` is the control.

## What the tests do and do not cover

Every Rust test asserts `circuits_equiv(&c, &r, tol)` — a numerical check that one input was
preserved. Those assertions have no counterpart here: `cancelGates_correct` and
`cnotMinGates_correct` prove the equivalence for *every* well-formed input. What is ported
is the structural half of each test — which gates survive, and how many — plus the
randomized sweeps, driven by the same xorshift generator the Rust tests use.

For `phase_fold_rand.rs` the port is sharper than the original: since the equivalence is a
theorem, each `#guard` pins the *exact* gate list the pass produces rather than a count, and
every one of them was checked against the corresponding Rust assertion. Rust's radian
constants become `π`-fractions with the same classification (`0.3 → 3/10`, `PI/4 → 1/4`).
