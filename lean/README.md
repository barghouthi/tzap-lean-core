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
| `TzapLean/Rewrite.lean` | Applying a *set* of scattered, interleaved rewrites at once: the tagging, `applyAll`, and the two conditions that make the splice sound. |
| `TzapLean/Pass.lean` | The `Pass` structure — a transformation *plus* proofs — with composition and pipelines. |
| `TzapLean/RandPass.lean` | `RandPass`: a pass with a seed distribution and a bound on its failure probability. Deterministic passes are the `error = 0` case. |
| `TzapLean/Pipeline.lean` | The three deterministic passes as `RandPass`es, at error `0`. The pipeline itself lives with the driver, in `Optimize.lean`. |
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
| `TzapLean/SynthTable.lean` | The bounded synthesis table: flat builder matrices, fingerprints, the library gate set, and the breadth-first build. |
| `TzapLean/TableCache.lean` | The on-disk table cache — the port of `table.rs`'s persistence. |
| `TzapLean/SuperOpt.lean` | `SuperOpt`: one forward scan with every window open at once, greedy selection over the whole circuit. Unverified — it proposes. |
| `TzapLean/SuperOptProof.lean` | `checkRewrite` — what vets one proposed rewrite — and the pass. |
| `TzapLean/SemanticsCheck.lean` | Independent validation of the semantics: unitarity of every gate, trace preservation, concrete amplitudes, and the `src/unitary.rs` suite. |
| `TzapLean/Tests.lean` | The Rust test suites of `circuit.rs`, `pass.rs`, `cancel.rs` and `cnot_min.rs`, as `#guard` checks. |
| `TzapLean/PhaseFoldTests.lean` | The `phase_fold_rand.rs` suite: 108 `#guard` checks. |
| `TzapLean/SuperOptTests.lean` | The behavioural half of the `super_opt` suite, as `#guard` checks. |
| `TzapLean/Qasm.lean` | OpenQASM 2.0 parser and serializer — the port of `src/qasm.rs`. |
| `TzapLean/Optimize.lean` | Levels, pass names, the pipeline as a `RandPass` (`passOf`/`tzapRound`/`tzapRun`), the driver that runs it, and the reported metrics. |
| `TzapLean/Cli.lean` | Flags, `--help`, and the run banner — `src/cli.rs` and `src/main.rs`. |
| `TzapLean/QasmTests.lean` | The parser suite and the option plumbing, as `#guard` checks. |

## The executable

```sh
lake build tzap-lean
./.lake/build/bin/tzap-lean circuit.qasm -o out.qasm -O3
```

By default a run prints only its final result. Rust narrates every pass of every round; on a
fixpoint run that is a dozen or more lines of intermediate counts, and the per-pass timings
were only ever useful while tuning the passes themselves. `--verbose` restores them. A cold
synthesis-table build is announced either way, since it takes tens of seconds.

Flags otherwise keep Rust's names and meanings, so a command line transfers between the two. What is
absent says so when asked for, rather than reporting an unknown flag: `--parallel`
(deliberately not ported), `--decompose-rz` / `--decompose-cz` / `--epsilon`, and the
`DecomposeToffoli` / `DecomposeCz` / `DecomposeRz` / `CliffordResynth` pass names. `--seed` is
new — `PhaseFoldRand` is randomized, so a run is only reproducible if its tags are.

**`rz` is rejected by the parser.** Angles here are exact rationals in units of `π`, and
gridsynth is not ported, so accepting an `rz` would mean carrying a gate nothing downstream
can lower. The front end says so at the door.

### Where this differs from Rust, measured

The current deterministic comparison uses a warm synthesis-table cache and
`--passes CnotMin,CancelGates,SuperOpt --fixpoint`. Median wall-clock times from three runs
on the same machine were:

| circuit | gates | Lean | Rust | ratio |
|---|---:|---:|---:|---:|
| `gf2^8` | 1,139 | 0.82 s | 0.01 s | 82× |
| `gf2^16` | 4,459 | 2.62 s | 0.02 s | 131× |
| `gf2^32` | 17,658 | 10.10 s | 0.05 s | 202× |

Both implementations produce the same gate counts on this pipeline: 874, 3,384, and 13,331.
Depth can differ slightly because independent gates may be emitted in a different order.
The Rust times are so short that process startup and table loading materially affect the first
two ratios; the conclusion is the scale of the gap, not the last digit.

One unrelated cost was hiding the pass comparison: `Metrics.of` computed depth by replaying
the entire gate list once per qubit, and the driver called it around every pass. It now computes
all counters and depth in one array-backed gate walk. On `gf2^32`, a `CnotMin` invocation fell
from about 12.1 s total to 0.13 s, and the deterministic pipeline fell from about 28.1 s to
10.1 s. This changes reporting only, not optimizer decisions or output.

### Scaling

The `gf2^k_mult` family is the useful stress test, because gate count grows quadratically in
`k` while qubit count grows linearly — so *gates per qubit* doubles at every step:

| circuit | qubits | gates | gates/qubit | Lean deterministic pipeline |
|---|---|---|---|---|
| `gf2^8` | 24 | 1,139 | 47 | 0.82 s |
| `gf2^16` | 48 | 4,459 | 93 | 2.62 s |
| `gf2^32` | 96 | 17,658 | 184 | 10.10 s |

Lean time grows 3.2× and 3.9× as gate count grows 3.9× and 4.0×. The scan is therefore close
to linear in gates on this family now; the remaining problem is the very large constant.
Post-fix sampling puts nearly all useful time under `SuperOpt`, principally below
`Scan.consider`: for every live-window extension Lean materializes the member gates,
localizes them, rebuilds a `FlatMat`, normalizes it, fingerprints it, and probes the table.

Rust avoids repeating that work with a process-persistent `MatrixStore`:

1. A compact support-local gate-sequence key interns each distinct window shape. The cached
   value contains both its matrix and its synthesis result, including a failed lookup.
2. A live window remembers its interned state. When one gate extends the same support, a
   `(state, gate-code)` transition normally finds the successor without rebuilding or hashing
   the sequence.
3. The store survives fixpoint rounds, and incremental mode only permits anchors near gates
   changed by the previous round.

Lean currently has none of those three caches. Its scan already has Rust-style per-qubit
indices (`Scan.byQubit` for live windows and `Scan.gbq` for gate history), so window discovery
is not the main gap. The highest-value next port is the compact canonical-shape store,
including negative synthesis results; then add transition states to `LiveWin`, persist the
store in the optimizer driver, and finally carry an incremental anchor frontier between
rounds. These are search-only changes: the existing proposal checker remains the soundness
boundary, so the proof does not need to trust the cache.

### Matching Rust's window and greedy schedule

A window is the connected closure of its anchor: the gates of a span that reach the anchor
through shared wires, with everything else in the span disjoint from the window's wires and so
commuting past it. A gate that brings in a *new* wire therefore pulls in the earlier gates on
that wire, retroactively — `expand_component_closure` in Rust, `closeSpan` here. This port
used to abandon a window instead whenever an already-skipped gate touched a newly-bridged
wire, which meant it systematically missed every rewrite that has to be discovered that way:
`x q0; h q1; cx q0,q1; x q0` came back unchanged where Rust finds a three-gate replacement.
Both directions of that are now in `SuperOptTests`.

The greedy schedule matches too, and getting there was the larger half. Rust keeps every live
window open at once, sorts the candidates a gate completes by anchor age, and lets the first
one with a shorter replacement claim its gates; anything overlapping a claimed gate is refused
afterwards, and one final pass splices every selection in at its window's anchor
(`RewriteSet`). Selecting the window that *completes* earliest rather than the one that
*starts* earliest is only expressible if the windows are all alive together, which is a
different shape of algorithm from "grow one window, commit its first hit, move on" — and a
different shape of theorem, because the rewrites are then chosen as a *set* over the original
gate list, scattered and interleaved.

That theorem is `applyAll_correct`. The trick that makes it tractable is to stop talking about
indices: a selection is a **tagging**, every gate carrying the rewrite that claims it, so
splicing is a structural recursion and its correctness a list induction rather than a
permutation argument over positions. Two conditions carry it, and both survive taking
sublists, which is exactly what the recursion does to the list:

* `OnSupp` — a claimed gate is unitary and lives on its rewrite's wires;
* `Sep` — a gate that a later gate's rewrite does not claim misses that rewrite's wires.

`gather_equiv` is where they are spent: a rewrite's scattered gates can be gathered at the
first of them because everything they cross on the way is disjoint from them.

The scan itself is **unverified, and no longer needs to be otherwise**. It proposes a tagging;
`checkRewrite` vets each rewrite against the gates it claims by exact matrix comparison, and
`sepB`/`onSuppB` decide the two conditions. A rewrite that fails is untagged and the rest
still stand; if the two conditions fail, nothing is rewritten. That is a strictly larger
freedom than the old arrangement, where the window search had to carry an invariant through
its own proof — and it is faster, because the exact matrix is now built once per *selected*
rewrite rather than once per window that got past a filter. The unverified search still builds
the flat matrix per emitted window; the canonical-shape cache described above is what should
remove that repetition.

Measured against Rust on the `feynman` set at `--passes CnotMin,CancelGates,SuperOpt
--fixpoint` — the deterministic pipeline, so the comparison is the scan and nothing else — the
two now agree everywhere checked, `adder_8` included, where this port had been 7 gates behind
and is now 4 ahead (821 against 825). At `-O3` seven of ten circuits are identical and the
three that differ are phase folding's doing, not the scan's.

Some other Lean passes still use list-based repeated scans where Rust uses per-qubit tracks;
`CancelGates.cancelCommutingPairs` is the clearest example. They are not visible bottlenecks on
this family after fixing metrics, so indexing them is lower priority than caching SuperOpt's
canonical window shapes.

Parsing *was* quadratic for the same family of reason — `Circuit.apply` appends with
`gates ++ [g]`, so folding it copied the list per gate — and is now linear: `gf2^32` went
from 3.2 s to 0.065 s, and `gf2^64` parses in 0.28 s.

`PhaseFoldRand` remains `O(n²)` in principle — it scans forward from each rotation for a later
one on the same parity, where Rust makes one pass keyed by a parity-to-group hash map — but
the constant is now small enough that it is no longer what dominates.

**Every level uses Rust's own `SuperOpt` bounds** — 3 wires, 25-gate windows, 200,000 entries,
with the same `table_gates = window_gates - 1` mapping. `--superopt-qubits`,
`--superopt-window-gates` and `--superopt-table-entries` override any of the three. There used
to be a `-Osuper` tier at 4 wires and 200,000 entries against Rust's 5 and 5,000,000, because
a single-threaded builder cannot reach the latter in a sensible time; it has been removed
rather than left inviting a comparison it could not survive.

`-O3` is `-O2` run to a true fixpoint; Rust's `-O3` also ends with a one-shot Clifford
re-synthesis, which is not ported. The table is cached to disk (`TableCache`), so the 76 s
cold build is paid once and a warm run loads its 549,456 unitaries in 0.07 s.

## The obligation

```lean
structure Pass where
  name : String
  run : Circuit → Circuit
  numQubits_run : ∀ c, (run c).numQubits = c.numQubits
  numCbits_run : ∀ c, (run c).numCbits = c.numCbits
  wf_run : ∀ c, c.Wf → (run c).Wf
  wellFormed_run : ∀ c, c.Wf → c.WellFormed → (run c).WellFormed
  flagsOk_run : ∀ c, c.FlagsOk → (run c).FlagsOk
  correct : ∀ c, c.Wf → Equivalent c.numQubits c.numCbits (run c).gates c.gates
```

`Pass.comp` and `Pass.runAll` compose that obligation, so any pipeline of passes is correct
by construction (`Pass.correct_runAll`).

The last two are about the output being a *circuit*, not about what it means. `WellFormed` is
"every operand names a slot that was declared" — without it the back end can emit a subscript
past the end of the register. `FlagsOk` is "the cached `has*` flags describe the gates that
came out", which every pass gets by rebuilding them through `Circuit.withGates`. Together with
`Qasm.parse_valid`, which establishes all three of `Wf`, `WellFormed` and `FlagsOk` for
whatever the front end accepts, `Pass.structural_runAll` closes the loop from parse to emit.

`Circuit.Wf` is "multi-qubit gates have distinct operands". It is genuinely needed: `cnot q q`
is idempotent, not self-inverse, so cancelling a pair of them would be unsound — and the
parser checks it rather than assuming it, since `cx q[0],q[0]` is otherwise perfectly good
QASM syntax. (The Rust front end does *not* check; there it is a latent bug rather than a
broken proof.)

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
against the pass, and everything around it in the pipeline is exact, so this single term is
the whole of the optimizer's error budget per round.

The seed *is* the randomness: `Seed c = Sample (varBound c) k`, one uniform `k`-bit tag per
variable, under `PMF.uniformOfFintype`. Nothing is sampled in the proof — the bad set is
measured. The algorithm, in turn, is a pure function of a draw stream `Draws k`, so entropy
enters at exactly one place: `phaseFoldIO` draws a `Sample` and pads it into that stream,
which is the same object the theorem quantifies over. (`liftSample` is noncomputable, living
with the `Finsupp` machinery, so the runtime uses `padSample`; `padSample_eq` records that
they are the same function, and `phaseFoldIO_run` records that what the runtime computes is
`(PhaseFoldRand k).run c s` and not a lookalike.)

Drawn *afresh on every call*, which is the point of doing it there rather than expanding one
seed into a stream up front. The driver runs the pipeline in rounds, and round two's circuit
depends on round one's tags; a single stream reused across rounds is an adaptive use that no
union bound here covers. `randomSample` draws a bit at a time from the low bit of a generator
step, which is uniform as soon as the generator is — asking `randNat` for a whole `k`-bit word
would reduce a value that is not a multiple of `2ᵏ` wide modulo `2ᵏ`, and would not be.
`--seed` seeds that generator (`IO.setRandSeed`) rather than substituting a deterministic
stream for the uniform one the bound is about.

## The pipeline, once

`Level.pipeline` is a list of pass names; `passOf` says which verified object each name
denotes, `tzapRound` composes them in that order, and `tzapRun` repeats the round while the
gate count keeps falling — `RandPass.fixpointShrink`, whose rule is literally the driver's.
`stepOf`, the function the driver calls, is that object's `run`; the four `stepOf_*_run`
theorems are `rfl`. So there is one pipeline, not a modelled one and a run one:

```lean
theorem tzapRun_correct … :
  ((tzapRun cfg tbl names fuel).dist c).toOuterMeasure
      {s | ¬ Equivalent … ((tzapRun cfg tbl names fuel).run c s).gates c.gates}
    ≤ (tzapRun cfg tbl names fuel).error c
```

with `fixpointShrink_error_le` and `pipeline_error_le` bounding that error by (rounds ×
passes) times one phase fold's `C(t,2)·2⁻ᵏ`. Drop `PhaseFoldRand` from `--passes` and
`tzapRun_exact` says the bound is `0` and *every* run is right. `tzapRun_structural` says the
output is a circuit the back end may print, for every seed.

## What is trusted

Everything above is machine-checked from `propext`, `Classical.choice` and `Quot.sound`. Three
things are not, and they are all at the edges:

1. **`IO.rand` is uniform.** No Lean theorem can say otherwise; the point of `randomSample` is
   to keep the assumption to exactly this and nothing more.
2. **The `IO` round loop matches `fixpointShrink`.** An `IO` action is opaque to the logic, so
   `runToFixpoint`'s rule and `fixpointShrink_run`'s equation are a correspondence to read
   rather than a theorem. They are kept adjacent in `Optimize.lean` for that reason.
3. **The unverified filters** — `SuperOpt`'s per-qubit index and the on-disk table cache — can
   only cost an optimization, never soundness: every rewrite is still checked by the verified
   path before it is taken.

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

### The table

Candidates come from a precomputed synthesis table, as in `src/super_opt/table.rs`. It is
built breadth-first, one gate at a time: because layers are visited in gate-count order, **the
first circuit to reach a unitary is a smallest one**, so a table hit *is* the synthesis answer
and lookup does no searching. Two prunes keep the frontier small without losing any unitary —
a child never follows its parent's inverse, and among qubit-disjoint neighbours only the
canonically ordered interleaving is expanded — and circuits are stored prefix-shared, each
node recording just its last gate and its parent.

The enumeration needs a *key*, and that is what `ExactMat.key` describes: normalize the `√2`
denominator, rotate to the canonical global phase (the power of `ω` making the first nonzero
entry's coefficients lexicographically least — no division, no rounding), and flatten the
coefficients. The table stores a 64-bit fingerprint of that key, as Rust does. A lookup is
only a proposal; the pass re-computes the exact matrices before accepting it.

The library the table draws from is deliberately **not** every gate the pass can read: `ccx`
and `cz` are excluded, so superoptimization never *introduces* them — a Toffoli costs about
seven `T` once the pipeline lowers it, and `cz` would leave the `H`/`X`/`Z`/`S`/`T`/`CX`
emission basis. Windows *containing* those gates are still matched and simplified.

**None of this is verified, and none of it needs to be.** The table's BFS, its prunes, its
key, and the flat-array reification that makes the build tractable all sit outside the proof,
because `accepts` re-derives every candidate's matrix from scratch and compares it exactly
before a rewrite is taken. A wrong table costs optimization, never correctness — so it could
be replaced by Rust's on-disk cache, or by a smarter enumeration, without touching a line of
the proof. The identities in the test file — `h·z·h = x`, `x·cx·x = x⊗cx`, `(HS)³ = 1`, a `T`
commuting through a `CNOT` control — are *discovered*, not listed.

As in Rust, skipped gates stay interleaved. `applyAll` emits a replacement at its first
claimed gate, removes its other claimed gates, and copies every unclaimed gate in place.

### Persisting the table

Building the table is the one-time cost the design trades for, so — as in Rust — it is written
to disk and read back by later runs, under `~/.tzap-lean/superopt-tables/`. The layout follows
`table.rs`: a magic number, a format version, the bounds the table was built for, then one
fixed-width record per arena node — fingerprint, parent, and last gate. The
fingerprint-to-node map is rebuilt on read, since nodes and fingerprints are one to one.

Every read is validated against the bounds being asked for, and **any failure — missing file,
truncated write, version bump, bounds mismatch — falls back to rebuilding**, so a bad cache
file can waste a read but never produce a wrong table. Writes go to a temporary sibling and
are renamed into place, so a reader never sees a partial file. The version is in the file name
as well as its header, so a bump cannot collide with old files.

The table is indexed by a 64-bit **fingerprint** of the canonical key rather than the key
itself, again as in Rust. That is what makes the file small and the probe fast, and it is safe
for the usual reason: a hit is only ever a candidate, and `accepts` recomputes the
replacement's matrix and compares it exactly before any rewrite is taken. A collision costs a
missed optimization, never a wrong one.

Measured, at Rust's own `-O3` bounds (3 wires, 25-gate windows, 200,000 entries): 549,456
unitaries, **24 s to build, 0.08 s to load**, 8.2 MB on disk.

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
  output matches the Rust pass gate for gate. `SuperOpt` is the same idea at a larger scale:
  its candidate replacements come from an unverified precomputed table and are accepted only
  after an exact matrix comparison, so the whole table — enumeration, prunes, keys and all —
  may be replaced without touching a line of the proof.

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
