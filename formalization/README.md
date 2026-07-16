# tzap-lean: A Lean 4 Formalization of tzap

A machine-checked formalization, in Lean 4 with Mathlib, of the semantics,
static analysis, and optimization algorithm from the TZap paper on phase
folding of quantum circuits. It covers the exact weighted-relation semantics,
the symbolic parity analysis and its soundness, the phase-folding rewrite, the
randomized (hash-based) analysis with its collision bound, and Algorithm 1
itself — both the exact and the randomized variants — with end-to-end
correctness theorems.

## Headline results

| Theorem | File | Statement (informal) |
|---|---|---|
| `SuperOpt.Algorithm.optimize_correct` | `TZap/SuperOpt/Algorithm.lean` | The anchored connected-component SuperOpt pass, with skipped unrelated gates and retroactive bridge closure, preserves exact weighted-relation semantics. |
| `Unitary.unitary_agrees` | `TZap/Unitary.lean` | Dense unitary matrix semantics is exactly equal to the weighted-relation semantics after swapping the matrix indices. |
| `RandomizedAlgorithm.randomized_fold_correct` | `TZap/RandomizedAlgorithm.lean` | The randomized Algorithm 1 with `k`-bit hashes returns a non-equivalent circuit with probability at most `C(t,2) · 2⁻ᵏ`, where `t` is the number of `Rz` gates. |
| `RandomizedSoundness.randomized_analysis_sound` | `TZap/RandomizedSoundness.lean` | A semantically false equality reported by the randomized analysis with `k`-bit hashes has probability at most `2⁻ᵏ`. |
| `Algorithm.fold_correct` | `TZap/Algorithm.lean` | The exact Algorithm 1 preserves circuit semantics: `⟦fold C⟧ = ⟦C⟧`. |
| `PhaseFolding.phase_folding` | `TZap/PhaseFolding.lean` | The single-merge rewrite: if the parity condition holds, merging two rotations preserves semantics. |
| `Soundness.parity_equality_sound` | `TZap/Soundness.lean` | Every parity equality claimed by the symbolic analysis holds on every supported transition. |
| `Collision.affine_collision_bound` | `TZap/Collision.lean` | Two distinct affine parities collide under uniform `k`-bit hashing with probability at most `2⁻ᵏ`. |

## Building

Requires [elan](https://github.com/leanprover/elan); the toolchain
(`leanprover/lean4:v4.30.0`, pinned in `lean-toolchain`) and Mathlib are
fetched automatically.

```sh
lake exe cache get   # fetch prebuilt Mathlib (strongly recommended)
lake build           # builds the library and the tzapCheck executable
```

## Structure

The modules, in dependency order:

### Semantics

- **`TZap/WeightedRelation.lean`** — Complex-weighted relations
  `α → β → ℂ` (finite matrices), with identity, composition (summing
  amplitudes over the intermediate basis), associativity, and a witness lemma:
  a nonzero composite amplitude has a nonzero-amplitude path.

- **`TZap/Circuit.lean`** — Syntax. Basis states are `Fin n → Bool`; gates are
  `CNOT`, `H`, `X`, and `Rz θ`; a circuit is a list of gates executed
  head-first.

- **`TZap/Semantics.lean`** — Exact complex semantics. Each gate denotes a
  weighted relation (`Rz θ = diag(1, e^{iθ})`, Hadamard with `±1/√2`
  coefficients); circuits compose gate relations. Key algebraic facts:
  `phase_add` (`Rz` angles add on equal parity bits) and nonzero-amplitude
  shape lemmas used throughout the soundness proofs.

- **`TZap/Unitary.lean`** — General exact dense-matrix semantics using the
  row-output/column-input convention and left-applied gate matrices. Its gates
  use the formalization's weighted-relation convention, including
  `Rz θ = diag(1, e^{iθ})`. `unitary_agrees` proves literal equality after
  swapping the matrix indices.

- **`TZap/SuperOpt/Table.lean`** — The optimizer-specific abstract
  unitary-to-circuit synthesis table and its exact soundness contract.

- **`TZap/SuperOpt/Algorithm.lean`** — The Rust-style connected-window pass.
  Every gate becomes an anchor; its component grows across later gates while
  unrelated gates are skipped, and later bridge gates retroactively pull in
  earlier disconnected components. Windows are bounded by gate count and
  qubit support, table results must be strictly shorter, and accepted windows
  are removed before scanning the remaining gates. `optimize_correct` proves
  exact weighted-relation equivalence.

### Symbolic parity analysis

- **`TZap/Symbolic.lean`** — The abstract domain. A `Parity` is a Boolean
  affine expression (`const`, `var`, `xor`) over ℕ-indexed variables; a
  symbolic `State` assigns a parity to each qubit plus a fresh-variable
  counter. The four transfer functions of the paper (`CNOT` xors parities,
  `X` flips, `H` allocates a fresh variable, `Rz` is the identity) and the
  analysis `analyze = analyzeFrom initial`, with boundedness invariants.

- **`TZap/Soundness.lean`** — Soundness of the analysis against the exact
  semantics (the appendix theorem). Every input/output pair with nonzero
  amplitude is realized by a valuation of the initial and Hadamard-allocated
  variables (`symbolic_soundness`); consequently, any claimed input/output
  parity equality is true on every supported transition
  (`parity_equality_sound`). The induction (`analyzeFrom_sound`) is
  generalized over an arbitrary well-formed starting state, which is what the
  algorithm proofs below reuse.

### Phase folding (the rewrite)

- **`TZap/PhaseFolding.lean`** — Circuit equivalence (`⟦C⟧ = ⟦D⟧` as weighted
  relations), the paper's side `Condition` (the parity at the first rotation
  site equals the parity at the second on all reachable states), and the exact
  phase-folding theorem: under the condition,
  `pre ; Rz θ q ; middle ; Rz φ q' ; suffix ≡ pre ; middle ; Rz (θ+φ) q' ; suffix`.

### Algorithm 1 (exact)

- **`TZap/Algorithm.lean`** — The executable optimizer and its correctness.
  - `mergeInto s p θ gs` forwards the angle `θ` into the first later `Rz`
    whose parity (under the evolving symbolic state) has the same canonical
    affine form as `p`.
  - `foldFrom` / `fold` implement Algorithm 1: one left-to-right pass; each
    `Rz` either forwards its angle into the next occurrence of its parity or
    is kept. Repeated forwarding leaves each merged group as a single `Rz` at
    its **last** position, exactly as in the paper. Termination is by circuit
    length (`mergeInto` preserves length).
  - `fold_correct : Equivalent (fold C) C`. The proof is a direct induction
    over the pass. The key lemma `mergeInto_sound` shows a single forward
    merge multiplies every amplitude of the tail by exactly
    `phase θ (p.eval v)` for any valuation `v` consistent with the symbolic
    state at the merge point; consistency is threaded through intermediate
    gates with `step_preserves_consistency`.

### Randomized analysis and hashing

- **`TZap/Affine.lean`** — Canonical affine normal forms over 𝔽₂: a `Form` is
  a constant plus an `𝔽₂`-coefficient vector (`Finsupp`); `normalize` maps
  parity expressions to forms, commuting with evaluation.

- **`TZap/FiniteProbability.lean`** — The probability layer, built directly on
  Mathlib's `PMF.uniformOfFintype` with event probabilities as `ℝ≥0∞`
  outer-measure masses. The one project-specific result is
  `uniform_fiber_of_surjective`: every fiber of a surjective additive
  homomorphism between finite groups has probability `|B|⁻¹` under the uniform
  PMF — the group-theoretic engine behind the collision bound.

- **`TZap/Randomized.lean`** — The randomized analysis: each variable draws a
  uniform `k`-bit string, and every qubit carries the 𝔽₂-sum of its parity's
  draws. Deterministic given an explicit draw stream, it is shown to be
  exactly the symbolic analysis evaluated under the draws
  (`analyze_correspond`).

- **`TZap/Collision.lean`** — The collision bound: two *distinct* affine forms
  hash equal under a uniform sample with probability at most `2⁻ᵏ`
  (`affine_collision_bound`). Proved by reducing collision to membership in a
  fiber of a surjective 𝔽₂-linear map.

- **`TZap/RandomizedSoundness.lean`** — Soundness of the randomized analysis:
  if some supported transition disagrees at the queried qubits, a false
  randomized equality occurs with probability at most `2⁻ᵏ`.

- **`TZap/RandomizedPhaseFolding.lean`** — The per-merge guarantee: accepting
  a merge whose rewritten circuit is *not* equivalent happens with probability
  at most `2⁻ᵏ` (`randomized_phase_folding`), and the dichotomy form.

### Algorithm 1 (randomized)

- **`TZap/RandomizedAlgorithm.lean`** — The hash-based optimizer and its
  probabilistic correctness.
  - `mergeIntoR` / `foldFromR` / `foldR`: the same single pass as `fold`, but
    the state carries `k`-bit hashes and merge decisions compare hashes.
  - `rzParities C`: the parities at rotation sites — exactly the values the
    algorithm ever compares.
  - `foldFromR_eq_foldFrom`: on a *faithful* sample (no two compared parities
    with distinct normal forms hash equal), the randomized pass makes
    gate-for-gate the same decisions as the exact algorithm, so
    `foldR draws C = fold C`; correctness on faithful samples follows from
    `fold_correct` (`foldR_correct_of_faithful`). The converse direction is
    free: hashing factors through normalization.
  - `collides_probability_le`: a union bound over the `C(t,2)` pairs of
    compared parities bounds the probability of an unfaithful sample by
    `C(t,2) · 2⁻ᵏ`.
  - `randomized_fold_correct`: therefore the randomized optimizer returns a
    non-equivalent circuit with probability at most `C(t,2) · 2⁻ᵏ`:

    ```lean
    theorem randomized_fold_correct {n k : Nat} (C : Circuit n) :
        (PMF.uniformOfFintype
            (Sample (Symbolic.analyze C).nextFresh k)).toOuterMeasure
            {sample | ¬ PhaseFolding.Equivalent (foldR (liftSample sample) C) C} ≤
          ((rzParities C).length.choose 2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ k
    ```

## Design notes

- **Exact, not approximate.** All semantics are exact complex amplitudes
  (no floating point), probabilities are exact `ℝ≥0∞` masses of Mathlib's
  uniform PMF over finite sample spaces, and phase-folding equivalence is
  equality of weighted relations — a stronger property than equality up to
  global phase. The SuperOpt matrix semantics uses the same convention and
  is exactly equal to the weighted-relation semantics after transposition.
- **Randomness as an explicit sample.** The randomized analysis is a
  deterministic function of an explicit draw stream; probabilistic statements
  quantify over the finite space `Sample m k = Fin m → Fin k → 𝔽₂` under
  `PMF.uniformOfFintype`, with events measured by its outer measure.
- **Parity comparison up to normal form.** The algorithms compare parities by
  their canonical affine form (`Affine.normalize`), matching the paper's set
  membership `p ∈ S` and making the exact and randomized algorithms agree
  precisely on faithful samples.

## Relation to the paper

| Paper | Formalization |
|---|---|
| §Semantics: weighted relations | `WeightedRelation.lean`, `Semantics.lean` |
| §Analysis: abstract state, transfer functions | `Symbolic.lean` |
| Soundness theorem (appendix) | `Soundness.lean` |
| Phase-folding theorem | `PhaseFolding.lean` |
| **Algorithm 1** | `Algorithm.lean` |
| §Hashing: randomized parities | `Affine.lean`, `Randomized.lean`, `Collision.lean` |
| Randomized soundness | `RandomizedSoundness.lean`, `RandomizedPhaseFolding.lean` |
| **Algorithm 1, randomized** | `RandomizedAlgorithm.lean` |
