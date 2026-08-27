import TzapLean.Merge
import TzapLean.CnotMin

/-!
# `PhaseFoldRand`: the algorithm

The executable half of phase folding, following `src/phase_fold_rand.rs`. Each wire carries a
random `k`-bit *tag* standing for the parity it holds: `x` complements the tag, `cnot` XORs
the control's into the target's, `h`, `ccx` and `reset` draw a fresh one, and everything else
leaves tags alone. Two rotations may merge when their wires' tags agree — or are complements,
in which case the angle merges negated.

Nothing here mentions `Form`: like Rust, the pass only ever compares tags. The symbolic
parities live in `TzapLean.Analysis` and are attached to this algorithm in
`TzapLean.PhaseFoldProof`, where a tag collision is the *only* way the pass can be wrong.
-/

namespace TzapLean

open Form

/-! ## Tag states -/

/-- The all-ones tag: the hash of the constant parity `1`, i.e. Rust's bitwise `!`. -/
def ones (k : Nat) : BitString k := fun _ => 1

/-- A tag, as the algorithm stores it: `k` bits in an array of `Bool`.

Two departures from the theory's `BitString k = Fin k → F₂`, both forced by measurement:

* **An array, not a function.** `x` and `cnot` build a tag out of old ones, so a stored
  function would be a closure over its predecessors and reading one bit of a tag `d` gates
  deep would cost `kᵈ` — measured at exactly `k` per `cnot`. An array has nothing to rebuild.
* **`Bool`, not `F₂`.** Arithmetic in `ZMod 2` goes through a ring instance that cannot be
  specialized; one 64-entry XOR costs 43 µs against 0.07 µs for the same array of `Bool` —
  about 600×, and the dominant cost of the whole pass.

`bitsToArr` is the bridge to the theory, and `bitsToArr_inj` is what lets a proof read an
equality of stored tags back as an equality of the functions they stand for. -/
abbrev Tag := Array Bool

/-- The array of a tag function's bits. -/
def bitsToArr {k : Nat} (t : BitString k) : Tag :=
  ((List.finRange k).map fun j => unbit (t j)).toArray

@[simp] theorem size_bitsToArr {k : Nat} (t : BitString k) : (bitsToArr t).size = k := by
  simp [bitsToArr]

@[simp] theorem getElem_bitsToArr {k : Nat} (t : BitString k) (j : Fin k) :
    (bitsToArr t)[(j : Nat)]'(by simp) = unbit (t j) := by
  simp [bitsToArr]

/-- Distinct tag functions have distinct arrays, so comparing arrays decides the functions. -/
theorem bitsToArr_inj {k : Nat} {a b : BitString k} (h : bitsToArr a = bitsToArr b) : a = b := by
  funext j
  refine unbit_inj ?_
  have hj : (bitsToArr a)[(j : Nat)]'(by simp) = (bitsToArr b)[(j : Nat)]'(by simp) := by
    simp only [h]
  simpa using hj

/-- The all-ones tag. -/
def onesArr (k : Nat) : Tag := Array.replicate k true

theorem onesArr_eq (k : Nat) : onesArr k = bitsToArr (ones k) := by
  apply Array.ext
  · simp [onesArr]
  · intro i h1 h2
    simp [onesArr, bitsToArr, ones, unbit]

/-- Bitwise XOR of two tags. -/
def xorArr (a b : Tag) : Tag := (a.zip b).map fun p => p.1 ^^ p.2

theorem xorArr_bitsToArr {k : Nat} (a b : BitString k) :
    xorArr (bitsToArr a) (bitsToArr b) = bitsToArr (a + b) := by
  apply Array.ext
  · simp [xorArr]
  · intro i h1 h2
    have hi : i < k := by simpa using h2
    have e : ∀ (t : BitString k), (bitsToArr t)[i]'(by simpa using hi) = unbit (t ⟨i, hi⟩) := by
      intro t
      simpa using getElem_bitsToArr t ⟨i, hi⟩
    simp only [xorArr, Array.getElem_map, Array.getElem_zip, e]
    exact (unbit_add _ _).symm

/-! ## Tag states -/

/-- Per-wire tags, plus the index of the next unused draw. -/
structure TState (k : Nat) where
  /-- One tag per wire. -/
  tags : List Tag
  /-- The next unused draw index. -/
  fresh : Nat

namespace TState

/-- Wire `q`'s tag (the zero tag for a wire the state does not cover). -/
def tagOf {k : Nat} (ts : TState k) (q : Qubit) : Tag :=
  ts.tags.getD q (bitsToArr (0 : BitString k))

/-- Wire `i` starts out tagged with the `i`-th draw. -/
def initial {k : Nat} (draws : Draws k) (n : Nat) : TState k where
  tags := (List.range n).map fun i => bitsToArr (draws i)
  fresh := n

/-- The Rust transfer functions, on tags. -/
def step {k : Nat} (draws : Draws k) (ts : TState k) (g : Gate) : TState k :=
  match g with
  | .x q => { ts with tags := ts.tags.set q (xorArr (ts.tagOf q) (onesArr k)) }
  | .cnot c t => { ts with tags := ts.tags.set t (xorArr (ts.tagOf t) (ts.tagOf c)) }
  | .h q => { tags := ts.tags.set q (bitsToArr (draws ts.fresh)), fresh := ts.fresh + 1 }
  | .ccx _ _ t => { tags := ts.tags.set t (bitsToArr (draws ts.fresh)), fresh := ts.fresh + 1 }
  | .reset q => { tags := ts.tags.set q (bitsToArr (draws ts.fresh)), fresh := ts.fresh + 1 }
  | _ => ts

/-- The tag state after a gate list. -/
def steps {k : Nat} (draws : Draws k) (ts : TState k) : List Gate → TState k
  | [] => ts
  | g :: gs => steps draws (ts.step draws g) gs

end TState

/-! ## Matching -/

/-- Compare a later site's tag with a pending one: `some false` when they agree, `some true`
when the later wire carries the complementary parity (Rust's canonicalisation), `none`
otherwise. -/
def matchTag (k : Nat) (pending later : Tag) : Option Bool :=
  if later == pending then some false
  else if later == xorArr pending (onesArr k) then some true
  else none

/-! ## The fold -/

/-- Scan forward for a rotation on the same parity, carrying the tag state. A gate that is
not unitary stops the scan: this pass never folds across a `measure` or a `reset`. -/
def mergeInto {k : Nat} (draws : Draws k) (ts : TState k) (tag : Tag) (θ : ℚ) :
    List Gate → Option (List Gate)
  | [] => none
  | g :: gs =>
      if g.isUnitary then
        match rotAngle g with
        | some (φ, q') =>
            match matchTag k tag (ts.tagOf q') with
            | some sign => some (Gate.rz (φ + signedAngle sign θ) q' :: gs)
            | none => (mergeInto draws (ts.step draws g) tag θ gs).map (g :: ·)
        | none => (mergeInto draws (ts.step draws g) tag θ gs).map (g :: ·)
      else none

/-- Merging rewrites one rotation in place, so the list keeps its length. -/
theorem mergeInto_length {k : Nat} (draws : Draws k) (tag : Tag) (θ : ℚ) :
    ∀ (gs gs' : List Gate) (ts : TState k), mergeInto draws ts tag θ gs = some gs' →
      gs'.length = gs.length := by
  intro gs
  induction gs with
  | nil => intro gs' ts h; simp [mergeInto] at h
  | cons g gs ih =>
      intro gs' ts h
      simp only [mergeInto] at h
      split at h
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h
            subst h
            simp
          · rcases Option.map_eq_some_iff.1 h with ⟨t, ht, rfl⟩
            simp [ih t _ ht]
        · rcases Option.map_eq_some_iff.1 h with ⟨t, ht, rfl⟩
          simp [ih t _ ht]
      · exact absurd h (by simp)

/-- Fold a gate list: every rotation is pushed forward into the next rotation on its parity,
if there is one. -/
def foldFrom {k : Nat} (draws : Draws k) (ts : TState k) : List Gate → List Gate
  | [] => []
  | g :: gs =>
      match rotAngle g with
      | some (θ, q) =>
          match hm : mergeInto draws ts (ts.tagOf q) θ gs with
          | some gs' => foldFrom draws ts gs'
          | none => g :: foldFrom draws (ts.step draws g) gs
      | none => g :: foldFrom draws (ts.step draws g) gs
  termination_by gs => gs.length
  decreasing_by
    all_goals
      first
        | (rw [mergeInto_length draws (ts.tagOf q) θ gs gs' ts hm]; simp)
        | simp

/-- Re-emit every rotation as Clifford+T where its angle allows, dropping those that
cancelled — the tail of Rust's reconstruction loop. -/
def emitAll : List Gate → List Gate
  | [] => []
  | g :: gs =>
      (match rotAngle g with
        | some (a, q) => emitRotation q a
        | none => [g]) ++ emitAll gs

/-- Phase folding on a gate list, with the draws supplied. -/
def phaseFoldGates {k : Nat} (draws : Draws k) (n : Nat) (gs : List Gate) : List Gate :=
  emitAll (foldFrom draws (TState.initial draws n) gs)

/-- Phase folding on a circuit. -/
def phaseFold {k : Nat} (draws : Draws k) (c : Circuit) : Circuit where
  numQubits := c.numQubits
  numCbits := c.numCbits
  gates := phaseFoldGates draws c.numQubits c.gates

@[simp] theorem phaseFold_numQubits {k : Nat} (draws : Draws k) (c : Circuit) :
    (phaseFold draws c).numQubits = c.numQubits := rfl

@[simp] theorem phaseFold_numCbits {k : Nat} (draws : Draws k) (c : Circuit) :
    (phaseFold draws c).numCbits = c.numCbits := rfl

/-! ## Where the randomness comes from

The pass is a pure function of `draws`, so entropy enters only here, at the boundary. A run
draws exactly the object the correctness theorem quantifies over: one uniform `k`-bit tag per
variable, `Sample (varBound c) k`. `padSample` is the executable copy of `liftSample` (which
is noncomputable, living with the `Finsupp` machinery); the two are definitionally equal, as
`padSample_eq` records, so `phaseFoldIO` runs the very distribution `PhaseFoldRand.correct`
bounds — modulo the one thing no proof can supply, that `IO.rand` is uniform. -/

/-- The number of variables a circuit's analysis can allocate: one per wire, plus at most one
per gate (`h`, `ccx` and `reset` are the only allocating gates). -/
def varBound (c : Circuit) : Nat := c.numQubits + c.gates.length

/-- Executable `liftSample`: pad a finite seed out to a draw stream. -/
def padSample {m k : Nat} (sample : Sample m k) : Draws k :=
  fun i => if h : i < m then sample ⟨i, h⟩ else 0

theorem padSample_eq {m k : Nat} (sample : Sample m k) : padSample sample = liftSample sample :=
  rfl

/-- A deterministic draw stream from a seed: splitmix64 bit mixing, one `k`-bit tag per
variable. Used by the CLI, where a run is reproducible from `--seed`. -/
def seedDraws {k : Nat} (seed : Nat) : Draws k := fun i =>
  let x : UInt64 := (seed.toUInt64 + i.toUInt64 + 1) * 0x9E3779B97F4A7C15
  let x := (x ^^^ (x >>> 30)) * 0xBF58476D1CE4E5B9
  let x := (x ^^^ (x >>> 27)) * 0x94D049BB133111EB
  let x := x ^^^ (x >>> 31)
  fun j => ((x >>> j.val.toUInt64).toNat % 2 : Nat)

/-- Draw one uniform `k`-bit tag per variable from the runtime's generator. -/
def randomSample (m k : Nat) : IO (Sample m k) := do
  let mut rows : Array (Array (ZMod 2)) := #[]
  for _ in [0:m] do
    let mut bits : Array (ZMod 2) := #[]
    for _ in [0:k] do
      let b ← IO.rand 0 1
      bits := bits.push (b : ZMod 2)
    rows := rows.push bits
  return fun i j => (rows[i.val]!)[j.val]!

/-- Phase folding with freshly drawn tags: the pass as it would actually be run. -/
def phaseFoldIO (k : Nat) (c : Circuit) : IO Circuit := do
  let sample ← randomSample (varBound c) k
  return phaseFold (padSample sample) c

end TzapLean
