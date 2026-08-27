import TzapLean.ExactMat

/-!
# The Bounded Clifford+T Synthesis Table

`SuperOpt` asks a question — "is there a shorter circuit with this unitary?" — that has the
same answer every time it is asked of the same unitary. So the answer is computed once, for
every unitary reachable within the bounds, and stored: this is `src/super_opt/table.rs`.

The table is built breadth-first, one gate at a time. Because layers are visited in
gate-count order, **the first circuit to reach a unitary is a smallest one**, so a table hit
*is* the synthesis answer — no search at lookup time. Two prunes keep the frontier small
without losing any unitary: a child never follows its parent's inverse, and among
qubit-disjoint neighbours only the canonically ordered interleaving is expanded.

The enumeration needs a *key*: a matrix, canonicalized so that any two representatives of the
same operator hash alike. `ExactMat.key` supplies it — normalize the `√2` denominator, rotate
to the canonical global phase, flatten the coefficients. Rust hashes this down to 64 bits and
guards against collisions by re-comparing matrices; here the key is the exact coefficient
list, so a hit is already exact. Either way the pass re-verifies before rewriting, so the
table is a *source of candidates* and never load-bearing for correctness.

Circuits are stored prefix-shared, as in `synthesis_arena.rs`: BFS only ever extends a
circuit by one gate, so the entries form a tree and each node records just its last gate and
its parent.
-/

namespace TzapLean

/-! ## Canonical keys -/

namespace Cyc

/-- Whether a coefficient tuple is zero. -/
def isZero (x : Cyc) : Bool := x.a == 0 && x.b == 0 && x.c == 0 && x.d == 0

/-- The coefficients, in order. -/
def toList (x : Cyc) : List Int := [x.a, x.b, x.c, x.d]

end Cyc

/-- Lexicographic comparison on coefficient tuples. -/
def lexLt : List Int → List Int → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else lexLt as bs

namespace ExactMat

/-- A basis state's row number: wire `0` is the most significant bit, as in Rust. Used only
to index the builder's scratch arrays — nothing downstream depends on the numbering. -/
def idx {n : Nat} (b : Basis n) : Nat :=
  (List.finRange n).foldl (fun acc j => 2 * acc + (if b j then 1 else 0)) 0

/-- Collapse a matrix's entries into a flat array.

A matrix here is a *function*, so an entry of a circuit's matrix re-walks every gate applied
so far. That is fine for the handful of matrices the pass builds, and hopeless for the
hundreds of thousands the table enumerates, where each is one gate deeper than the last.
Reifying after each step keeps the chain one level deep.

This is used only by the table builder, which is unverified — a wrong `reify` could cost
table hits, never correctness, since `accepts` re-derives every candidate's matrix from
scratch before a rewrite is taken. -/
def reify {n : Nat} (M : ExactMat n) : ExactMat n :=
  let dim := 2 ^ n
  let arr : Array Cyc := Id.run do
    let mut a : Array Cyc := Array.replicate (dim * dim) 0
    for r in basisList n do
      for c in basisList n do
        a := a.set! (idx r * dim + idx c) (M.get r c)
    return a
  { den := M.den, get := fun o i => arr[idx o * dim + idx i]! }

/-- The power of `ω` making the first nonzero entry's coefficients lexicographically least.
This picks one representative from the eight Clifford+T global phases, with no division and
no rounding. -/
def canonicalPhase {n : Nat} (M : ExactMat n) : Nat :=
  match M.entries.find? (fun x => !x.isZero) with
  | none => 0
  | some pivot =>
      (List.range 8).foldl
        (fun best p =>
          if lexLt (pivot.timesOmega p).toList (pivot.timesOmega best).toList then p else best) 0

/-- **The table key**: denominator and phase both canonicalized, coefficients flattened. Two
gate lists with the same key denote the same operator up to global phase. -/
def key {n : Nat} (M : ExactMat n) : List Int :=
  let N := M.normalize
  let p := N.canonicalPhase
  (N.den : Int) :: N.entries.flatMap fun x => (x.timesOmega p).toList

end ExactMat

/-! ## The library gate set

Deliberately **not** every gate the pass can read. `ccx` and `cz` are excluded so
superoptimization never *introduces* them: a Toffoli costs about seven `T` once the pipeline
lowers it, and `cz` would leave the `H`/`X`/`Z`/`S`/`T`/`CX` emission basis. Windows
*containing* those gates are still matched and simplified — their unitaries come from the
input — but such gates are never emitted. -/

/-- A gate the table may emit. -/
inductive LibGate where
  /-- Pauli `X`. -/
  | x (q : Nat)
  /-- Hadamard. -/
  | h (q : Nat)
  /-- Phase `S`. -/
  | s (q : Nat)
  /-- Inverse phase. -/
  | sdg (q : Nat)
  /-- Pauli `Z`. -/
  | z (q : Nat)
  /-- `T`. -/
  | t (q : Nat)
  /-- Inverse `T`. -/
  | tdg (q : Nat)
  /-- Controlled `X`. -/
  | cnot (control target : Nat)
deriving DecidableEq, Repr, Inhabited, Ord, Hashable

namespace LibGate

/-- The circuit gate a library gate stands for. -/
def toGate : LibGate → Gate
  | .x q => .x q
  | .h q => .h q
  | .s q => .s q
  | .sdg q => .sdg q
  | .z q => .z q
  | .t q => .t q
  | .tdg q => .tdg q
  | .cnot c tgt => .cnot c tgt

/-- The wires a library gate touches. -/
def qubits : LibGate → List Nat
  | .x q | .h q | .s q | .sdg q | .z q | .t q | .tdg q => [q]
  | .cnot c tgt => [c, tgt]

/-- Whether two library gates share no wire. -/
def isDisjoint (a b : LibGate) : Bool := a.qubits.all fun q => !b.qubits.contains q

/-- Whether `b` undoes `a` — the first prune: a child never follows its parent's inverse,
since the product would revisit the grandparent's unitary. -/
def isInverseOf : LibGate → LibGate → Bool
  | .s q, .sdg r | .sdg q, .s r | .t q, .tdg r | .tdg q, .t r => q == r
  | .x q, .x r | .h q, .h r | .z q, .z r => q == r
  | .cnot c₁ t₁, .cnot c₂ t₂ => c₁ == c₂ && t₁ == t₂
  | _, _ => false

end LibGate

/-- Every library gate on `k` wires: seven one-wire gates per wire, then every ordered pair
of distinct wires as a `cnot`. -/
def libGates (k : Nat) : List LibGate :=
  (List.range k).flatMap
      (fun q => [.x q, .h q, .s q, .sdg q, .z q, .t q, .tdg q]) ++
    (List.range k).flatMap fun c =>
      (List.range k).filterMap fun tgt => if c == tgt then none else some (.cnot c tgt)

/-! ## The table -/

/-- How far the table is built. -/
structure SuperOptTableConfig where
  /-- Widest table width, in wires. -/
  maxQubits : Nat := 2
  /-- Deepest circuit the enumeration reaches. -/
  maxGates : Nat := 4
  /-- Cap on stored unitaries per width, so a build always terminates promptly. -/
  maxEntriesPerQubit : Nat := 200000
deriving Repr, DecidableEq, Hashable

/-- One stored circuit: its last gate plus the node holding the rest. The root — the empty
circuit, i.e. the identity — has neither. -/
structure CircuitNode where
  /-- The node holding everything but the last gate. -/
  parent : Nat
  /-- The last gate. -/
  gate : LibGate
deriving Repr, Inhabited

/-- One width of the table, stored as a prefix-sharing arena. -/
structure WidthTable where
  /-- Canonical key of each stored unitary, mapped to its node. -/
  keys : Std.HashMap (List Int) Nat := ∅
  /-- The arena; node `0` is the root. -/
  nodes : Array (Option CircuitNode) := #[none]
  /-- Whether the entry cap stopped the build. -/
  saturated : Bool := false
  /-- The last depth completed. -/
  depth : Nat := 0
deriving Inhabited

namespace WidthTable

/-- Recover a stored circuit by walking to the root. -/
def circuitOf (w : WidthTable) (node : Nat) : List LibGate :=
  go w.nodes.size node []
where
  /-- Walk up the parent chain, accumulating gates front-first. -/
  go : Nat → Nat → List LibGate → List LibGate
    | 0, _, acc => acc
    | fuel + 1, i, acc =>
        match w.nodes[i]? with
        | some (some nd) => go fuel nd.parent (nd.gate :: acc)
        | _ => acc

/-- How many unitaries this width stores. -/
def size (w : WidthTable) : Nat := w.keys.size

end WidthTable

/-- Build one width breadth-first. Layers are visited in gate-count order, so the first
circuit reaching a unitary is a smallest one. -/
def buildWidth (k : Nat) (cfg : SuperOptTableConfig) : WidthTable := Id.run do
  let idM := ExactMat.id k
  let gates := libGates k
  let mut tbl : WidthTable :=
    { keys := (∅ : Std.HashMap (List Int) Nat).insert idM.key 0, nodes := #[none] }
  let mut frontier : Array (Nat × ExactMat k) := #[(0, idM)]
  let mut stop := false
  for depth in [1 : cfg.maxGates + 1] do
    if stop then break
    let mut accepted : Array (Nat × ExactMat k) := #[]
    for (parent, base) in frontier do
      if stop then break
      let last : Option LibGate := (tbl.nodes[parent]?.join).map (·.gate)
      for g in gates do
        if stop then break
        -- the two prunes
        let pruned : Bool :=
          match last with
          | some l => l.isInverseOf g || (l.isDisjoint g && compare g l == .lt)
          | none => false
        if pruned then continue
        match (ExactMat.applyGate g.toGate base).map ExactMat.reify with
        | none => pure ()
        | some child =>
            let ky := child.key
            if tbl.keys.contains ky then pure ()
            else if tbl.size ≥ cfg.maxEntriesPerQubit then
              tbl := { tbl with saturated := true }
              stop := true
            else
              let node := tbl.nodes.size
              tbl := { tbl with keys := tbl.keys.insert ky node,
                                nodes := tbl.nodes.push (some ⟨parent, g⟩) }
              accepted := accepted.push (node, child)
    tbl := { tbl with depth := depth }
    if accepted.isEmpty then break
    frontier := accepted
  return tbl

/-- The synthesis table: one `WidthTable` per width, indexed by wire count. -/
structure SynthTable where
  /-- Widths `0 … maxQubits`; index `0` is unused. -/
  widths : Array WidthTable
deriving Inhabited

/-- Build the table for a configuration. -/
def buildTable (cfg : SuperOptTableConfig) : SynthTable :=
  { widths := (Array.range (cfg.maxQubits + 1)).map fun k =>
      if k == 0 then default else buildWidth k cfg }

/-- Look a unitary up. A hit is the shortest circuit the enumeration found for it; the
caller still re-verifies before rewriting. -/
def SynthTable.synthesize (tbl : SynthTable) (k : Nat) (M : ExactMat k) : Option (List Gate) :=
  match tbl.widths[k]? with
  | none => none
  | some w =>
      match w.keys.get? M.key with
      | none => none
      | some node => some ((w.circuitOf node).map LibGate.toGate)

end TzapLean
