import TzapLean.ExactMat
import TzapLean.Locality
import TzapLean.SynthTable

/-!
# `SuperOpt`: the Algorithm

A forward scan that carves out small *windows* — causally connected groups of gates on a few
wires — computes each window's exact matrix, and replaces it whenever a shorter gate list has
the same matrix. Nothing is matched syntactically: any identity expressible in the search
space is found without ever being written down.

Candidates come from the precomputed synthesis table (`SynthTable.lean`): a window's matrix
is canonicalized to a key and looked up, and a hit *is* the shortest circuit the enumeration
found for that unitary. The table is unverified — its BFS, its prunes, its key, its reified
matrices are all outside the proof — because every candidate is re-verified by `accepts`
before it is taken. A wrong table costs optimization, never correctness.

This is `src/super_opt/mod.rs`, with one deliberate departure: **skipped gates move to just
after the replacement** rather than staying interleaved. They commute with every window gate,
so this is invisible; it keeps the reconstruction to one list splice.

Windows are subsequences, not slices: gates in between that share no wire with the window are
simply skipped. The invariant that makes this sound — *no skipped gate touches the window's
support* — is maintained by re-checking every skipped gate when a new member widens the
support, and it is the hypothesis the correctness proof consumes.
-/

namespace TzapLean

/-- Limits on window growth and on how far the search looks. -/
structure SuperOptConfig where
  /-- Widest window, in wires. -/
  maxQubits : Nat := 2
  /-- Longest window, in gates. -/
  maxWindow : Nat := 6
deriving Repr

/-- Gates a window may contain: `rz` is outside the exact Clifford+T domain, and
`measure`/`reset` are not unitary. -/
def isWindowGate (g : Gate) : Bool :=
  match g with
  | .rz _ _ | .measure _ _ | .reset _ => false
  | _ => true

/-- Whether a gate touches any of these wires. -/
def touches (S : List Qubit) (g : Gate) : Bool := g.qubitsOf.any (fun q => S.contains q)

/-- `S`, plus any of these wires that are new. -/
def widen (S : List Qubit) : List Qubit → List Qubit
  | [] => S
  | q :: qs => widen (if S.contains q then S else S ++ [q]) qs

/-- A window under construction.

The skipped and consumed lists are stored **most recent first**. They grow once per gate the
scan passes, and `xs ++ [g]` copies the whole list each time, so keeping them forward-ordered
made a single window's scan quadratic in its span — the dominant cost of the pass. Cons is
`O(1)`; the two derived accessors below reverse once, and only where the order is actually
needed. Members are capped at `maxWindow`, so they stay forward-ordered. -/
structure Win where
  /-- The wires the window covers. -/
  support : List Qubit
  /-- The window's gates, in order. -/
  members : List Gate
  /-- Gates of the span that the window skipped, most recent first. -/
  revSkipped : List Gate
  /-- The whole span consumed so far, most recent first — the gates a rewrite replaces. -/
  revConsumed : List Gate

/-- Gates of the span that the window skipped, in order. -/
def Win.skipped (w : Win) : List Gate := w.revSkipped.reverse

/-- The whole span consumed so far, in order. -/
def Win.consumed (w : Win) : List Gate := w.revConsumed.reverse

@[simp] theorem Win.skipped_extend (w : Win) (sup : List Qubit) (mem : List Gate) (g : Gate) :
    (Win.mk sup mem w.revSkipped (g :: w.revConsumed)).skipped = w.skipped := rfl

@[simp] theorem Win.consumed_extend (w : Win) (sup : List Qubit) (mem : List Gate) (g : Gate) :
    (Win.mk sup mem w.revSkipped (g :: w.revConsumed)).consumed = w.consumed ++ [g] := by
  simp [Win.consumed]

@[simp] theorem Win.skipped_skip (w : Win) (g : Gate) :
    (Win.mk w.support w.members (g :: w.revSkipped) (g :: w.revConsumed)).skipped
      = w.skipped ++ [g] := by
  simp [Win.skipped]

@[simp] theorem Win.consumed_skip (w : Win) (g : Gate) :
    (Win.mk w.support w.members (g :: w.revSkipped) (g :: w.revConsumed)).consumed
      = w.consumed ++ [g] := by
  simp [Win.consumed]

/-- The window an anchor gate starts. -/
def Win.start (g : Gate) : Win where
  support := g.qubitsOf
  members := [g]
  revSkipped := []
  revConsumed := [g]

@[simp] theorem Win.members_start (g : Gate) : (Win.start g).members = [g] := rfl

@[simp] theorem Win.support_start (g : Gate) : (Win.start g).support = g.qubitsOf := rfl

@[simp] theorem Win.skipped_start (g : Gate) : (Win.start g).skipped = [] := rfl

@[simp] theorem Win.consumed_start (g : Gate) : (Win.start g).consumed = [g] := rfl

/-! ## Proposing and verifying a replacement -/

/-- Whether a candidate is usable *and* really has the window's matrix, up to global phase.
This is the check the correctness proof consumes; the search that proposes candidates is
unverified, so everything the proof needs is re-established here. -/
def accepts {k : Nat} (target : ExactMat k) (cand : List Gate) : Bool :=
  cand.all (fun g => g.qubitsOf.all (fun q => q < k) && decide g.Wf) &&
    (match ExactMat.matrixOf k cand with
     | none => false
     | some N => (ExactMat.phaseMatch target N.normalize).isSome)

/-- Rename a local circuit back to the window's physical wires. -/
def globalizeGate (S : List Qubit) : Gate → Gate := mapQubits (fun i => S.getD i 0)

/-- Whether the table might answer for this window.

`trySynth` builds the window's matrix through `ExactMat`, which is indexed by a *function*, so
every entry access walks the chain of gates applied so far — profiling put `Basis.get`,
`Basis.set` and closure application at the top of the pass. That cost is worth paying once a
replacement exists, and wasted on the overwhelming majority of windows that have none. This
filter answers the same question on the flat representation the table itself is built with.

It is unverified in both directions, and safe in both: a false negative costs an optimization,
a false positive costs one wasted verified lookup. Nothing downstream trusts it — `trySynth`
still computes the real matrix and `accepts` still compares exactly. -/
def windowMayHold (tbl : SynthTable) (k : Nat) (fm : Option FlatMat) : Bool :=
  match fm with
  | none => false
  | some M => tbl.mayHold k M

/-- Whether the table holds a replacement for this window strictly shorter than it — the
question `trySynth` will go on to answer exactly. -/
def windowHasShorter (tbl : SynthTable) (k : Nat) (fm : Option FlatMat) (len : Nat) : Bool :=
  match fm with
  | none => false
  | some M => tbl.hasShorter k M len

/-- Look for a strictly shorter replacement for a window, verified before it is returned. -/
def trySynth (tbl : SynthTable) (w : Win) : Option (List Gate) :=
  if w.members.length ≤ 1 then none
  else
    match ExactMat.matrixOf w.support.length (localizeGates w.support w.members) with
    | none => none
    | some M =>
        match tbl.synthesize w.support.length M.normalize with
        | none => none
        | some cand =>
            if accepts M.normalize cand && cand.length < w.members.length then
              some (cand.map (globalizeGate w.support))
            else none

/-- `trySynth`, but skipping the expensive exact-matrix build when the filter says the table
holds nothing for this window. Same answer whenever the filter is right, and a strictly
verified answer either way. -/
def trySynthFiltered (tbl : SynthTable) (fm : Option FlatMat) (w : Win) : Option (List Gate) :=
  if windowMayHold tbl w.support.length fm then trySynth tbl w else none

/-- The window's flat matrix after one more gate: extended in place when the support is
unchanged, rebuilt when the gate brings a new wire in (at most `maxQubits` times per window). -/
def extendFlat (sup : List Qubit) (fm : Option FlatMat) (w : Win) (g : Gate) : Option FlatMat :=
  if sup.length == w.support.length then fm.bind (·.applyGate (localizeGate w.support g))
  else FlatMat.ofGates sup.length (localizeGates sup (w.members ++ [g]))

/-! ## The per-qubit index

`tryWindow` walks the gate list one gate at a time, and most gates it walks touch none of the
window's wires. The expected distance to the next gate on a given wire is `gates/qubit`, so a
window that accepts `maxWindow` members walks about `maxWindow × gates/qubit` gates — on
`gf2^16` that is ~2,300 gates per anchor, and it is where the pass spent its time.

Rust does not scan for the gates it cares about, it looks them up: `tracks[q]` holds the
indices of the gates touching wire `q`, so a lookahead visits only those. This is that index,
used to answer one question cheaply — *would this anchor produce a rewrite at all?* — before
the verified scan runs.

**Everything in this section is unverified, and safe in both directions.** A false negative
skips an anchor that had a rewrite, costing an optimization; a false positive costs one
wasted verified scan. `tryWindow` still produces every rewrite that is taken, and
`tryWindow_correct` still proves it. -/

/-- Per-wire gate indices, ascending. -/
def buildTracks (n : Nat) (gs : Array Gate) : Array (Array Nat) := Id.run do
  let mut tr : Array (Array Nat) := Array.replicate n #[]
  for h : i in [0 : gs.size] do
    for q in gs[i].qubitsOf do
      if q < n then tr := tr.modify q (·.push i)
  return tr

/-- Index of the first entry of a sorted array strictly greater than `x`. -/
def upperBoundIdx (a : Array Nat) (x : Nat) : Nat :=
  go a.size 0 a.size
where
  /-- Binary search, with the interval width as fuel. -/
  go : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if a[mid]! ≤ x then go fuel (mid + 1) hi else go fuel lo mid
      else lo

/-- The first gate on wire `q` strictly after index `i`. -/
def nextOn (tracks : Array (Array Nat)) (q i : Nat) : Option Nat :=
  match tracks[q]? with
  | none => none
  | some a =>
      let j := upperBoundIdx a i
      if j < a.size then some a[j]! else none

/-- Is any gate on wire `q` strictly between `lo` and `hi`? -/
def anyOn (tracks : Array (Array Nat)) (q lo hi : Nat) : Bool :=
  match nextOn tracks q lo with
  | none => false
  | some j => j < hi

/-- The first gate after `i` touching any wire of `S`. -/
def nextTouching (tracks : Array (Array Nat)) (S : List Qubit) (i : Nat) : Option Nat :=
  S.foldl (fun best q =>
    match nextOn tracks q i with
    | none => best
    | some j => some (match best with | none => j | some b => min b j)) none

/-- Would the window anchored at `i` reach a rewrite? Replays `tryWindow`'s growth through
the index, visiting only gates that touch the window — never the gaps between them.

The one subtle check is `tryWindow`'s "no skipped gate touches the widened support": a skipped
gate is one in the span that misses the current support, so it can only touch the *new* wire a
gate brings in, and the index answers that directly. -/
def anchorMayFire (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) (gs : Array Gate)
    (tracks : Array (Array Nat)) (anchor : Nat) : Bool :=
  let a := gs[anchor]!
  go (cfg.maxWindow + 1) a.qubitsOf [a] 1
    (FlatMat.ofGates a.qubitsOf.length (localizeGates a.qubitsOf [a])) anchor
where
  /-- Walk the window's own gates, widest-first, until it fires or dies. The window's matrix
  is carried and extended in place, rebuilt only when a gate brings a new wire in — rebuilding
  it per step made the filter quadratic in the window's length. -/
  go : Nat → List Qubit → List Gate → Nat → Option FlatMat → Nat → Bool
  | 0, _, _, _, _, _ => false
  | fuel + 1, sup, members, count, fm, i =>
      match nextTouching tracks sup i with
      | none => false
      | some j =>
          let g := gs[j]!
          let sup' := widen sup g.qubitsOf
          if !isWindowGate g || !g.qubitsOf.all (fun q => q < n) || !decide g.Wf
              || sup'.length > cfg.maxQubits || count + 1 > cfg.maxWindow then false
          else if (sup'.filter (fun q => !sup.contains q)).any
              (fun w => anyOn tracks w anchor j) then false
          else
            let members' := members ++ [g]
            let fm' :=
              if sup'.length == sup.length then fm.bind (·.applyGate (localizeGate sup g))
              else FlatMat.ofGates sup'.length (localizeGates sup' members')
            if windowHasShorter tbl sup'.length fm' (count + 1) then true
            else go fuel sup' members' (count + 1) fm' j

/-! ## The scan -/

/-- Grow a window through the gates that follow it, rewriting at the first hit. The result
replaces the whole consumed span *and* the gates after it. -/
def tryWindow (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) (fm : Option FlatMat)
    (w : Win) (cnt : Nat) : List Gate → Option (List Gate × List Gate × List Gate × Nat)
  | [] => none
  | g :: rest =>
      if touches w.support g then
        if isWindowGate g && g.qubitsOf.all (fun q => q < n) && decide g.Wf &&
            (widen w.support g.qubitsOf).length ≤ cfg.maxQubits &&
            w.members.length + 1 ≤ cfg.maxWindow &&
            !w.skipped.any (fun s => touches (widen w.support g.qubitsOf) s) then
          -- The cheap filter first: only build the window's exact matrix when the table
          -- might actually answer for it (see `windowMayHold`).
          match trySynthFiltered tbl (extendFlat (widen w.support g.qubitsOf) fm w g)
              ⟨widen w.support g.qubitsOf, w.members ++ [g], w.revSkipped,
                g :: w.revConsumed⟩ with
          | some repl => some (repl, w.skipped, rest, cnt + 1)
          | none =>
              tryWindow cfg tbl n (extendFlat (widen w.support g.qubitsOf) fm w g)
                ⟨widen w.support g.qubitsOf, w.members ++ [g], w.revSkipped,
                  g :: w.revConsumed⟩ (cnt + 1) rest
        else none
      else
        tryWindow cfg tbl n fm
          ⟨w.support, w.members, g :: w.revSkipped, g :: w.revConsumed⟩ (cnt + 1) rest

/-- The tail a rewrite leaves is a suffix of what the window was scanning, so a sweep that
continues from it makes progress. -/
theorem tryWindow_tail_le {cfg : SuperOptConfig} {tbl : SynthTable} {n : Nat} :
    ∀ (rest : List Gate) (fm : Option FlatMat) (w : Win) (cnt : Nat)
      (repl sk tail : List Gate) (k : Nat),
      tryWindow cfg tbl n fm w cnt rest = some (repl, sk, tail, k) →
        tail.length ≤ rest.length := by
  intro rest
  induction rest with
  | nil => intro fm w cnt repl sk tail k h; rw [tryWindow] at h; exact absurd h (by simp)
  | cons g rest ih =>
      intro fm w cnt repl sk tail k h
      rw [tryWindow] at h
      split at h
      · split at h
        · split at h
          · rw [Option.some.injEq] at h
            obtain ⟨-, -, rfl⟩ := h
            simp
          · exact le_trans (ih _ _ _ _ _ _ _ h) (by simp)
        · exact absurd h (by simp)
      · exact le_trans (ih _ _ _ _ _ _ _ h) (by simp)

/-- Whether a gate may anchor a window. -/
def canAnchor (cfg : SuperOptConfig) (n : Nat) (g : Gate) : Bool :=
  isWindowGate g && g.qubitsOf.length ≤ cfg.maxQubits &&
    g.qubitsOf.all (fun q => q < n) && decide g.Wf

/-- One sweep: rewrite every window that claims a replacement, **continuing past each one**
rather than restarting.

The old shape found a single rewrite and re-scanned the circuit from the top, which is
`O(rewrites × gates)` — measured at 25 s on a circuit with 256 of them, against Rust's 0.012 s.
Rust collects every non-overlapping rewrite in one scan and applies them together; continuing
from the tail a rewrite leaves is the same idea, and each rewrite is still justified on its own
by `tryWindow_correct`, so the correctness argument composes by transitivity. -/
def sweepOnce (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) (gs : Array Gate)
    (tracks : Array (Array Nat)) : Nat → Nat → List Gate → List Gate
  | 0, _, gs => gs
  | _ + 1, _, [] => []
  | fuel + 1, at_, g :: rest =>
      if canAnchor cfg n g && anchorMayFire cfg tbl n gs tracks at_ then
        match tryWindow cfg tbl n
            (FlatMat.ofGates (Win.start g).support.length
              (localizeGates (Win.start g).support (Win.start g).members))
            (Win.start g) 0 rest with
        -- `tryWindow` hands back how many gates it consumed, so the index advances in `O(1)`.
        -- Recovering it from `tail.length` instead cost a walk of the whole remaining list on
        -- every rewrite, which was quadratic on its own.
        | some (repl, sk, tail, consumed) =>
            repl ++ sk ++ sweepOnce cfg tbl n gs tracks fuel (at_ + 1 + consumed) tail
        | none => g :: sweepOnce cfg tbl n gs tracks fuel (at_ + 1) rest
      else g :: sweepOnce cfg tbl n gs tracks fuel (at_ + 1) rest

/-- Sweep until a sweep changes nothing. One sweepOnce already takes every rewrite it can see; a
second is only needed because a rewrite can expose a new window. -/
def superOptAux (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) : Nat → List Gate → List Gate
  | 0, gs => gs
  | fuel + 1, gs =>
      let arr := gs.toArray
      let gs' := sweepOnce cfg tbl n arr (buildTracks n arr) gs.length 0 gs
      if gs'.length < gs.length then superOptAux cfg tbl n fuel gs' else gs'

/-- Peephole superoptimization of a gate list over `n` wires. -/
def superOptGates (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) (gs : List Gate) :
    List Gate :=
  superOptAux cfg tbl n gs.length gs

/-- Peephole superoptimization of a circuit. -/
def superOpt (cfg : SuperOptConfig) (tbl : SynthTable) (c : Circuit) : Circuit :=
  c.withGates (superOptGates cfg tbl c.numQubits c.gates)

end TzapLean
