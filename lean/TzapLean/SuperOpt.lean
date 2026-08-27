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

/-! ## The scan -/

/-- Grow a window through the gates that follow it, rewriting at the first hit. The result
replaces the whole consumed span *and* the gates after it. -/
def tryWindow (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) (fm : Option FlatMat)
    (w : Win) : List Gate → Option (List Gate × List Gate × List Gate)
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
          | some repl => some (repl, w.skipped, rest)
          | none =>
              tryWindow cfg tbl n (extendFlat (widen w.support g.qubitsOf) fm w g)
                ⟨widen w.support g.qubitsOf, w.members ++ [g], w.revSkipped,
                  g :: w.revConsumed⟩ rest
        else none
      else
        tryWindow cfg tbl n fm
          ⟨w.support, w.members, g :: w.revSkipped, g :: w.revConsumed⟩ rest

/-- The tail a rewrite leaves is a suffix of what the window was scanning, so a sweep that
continues from it makes progress. -/
theorem tryWindow_tail_le {cfg : SuperOptConfig} {tbl : SynthTable} {n : Nat} :
    ∀ (rest : List Gate) (fm : Option FlatMat) (w : Win) (repl sk tail : List Gate),
      tryWindow cfg tbl n fm w rest = some (repl, sk, tail) → tail.length ≤ rest.length := by
  intro rest
  induction rest with
  | nil => intro fm w repl sk tail h; rw [tryWindow] at h; exact absurd h (by simp)
  | cons g rest ih =>
      intro fm w repl sk tail h
      rw [tryWindow] at h
      split at h
      · split at h
        · split at h
          · rw [Option.some.injEq] at h
            obtain ⟨-, -, rfl⟩ := h
            simp
          · exact le_trans (ih _ _ _ _ _ h) (by simp)
        · exact absurd h (by simp)
      · exact le_trans (ih _ _ _ _ _ h) (by simp)

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
def sweepOnce (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) : Nat → List Gate → List Gate
  | 0, gs => gs
  | _ + 1, [] => []
  | fuel + 1, g :: rest =>
      if canAnchor cfg n g then
        match tryWindow cfg tbl n
            (FlatMat.ofGates (Win.start g).support.length
              (localizeGates (Win.start g).support (Win.start g).members)) (Win.start g) rest with
        | some (repl, sk, tail) => repl ++ sk ++ sweepOnce cfg tbl n fuel tail
        | none => g :: sweepOnce cfg tbl n fuel rest
      else g :: sweepOnce cfg tbl n fuel rest

/-- Sweep until a sweep changes nothing. One sweepOnce already takes every rewrite it can see; a
second is only needed because a rewrite can expose a new window. -/
def superOptAux (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) : Nat → List Gate → List Gate
  | 0, gs => gs
  | fuel + 1, gs =>
      let gs' := sweepOnce cfg tbl n gs.length gs
      if gs'.length < gs.length then superOptAux cfg tbl n fuel gs' else gs'

/-- Peephole superoptimization of a gate list over `n` wires. -/
def superOptGates (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) (gs : List Gate) :
    List Gate :=
  superOptAux cfg tbl n gs.length gs

/-- Peephole superoptimization of a circuit. -/
def superOpt (cfg : SuperOptConfig) (tbl : SynthTable) (c : Circuit) : Circuit :=
  { c with gates := superOptGates cfg tbl c.numQubits c.gates }

end TzapLean
