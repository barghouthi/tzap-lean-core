import TzapLean.SuperOptProof
import TzapLean.PhaseFoldRand
import TzapLean.Qasm
import TzapLean.TableCache
import TzapLean.Pipeline

/-!
# The Optimizer Driver

A port of the parts of `src/optimize.rs` this development can support: the optimization
levels, the pass names selectable by `--passes`, the fixpoint loop, and the metrics the CLI
reports.

Three of the four passes are `Pass`es and carry their proofs. `PhaseFoldRand` is a `RandPass`,
so it is *not* a `Pass` at any fixed seed — that is the whole content of `RandPass.lean` — and
the driver draws it a fresh seed on every call.

The pipeline is defined once, as a `RandPass`: `passOf` sends a pass name to the verified
object, `tzapRound` composes them in the order the driver runs them, and `tzapRun` repeats the
round on the driver's own rule. `stepOf` — what the driver actually calls — is then that
object's `run`, which the `stepOf_*_run` theorems record by `rfl`. There is no second,
informal pipeline for the two to drift apart.

Not ported: `DecomposeToffoli`, `DecomposeCz`, `DecomposeRz` (gridsynth), `CliffordResynth`,
and parallel chunking. `Level.O3` is therefore `O2` run to a true fixpoint, without Rust's
one-shot Clifford re-synthesis at the end.
-/

namespace TzapLean

/-! ## Metrics -/

/-- The counters the CLI reports, from one walk of the gate list. -/
structure Metrics where
  /-- Total gates. -/
  gates : Nat := 0
  /-- `cnot` and `cz` gates. -/
  twoQubit : Nat := 0
  /-- Circuit depth. -/
  depth : Nat := 0
  /-- `t` and `tdg` gates. -/
  t : Nat := 0
  /-- `rz` gates. -/
  rz : Nat := 0
deriving Repr, Inhabited, DecidableEq

/-- Measure a circuit. -/
def Metrics.of (c : Circuit) : Metrics where
  gates := c.gates.length
  twoQubit := count2q c
  depth := TzapLean.depth c
  t := countT c
  rz := countRz c

/-! ## Levels and passes -/

/-- Which default pipeline to run. -/
inductive Level where
  /-- Randomized phase folding + gate cancellation. Fastest. -/
  | O1
  /-- Adds `SuperOpt`, capped at two rounds. -/
  | O2
  /-- Like `O2`, run to a true fixpoint. The default. -/
  | O3
  /-- Fixpoint optimization with wider `SuperOpt` bounds. -/
  | Osuper
deriving Repr, DecidableEq, Inhabited

/-- A pass selectable by name in `--passes`. -/
inductive PassName where
  /-- Cancel adjacent self-inverse pairs and reduce Hadamards. -/
  | CancelGates
  /-- Re-synthesize CNOT-dihedral blocks. -/
  | CnotMin
  /-- Peephole superoptimization against the synthesis table. -/
  | SuperOpt
  /-- Randomized phase folding. -/
  | PhaseFoldRand
deriving Repr, DecidableEq, Inhabited

namespace PassName

/-- All passes — name, variant, and what it carries — in a stable order for listing. -/
def all : List (String × PassName × String) :=
  [ ("CancelGates", .CancelGates,
     "Cancel adjacent self-inverse gate pairs and reduce Hadamards"),
    ("CnotMin", .CnotMin,
     "Re-synthesize CNOT-dihedral blocks to cut CNOT count"),
    ("SuperOpt", .SuperOpt,
     "Peephole superoptimization against the exact synthesis table"),
    ("PhaseFoldRand", .PhaseFoldRand,
     "Merge rotations on the same parity (randomized; see --seed)") ]

/-- Parse a pass name. -/
def parse (s : String) : Option PassName :=
  (all.find? (·.1 == s)).map (·.2.1)

/-- Every pass name, comma-separated — for error messages. -/
def allNames : String := String.intercalate ", " (all.map (·.1))

/-- Whether this pass carries an unconditional correctness proof. `PhaseFoldRand` does not:
it is a `RandPass`, right except with probability at most `C(t,2)·2⁻ᵏ`. -/
def verified : PassName → Bool
  | .PhaseFoldRand => false
  | _ => true

end PassName

/-! ## Options -/

/-- `SuperOpt` window and table bounds, `none` meaning "whatever the level implies". -/
structure SuperOptBounds where
  /-- Widest window and table, in wires. -/
  qubits : Option Nat := none
  /-- Longest window, in gates. -/
  windowGates : Option Nat := none
  /-- Cap on stored unitaries per table width. -/
  tableEntries : Option Nat := none
deriving Repr, Inhabited

/-- Everything the driver needs. -/
structure Options where
  /-- Which default pipeline, when `passes` is absent. -/
  level : Level := .O3
  /-- An explicit pipeline, overriding `level`. -/
  passes : Option (List PassName) := none
  /-- Repeat the pipeline until the gate count stops decreasing. -/
  fixpoint : Bool := false
  /-- `SuperOpt` bounds overrides. -/
  superopt : SuperOptBounds := {}
  /-- Seed for `PhaseFoldRand`; `none` draws from the OS. -/
  seed : Option Nat := none
  /-- Narrate every pass of every round, as the Rust CLI does. Off by default: the final
  result is what a run is usually for. -/
  verbose : Bool := false
deriving Repr, Inhabited

/-- The window/table bounds a level implies.

`O1`–`O3` use Rust's own bounds: 3 wires, 25-gate windows, a 200,000-entry table. That table
takes about 76 seconds to build here against Rust's parallel builder, which is affordable only
because it is built once and cached (`TableCache`) — a warm run loads its 549,456 unitaries in
0.07 s.

`Osuper` is where this parts company with Rust, which uses 5 wires and 5,000,000 entries: at
that size a single-threaded build is not worth waiting for. 4 wires and 200,000 entries is the
widest tier that builds in a tolerable time — 800,000 unitaries in 70 s, then 0.12 s a run. -/
def Level.bounds : Level → Nat × Nat × Nat
  | .O1 => (3, 25, 200000)
  | .O2 => (3, 25, 200000)
  | .O3 => (3, 25, 200000)
  | .Osuper => (4, 40, 200000)

/-- Resolve the bounds for a run: level preset, then any explicit override. -/
def resolveBounds (o : Options) : SuperOptConfig × SuperOptTableConfig :=
  let (q, w, e) := o.level.bounds
  let q := o.superopt.qubits.getD q
  let w := o.superopt.windowGates.getD w
  let e := o.superopt.tableEntries.getD e
  -- A table entry only ever replaces a strictly larger window, so the table never needs to
  -- be deeper than `windowGates - 1`.
  ({ maxQubits := q, maxWindow := w }, { maxQubits := q, maxGates := w - 1,
                                         maxEntriesPerQubit := e })

/-- Whether a level's pipeline includes `SuperOpt`, and so pays for a table. -/
def Level.usesSuperOpt : Level → Bool
  | .O1 => false
  | _ => true

/-! ## Running -/

/-- Tag width for phase folding: 63 bits, so one round misleads the pass with probability at
most `C(t,2)·2⁻⁶³`. -/
def tagBits : Nat := 63

/-- **The verified object a pass name denotes.** The three deterministic passes enter at
error `0` with a one-point seed; phase folding is the one that consumes randomness. -/
noncomputable def passOf (cfg : SuperOptConfig) (tbl : SynthTable) : PassName → RandPass
  | .CancelGates => CancelGatesR
  | .CnotMin => CnotMinR
  | .SuperOpt => SuperOptR cfg tbl
  | .PhaseFoldRand => PhaseFoldRand tagBits

/-- The pipeline a level runs, when `--passes` is absent.

`CnotMin` leads the sweep: it re-synthesizes whole CNOT-dihedral blocks, reshaping the circuit
far more than the peephole rewriter does, and the passes after it work on the result. -/
def Level.pipeline : Level → List PassName
  | .O1 => [.CancelGates, .PhaseFoldRand]
  | _ => [.CnotMin, .CancelGates, .SuperOpt, .PhaseFoldRand]

/-- **One round**: the named passes, in the order the driver runs them. -/
noncomputable def tzapRound (cfg : SuperOptConfig) (tbl : SynthTable) (names : List PassName) :
    RandPass := RandPass.pipeline (names.map (passOf cfg tbl))

/-- **The whole run**: the round, repeated while it keeps removing gates, at most `fuel`
times. This is `runToFixpoint` below, as a pass. -/
noncomputable def tzapRun (cfg : SuperOptConfig) (tbl : SynthTable) (names : List PassName)
    (fuel : Nat) : RandPass := (tzapRound cfg tbl names).fixpointShrink fuel

/-! ### What the run is worth

Two statements, and between them they say what the optimizer guarantees.

`tzapRun_correct` is the general one: the output denotes the same channel as the input except
on a set of seeds whose measure is at most `error`, which by `fixpointShrink_error_le` and
`pipeline_error_le` is at most (rounds × passes) times one phase fold's `C(t,2)·2⁻ᵏ`. Note
that this needs no independence *between* rounds' failure events — a union bound never does —
only that each round's tags are drawn afresh, which is why `phaseFoldIO` draws per call.

`tzapRun_exact` is the special one: drop `PhaseFoldRand` from `--passes` and the bound is
`0`, so *every* run is right, and the randomized machinery gives back exactly the
unconditional `Pass` guarantee. -/

theorem passOf_error_eq_zero {nm : PassName} (h : nm ≠ .PhaseFoldRand) (cfg : SuperOptConfig)
    (tbl : SynthTable) (c : Circuit) : (passOf cfg tbl nm).error c = 0 := by
  cases nm <;> simp_all [passOf, CancelGatesR, CnotMinR, SuperOptR]

theorem tzapRound_error_eq_zero {names : List PassName} (h : PassName.PhaseFoldRand ∉ names)
    (cfg : SuperOptConfig) (tbl : SynthTable) (c : Circuit) :
    (tzapRound cfg tbl names).error c = 0 := by
  refine le_antisymm ?_ (by simp)
  have := RandPass.pipeline_error_le 0 (names.map (passOf cfg tbl)) ?_ c
  · simpa [tzapRound] using this
  · intro p hp c
    obtain ⟨nm, hnm, rfl⟩ := List.mem_map.1 hp
    exact le_of_eq (passOf_error_eq_zero (by rintro rfl; exact h hnm) cfg tbl c)

theorem tzapRun_error_eq_zero {names : List PassName} (h : PassName.PhaseFoldRand ∉ names)
    (cfg : SuperOptConfig) (tbl : SynthTable) (fuel : Nat) (c : Circuit) :
    (tzapRun cfg tbl names fuel).error c = 0 := by
  refine le_antisymm ?_ (by simp)
  have := RandPass.fixpointShrink_error_le (tzapRound cfg tbl names) 0
    (fun c => le_of_eq (tzapRound_error_eq_zero h cfg tbl c)) fuel c
  simpa [tzapRun] using this

/-- **The optimizer is correct.** For a well-formed circuit, the pipeline's output denotes the
same channel as its input, except on a set of seeds of measure at most `error`. -/
theorem tzapRun_correct (cfg : SuperOptConfig) (tbl : SynthTable) (names : List PassName)
    (fuel : Nat) (c : Circuit) (hc : c.Wf) :
    ((tzapRun cfg tbl names fuel).dist c).toOuterMeasure
        {s | ¬ Equivalent c.numQubits c.numCbits
          ((tzapRun cfg tbl names fuel).run c s).gates c.gates}
      ≤ (tzapRun cfg tbl names fuel).error c :=
  (tzapRun cfg tbl names fuel).correct c hc

/-- **…and exactly correct without the randomized pass.** -/
theorem tzapRun_exact {names : List PassName} (h : PassName.PhaseFoldRand ∉ names)
    (cfg : SuperOptConfig) (tbl : SynthTable) (fuel : Nat) (c : Circuit) (hc : c.Wf)
    {s : (tzapRun cfg tbl names fuel).Seed c}
    (hs : s ∈ ((tzapRun cfg tbl names fuel).dist c).support) :
    Equivalent c.numQubits c.numCbits ((tzapRun cfg tbl names fuel).run c s).gates c.gates :=
  RandPass.correct_of_error_eq_zero _ c hc (tzapRun_error_eq_zero h cfg tbl fuel c) hs

/-- **The run returns a circuit the back end may print**, for any seed: operands in range and
honest `has*` flags, from `RandPass`'s structural obligations. With `Qasm.parse_valid`, which
establishes the same of whatever the front end accepts, this holds from parse to emit. -/
theorem tzapRun_structural (cfg : SuperOptConfig) (tbl : SynthTable) (names : List PassName)
    (fuel : Nat) (c : Circuit) (hc : c.Structural)
    (s : (tzapRun cfg tbl names fuel).Seed c) :
    ((tzapRun cfg tbl names fuel).run c s).Structural :=
  ⟨(tzapRun cfg tbl names fuel).wellFormed_run c s hc.1,
   (tzapRun cfg tbl names fuel).flagsOk_run c s hc.2⟩

/-! ## Running -/

/-- A pass as the driver runs it: a name and a circuit transformation.

`run` is an `IO` action because phase folding draws its tags there — and nowhere else does
the driver touch entropy. -/
structure Step where
  /-- The name shown in the progress output. -/
  name : String
  /-- The transformation. -/
  run : Circuit → IO Circuit

/-- Build the transformation for one pass name.

Each of these is `(passOf cfg tbl nm).run` at the seed drawn for it — see the four `rfl`
theorems below. Nothing else is going on: the driver is the model, executed. -/
def stepOf (cfg : SuperOptConfig) (tbl : SynthTable) : PassName → Step
  | .CancelGates => ⟨"Gate cancellation", fun c => pure (CancelGates.run c)⟩
  | .CnotMin => ⟨"CNOT minimization", fun c => pure (CnotMin.run c)⟩
  | .SuperOpt => ⟨"Superoptimization", fun c => pure (superOpt cfg tbl c)⟩
  | .PhaseFoldRand => ⟨"Phase folding", phaseFoldIO tagBits⟩

theorem stepOf_cancelGates_run (cfg : SuperOptConfig) (tbl : SynthTable) (c : Circuit) :
    CancelGates.run c = (passOf cfg tbl .CancelGates).run c () := rfl

theorem stepOf_cnotMin_run (cfg : SuperOptConfig) (tbl : SynthTable) (c : Circuit) :
    CnotMin.run c = (passOf cfg tbl .CnotMin).run c () := rfl

theorem stepOf_superOpt_run (cfg : SuperOptConfig) (tbl : SynthTable) (c : Circuit) :
    superOpt cfg tbl c = (passOf cfg tbl .SuperOpt).run c () := rfl

theorem stepOf_phaseFold_run (cfg : SuperOptConfig) (tbl : SynthTable) (c : Circuit)
    (s : Sample (varBound c) tagBits) :
    phaseFold tagBits (wordsOf tagBits (padSample s)) c =
      (passOf cfg tbl .PhaseFoldRand).run c s := rfl

/-- How many fixpoint rounds a level allows: `O2` is the cheap bounded tier, the rest run out
fully. -/
def Level.maxRounds : Level → Option Nat
  | .O2 => some 2
  | _ => none

/-! ## Formatting -/

/-- Thousands separators, as Rust's `fmt_num`. -/
def fmtNum (n : Nat) : String :=
  let ds := (toString n).toList
  let grouped :=
    ds.reverse.foldl (fun (acc, i) c =>
      (if i ≠ 0 && i % 3 == 0 then c :: ',' :: acc else c :: acc, i + 1)) ([], 0) |>.1
  String.mk grouped

/-- Seconds to three decimal places. -/
def fmtSecs (nanos : Nat) : String :=
  let ms := nanos / 1000000
  s!"{ms / 1000}.{String.ofList ((toString (ms % 1000)).toList.reverse.take 3 |>.reverse)
      |> fun x => (String.ofList (List.replicate (3 - x.length) '0')) ++ x}"

/-- A percentage reduction from `before` to `after`, one decimal place. -/
def fmtPct (before after : Nat) : String :=
  if before == 0 then "0.0"
  else
    let tenths := ((before - min before after) * 1000) / before
    s!"{tenths / 10}.{tenths % 10}"

/-! ## The run -/

/-- Force a `Nat` before reading the clock.

Lean's `let` is lazy, so a timing that brackets an unforced binding measures the cost of
allocating a thunk and nothing else. `IO.lazyPure` evaluates its thunk when the action runs,
and a `Nat` in weak head normal form is fully evaluated — so forcing a sum of counters forces
the work that produced them. (Branching on the value instead does *not* work: with both arms
equal, the compiler drops the test.) -/
def force (n : Unit → Nat) : IO Unit := do
  let _ ← IO.lazyPure n
  pure ()

/-- Run one pass.

Rust narrates every pass of every round; this reports only the final result. On a fixpoint
run that is a dozen or more lines of intermediate counts replaced by one summary, and the
per-pass timing was only ever useful while tuning the passes themselves — `--verbose` still
prints it. -/
def runStep (verbose : Bool) (st : Step) (c : Circuit) : IO Circuit := do
  if !verbose then
    return ← st.run c
  let t0 ← IO.monoNanosNow
  let out ← st.run c
  let m := Metrics.of out
  force fun _ => m.gates + m.twoQubit + m.depth + m.t + m.rz
  let t1 ← IO.monoNanosNow
  let rzPart := if m.rz > 0 then s!" · {fmtNum m.rz} Rz" else ""
  IO.eprintln s!"  {st.name}"
  IO.eprintln
    s!"\t└─ {fmtNum c.gates.length} → {fmtNum m.gates} gates · {fmtNum m.twoQubit} 2q gates · \
       {fmtNum m.t} T/Tdg{rzPart} · {fmtNum m.depth} depth · {fmtSecs (t1 - t0)}s"
  IO.eprintln ""
  return out

/-- Run every pass once, in order: `RandPass.pipeline`, executed. -/
def runPipeline (verbose : Bool) (steps : List Step) (c : Circuit) : IO Circuit :=
  steps.foldlM (fun acc st => runStep verbose st acc) c

/-- How many rounds a run may take.

`Level.maxRounds` when the level caps them; otherwise `gates + 1`, which is the whole loop:
a round that removes no gate ends it, so no more than `gates` rounds can continue. This is
the `fuel` `tzapRun` is indexed by. -/
def roundFuel (maxRounds : Option Nat) (c : Circuit) : Nat :=
  maxRounds.getD (c.gates.length + 1)

/-- Repeat the pipeline while it keeps removing gates, at most `roundFuel` rounds.

The loop rule is `RandPass.fixpointShrink`'s: run the round, and go again exactly when the
gate count fell (`fixpointShrink_run` states the same equation as a rewrite). What is *not* a
Lean theorem is the correspondence between this `IO` loop and that term — an `IO` action is
opaque to the logic — so it is a correspondence to read, one rule against the other, and the
two are kept adjacent for that reason. -/
def runToFixpoint (verbose : Bool) (steps : List Step) (c : Circuit) (maxRounds : Option Nat) :
    IO Circuit := do
  let mut current := c
  let mut fuel := roundFuel maxRounds c
  let mut round := 0
  repeat
    if fuel = 0 then break
    fuel := fuel - 1
    let before := current.gates.length
    if verbose then IO.eprintln s!"  ── round {round + 1} ──"
    current ← runPipeline verbose steps current
    round := round + 1
    if !(current.gates.length < before) then break
  return current

/-- The result of a run: the counts the banner compares. -/
structure Report where
  /-- The circuit as the pipeline received it. -/
  baseline : Metrics
  /-- The circuit the pipeline returned. -/
  output : Metrics
deriving Repr, Inhabited

/-- Run the optimizer. Builds the synthesis table first when the pipeline needs one, and
draws `PhaseFoldRand`'s tags from `seed` (or the OS, when absent). -/
def optimize (c : Circuit) (o : Options) : IO (Circuit × Report) := do
  let names := o.passes.getD o.level.pipeline
  let (cfg, tcfg) := resolveBounds o
  -- Only pay for a table if some selected pass will consult it.
  let needsTable := names.contains .SuperOpt
  let tbl ← if needsTable then do
      -- Captured before the load below can create the file, so a cold run says so.
      let cached ← TableCache.isCached tcfg
      -- A cold build takes tens of seconds, so it is announced even quietly; a warm load is
      -- fast enough to stay silent unless asked for.
      if !cached then
        IO.eprintln "  🔧 Building superoptimizer table (one-time — cached for future use)..."
      let t0 ← IO.monoNanosNow
      let (tbl, fromCache) ← TableCache.loadOrBuild tcfg
      let total := (List.range (tcfg.maxQubits + 1)).foldl
        (fun acc k => acc + (tbl.widths[k]?.map WidthTable.size |>.getD 0)) 0
      force fun _ => total
      let t1 ← IO.monoNanosNow
      if o.verbose || !fromCache then
        let verb := if fromCache then "Loaded" else "Built"
        IO.eprintln s!"  {verb} superoptimizer table ({fmtNum total} unitaries) in \
                       {fmtSecs (t1 - t0)}s"
        IO.eprintln ""
      pure tbl
    else pure default
  -- `--seed` fixes the generator every draw comes from, rather than substituting a
  -- deterministic stream for the uniform one the bound is about.
  match o.seed with
  | some sd => IO.setRandSeed sd
  | none => pure ()
  let steps := names.map (stepOf cfg tbl)
  let baseline := Metrics.of c
  -- Each branch is `tzapRun cfg tbl names fuel` for the fuel named beside it; a single
  -- `runPipeline` is the `fuel = 1` case, since one round then meets `fixpointShrink 0 = id`.
  let result ←
    if o.passes.isSome then
      if o.fixpoint then runToFixpoint o.verbose steps c none      -- fuel = gates + 1
      else runPipeline o.verbose steps c                           -- fuel = 1
    else if o.level.usesSuperOpt then
      runToFixpoint o.verbose steps c o.level.maxRounds            -- fuel = maxRounds
    else if o.fixpoint then runToFixpoint o.verbose steps c none   -- fuel = gates + 1
    else runPipeline o.verbose steps c                             -- fuel = 1
  return (result, ⟨baseline, Metrics.of result⟩)

end TzapLean
