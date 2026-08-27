import TzapLean.SuperOptProof
import TzapLean.PhaseFoldRand
import TzapLean.Qasm
import TzapLean.TableCache

/-!
# The Optimizer Driver

A port of the parts of `src/optimize.rs` this development can support: the optimization
levels, the pass names selectable by `--passes`, the fixpoint loop, and the metrics the CLI
reports.

Three of the four passes are `Pass`es and carry their proofs. `PhaseFoldRand` is a `RandPass`,
so it is *not* a `Pass` at any fixed seed — that is the whole content of `RandPass.lean` — and
the driver runs it at a seed drawn once per invocation. So the pipeline here is a list of
plain `Circuit → Circuit` functions, not a list of `Pass`es: what each one carries is recorded
in `PassName.verified` and reported by `--passes-info`, rather than silently implied.

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

/-- A pass as the driver runs it: a name and a circuit transformation. -/
structure Step where
  /-- The name shown in the progress output. -/
  name : String
  /-- The transformation. -/
  run : Circuit → Circuit

/-- Build the transformation for one pass name. -/
def stepOf (draws : Draws 64) (cfg : SuperOptConfig) (tbl : SynthTable) : PassName → Step
  | .CancelGates => ⟨"Gate cancellation", CancelGates.run⟩
  | .CnotMin => ⟨"CNOT minimization", CnotMin.run⟩
  | .SuperOpt => ⟨"Superoptimization", superOpt cfg tbl⟩
  | .PhaseFoldRand => ⟨"Phase folding", phaseFold draws⟩

/-- The pipeline a level runs, when `--passes` is absent.

`CnotMin` leads the sweep: it re-synthesizes whole CNOT-dihedral blocks, reshaping the circuit
far more than the peephole rewriter does, and the passes after it work on the result. -/
def Level.pipeline : Level → List PassName
  | .O1 => [.CancelGates, .PhaseFoldRand]
  | _ => [.CnotMin, .CancelGates, .SuperOpt, .PhaseFoldRand]

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
  s!"{ms / 1000}.{String.mk ((toString (ms % 1000)).toList.reverse.take 3 |>.reverse)
      |> fun x => (String.mk (List.replicate (3 - x.length) '0')) ++ x}"

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

/-- Run one pass, printing the line Rust's `pass_done` prints. -/
def runStep (st : Step) (c : Circuit) : IO Circuit := do
  let t0 ← IO.monoNanosNow
  let out := st.run c
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

/-- Run every pass once, in order. -/
def runPipeline (steps : List Step) (c : Circuit) : IO Circuit :=
  steps.foldlM (fun acc st => runStep st acc) c

/-- Repeat the pipeline until the gate count stops decreasing, or `maxRounds` rounds have
run. -/
def runToFixpoint (steps : List Step) (c : Circuit) (maxRounds : Option Nat) : IO Circuit := do
  let mut current := c
  let mut round := 0
  repeat
    let before := current.gates.length
    IO.eprintln s!"  ── round {round + 1} ──"
    current ← runPipeline steps current
    round := round + 1
    let reduced := current.gates.length < before
    if !reduced then break
    if maxRounds.any (round ≥ ·) then break
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
      if cached then
        IO.eprint "  Loading superoptimizer table..."
      else
        IO.eprintln "  🔧 Building superoptimizer table (one-time — cached for future use)..."
      let t0 ← IO.monoNanosNow
      let (tbl, fromCache) ← TableCache.loadOrBuild tcfg
      let total := (List.range (tcfg.maxQubits + 1)).foldl
        (fun acc k => acc + (tbl.widths[k]?.map WidthTable.size |>.getD 0)) 0
      force fun _ => total
      let t1 ← IO.monoNanosNow
      let verb := if fromCache then "Loaded" else "Built"
      if cached then IO.eprint "\r"
      IO.eprintln s!"  {verb} superoptimizer table ({fmtNum total} unitaries) in \
                     {fmtSecs (t1 - t0)}s"
      IO.eprintln ""
      pure tbl
    else pure default
  let seed ← match o.seed with
    | some s => pure s
    | none => do
        let a ← IO.rand 0 (2 ^ 31 - 1)
        let b ← IO.rand 0 (2 ^ 31 - 1)
        pure (a * (2 ^ 31) + b)
  let draws : Draws 64 := seedDraws seed
  let steps := names.map (stepOf draws cfg tbl)
  let baseline := Metrics.of c
  let result ←
    if o.passes.isSome then
      if o.fixpoint then runToFixpoint steps c none else runPipeline steps c
    else if o.level.usesSuperOpt then
      runToFixpoint steps c o.level.maxRounds
    else if o.fixpoint then runToFixpoint steps c none
    else runPipeline steps c
  return (result, ⟨baseline, Metrics.of result⟩)

end TzapLean
