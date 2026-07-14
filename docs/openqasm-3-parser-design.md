# OpenQASM 3.0 import design

Status: proposed  
Scope: parsing and lowering OpenQASM 3.0 input into TZap's existing circuit model  
Last updated: 2026-07-13

## Decision summary

Add a version-dispatched OpenQASM front end with four explicit stages:

```text
source -> syntax tree -> resolved static program -> lowered Circuit
```

Keep the current OpenQASM 2 parser working while adding a separate OpenQASM 3 path. Use an existing Rust OpenQASM 3 lexer/parser behind a small adapter, then own the semantic analysis and lowering in TZap. The first release should accept the statically resolvable circuit subset that can be represented faithfully by `Circuit`; it should report a precise “valid OpenQASM, unsupported by TZap” diagnostic for dynamic control, timing, calibration, or gates outside TZap's basis.

This separation is the central design choice. OpenQASM 3 parsing is much larger than recognizing new spellings for registers and measurements: its grammar includes scopes, declarations, expressions, gate definitions and modifiers, subroutines, control flow, timing, calibration blocks, and physical qubits. Extending the current semicolon-and-prefix parser would be inexpensive initially but would make correct scoping, expression parsing, diagnostics, and future support disproportionately expensive.

The paper's compilation model also argues for keeping gates, controls, powers, and timing intent structured until a deliberate lowering pass: decomposing them during parsing can both lose semantics and hide later optimization opportunities. The proposed static-operation layer follows that model while remaining small enough for TZap.

## Goals

- Parse the official OpenQASM 3.0 grammar, including enough structure to diagnose unsupported constructs accurately.
- Preserve all existing OpenQASM 2 behavior and the `Circuit::from_qasm(&str)` entry point.
- Lower the common static-circuit interchange subset: virtual qubits, classical bits, standard gates supported by TZap, reset, and measurement.
- Add cheap but meaningful support for compile-time constants, register broadcasting, user-defined gates, and selected gate modifiers.
- Never silently discard a statement that can affect circuit semantics or optimization legality.
- Produce source-spanned errors with a stable distinction between syntax, semantic, include, and lowering failures.
- Bound include expansion, gate expansion, expression evaluation, and loop unrolling so hostile or accidental inputs cannot cause unbounded work.

## Non-goals for the first release

- Executing measurement-dependent `if`/`while` control flow.
- Modeling a real-time classical controller.
- OpenPulse, `cal`, `defcal`, scheduling, durations, `delay`, or `box` semantics.
- Preserving a general OpenQASM 3 program for round-trip serialization.
- Supporting every gate in `stdgates.inc` before the TZap IR can represent or decompose it faithfully.
- Replacing the existing OpenQASM 2 serializer. OpenQASM 3 output is a separate future feature.

## Sources of truth

Implementation and tests should pin behavior to OpenQASM **3.0**, not to the changing live specification.

- [OpenQASM 3.0 specification](https://openqasm.com/versions/3.0/index.html)
- [Official 3.0 lexer and parser grammar](https://openqasm.com/versions/3.0/grammar/index.html)
- [Version strings, comments, and textual includes](https://openqasm.com/versions/3.0/language/comments.html)
- [Types, constants, registers, indexing, and casts](https://openqasm.com/versions/3.0/language/types.html)
- [Gate calls, broadcasting, definitions, built-ins, and modifiers](https://openqasm.com/versions/3.0/language/gates.html)
- [Reset and measurement](https://openqasm.com/versions/3.0/language/insts.html)
- [Classical expressions and control flow](https://openqasm.com/versions/3.0/language/classical.html)
- [Scoping rules](https://openqasm.com/versions/3.0/language/scope.html)
- [Standard library contract](https://openqasm.com/language/standard_library.html), filtered to entries available in version 3.0
- [OpenQASM 3 paper](https://arxiv.org/abs/2104.14722)

The official grammar is a syntactic definition only; it explicitly leaves scope and other semantic rejection to implementations. Grammar acceptance must therefore not be treated as successful import.

## Current TZap constraints

The current implementation has properties that should shape the new front end:

- `src/qasm.rs` is a hand-written OpenQASM 2 parser. It strips comments, splits statements on semicolons, and dispatches with string prefixes.
- `Circuit::from_qasm` returns `Result<Circuit, String>` and always calls that parser.
- `Circuit` is a flat list with qubit and classical-bit counts. It has no blocks, classical variables, conditional edges, timing, source locations, or include identity.
- The IR supports `x`, `h`, `s`, `sdg`, `z`, `t`, `tdg`, `rz`, CNOT, CCX, measurement, and reset. The current parser expands CZ to H-CNOT-H.
- The serializer always emits OpenQASM 2.0 and flattens named registers into one quantum and one classical register.
- The current parser ignores `include` and `barrier` statements. That behavior must not be copied into the OpenQASM 3 path: arbitrary includes can define gates, and a barrier constrains legal optimization.

These constraints mean “support OpenQASM 3” initially means “parse OpenQASM 3 and compile its static, representable subset into the existing IR,” not “represent every OpenQASM 3 program.”

## Proposed architecture

### Module layout

Refactor without changing the public entry point:

```text
src/qasm/
  mod.rs                  version detection, public facade, legacy String errors
  diagnostic.rs           spans, source IDs, structured errors
  qasm2.rs                current parser and serializer, moved mostly unchanged
  qasm3/
    mod.rs                parse options and pipeline orchestration
    syntax.rs             third-party parser adapter; no TZap semantics
    ast.rs                small owned AST used by the remaining stages
    include.rs            stdgates intrinsic and optional include resolver
    resolve.rs            scopes, declarations, names, types, operand shapes
    const_eval.rs         bounded compile-time expression evaluation
    expand.rs             broadcasts, static loops, gate definitions/modifiers
    lower.rs              checked conversion to Circuit/Gate
    stdgates.rs           version-3.0 symbols and lowering recipes
```

`qasm3::syntax` is the only module allowed to expose third-party parser types. This limits dependency churn and makes replacing the parser possible without rewriting name resolution and lowering.

### Front-end dependency

Use the Qiskit-maintained Rust `oq3_lexer`, `oq3_parser`, and `oq3_syntax` crates for the concrete syntax tree, pinned to an exact tested version. They already implement a lossless, source-spanned OpenQASM 3 parser and are a better cost/accuracy tradeoff than transcribing the approximately 500-line official lexer/parser grammar into a second hand-written parser.

Before committing to the dependency, complete a short compatibility spike with these pass/fail checks:

1. It builds on TZap's supported Rust toolchain and has a license compatible with Apache-2.0.
2. It parses a frozen corpus derived from the official 3.0 grammar and examples.
3. It exposes byte ranges for syntax errors and all nodes TZap needs.
4. It does not require Python, ANTLR, generated artifacts at build time, or a large runtime.
5. A minimal QASM file adds acceptable compile time and binary size.

If the spike fails, generate a parser from the official 3.0 ANTLR grammar at release-engineering time and commit the generated Rust source. Do not fall back to growing the existing line parser.

Do not initially depend on the third-party semantic-analysis crate. TZap's semantic target is deliberately narrower, and its lowering rules, resource limits, global-phase policy, and diagnostics need to remain under TZap's control.

### Version dispatch

`qasm::parse` should perform a token-aware pre-scan that skips whitespace and both comment forms, then reads an optional version statement. It must not use a substring search.

- `OPENQASM 2[.0];` dispatches to the unchanged QASM 2 parser.
- `OPENQASM 3;` and `OPENQASM 3.0;` dispatch to the QASM 3 pipeline. Per the 3.0 specification, an omitted minor version means zero.
- Any other explicit major/minor version returns `UnsupportedVersion`.
- For a missing version statement, preserve current behavior by defaulting to QASM 2. Add `ParseOptions::default_version` so callers can choose QASM 3 explicitly.
- A repeated or non-leading version statement is a QASM 3 semantic error.

This preserves existing callers while making version behavior explicit for new APIs.

### Syntax tree and owned AST

The parser adapter should convert only the nodes needed by later stages into a compact, owned AST. Every AST node carries a `Span { source_id, start, end }`.

Important node families are:

- version and include statements;
- declarations (`qubit`, `bit`, legacy `qreg`/`creg`, `const`);
- expressions with the official precedence and associativity;
- indexed operands, sets, slices, and ranges;
- gate calls and modifier lists;
- measurement assignment, legacy measurement arrow, reset, and barrier;
- gate definitions and blocks;
- control-flow and other unsupported statements as typed nodes, not generic text.

Keeping typed unsupported nodes is important: the lowerer can say that `delay` is unsupported at its exact location instead of reporting a misleading parse error.

Calibration bodies are the exception. Preserve their source span and opaque text; the host OpenQASM parser is not expected to parse an OpenPulse body.

## Semantic analysis

### Names and scopes

Use a stack of symbol tables with distinct symbol kinds:

```rust
enum Symbol {
    Qubits(QubitBinding),
    Bits(BitBinding),
    Const(ConstValue),
    Gate(GateDefinition),
    UnsupportedValue(Type),
}
```

Resolve declarations in source order. OpenQASM 3 requires symbols to be declared before use and does not allow forward calls that imply mutual recursion. Detect duplicate declarations, unknown names, kind mismatches, recursive gate expansion, and illegal declaration scopes before lowering.

Virtual quantum and classical registers receive contiguous TZap offsets at declaration time. Keep their original name, width, and span until lowering; flattening early makes diagnostics such as “index 5 is outside `anc[3]`” harder.

### Compile-time values

Evaluate only expressions proven to be compile-time constants. The first release needs:

- decimal, binary, octal, and hexadecimal integers with separators;
- floating-point literals and exponents;
- `pi`/`π`, `tau`/`τ`, and `euler`/`ℇ`;
- parentheses; unary `-`, `!`, and `~` where typed;
- arithmetic, comparison, equality, Boolean, and integer bit operations needed by static expansion;
- casts needed for constant register sizes, indices, gate parameters, and loop bounds;
- the 3.0 built-in constant functions used in gate angles, added incrementally from conformance tests.

Avoid converting angle expressions directly to `f64` during parsing. Represent the common form exactly:

```rust
enum RealConst {
    PiMultiple { numerator: i128, denominator: u128 },
    Float(f64),
}
```

Normalize rational multiples of π after every operation and convert to `f64` only when constructing `Gate::rz`. This cheaply avoids errors in common expressions such as `pi/4 + pi/4`, improves inverse/modifier simplification, and makes equality tests stable. Operations that cannot remain a rational multiple of π fall back to checked `f64` evaluation.

Reject NaN, infinity, division by zero, overflow, negative widths, non-integral indices, and runtime-dependent values with the expression's span. Apply explicit limits to expression depth and exponent size.

### Operand shapes and broadcasting

Resolve each quantum or bit operand to an ordered vector of flat indices. Support single indices and whole registers first; add ranges, sets, aliases, and concatenation later.

For a gate call, follow OpenQASM broadcasting rather than taking a Cartesian product:

1. Find the maximum operand width.
2. Every operand must have width one or that maximum width.
3. A scalar operand is reused for each instance; register operands are zipped by index.
4. Reject duplicate qubits within a single instantiated gate when the gate requires distinct operands.

For measurement, source and destination widths must match after resolution. Both `c = measure q;` and `measure q -> c;` lower to one `Gate::measure` per pair. A measurement with no destination is syntactically valid but cannot be represented by the current IR; reject it until the IR gains an explicit discard form.

### Includes

Treat includes as semantic input, not ignorable metadata.

`include "stdgates.inc";` is intrinsic. It installs exactly the gate names and definitions available in OpenQASM 3.0, with no file-system lookup. Gate names from the standard library are available only after the include; do not implicitly predeclare them.

For arbitrary includes, introduce an injected resolver:

```rust
pub trait IncludeResolver {
    fn resolve(&self, from: SourceId, requested: &str)
        -> Result<ResolvedSource, IncludeError>;
}
```

- `Circuit::from_qasm(&str)` uses a resolver that allows `stdgates.inc` only.
- A new file-oriented API and the CLI use a resolver relative to the including file.
- Track canonical source identity to detect cycles.
- Limit include depth, source count, individual source size, and total expanded bytes.
- Preserve each source separately for diagnostics; includes have textual, source-order semantics but need not be physically concatenated.

The CLI should not allow an included file to escape configured include roots unless the caller opts in.

## Gate expansion and lowering

### Lowering contract

Lowering succeeds only if the resolved program is a finite, static sequence of operations that `Circuit` can represent without changing semantics under TZap's equivalence policy.

The default equivalence policy should be exact up to one whole-program global phase. It must be explicit in `ParseOptions`, because phase-dropping transformations are unsafe inside a later control modifier. In particular, do not lower a gate body modulo global phase and then apply `ctrl @` to the lowered body.

Expansion should operate on a phase-aware intermediate operation:

```rust
enum StaticOp {
    Gate { kind: StaticGate, params: Vec<RealConst>, qubits: Vec<usize>, span: Span },
    Measure { qubit: usize, cbit: usize, span: Span },
    Reset { qubit: usize, span: Span },
    Fence { qubits: Vec<usize>, span: Span },
}
```

Only `lower.rs` converts `StaticOp` to `Circuit`. This avoids baking parser concerns into `Circuit` and leaves room for faithful barrier support later.

### Initial gate mapping

The initial importer can lower these names after their definitions are in scope:

| OpenQASM operation | TZap lowering |
| --- | --- |
| `x`, `h`, `s`, `sdg`, `z`, `t`, `tdg`, `rz` | Direct `Gate` variant |
| `cx`, `CX` | `Gate::cnot` (`CX` only when provided by `stdgates.inc`) |
| `ccx` | `Gate::ccx` |
| `cz` | H-CNOT-H, as today |
| `reset` | One reset per resolved qubit |
| assigned `measure` | One measurement per source/destination pair |

Other 3.0 standard gates should be recognized but rejected as `UnsupportedGate` until one of these is true:

- a tested exact decomposition into the existing basis is available;
- `Circuit::Gate` is extended with the operation; or
- the user explicitly selects a lossy/global-phase equivalence mode that makes the decomposition legal.

Do not label `stdgates.inc` as fully supported when only the table above is lowerable.

### User-defined gates

Support `gate` definitions by hygienically inlining their bodies after name and arity checking:

- bind classical parameters to constant values and formal qubits to resolved operands;
- create a fresh local scope for each expansion;
- permit calls only to earlier definitions and built-ins already in scope;
- reject measurement, reset, classical mutation, or other non-unitary statements in a gate body as required by the language;
- detect direct and indirect recursion even though valid source-order rules should already prevent it;
- cap expansion depth and total emitted operations.

This gives broad compatibility with generator-produced static circuits without expanding `Circuit` itself.

### Gate modifiers

Implement modifiers after ordinary gate calls and definitions work. A cheap useful subset is:

- `inv @`: self-inverse for H/X/Z/CX/CZ/CCX; swap S with Sdg and T with Tdg; negate RZ angles; reverse and invert an expanded gate body.
- `pow(k) @` for a compile-time integer `k`: repeat for positive values, use the inverse for negative values, and emit nothing for zero, subject to expansion limits.
- `ctrl @ x` -> CNOT, `ctrl(2) @ x` -> CCX, and `ctrl @ z` -> the tested CZ decomposition.
- `negctrl @ x`: surround the control with X gates, apply the positive-control form, then undo X.

Reject fractional powers, unsupported controlled gates, and control counts outside the IR basis. Apply modifier nesting in the exact order specified by OpenQASM and cover order-sensitive combinations with conformance tests.

### Static control flow

The parser should recognize all control-flow syntax. The initial lowerer should:

- unroll `for` only when the iterable is a compile-time finite range or set;
- fold `if` only when its condition is a compile-time constant independent of measurements and mutable runtime state;
- reject `while`, `break`, `continue`, and runtime conditions;
- cap unrolled iterations and emitted gates.

Dynamic circuits require a control-flow IR and are not a parser-only change.

### Barriers, timing, and phase

Do not silently drop `barrier`, `delay`, `box`, `cal`, or `defcal`.

- A barrier can be parsed into `StaticOp::Fence`, but lowering must fail until every optimization pass preserves fences or the driver splits optimization into fence-delimited regions.
- Timing and calibration statements receive a targeted `UnsupportedTiming` or `UnsupportedCalibration` diagnostic.
- A top-level, uncontrolled `gphase` can be dropped only under the documented whole-program-global-phase policy. A controlled global phase is observable and must be rejected until represented faithfully.

## Public API

Preserve the existing convenience method:

```rust
impl Circuit {
    pub fn from_qasm(source: &str) -> Result<Self, String>;
}
```

Add a structured API and keep string formatting at the compatibility boundary:

```rust
pub enum QasmVersion { V2_0, V3_0 }

pub struct ParseOptions<'a> {
    pub default_version: QasmVersion,
    pub include_resolver: &'a dyn IncludeResolver,
    pub limits: ParseLimits,
    pub global_phase: GlobalPhasePolicy,
}

pub fn parse_qasm(
    source_name: &str,
    source: &str,
    options: &ParseOptions<'_>,
) -> Result<Circuit, Vec<Diagnostic>>;
```

Diagnostics should contain a stable code, category, message, primary span, optional secondary spans, and notes. Example categories:

- `QASM-SYNTAX-*`
- `QASM-NAME-*`
- `QASM-TYPE-*`
- `QASM-INCLUDE-*`
- `QASM-UNSUPPORTED-*`
- `QASM-LIMIT-*`

The CLI should render `path:line:column`, the source line, and a caret. Library users should be able to render diagnostics themselves.

## Feature rollout

“Parse” below means the syntax tree and typed AST preserve the construct. “Lower” means conversion to the current `Circuit` succeeds.

| Feature | Parse in first merge | Lower in first merge | Follow-up |
| --- | ---: | ---: | --- |
| `OPENQASM 3[.0]` | Yes | Yes | — |
| Comments and whitespace | Yes | Yes | — |
| `qubit[n]`, `bit[n]` | Yes | Yes | Slices/aliases |
| Legacy `qreg`/`creg` | Yes | Yes | — |
| `stdgates.inc` | Yes | Supported subset | More decompositions |
| Arbitrary includes | Yes | CLI/file API | Configurable roots |
| Constant angle expressions | Yes | Yes | Full typed constant functions |
| Gate calls and broadcasting | Yes | Supported gates | Slices/concatenation |
| Measurement assignment/arrow | Yes | Assigned results | Discarded results |
| Reset | Yes | Yes | — |
| Gate definitions | Yes | Static unitary subset | Richer types |
| `inv`, integer `pow`, selected controls | Yes | Selected subset | More bases |
| Static `for` and constant `if` | Yes | Bounded expansion | More iterables |
| Runtime control flow | Yes | No | Requires new IR |
| Barrier | Yes | No | Add optimization fences |
| Physical `$n` qubits | Yes | No | Requires target/layout API |
| `def`, `extern`, input/output, arrays | Yes | No | Requires classical IR |
| Delay, box, duration, stretch | Yes | No | Requires timing IR |
| Calibrations/OpenPulse | Opaque body | No | Separate subsystem |

If schedule pressure is high, the first shippable slice can stop after declarations, constant RZ expressions, direct supported gate calls, reset, and assigned measurement. The architecture should still land with distinct syntax, resolution, and lowering stages so later features do not require another rewrite.

## Testing strategy

### Frozen conformance corpus

Check in small, attributed fixtures derived from the official 3.0 grammar, specification examples, and the version-3.0 standard library. Organize them as:

```text
tests/qasm3/
  parse/pass/
  parse/fail/
  lower/pass/
  lower/unsupported/
  include/
  limits/
```

Every supported feature needs positive and negative cases. Every intentionally unsupported statement needs a test proving that it is diagnosed, not ignored.

### Semantic tests

- Compare lowered gate sequences for hand-checkable programs.
- Test multiple named registers and flat-offset mapping.
- Test scalar/register broadcasting, mismatched widths, empty/invalid ranges, and index boundaries.
- Test declaration-before-use, shadowing, duplicate symbols, gate arities, and recursive expansion.
- Test exact rational-π simplification and one-time conversion to `f64`.
- Test include order, nested relative paths, missing files, cycles, and resource limits.
- Test modifier order and global-phase-sensitive controlled cases.
- Keep the complete OpenQASM 2 test suite unchanged as a regression gate.

### Differential and property testing

In development/CI tooling, parse the same static-subset corpus with an independent OpenQASM 3 implementation and compare success/failure plus normalized AST facts. Do not make Python/Qiskit a runtime dependency.

Add property tests for expression parsing/evaluation and broadcasting. Once the adapter is stable, fuzz lexer/parser input and assert no panic, bounded resource use, valid spans, and deterministic diagnostics.

### End-to-end acceptance examples

At minimum, these forms should import to equivalent `Circuit` values:

```qasm
OPENQASM 3.0;
include "stdgates.inc";

qubit[2] q;
bit[2] c;
h q[0];
cx q[0], q[1];
rz(pi / 4 + pi / 4) q[1];
c = measure q;
```

```qasm
OPENQASM 3;
include "stdgates.inc";

gate bell a, b {
    h a;
    cx a, b;
}

qubit[2] q;
bit[2] c;
bell q[0], q[1];
measure q -> c;
```

A syntactically valid dynamic example must instead fail clearly at lowering:

```qasm
qubit q;
bit result = measure q;
if (result) {
    x q;
}
```

Expected diagnostic: the condition depends on a runtime measurement and cannot be lowered to TZap's static `Circuit` IR.

## Delivery sequence

1. **Dependency and corpus spike:** freeze official 3.0 fixtures, validate the Rust parser dependency, and record compile-size impact.
2. **Architecture refactor:** move the current implementation to `qasm/qasm2.rs`, add token-aware dispatch and structured diagnostics, with no behavior change.
3. **Minimum QASM 3 importer:** declarations, exact constant angles, direct supported gates, broadcasting, reset, and both assigned measurement syntaxes.
4. **Includes and definitions:** intrinsic versioned `stdgates.inc`, file resolver, user gate definitions, expansion limits.
5. **Static language features:** selected modifiers, static `for`, constant `if`, slices and aliases as demanded by real corpora.
6. **IR proposals:** separately design barriers, dynamic control, physical layouts, timing, and OpenQASM 3 serialization. These should not block the static importer.

Each step should be independently releasable and keep OpenQASM 2 tests green.

## Acceptance criteria for “OpenQASM 3 parsing enabled”

- `Circuit::from_qasm` automatically dispatches explicit OpenQASM 2.0 and 3.0 sources.
- The two end-to-end static examples above lower successfully.
- Common QASM 3 output using the supported gate basis, declarations, reset, and measurement imports without preprocessing.
- Unsupported but valid constructs produce a source-spanned `QASM-UNSUPPORTED-*` diagnostic.
- No include, barrier, control-flow, timing, or calibration statement is silently ignored.
- QASM 2 behavior and serialization remain unchanged.
- Parser, include, expression, and expansion resource limits are tested.
- The README states the supported **OpenQASM 3 static subset**, not unqualified “OpenQASM 3 support.”

## Open questions

1. Is whole-program equivalence up to global phase already TZap's formal contract? If not, `p`/`phase`, `gphase`, and some standard-library decompositions must remain unsupported until the IR records global phase.
2. Should barriers become first-class IR nodes, or should the driver optimize independent fence-delimited regions? The latter is likely cheaper but needs care around measurement and reset.
3. Which external tools produce the QASM 3 files users most want to import? Their corpus should determine whether aliases/slices, custom gate definitions, or additional standard gates come immediately after the minimum importer.
4. Should a missing version continue to mean QASM 2 forever, or become an error in a future major TZap release?
