// Verified abstract core of the Guardians taint check.
//
// Guardians (Meijer, "Guardians of the Agents", CACM Jan 2026) verifies an
// agent's workflow BEFORE any tool runs: tainted data from a `source` tool must
// not reach a `sink` parameter. This file proves the heart of that check.
//
// Abstraction (v0): the workflow is a LINEAR pipeline of tool calls `tools`,
// each value carries a single boolean taint, and a tool's effect on taint is
// given by two higher-order parameters — `introduces` (a source) and `sanitizes`
// (a sanitizer, e.g. redact). Nothing else is assumed about them. A thin,
// unverified adapter is what would map the real workflow AST (SymRef bindings,
// per-rule labels) onto this core; the proofs here are generated from this TS.
//
// What is NOT yet modeled: conditionals/loops (where the static check must
// OVER-approximate by unioning branches) and label sets / per-source provenance.
// Those are the next increments — that is where the soundness stops being tight.

// Taint of the value after running `tools` from incoming taint `t0`. A sanitizer
// clears taint outright; otherwise a tool passes taint through and a source adds
// it. This is the static semantics the verifier reasons about.
export function taintAfter(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0: boolean,
  tools: number[],
): boolean {
  //@ verify
  //@ decreases tools.length
  if (tools.length === 0) return t0;
  const next = sanitizes(tools[0]) ? false : t0 || introduces(tools[0]);
  return taintAfter(introduces, sanitizes, next, tools.slice(1));
}

// Monotonicity in the incoming taint: a more-tainted input can only yield a
// more-tainted output. This is the core soundness building block — it says the
// pipeline never "loses track" of upstream taint except through a sanitizer.
export function taintMonotone(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0a: boolean,
  t0b: boolean,
  tools: number[],
): boolean {
  //@ verify
  //@ requires t0a ==> t0b
  //@ decreases tools.length
  //@ ensures taintAfter(introduces, sanitizes, t0a, tools) ==> taintAfter(introduces, sanitizes, t0b, tools)
  if (tools.length === 0) return true;
  const na = sanitizes(tools[0]) ? false : t0a || introduces(tools[0]);
  const nb = sanitizes(tools[0]) ? false : t0b || introduces(tools[0]);
  return taintMonotone(introduces, sanitizes, na, nb, tools.slice(1));
}

// The attack is caught: if data starts tainted and NO tool downstream sanitizes,
// the value is still tainted at the end of the pipeline. So a fetch(source) →
// send(sink) workflow with no redaction is provably flagged by the checker.
export function noSanitizerKeepsTaint(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0: boolean,
  tools: number[],
): boolean {
  //@ verify
  //@ requires t0
  //@ requires forall(i, 0 <= i && i < tools.length ==> !sanitizes(tools[i]))
  //@ decreases tools.length
  //@ ensures taintAfter(introduces, sanitizes, t0, tools) === true
  if (tools.length === 0) return true;
  const next = sanitizes(tools[0]) ? false : t0 || introduces(tools[0]);
  return noSanitizerKeepsTaint(introduces, sanitizes, next, tools.slice(1));
}

// The fix works: a sanitizer as the final step clears taint regardless of any
// upstream source. So inserting redact immediately before send(sink) makes the
// checker accept — and it accepts for a real reason, not by being vacuously lax.
export function endSanitizerClean(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0: boolean,
  tools: number[],
): boolean {
  //@ verify
  //@ requires tools.length > 0
  //@ requires sanitizes(tools[tools.length - 1])
  //@ decreases tools.length
  //@ ensures taintAfter(introduces, sanitizes, t0, tools) === false
  if (tools.length === 1) return true;
  const next = sanitizes(tools[0]) ? false : t0 || introduces(tools[0]);
  return endSanitizerClean(introduces, sanitizes, next, tools.slice(1));
}

// ---------------------------------------------------------------------------
// v1: conditionals — where the static check must OVER-approximate.
//
// A workflow is now a sequence of blocks; a block is either a single tool or a
// conditional whose two branches are linear pipelines. At verification time the
// checker does not know which branch will run, so a conditional taints the value
// if EITHER branch would (a union). The concrete execution takes exactly one
// branch (`chooseThen`). Soundness is therefore no longer tight: we prove the
// abstract result OVER-approximates every concrete run, for ALL branch choices.

type Block =
  | { kind: "tool"; tool: number }
  | { kind: "cond"; thenB: number[]; elseB: number[] };

// Static effect of one block: a tool steps taint; a conditional unions the taint
// of both branch pipelines (over-approximation — neither branch is ruled out).
export function blockAbstract(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0: boolean,
  b: Block,
): boolean {
  //@ verify
  if (b.kind === "tool") return sanitizes(b.tool) ? false : t0 || introduces(b.tool);
  return taintAfter(introduces, sanitizes, t0, b.thenB) || taintAfter(introduces, sanitizes, t0, b.elseB);
}

// Concrete effect of one block: a conditional runs exactly the branch picked by
// `chooseThen`. Quantifying over all `chooseThen` covers every possible run.
export function blockConcrete(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  chooseThen: (b: Block) => boolean,
  t0: boolean,
  b: Block,
): boolean {
  //@ verify
  if (b.kind === "tool") return sanitizes(b.tool) ? false : t0 || introduces(b.tool);
  return chooseThen(b)
    ? taintAfter(introduces, sanitizes, t0, b.thenB)
    : taintAfter(introduces, sanitizes, t0, b.elseB);
}

// Per-block soundness (the base case): one concrete block can only be less
// tainted than the abstract over-approximation of the same block.
export function blockSound(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  chooseThen: (b: Block) => boolean,
  t0: boolean,
  b: Block,
): boolean {
  //@ verify
  //@ ensures blockConcrete(introduces, sanitizes, chooseThen, t0, b) ==> blockAbstract(introduces, sanitizes, t0, b)
  return true;
}

// Per-block monotonicity in incoming taint. The conditional case relies on
// taintAfter being monotone (v0's taintMonotone) along each branch pipeline.
export function blockAbstractMonotone(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0a: boolean,
  t0b: boolean,
  b: Block,
): boolean {
  //@ verify
  //@ requires t0a ==> t0b
  //@ ensures blockAbstract(introduces, sanitizes, t0a, b) ==> blockAbstract(introduces, sanitizes, t0b, b)
  return true;
}

// Fold the static effect across the whole block sequence.
export function workflowAbstract(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0: boolean,
  blocks: Block[],
): boolean {
  //@ verify
  //@ decreases blocks.length
  if (blocks.length === 0) return t0;
  return workflowAbstract(introduces, sanitizes, blockAbstract(introduces, sanitizes, t0, blocks[0]), blocks.slice(1));
}

// Fold one concrete run (a fixed branch-choice function) across the sequence.
export function workflowConcrete(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  chooseThen: (b: Block) => boolean,
  t0: boolean,
  blocks: Block[],
): boolean {
  //@ verify
  //@ decreases blocks.length
  if (blocks.length === 0) return t0;
  return workflowConcrete(introduces, sanitizes, chooseThen, blockConcrete(introduces, sanitizes, chooseThen, t0, blocks[0]), blocks.slice(1));
}

// Whole-sequence abstract monotonicity — carries an incoming-taint implication
// through the entire fold. Needed to compose per-block soundness across steps.
export function workflowAbstractMonotone(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0a: boolean,
  t0b: boolean,
  blocks: Block[],
): boolean {
  //@ verify
  //@ requires t0a ==> t0b
  //@ ensures workflowAbstract(introduces, sanitizes, t0a, blocks) ==> workflowAbstract(introduces, sanitizes, t0b, blocks)
  // Pure carrier: the induction lives in the generated `_ensures` lemma (it must
  // invoke blockAbstractMonotone, which a Dafny *function* body cannot call).
  return true;
}

// THE v1 THEOREM. The static taint result over-approximates every concrete run
// of a branching workflow: for ANY branch-choice function, if the concrete run
// is tainted at the end then the static checker already flagged it. So a clean
// static verdict soundly rules out a tainted sink on every path.
export function workflowSound(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  chooseThen: (b: Block) => boolean,
  t0: boolean,
  blocks: Block[],
): boolean {
  //@ verify
  //@ decreases blocks.length
  //@ ensures workflowConcrete(introduces, sanitizes, chooseThen, t0, blocks) ==> workflowAbstract(introduces, sanitizes, t0, blocks)
  if (blocks.length === 0) return true;
  return workflowSound(introduces, sanitizes, chooseThen, blockConcrete(introduces, sanitizes, chooseThen, t0, blocks[0]), blocks.slice(1));
}
