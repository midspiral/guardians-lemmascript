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
