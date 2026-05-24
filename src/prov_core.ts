// v2: per-source provenance — the actual Guardians taint analysis.
//
// In v0/v1 taint was one bit. Real Guardians tracks WHICH source contributed to
// a value (its lineage), so a taint rule fires only when its source is actually
// present, and a sanitizer clears one specific source (per-rule). We represent a
// value's provenance extensionally: `provAfter(..., lbl)` answers "is `lbl` in
// this value's lineage?". The provenance set is the family over all labels — no
// Set type needed, and the soundness statements stay first-order via
// forall(lbl, ...). `introduces`/`sanitizes` now take the label.
// (`label` is a Dafny keyword, so the parameter is named `lbl`.)
//
// The payoff over single-bit taint is the JOIN: a tool consuming several inputs
// is tainted by a source if ANY input carried it (`joinFlagsContributingSource`),
// which is how taint propagates transitively through multi-input tools — and why
// sanitizing one source leaves the others intact (per-label structure).

// Lineage membership of `lbl` after running `tools` from incoming taint `t0`
// (the per-label projection of the value's provenance set).
export function provAfter(
  introduces: (tool: number, lbl: number) => boolean,
  sanitizes: (tool: number, lbl: number) => boolean,
  t0: boolean,
  tools: number[],
  lbl: number,
): boolean {
  //@ verify
  //@ decreases tools.length
  if (tools.length === 0) return t0;
  const next = sanitizes(tools[0], lbl) ? false : t0 || introduces(tools[0], lbl);
  return provAfter(introduces, sanitizes, next, tools.slice(1), lbl);
}

// Without a sanitizer for `lbl` downstream, an already-present source stays in
// the lineage. (Per-label analog of v0's noSanitizerKeepsTaint.)
export function provKeeps(
  introduces: (tool: number, lbl: number) => boolean,
  sanitizes: (tool: number, lbl: number) => boolean,
  t0: boolean,
  tools: number[],
  lbl: number,
): boolean {
  //@ verify
  //@ requires t0
  //@ requires forall(i, 0 <= i && i < tools.length ==> !sanitizes(tools[i], lbl))
  //@ decreases tools.length
  //@ ensures provAfter(introduces, sanitizes, t0, tools, lbl) === true
  if (tools.length === 0) return true;
  const next = sanitizes(tools[0], lbl) ? false : t0 || introduces(tools[0], lbl);
  return provKeeps(introduces, sanitizes, next, tools.slice(1), lbl);
}

// A sanitizer for `lbl` as the final step clears that source — and only that
// source, since the analysis is per-label. (Per-rule redaction works.)
export function endSanitizerClearsLabel(
  introduces: (tool: number, lbl: number) => boolean,
  sanitizes: (tool: number, lbl: number) => boolean,
  t0: boolean,
  tools: number[],
  lbl: number,
): boolean {
  //@ verify
  //@ requires tools.length > 0
  //@ requires sanitizes(tools[tools.length - 1], lbl)
  //@ decreases tools.length
  //@ ensures provAfter(introduces, sanitizes, t0, tools, lbl) === false
  if (tools.length === 1) return true;
  const next = sanitizes(tools[0], lbl) ? false : t0 || introduces(tools[0], lbl);
  return endSanitizerClearsLabel(introduces, sanitizes, next, tools.slice(1), lbl);
}

// The rule fires for a genuinely present source: if SOME tool introduces `lbl`
// and no tool sanitizes it, that source reaches the end of the pipeline. Unlike
// provKeeps this does not assume incoming taint — the source appears mid-stream,
// so the proof case-splits on whether the head is the source. Pure carrier: its
// induction invokes provKeeps, which a Dafny function body cannot call.
export function introducedSourcePresent(
  introduces: (tool: number, lbl: number) => boolean,
  sanitizes: (tool: number, lbl: number) => boolean,
  tools: number[],
  lbl: number,
): boolean {
  //@ verify
  //@ requires forall(i, 0 <= i && i < tools.length ==> !sanitizes(tools[i], lbl))
  //@ requires exists(i, 0 <= i && i < tools.length && introduces(tools[i], lbl))
  //@ ensures provAfter(introduces, sanitizes, false, tools, lbl) === true
  return true;
}

// THE v2 PAYOFF. A join — a tool consuming the outputs of two prior branches — is
// tainted by `lbl` if EITHER branch contributed it. So a source introduced in
// one input is provably flagged at the join, i.e. taint propagates transitively
// through multi-input tools. Pure carrier: invokes introducedSourcePresent.
export function joinFlagsContributingSource(
  introduces: (tool: number, lbl: number) => boolean,
  sanitizes: (tool: number, lbl: number) => boolean,
  branchA: number[],
  branchB: number[],
  lbl: number,
): boolean {
  //@ verify
  //@ requires forall(i, 0 <= i && i < branchA.length ==> !sanitizes(branchA[i], lbl))
  //@ requires exists(i, 0 <= i && i < branchA.length && introduces(branchA[i], lbl))
  //@ ensures provAfter(introduces, sanitizes, false, branchA, lbl) || provAfter(introduces, sanitizes, false, branchB, lbl)
  return true;
}
