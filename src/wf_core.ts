// v2.5: taint over the REAL recursive workflow AST.
//
// v1 (taint_core.ts) modeled conditionals as `Block = tool | cond` whose
// branches were LINEAR pipelines — no nesting. This file removes that
// restriction: a workflow `Wf` is a recursive datatype where a conditional's
// branches are themselves full workflows, so conditionals nest to any depth.
// `Wf` is a cons-list of operations, each carrying its continuation `rest`:
//   done | tool(tool, rest) | cond(thenB, elseB, rest)
// Recursion is structural over the datatype (Dafny infers termination), exactly
// as in examples/preorder.ts.
//
// The over-approximation and its soundness are re-proved here against this
// faithful AST: the static check unions a conditional's branches (it cannot know
// which runs); the concrete run picks one; a clean static verdict rules out a
// tainted sink on every path, at every nesting depth.

type Wf =
  | { kind: "done" }
  | { kind: "tool"; tool: number; rest: Wf }
  | { kind: "cond"; thenB: Wf; elseB: Wf; rest: Wf };

// Static taint after running `wf` from incoming taint `t0`. A conditional taints
// the value if EITHER branch would (over-approximation), then the result flows
// into the continuation `rest`.
export function taintWf(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0: boolean,
  wf: Wf,
): boolean {
  //@ verify
  //@ decreases wf
  if (wf.kind === "done") return t0;
  if (wf.kind === "tool") {
    const next = sanitizes(wf.tool) ? false : t0 || introduces(wf.tool);
    return taintWf(introduces, sanitizes, next, wf.rest);
  }
  const branched = taintWf(introduces, sanitizes, t0, wf.thenB) || taintWf(introduces, sanitizes, t0, wf.elseB);
  return taintWf(introduces, sanitizes, branched, wf.rest);
}

// Concrete run: a conditional takes exactly the branch chosen by `chooseThen`.
export function taintWfConcrete(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  chooseThen: (wf: Wf) => boolean,
  t0: boolean,
  wf: Wf,
): boolean {
  //@ verify
  //@ decreases wf
  if (wf.kind === "done") return t0;
  if (wf.kind === "tool") {
    const next = sanitizes(wf.tool) ? false : t0 || introduces(wf.tool);
    return taintWfConcrete(introduces, sanitizes, chooseThen, next, wf.rest);
  }
  const branched = chooseThen(wf)
    ? taintWfConcrete(introduces, sanitizes, chooseThen, t0, wf.thenB)
    : taintWfConcrete(introduces, sanitizes, chooseThen, t0, wf.elseB);
  return taintWfConcrete(introduces, sanitizes, chooseThen, branched, wf.rest);
}

// Monotone in incoming taint, over the whole (nested) AST. Pure carrier: the cond
// case must invoke this lemma on the branches to know the branch-union is
// monotone before recursing into `rest` — which a Dafny function body cannot do.
export function taintWfMonotone(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0a: boolean,
  t0b: boolean,
  wf: Wf,
): boolean {
  //@ verify
  //@ requires t0a ==> t0b
  //@ ensures taintWf(introduces, sanitizes, t0a, wf) ==> taintWf(introduces, sanitizes, t0b, wf)
  return true;
}

// THE v2.5 THEOREM. Over the real nested AST: for any branch-choice function, a
// concrete run that ends tainted was already flagged by the static check. So a
// clean static verdict rules out a tainted sink on every path through arbitrarily
// nested conditionals. Pure carrier; structural induction composes branch
// soundness with taintWfMonotone over the continuation.
export function taintWfSound(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  chooseThen: (wf: Wf) => boolean,
  t0: boolean,
  wf: Wf,
): boolean {
  //@ verify
  //@ ensures taintWfConcrete(introduces, sanitizes, chooseThen, t0, wf) ==> taintWf(introduces, sanitizes, t0, wf)
  return true;
}

// The actual taint RULE, not just taint flow: does tainted data reach a SINK
// tool anywhere in the workflow? A sink reached while the taint bit is set is a
// leak; a conditional leaks if either branch leaks, and its branch-taint flows
// into the continuation. `isSink` marks sink tools. (This is the order/control
// model — coarser than data-provenance taint, but it is what we prove sound.)
export function leaksWf(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  isSink: (tool: number) => boolean,
  t0: boolean,
  wf: Wf,
): boolean {
  //@ verify
  //@ decreases wf
  if (wf.kind === "done") return false;
  if (wf.kind === "tool") {
    const here = isSink(wf.tool) && t0;
    const next = sanitizes(wf.tool) ? false : t0 || introduces(wf.tool);
    return here || leaksWf(introduces, sanitizes, isSink, next, wf.rest);
  }
  const branched = taintWf(introduces, sanitizes, t0, wf.thenB) || taintWf(introduces, sanitizes, t0, wf.elseB);
  return (
    leaksWf(introduces, sanitizes, isSink, t0, wf.thenB) ||
    leaksWf(introduces, sanitizes, isSink, t0, wf.elseB) ||
    leaksWf(introduces, sanitizes, isSink, branched, wf.rest)
  );
}

// Concrete run: a conditional leaks via the single branch it actually takes.
export function leaksWfConcrete(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  isSink: (tool: number) => boolean,
  chooseThen: (wf: Wf) => boolean,
  t0: boolean,
  wf: Wf,
): boolean {
  //@ verify
  //@ decreases wf
  if (wf.kind === "done") return false;
  if (wf.kind === "tool") {
    const here = isSink(wf.tool) && t0;
    const next = sanitizes(wf.tool) ? false : t0 || introduces(wf.tool);
    return here || leaksWfConcrete(introduces, sanitizes, isSink, chooseThen, next, wf.rest);
  }
  const branchLeak = chooseThen(wf)
    ? leaksWfConcrete(introduces, sanitizes, isSink, chooseThen, t0, wf.thenB)
    : leaksWfConcrete(introduces, sanitizes, isSink, chooseThen, t0, wf.elseB);
  const branched = chooseThen(wf)
    ? taintWfConcrete(introduces, sanitizes, chooseThen, t0, wf.thenB)
    : taintWfConcrete(introduces, sanitizes, chooseThen, t0, wf.elseB);
  return branchLeak || leaksWfConcrete(introduces, sanitizes, isSink, chooseThen, branched, wf.rest);
}

// Leak detection is monotone in incoming taint. Pure carrier.
export function leaksWfMonotone(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  isSink: (tool: number) => boolean,
  t0a: boolean,
  t0b: boolean,
  wf: Wf,
): boolean {
  //@ verify
  //@ requires t0a ==> t0b
  //@ ensures leaksWf(introduces, sanitizes, isSink, t0a, wf) ==> leaksWf(introduces, sanitizes, isSink, t0b, wf)
  return true;
}

// THE verified taint-rule check over the real nested AST: if any concrete run
// leaks tainted data to a sink, the static check already flagged it. So a clean
// `leaksWf` verdict rules out a tainted sink on every path, at every nesting
// depth — this is the taint decision the adapter can call with a proof behind it.
// Pure carrier; structural induction composing branch soundness, taintWfSound,
// and the two monotonicity lemmas over the continuation.
export function leaksWfSound(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  isSink: (tool: number) => boolean,
  chooseThen: (wf: Wf) => boolean,
  t0: boolean,
  wf: Wf,
): boolean {
  //@ verify
  //@ ensures leaksWfConcrete(introduces, sanitizes, isSink, chooseThen, t0, wf) ==> leaksWf(introduces, sanitizes, isSink, t0, wf)
  return true;
}

// ---------------------------------------------------------------------------
// Unified verifier: taint (leaksWf) AND a security automaton, over the real AST.
//
// The automaton here is the demo's shape — a single absorbing error transition on
// a target tool under a symbolic guard (e.g. no_external_send on send_email). For
// that shape, "an error is reachable" is exactly "the target tool occurs on some
// path", which — because tool membership decomposes over branch-then-continuation
// — needs no state threading and no set-of-states: a clean structural recursion.
// (automaton_core.ts proves the GENERAL automaton over-approximation, over
// sequences; this is its Wf-level lifting for the single-target shape.)

// Static: does a target tool occur on ANY path of the workflow?
export function reachesTargetWf(isTarget: (tool: number) => boolean, wf: Wf): boolean {
  //@ verify
  //@ decreases wf
  if (wf.kind === "done") return false;
  if (wf.kind === "tool") return isTarget(wf.tool) || reachesTargetWf(isTarget, wf.rest);
  return reachesTargetWf(isTarget, wf.thenB) || reachesTargetWf(isTarget, wf.elseB) || reachesTargetWf(isTarget, wf.rest);
}

// Concrete: does a target tool occur on the TAKEN path? (membership over the
// chosen branch then the continuation — both checked independently.)
export function reachesTargetWfConcrete(
  isTarget: (tool: number) => boolean,
  chooseThen: (wf: Wf) => boolean,
  wf: Wf,
): boolean {
  //@ verify
  //@ decreases wf
  if (wf.kind === "done") return false;
  if (wf.kind === "tool") return isTarget(wf.tool) || reachesTargetWfConcrete(isTarget, chooseThen, wf.rest);
  const branch = chooseThen(wf)
    ? reachesTargetWfConcrete(isTarget, chooseThen, wf.thenB)
    : reachesTargetWfConcrete(isTarget, chooseThen, wf.elseB);
  return branch || reachesTargetWfConcrete(isTarget, chooseThen, wf.rest);
}

// The taken path is one of the workflow's paths, so a target on it is a target
// on some path. Pure carrier; structural induction.
export function reachesTargetWfSound(
  isTarget: (tool: number) => boolean,
  chooseThen: (wf: Wf) => boolean,
  wf: Wf,
): boolean {
  //@ verify
  //@ ensures reachesTargetWfConcrete(isTarget, chooseThen, wf) ==> reachesTargetWf(isTarget, wf)
  return true;
}

// The unified STATIC verdict: no taint leak to a sink, and no automaton target
// reachable. This is the Wf-level analogue of Python's guardians.verify().ok.
export function verifyWf(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  isSink: (tool: number) => boolean,
  isTarget: (tool: number) => boolean,
  t0: boolean,
  wf: Wf,
): boolean {
  //@ verify
  return !leaksWf(introduces, sanitizes, isSink, t0, wf) && !reachesTargetWf(isTarget, wf);
}

// THE CAPSTONE. A clean unified verdict rules out, on EVERY concrete path: a taint
// leak to a sink AND an automaton error. Both safety properties from one static
// check over the real nested/looping-free AST. Pure carrier; composes
// leaksWfSound and reachesTargetWfSound.
export function verifyWfSound(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  isSink: (tool: number) => boolean,
  isTarget: (tool: number) => boolean,
  chooseThen: (wf: Wf) => boolean,
  t0: boolean,
  wf: Wf,
): boolean {
  //@ verify
  //@ ensures verifyWf(introduces, sanitizes, isSink, isTarget, t0, wf) ==> (!leaksWfConcrete(introduces, sanitizes, isSink, chooseThen, t0, wf) && !reachesTargetWfConcrete(isTarget, chooseThen, wf))
  return true;
}

// ---------------------------------------------------------------------------
// Marshalling: from a Guardians-style source workflow onto this `Wf` AST.
//
// The adapter (src/verify.ts) receives a workflow as a flat LIST of steps, where
// a conditional step's two branches are THEMSELVES lists and a conditional does
// NOT carry its own continuation (the continuation is the rest of the list). This
// section proves that marshalling that source shape onto `Wf` — collapsing the
// two-level list-of-steps into `Wf`'s unified one-level form — preserves the leak
// verdict at ANY nesting depth. So the adapter can marshal with `buildWf` and
// check with the PROVED `leaksWf` (above), knowing it answers the source
// workflow's own question; composed with leaksWfSound (same module, same leaksWf)
// a clean verdict rules out a tainted sink on every path. The mutually recursive
// datatypes give Dafny structural termination over the nesting with no size measure.

type SrcStep =
  | { kind: "call"; tool: number }
  | { kind: "branch"; thenB: SrcList; elseB: SrcList };

type SrcList =
  | { kind: "nil" }
  | { kind: "cons"; head: SrcStep; tail: SrcList };

// Marshal the source list onto the `Wf` AST: a conditional step becomes a `cond`
// node whose `rest` is the marshalled continuation (the list's tail).
export function buildWf(list: SrcList): Wf {
  //@ verify
  //@ decreases list
  if (list.kind === "nil") return { kind: "done" };
  const head = list.head;
  if (head.kind === "call") return { kind: "tool", tool: head.tool, rest: buildWf(list.tail) };
  return { kind: "cond", thenB: buildWf(head.thenB), elseB: buildWf(head.elseB), rest: buildWf(list.tail) };
}

// The source-level taint semantics (defined directly over the source list,
// independently of the marshalling — the "right question" buildWf must preserve).
export function taintSrc(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0: boolean,
  list: SrcList,
): boolean {
  //@ verify
  //@ decreases list
  if (list.kind === "nil") return t0;
  const head = list.head;
  if (head.kind === "call") {
    const next = sanitizes(head.tool) ? false : t0 || introduces(head.tool);
    return taintSrc(introduces, sanitizes, next, list.tail);
  }
  const branched = taintSrc(introduces, sanitizes, t0, head.thenB) || taintSrc(introduces, sanitizes, t0, head.elseB);
  return taintSrc(introduces, sanitizes, branched, list.tail);
}

// The source-level leak semantics (does tainted data reach a sink), over the list.
export function leaksSrc(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  isSink: (tool: number) => boolean,
  t0: boolean,
  list: SrcList,
): boolean {
  //@ verify
  //@ decreases list
  if (list.kind === "nil") return false;
  const head = list.head;
  if (head.kind === "call") {
    const here = isSink(head.tool) && t0;
    const next = sanitizes(head.tool) ? false : t0 || introduces(head.tool);
    return here || leaksSrc(introduces, sanitizes, isSink, next, list.tail);
  }
  const branched = taintSrc(introduces, sanitizes, t0, head.thenB) || taintSrc(introduces, sanitizes, t0, head.elseB);
  return (
    leaksSrc(introduces, sanitizes, isSink, t0, head.thenB) ||
    leaksSrc(introduces, sanitizes, isSink, t0, head.elseB) ||
    leaksSrc(introduces, sanitizes, isSink, branched, list.tail)
  );
}

// Marshalling preserves taint, at every nesting depth. Pure carrier: the branch
// case must invoke this lemma on the sub-lists (a Dafny function body cannot).
export function taintSrcFaithful(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0: boolean,
  list: SrcList,
): boolean {
  //@ verify
  //@ ensures taintWf(introduces, sanitizes, t0, buildWf(list)) === taintSrc(introduces, sanitizes, t0, list)
  return true;
}

// THE MARSHALLING THEOREM. The marshalled AST's PROVED leak check (leaksWf) agrees
// with the source workflow's own leak semantics, for conditionals nested to ANY
// depth — so buildWf does not distort the question leaksWf answers. Composed with
// leaksWfSound (above, the same leaksWf), the adapter's marshalling + check is
// backed end-to-end: a clean verdict rules out a tainted sink on every path.
// Pure carrier; structural induction composing taintSrcFaithful and the leak
// recursion over branches and continuation.
export function leaksSrcFaithful(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  isSink: (tool: number) => boolean,
  t0: boolean,
  list: SrcList,
): boolean {
  //@ verify
  //@ ensures leaksWf(introduces, sanitizes, isSink, t0, buildWf(list)) === leaksSrc(introduces, sanitizes, isSink, t0, list)
  return true;
}
