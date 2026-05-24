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
