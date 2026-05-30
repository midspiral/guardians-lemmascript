// UNVERIFIED adapter — the "thin glue" half of the verified-core + adapter split.
//
// Maps a small Guardians-style Workflow + Policy (now with conditionals) onto the
// VERIFIED cores and returns verdicts. It reports TWO taint verdicts:
//
//   taintPrecise — binding-provenance, via prov_core.provAfter over the lineage
//                  of the sink argument. Matches Python's data-flow taint.
//   taintWf      — the PROVED taint-rule check. The workflow is marshalled by
//                  wf_core.buildWf and checked by leaksWf, BOTH proved:
//                  wf_core.leaksSrcFaithful proves the marshalling preserves
//                  the source workflow's leak verdict at any nesting depth, and
//                  wf_core.leaksWfSound proves a clean verdict rules out a tainted
//                  sink on every path. This is the order/control model: a SOUND
//                  OVER-APPROXIMATION of Python's analysis — it flags a superset,
//                  and may conservatively over-flag (e.g. a sink that runs after a
//                  source but does not consume its data).
//
// What remains unproved glue: the Step[] -> source-datatype transcription
// (buildSrc, a 1:1 shape copy), the lineage tracing for taintPrecise, and the
// string->int tool interning. The marshalling into the Wf AST and the taint /
// automaton DECISIONS are the proved functions. NOT modeled: Z3 preconditions.
import { provAfter } from "./prov_core";
import { buildWf, leaksWf } from "./wf_core";
import { reachesErrorAbstract } from "./automaton_core";

export type SymRef = { ref: string };
export type Arg = SymRef | string | number;
export type ToolStep = { tool: string; args: Record<string, Arg>; bind?: string };
export type CondStep = { cond: string; thenSteps: Step[]; elseSteps: Step[] };
export type Step = ToolStep | CondStep;
export type Workflow = { steps: Step[] };
export type TaintRule = { name: string; sourceTool: string; sinkTool: string; sinkParam: string };
export type Policy = {
  allowedTools: string[];
  sources: string[];
  sanitizers: string[];
  taintRules: TaintRule[];
  automataOnTool: string[];
};
export type Verdict = { ok: boolean; taintPrecise: boolean; taintWf: boolean; automaton: boolean };

// Mirrors wf_core's source `SrcList`/`SrcStep` datatypes structurally, so the
// value built here is assignable to the PROVED buildWf's parameter.
type SrcStep =
  | { kind: "call"; tool: number }
  | { kind: "branch"; thenB: SrcList; elseB: SrcList };
type SrcList =
  | { kind: "nil" }
  | { kind: "cons"; head: SrcStep; tail: SrcList };

function isSymRef(a: Arg): a is SymRef {
  return typeof a === "object" && a !== null && "ref" in a;
}
function isCond(s: Step): s is CondStep {
  return "cond" in s;
}

// Flatten to the tool steps in both branches (for sink lookup, lineage, automaton).
function allToolSteps(steps: Step[]): ToolStep[] {
  const out: ToolStep[] = [];
  for (const s of steps) {
    if (isCond(s)) out.push(...allToolSteps(s.thenSteps), ...allToolSteps(s.elseSteps));
    else out.push(s);
  }
  return out;
}

// Tools (in order) whose output transitively feeds `ref`.
function lineage(tsteps: ToolStep[], ref: string): string[] {
  const producer = tsteps.find((s) => s.bind === ref);
  if (!producer) return [];
  const up: string[] = [];
  for (const a of Object.values(producer.args)) if (isSymRef(a)) up.push(...lineage(tsteps, a.ref));
  return [...up, producer.tool];
}

// Transcribe the Step[] into wf_core's source list datatype — a 1:1 shape copy
// (cons/tail, branch sub-lists, string->int interning), with NO restructuring.
// The load-bearing collapse into wf_core's `Wf` AST is wf_core.buildWf, which is
// PROVED verdict-faithful, so this transcription is the only marshalling glue left.
function buildSrc(steps: Step[], idOf: (n: string) => number): SrcList {
  if (steps.length === 0) return { kind: "nil" };
  const head = steps[0] as Step;
  const tail = buildSrc(steps.slice(1), idOf);
  if (isCond(head)) {
    const branch: SrcStep = { kind: "branch", thenB: buildSrc(head.thenSteps, idOf), elseB: buildSrc(head.elseSteps, idOf) };
    return { kind: "cons", head: branch, tail };
  }
  return { kind: "cons", head: { kind: "call", tool: idOf(head.tool) }, tail };
}

export function verify(wf: Workflow, policy: Policy): Verdict {
  const ids = new Map<string, number>();
  const idOf = (n: string): number => {
    if (!ids.has(n)) ids.set(n, ids.size);
    return ids.get(n) as number;
  };
  const nameOf = (id: number): string => {
    for (const [n, i] of ids) if (i === id) return n;
    return "";
  };
  const tsteps = allToolSteps(wf.steps);
  for (const s of tsteps) idOf(s.tool);

  const isSourceId = (t: number): boolean => policy.sources.includes(nameOf(t));
  const sanitizesId = (t: number): boolean => policy.sanitizers.includes(nameOf(t));

  // taintPrecise — binding provenance via the VERIFIED prov_core.provAfter.
  let taintPrecise = false;
  for (const rule of policy.taintRules) {
    const sink = tsteps.find((s) => s.tool === rule.sinkTool);
    if (!sink) continue;
    const arg = sink.args[rule.sinkParam];
    if (!arg || !isSymRef(arg)) continue;
    const chain = lineage(tsteps, arg.ref).map(idOf);
    const introducesL = (t: number, lbl: number): boolean => isSourceId(t) && t === lbl;
    const sanitizesL = (t: number, _lbl: number): boolean => sanitizesId(t);
    if (provAfter(introducesL, sanitizesL, false, chain, idOf(rule.sourceTool))) taintPrecise = true;
  }

  // taintWf — the PROVED taint-rule check: transcribe to the source datatype, then
  // marshal (PROVED buildWf) and check (PROVED leaksWf). leaksSrcFaithful ties the
  // verdict to the source workflow's own semantics; leaksWfSound makes it safety.
  const wfData = buildWf(buildSrc(wf.steps, idOf));
  let taintWf = false;
  for (const rule of policy.taintRules) {
    const introducesR = (t: number): boolean => t === idOf(rule.sourceTool) && isSourceId(t);
    const isSink = (t: number): boolean => t === idOf(rule.sinkTool);
    if (leaksWf(introducesR, sanitizesId, isSink, false, wfData)) taintWf = true;
  }

  // automaton — via the VERIFIED automaton_core.reachesErrorAbstract over the tool sequence.
  const seq = tsteps.map((s) => idOf(s.tool));
  let automaton = false;
  for (const tool of policy.automataOnTool) {
    const tId = idOf(tool);
    const isError = (st: number): boolean => st === 1;
    const nextOn = (st: number, t: number, guard: boolean): number => (t === tId && guard ? 1 : st);
    if (reachesErrorAbstract(isError, nextOn, 0, seq)) automaton = true;
  }

  return { ok: !(taintPrecise || automaton), taintPrecise, taintWf, automaton };
}
