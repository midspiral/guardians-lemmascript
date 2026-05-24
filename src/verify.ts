// UNVERIFIED adapter — the "thin glue" half of the verified-core + adapter split.
//
// It maps a small Guardians-style Workflow + Policy onto the VERIFIED cores and
// returns a verdict in the same shape as Python's guardians.verify(). The
// dataflow tracing and policy encoding here are ordinary (unproven) glue; the
// taint and automaton *decisions* are computed by the proved functions
// `provAfter` (prov_core) and `reachesErrorAbstract` (automaton_core).
//
// Coverage vs Python: taint + automaton. NOT modeled: Z3 preconditions/
// postconditions/frame (a separate check category) — so on a workflow that also
// violates a precondition, Python reports that extra category and we do not.
import { provAfter } from "./prov_core";
import { reachesErrorAbstract } from "./automaton_core";

export type SymRef = { ref: string };
export type Arg = SymRef | string | number;
export type Step = { tool: string; args: Record<string, Arg>; bind?: string };
export type Workflow = { steps: Step[] };
export type TaintRule = { name: string; sourceTool: string; sinkTool: string; sinkParam: string };
export type Policy = {
  allowedTools: string[];
  sources: string[]; // tools whose output is tainted
  sanitizers: string[]; // tools that clear taint
  taintRules: TaintRule[];
  automataOnTool: string[]; // tool names whose call (under a symbolic guard) can reach an error state
};
export type Violation = { category: string; message: string };
export type Result = { ok: boolean; violations: Violation[] };

function isSymRef(a: Arg): a is SymRef {
  return typeof a === "object" && a !== null && "ref" in a;
}

// Glue: the tools (in execution order) whose output transitively feeds `ref`.
function lineage(wf: Workflow, ref: string): string[] {
  const producer = wf.steps.find((s) => s.bind === ref);
  if (!producer) return [];
  const upstream: string[] = [];
  for (const a of Object.values(producer.args)) {
    if (isSymRef(a)) upstream.push(...lineage(wf, a.ref));
  }
  return [...upstream, producer.tool];
}

export function verify(wf: Workflow, policy: Policy): Result {
  const violations: Violation[] = [];

  // Stable int id per tool name, for the verified cores.
  const ids = new Map<string, number>();
  const idOf = (name: string): number => {
    if (!ids.has(name)) ids.set(name, ids.size);
    return ids.get(name) as number;
  };
  for (const s of wf.steps) idOf(s.tool);
  const nameOf = (id: number): string => {
    for (const [n, i] of ids) if (i === id) return n;
    return "";
  };

  // allowlist (pure glue)
  for (const s of wf.steps) {
    if (!policy.allowedTools.includes(s.tool)) {
      violations.push({ category: "allowlist", message: `Tool '${s.tool}' is not in the allowlist` });
    }
  }

  // taint — decided by the VERIFIED prov_core.provAfter.
  const introduces = (t: number, lbl: number): boolean => policy.sources.includes(nameOf(t)) && t === lbl;
  const sanitizes = (t: number, _lbl: number): boolean => policy.sanitizers.includes(nameOf(t));
  for (const rule of policy.taintRules) {
    const sink = wf.steps.find((s) => s.tool === rule.sinkTool);
    if (!sink) continue;
    const arg = sink.args[rule.sinkParam];
    if (!arg || !isSymRef(arg)) continue;
    const chain = lineage(wf, arg.ref).map(idOf); // tools feeding the sink parameter
    if (provAfter(introduces, sanitizes, false, chain, idOf(rule.sourceTool))) {
      violations.push({
        category: "taint",
        message: `Tainted data from '${rule.sourceTool}' flows to '${rule.sinkTool}.${rule.sinkParam}'`,
      });
    }
  }

  // automaton — decided by the VERIFIED automaton_core.reachesErrorAbstract.
  const seq = wf.steps.map((s) => idOf(s.tool));
  for (const tool of policy.automataOnTool) {
    const tId = idOf(tool);
    const isError = (state: number): boolean => state === 1;
    const nextOn = (state: number, t: number, guard: boolean): number => (t === tId && guard ? 1 : state);
    if (reachesErrorAbstract(isError, nextOn, 0, seq)) {
      violations.push({ category: "automaton", message: `Automaton on '${tool}' can reach an error state` });
    }
  }

  return { ok: violations.length === 0, violations };
}
