// Public type surface of the Guardians kernel, for consumers (e.g. henri's GVE mode).
//
// Self-contained on purpose: a consumer's typechecker resolves `guardians` to THIS
// declaration (via package.json `exports.types`) and, with `skipLibCheck`, does not
// deep-check the verified `src/*.ts`. That is the correct package boundary — guardians'
// source is checked by its own tsconfig + Dafny; a consumer checks only against these
// types. (The proof-carrier functions in src/wf_core.ts have `return true` bodies with
// spec-referenced params, which a consumer's stricter `noUnusedParameters` would
// otherwise flag.) Keep in sync with the `export`s in src/verify.ts.
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

// The high-level seam: marshals the plan onto the verified `Wf` AST (buildWf, proved
// faithful) and runs the proved checks. Consumers gate on the PROVED `taintWf` /
// `automaton` fields, not `ok` (which folds in the unverified `taintPrecise`).
export function verify(wf: Workflow, policy: Policy): Verdict;
