// Library entry point — the importable surface of the verified Guardians cores.
//
// Consumers (e.g. henri's generate-verify-execute mode) link this package and call
// `verify(workflow, policy)`. The taint/automaton DECISIONS inside are the PROVED
// functions: wf_core.buildWf (verdict-faithful marshalling) + wf_core.leaksWf
// (sound leak check), automaton_core.reachesErrorAbstract, prov_core.provAfter.
// See verify.ts for the trust boundary; the per-module proved cores remain
// importable directly (e.g. "guardians/wf_core") for advanced use.
//
// NOTE for consumers gating on safety: read the PROVED `taintWf` (and `automaton`)
// fields of the Verdict. Do NOT gate on `ok` — it is computed from `taintPrecise`,
// the UNVERIFIED binding-provenance verdict (it matches Python but is glue, not a
// theorem). `taintWf` is the sound over-approximation (flags a superset, never less).
export { verify } from "./verify.ts";
export type {
  SymRef,
  Arg,
  ToolStep,
  CondStep,
  Step,
  Workflow,
  TaintRule,
  Policy,
  Verdict,
} from "./verify.ts";

// The proved security-automaton reachability (automaton_core), for consumers that want
// to enforce a sequence/ordering policy directly: `automatonSound` proves a clean static
// verdict (`!reachesErrorAbstract`) means no concrete run reaches an error state.
export { reachesErrorAbstract } from "./automaton_core.ts";
