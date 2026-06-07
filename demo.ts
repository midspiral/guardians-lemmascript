// Runnable smoke demo: the *verified* functions are ordinary TypeScript and
// execute. This is not the missing end-to-end verifier (no AST/policy/executor) —
// it just calls the proved cores on concrete inputs.
import { taintAfter, workflowAbstract, workflowConcrete } from "./src/taint_core.ts";
import { provAfter } from "./src/prov_core.ts";
import { reachesErrorAbstract, reachesErrorConcrete } from "./src/automaton_core.ts";
import { framePreserved, nonVacuous } from "./src/frame_core.ts";

// Tool ids: 0=fetch_mail (source), 2=send_email (sink), 3=redact (sanitizer).
const introduces = (t: number) => t === 0;
const sanitizes = (t: number) => t === 3;

console.log("== taint (linear) ==");
console.log("fetch -> send         tainted?", taintAfter(introduces, sanitizes, false, [0, 2])); // true: attack
console.log("fetch -> redact -> send tainted?", taintAfter(introduces, sanitizes, false, [0, 3, 2])); // false: fixed

console.log("\n== taint (conditional over-approximation) ==");
// fetch, then a branch: then=[send], else=[redact, send].
const wf = [
  { kind: "tool", tool: 0 },
  { kind: "cond", thenB: [2], elseB: [3, 2] },
];
console.log("static verdict (any path unsafe?)", workflowAbstract(introduces, sanitizes, false, wf)); // true
console.log("concrete run taking SAFE else-branch", workflowConcrete(introduces, sanitizes, () => false, false, wf)); // false
// -> the checker rejects (true) because the then-path leaks, even though this run was clean.

console.log("\n== provenance (two sources + join) ==");
// 10=fetchX(intro X=10), 11=fetchY(intro Y=11). lbl is the source label queried.
const introP = (t: number, lbl: number) => t === lbl; // a fetch tool introduces its own label
const sanP = (_t: number, _lbl: number) => false;
const provJoin = (lbl: number) =>
  provAfter(introP, sanP, false, [10], lbl) || provAfter(introP, sanP, false, [11], lbl);
console.log("join lineage has X(10)?", provJoin(10)); // true
console.log("join lineage has Y(11)?", provJoin(11)); // true
console.log("join lineage has Z(12)?", provJoin(12)); // false

console.log("\n== security automaton (no external send) ==");
// state 0 safe, 1 error; tool 99 = send_email -> error iff guard (recipient external).
const isError = (s: number) => s === 1;
const nextOn = (s: number, t: number, guard: boolean) => (t === 99 && guard ? 1 : s);
const externalRecipient = () => true; // concrete: this send is external
console.log("static: send_email reachable-to-error?", reachesErrorAbstract(isError, nextOn, 0, [99])); // true
console.log("concrete (external recipient) errors?  ", reachesErrorConcrete(isError, nextOn, externalRecipient, 0, [99])); // true
console.log("static: workflow with no send safe?    ", !reachesErrorAbstract(isError, nextOn, 0, [])); // true

console.log("\n== frame conditions (delete_file overreach) ==");
// File ids: 1=foo.txt, 2=bar.txt. Pre: both present (content 1). The agent was told
// to delete foo.txt; an over-broad delete_file("*") wipes BOTH files.
const files = [1, 2];
const pre = (f: number) => (f === 1 || f === 2 ? 1 : 0);
const postOverbroad = (_f: number) => 0; // wiped foo AND bar
const star = (_f: number) => true; // frame from pattern "*"
const scoped = (f: number) => f === 1; // frame = just foo.txt
console.log('"*" frame protects anything?          ', nonVacuous(star, files)); // false: protects nothing
console.log("scoped {foo} frame protects anything? ", nonVacuous(scoped, files)); // true
console.log('"*" frame accepts the over-delete?    ', framePreserved(pre, postOverbroad, star, files)); // true: WAVED THROUGH
console.log("scoped frame accepts the over-delete? ", framePreserved(pre, postOverbroad, scoped, files)); // false: CAUGHT (bar changed, ∉ frame)
