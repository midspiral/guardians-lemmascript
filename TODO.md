# Potential future work

Where things stand today: the taint argument is proved end-to-end over the real
nested AST (`taint_core` → `prov_core` → `wf_core`) and over unbounded loops
(`loop_core`); security automata have a general soundness proof (`automaton_core`);
the marshalling of a source workflow onto the `Wf` AST is proved verdict-faithful
(`leaksSrcFaithful` in `wf_core`); and `src/verify.ts` runs the proved functions,
with `compare/` differentially testing the verdict against real Python Guardians.
**59 proof obligations, 0 errors.**

The items below are the honest gaps, grouped by what they buy. Rough size: **S**
(a session), **M** (a few), **L** (a project). Pick by goal — coverage (model more
of the paper), precision (tighten proved verdicts), or confidence (validate the
model against the reference).

---

## Coverage — model more of what Guardians checks

### Frame conditions — *L, highest novelty*
The paper's subtlest idea (the frame problem, McCarthy & Hayes 1969): an LLM asked
to delete `foo.txt` and `bar.txt` may emit `delete_file("*.txt")` because it
satisfies the postcondition more cheaply, wiping unintended files. The fix is a
frame condition (`forall file :: file not in glob(pattern) ==> unchanged`), and the
checker must reject *vacuous* frames (e.g. pattern `"*"` protects nothing).
- **Why:** the single biggest unmodeled gap, and the place a Dafny-backed proof has
  the most to add — Python's `DESIGN.md` lists `old()` state, set membership, and
  Dafny integration as *not implemented*.
- **Entry point:** a new `frame_core.ts`. Model a tiny `forall`-frame over an
  abstract file set; prove a non-vacuity lemma and a soundness lemma (a passing
  frame check ⟹ no out-of-pattern file changes). Needs pre/post (`old()`) state.

### General automata in the capstone — *M*
`verifyWfSound` currently uses the demo's automaton shape (`reachesTargetWf` — a
single guarded target, where "reachable" is mere tool membership). `automaton_core`
proves the *general* multi-state, guarded-transition automaton sound, but only over
flat tool **sequences**.
- **Why:** lifts the capstone from the demo shape to real finite-automaton policies.
- **Entry point:** thread automaton state through the nested `Wf` (a `reachesError`
  over `Wf` with state, branch-union of successor states), prove it sound by
  composing with `automaton_core`'s sequence-level result, and swap it into
  `verifyWf`/`verifyWfSound`.

### Scope / well-formedness + allowlist — *S–M, lower novelty*
Python also checks that every `SymRef` is in scope (bound before use, with the
conditional/loop scoping rules in `DESIGN.md`) and that every tool is allowlisted.
- **Why:** completeness against Python's static checks; simpler than the above.
- **Entry point:** an abstract scope-environment fold over `Wf`; prove "well-scoped
  ⟹ every ref resolves at execution." Allowlist is a near-trivial membership pass.

### Z3 preconditions / postconditions — *M*
Beyond frame conditions, Guardians checks tool pre/postconditions via Z3 on literal
args (symbolic ⟹ "could be violated"). Not modeled here at all.
- **Entry point:** likely folds in with the frame-conditions core.

---

## Precision — tighten the proved verdicts

### Make `taintWf` precise (match Python exactly) — *M*
`leaksWf` is order/control-based: it over-flags `fetchThenLiteralSend` (a sink that
runs *after* a source but doesn't consume its data). `taintPrecise` (via
`prov_core.provAfter`) is data-flow-precise and matches Python, but is wired in as a
separate verdict, not proved to be the leak rule.
- **Why:** turns "sound" into "sound *and* precise" — the one visible disagreement
  with Python disappears, with a proof rather than by testing.
- **Entry point:** define a data-flow-precise leak rule over `Wf` (taint flows only
  through `SymRef` lineage, not mere order), prove it sound, and relate it to
  `provAfter`. Then `verify.ts` reports one proved verdict instead of two.

---

## Confidence — validate model fidelity against the reference

### Broaden the differential harness — *S, cheap & high-value*
`compare/scenarios.ts` tests **5** email-agent scenarios. The **loop** core
(`loop_core`) and the **provenance/join** core (`prov_core`) have **no** end-to-end
cross-check against Python at all, and there's no scenario exercising a sanitizer
(`redact`) or deep nesting.
- **Why:** the cheapest way to strengthen the model-fidelity claim that underpins
  every soundness theorem — proofs are only as good as the model, and the model is
  only tied to reality through `compare/`.
- **Entry point:** add scenarios to `compare/scenarios.ts` + `compare/dump_py.py`
  for: a loop that conditionally leaks; a `redact` sanitizer breaking a chain; a
  two-source join (the `prov_core` payoff); a 3-deep nested conditional.

---

## Close the remaining adapter glue

The `taintWf` path is proved except a logic-free hop. Each of these shrinks the last
trusted surface in `src/verify.ts`.

### Prove `buildSrc` (`Step[]` → `SrcList`) faithful — *S*
The 1:1 transcription is a shape copy with no decisions, but it's still trusted.
Bringing it under proof (or a structural round-trip check) closes the gap between
the adapter's input type and `buildWf`'s proved input.

### The `taintPrecise` lineage tracing — *M, the real semantic glue*
`verify.ts`'s `lineage()` walk (which tools transitively feed a sink arg) is the
genuinely semantic piece of remaining glue. Proving it computes real data-flow
lineage requires a spec of dataflow taint — overlaps with "make `taintWf` precise."

### String→int tool interning — *S*
`idOf` maps tool-name strings to the ints the cores use. Logic-free, but document or
prove it's an injective relabeling so it can't collapse distinct tools.

---

## Docs

- ~~A diagram of the verified-core + thin-adapter split.~~ **Done** — the
  architecture/trust-boundary diagram lives canonically in the `README`
  ("Running it…"); `LS_TUTORIAL.md` §6 points to it (single source of truth).
- Once `taintWf` is precise or frame conditions land, update `LS_TUTORIAL.md` §4/§6
  and the `README` boundaries accordingly (including the diagram's PROVED/trusted
  labels).
