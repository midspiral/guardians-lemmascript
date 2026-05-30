# A LemmaScript tutorial: what this repo proves, and why it matters

This is a guided tour of the proofs in `guardians-lemmascript`. The
[`README`](README.md) lists the theorems; this document teaches you to *read* them —
the method (how a LemmaScript proof is written and checked), the recurring shape
(every theorem is the same three-part story), and then the content, built up in the
order the cores were written. By the end you should be able to open any `src/*_core.ts`
and know exactly what it claims and what the claim is worth.

No Dafny or LemmaScript background is assumed.

---

## 1. The one-sentence idea: verify the verifier

[Guardians](https://github.com/metareflection/guardians) (Erik Meijer, ["Guardians of
the Agents", CACM Jan 2026](https://cacm.acm.org/practice/guardians-of-the-agents/))
checks an agent's tool workflow *before* it runs, so that tainted data from a `source`
tool can never reach a `sink` parameter, and so that a guarded tool never fires on a
forbidden argument. That checker is an *algorithm*. The Python repo *implements* it and
trusts it (100 tests).

This repo asks the next question: **is the checking algorithm actually sound?** If the
static check passes, is the workflow *really* safe — on every input, every policy, every
runtime path, not just the ones a test happened to try? That is a statement with
universal quantifiers in it, and the only way to know it holds is to *prove* it. So:

> Python is a verifier — it answers "is *this* workflow safe?"
> This repo verifies the verifier — it proves "the check is sound for *all* workflows."

The proofs are machine-checked by [Dafny](https://dafny.org/). You do not have to trust
them; you (or CI) re-run Dafny and it either accepts every proof or it doesn't.

---

## 2. How a LemmaScript proof is written and checked

You never write Dafny by hand. You write **TypeScript** with a few `//@` annotation
comments, and the LemmaScript compiler (`lsc`) does the translation. The pipeline for
each core file `f`:

```
src/f.ts  ──lsc regen──▶  src/f.dfy.gen   (generated: the translation + the proof
   │                          │            obligations, regenerated, never hand-edited)
   │                          │
   └─ you complete ─────▶  src/f.dfy       (the .dfy.gen PLUS the inductive proof
                                            bodies you add — the only handwritten Dafny)
                              │
                          Dafny verifies f.dfy  ✓ / ✗
```

`f.dfy.gen` is a faithful, mechanical translation of your TypeScript — claims and all —
but with the proof bodies left as holes. `f.dfy` is that same file with the holes
filled. CI regenerates `.dfy.gen` from the `.ts` and checks it still matches (so the
`.ts` and the proof can never silently drift apart), then runs Dafny on `.dfy`.

### The annotations

Everything the prover needs lives in `//@` comments, so the `.ts` stays valid,
type-checkable TypeScript:

| annotation | meaning |
|---|---|
| `//@ verify` | translate & verify this function |
| `//@ requires P` | precondition — assume `P` on entry |
| `//@ ensures Q` | postcondition — **this is the claim being proved** |
| `//@ decreases E` | termination measure (`E` strictly decreases each recursive call) |
| `//@ type n nat` | refine a parameter's type (here `number` → natural number) |
| `forall(i, …)`, `exists(i, …)` | quantifiers, usable inside `requires`/`ensures` |

A function with no `ensures` (like `taintAfter`) is just a **definition** — it gives the
prover something to reason *about*. A function with an `ensures` is a **theorem**: the
`ensures` is the proposition, and the function body (plus, often, a generated lemma) is
the proof.

### A worked micro-example

Take `taintMonotone` from [`src/taint_core.ts`](src/taint_core.ts) — "a more-tainted
input can only produce a more-tainted output":

```ts
export function taintMonotone(introduces, sanitizes, t0a, t0b, tools): boolean {
  //@ verify
  //@ requires t0a ==> t0b
  //@ decreases tools.length
  //@ ensures taintAfter(introduces, sanitizes, t0a, tools)
  //@      ==> taintAfter(introduces, sanitizes, t0b, tools)
  if (tools.length === 0) return true;
  const na = sanitizes(tools[0]) ? false : t0a || introduces(tools[0]);
  const nb = sanitizes(tools[0]) ? false : t0b || introduces(tools[0]);
  return taintMonotone(introduces, sanitizes, na, nb, tools.slice(1));
}
```

The recursion *is* the induction: the empty-list case is the base case, and the
recursive call is the induction hypothesis applied to the tail. `lsc` turns this into a
Dafny lemma; the proof it generates into `taint_core.dfy` is exactly the structural
induction —

```dafny
decreases |tools|
if |tools| == 0 {
} else {
  var na := (if sanitizes(tools[0]) then false else (t0a || introduces(tools[0])));
  var nb := (if sanitizes(tools[0]) then false else (t0b || introduces(tools[0])));
  taintMonotone_ensures(introduces, sanitizes, na, nb, tools[1..]);   // ← IH on the tail
}
```

The base case is empty because it is trivially true; the step invokes the lemma on
`tools[1..]`. That recursive call to `..._ensures` is the induction hypothesis. Dafny
checks the whole thing.

### "Pure carriers"

You will notice many theorems have a body of just `return true`, with the real work in
the `ensures`:

```ts
export function taintWfSound(introduces, sanitizes, chooseThen, t0, wf): boolean {
  //@ verify
  //@ ensures taintWfConcrete(...) ==> taintWf(...)
  return true;   // ← the proof is NOT here
}
```

This is the **pure-carrier** pattern. A Dafny *function* body cannot call a lemma, but
many inductive proofs must invoke *another* lemma (an induction hypothesis on a subtree,
or a helper like `taintMonotone`). So `lsc` emits a separate `*_ensures` **lemma** for
the proof, and the TypeScript body is just a placeholder carrying the signature. When you
see `return true`, the proof lives in the generated `_ensures` lemma in the matching
`.dfy` — and it is allowed to compose other lemmas there. The code comments say which
ones (e.g. *"composes leaksWfSound and reachesTargetWfSound"*).

---

## 3. The shape every theorem has: abstract ⊇ concrete

Once you internalize this one pattern, every file reads the same way. Each safety
property is told as **three functions**:

| role | what it is | example (the taint leak rule) |
|---|---|---|
| **abstract** | what the *static checker* computes from the plan, *without* running it. Where the future is unknown (a branch, a guard, a loop count) it **over-approximates** — it assumes the worst reachable case. | `leaksWf` |
| **concrete** | what an *actual run* does, parameterized by the unknowns (`chooseThen` picks each branch, `guardHolds` resolves each guard, `n` is the iteration count). | `leaksWfConcrete` |
| **soundness** | the theorem tying them: `concrete ==> abstract`. If a real run is bad, the static checker already flagged it. | `leaksWfSound` |

The soundness direction is the one that matters for security: **`concrete ⟹ abstract`**.
Contrapositive: `¬abstract ⟹ ¬concrete` — *a clean static verdict means no concrete run
is bad.* That is precisely the license Guardians needs to admit a workflow before it runs.

The crucial move is that the unknowns are **universally quantified higher-order
parameters**. `chooseThen : (Wf) => boolean` is *any* branch-choice function; the theorem
ranges over all of them at once, so "clean verdict ⟹ safe" holds on **every path**, not
some sampled paths. Likewise `introduces`, `sanitizes`, `isSink`, `isTarget`, `nextOn`,
`guardHolds` are arbitrary — nothing is assumed about which tools are sources or sinks,
so each theorem holds for *every* policy assignment. There is no condition DSL to trust:
the semantics of a guard or a branch is just an opaque function the proof quantifies over.

Why over-approximate at all? Because the checker runs *before* the data exists. It cannot
know which branch a conditional will take or whether a guard will hold, so it explores
**all** possibilities and reports trouble if **any** of them is bad. Soundness is the
guarantee that this can only ever be *too cautious*, never too lax: it may reject a safe
workflow (a false alarm), but it will never admit an unsafe one. For a security check,
that is exactly the right direction to err.

---

## 4. What was proved, core by core

The cores were written as increments, each relaxing one simplifying assumption of the
last. Read them in this order.

### v0 — `taint_core.ts`: taint over a linear pipeline (single bit)

The simplest model: a workflow is a flat list of tools, a value carries one boolean of
taint, `introduces` marks sources, `sanitizes` marks sanitizers. `taintAfter` folds the
taint along the list. Four theorems pin down that this model behaves:

- **`taintMonotone`** — more incoming taint ⟹ more outgoing taint. Taint is never
  silently lost (only a sanitizer clears it). This is the load-bearing lemma every later
  soundness proof leans on.
- **`noSanitizerKeepsTaint`** — start tainted, no sanitizer downstream ⟹ still tainted at
  the end. So an un-redacted `fetch`(source) → `send`(sink) pipeline is *provably* flagged.
- **`endSanitizerClean`** — a sanitizer as the final step clears taint regardless of
  upstream sources. So the fix (insert `redact` before the sink) is *provably* accepted —
  and accepted for a real reason, not because the checker is vacuously lax.

### v1 — `taint_core.ts` (lower half): conditionals, and the first over-approximation

Now a workflow is a sequence of **blocks**, where a block is a tool *or* a conditional
whose two branches are pipelines. The checker cannot know which branch runs, so a
conditional's abstract taint is the **union** of both branches (`blockAbstract`); a
concrete run takes exactly one branch, chosen by `chooseThen` (`blockConcrete`).

- **`workflowSound`** — the first real over-approximation theorem: for **any**
  branch-choice function, a concrete run that ends tainted was already flagged by the
  static union. A clean static verdict rules out a tainted result on *every* branch. The
  proof composes per-block soundness (`blockSound`) with whole-sequence monotonicity
  (`workflowAbstractMonotone`, which leans on `taintMonotone`).

### v2 — `prov_core.ts`: per-source provenance (the *real* Guardians analysis)

Single-bit taint is too coarse: real Guardians tracks **which** source contributed to a
value, so a rule fires only when *its* source is in the lineage, and a sanitizer clears
*one* source. Provenance is represented per-label — `provAfter(…, lbl)` answers "is `lbl`
in this value's lineage?" — so the set is the family over all labels, and the soundness
statements stay first-order (`forall(lbl, …)`).

- **`introducedSourcePresent`** — a source introduced anywhere with no sanitizer
  downstream really does reach the end (the rule fires for genuinely-present sources).
- **`joinFlagsContributingSource`** — the payoff a single bit cannot express: a **join**
  (a tool consuming several inputs) is tainted by a source if *any* input carried it. This
  is taint propagating transitively through multi-input tools — and the per-label
  structure is exactly why sanitizing one source leaves the others intact.

### v2.5 — `wf_core.ts`: the real recursive AST, and the capstone

v1's conditionals had *linear* branches. This file removes that last restriction: a
workflow is a recursive datatype

```ts
type Wf = { kind: "done" }
        | { kind: "tool"; tool: number; rest: Wf }
        | { kind: "cond"; thenB: Wf; elseB: Wf; rest: Wf };
```

so a conditional's branches are themselves full workflows — **conditionals nest to any
depth**. Termination is structural over the datatype (`//@ decreases wf`). Everything is
re-proved over this faithful AST:

- **`taintWfSound`** — over-approximation soundness, now at every nesting depth. Structural
  induction composing branch soundness with `taintWfMonotone` over the continuation `rest`.
- **`leaksWfSound`** — soundness of the actual *taint rule* ("does tainted data reach a
  **sink**?", not just "is the value tainted"), over the nested AST. **This is the taint
  decision the adapter calls with a proof behind it.**
- **`reachesTargetWfSound`** — for the demo's automaton shape (a target tool under a
  symbolic guard), "error reachable" reduces to "target tool occurs on some path"; the
  taken path is one of the workflow's paths, so this decomposes structurally with no state
  threading.
- **`verifyWfSound`** — **the capstone** (see §5).

### v3 — `automaton_core.ts`: security automata in general

Guardians' other check is a finite automaton over the tool-call sequence, with guarded
transitions into error states. At verification time a guard's truth is unknown (symbolic
args), so the static analysis explores **both** outcomes of each guard
(`reachesErrorAbstract`); the concrete run follows the actual guard
(`reachesErrorConcrete`). Guards are HOF parameters — any automaton, no DSL.

- **`automatonSound`** — if any concrete run reaches an error state, the static checker
  (which explored all guard choices) already found a path to error.
- **`automatonSafeVerdict`** — the usable contrapositive: a clean static verdict ⟹ the
  concrete run never errors, for *any* data. This is the general result that
  `reachesTargetWf` specializes for the demo's single-target shape.

### v-loops — `loop_core.ts`: unbounded loops via a fixpoint

A conditional is a *finite* union of branches; a loop is a body that runs an *unbounded*
number of times, so a finite union no longer suffices — you need a **fixpoint** argument.
The key fact for a single taint bit, with `bodyTaint` monotone:

> `sat := t0 ‖ bodyTaint(t0)` is a one-step **pre-fixpoint**: `bodyTaint(sat) ⟹ sat`.

So `sat` soundly bounds the exit taint after *any* number of iterations — **no iteration
to a fixpoint is required**, one step suffices.

- **`satPrefixpoint`** — the pre-fixpoint fact above.
- **`loopExitSound`** — taint after `n` iterations is bounded by `sat`, for every `n`
  (induction on `n`, via `bodyMonotone` + the pre-fixpoint).
- **`loopLeakSound`** — if any iteration leaks, the body leaks from `sat`; so the static
  check `leaksBody(sat, body)` rules out a leak at *every* iteration count.

This is the one place the formalization arguably goes *deeper* than the Python reference:
"a loop is sound because `sat` is a pre-fixpoint" is the kind of claim tests cannot
establish — it quantifies over all iteration counts at once.

### marshalling — `wf_core.ts` (lower half): connecting the proved core to a real workflow

Every soundness theorem above assumes the workflow has *already* been turned into a `Wf`.
But a real `Workflow`/`Policy` arrives at the adapter ([`src/verify.ts`](src/verify.ts)) as
a flat **list of steps**, where a conditional step's two branches are themselves lists and
a conditional does *not* carry its own continuation (the continuation is the rest of the
list). Something has to **marshal** that shape onto `Wf` — and if the marshalling is wrong,
`leaksWfSound` is proving the right answer to the *wrong question*. So the marshalling
itself is proved, in the same file as the check it feeds.

The source shape is modeled with mutually recursive datatypes (which give Dafny structural
termination over the nesting for free — no size measure):

```ts
type SrcStep = { kind: "call"; tool: number }
             | { kind: "branch"; thenB: SrcList; elseB: SrcList };
type SrcList = { kind: "nil" }
             | { kind: "cons"; head: SrcStep; tail: SrcList };
```

`buildWf : SrcList → Wf` does the real work: it **collapses** this two-level
list-of-steps into `Wf`'s unified one-level form, pulling each conditional's continuation
(the list tail) into the `cond` node's `rest`. `leaksSrc` is the leak rule defined
*directly* on the source list — the "right question", independent of the marshalling.

- **`leaksSrcFaithful`** — the marshalling theorem: `leaksWf(buildWf(list)) === leaksSrc(list)`,
  at **any** nesting depth. So `buildWf` does not distort the question `leaksWf` answers.
  Because it lives in the *same module* as `leaksWfSound`, about the *same* `leaksWf`, the
  two compose with no copy that could drift: source workflow → `buildWf` (faithful) →
  `leaksWf` (sound) → safe on every path. (Structural induction; `taintSrcFaithful` handles
  the branch-union taint along the way.)

This is what lets the adapter call the proved functions and *mean* it. What still isn't
proved is the last, logic-free hop: `verify.ts` transcribes its `Step[]` into `SrcList`
1:1 (`buildSrc`) and interns string tool-names to ints — a shape copy with no decisions,
small enough to read by eye. (See §6, boundary 1.)

---

## 5. The capstone, in full

The headline theorem is **`verifyWfSound`** in [`src/wf_core.ts`](src/wf_core.ts). It
unifies both static checks into one verdict and proves that verdict sound. The static
check is:

```ts
verifyWf(introduces, sanitizes, isSink, isTarget, t0, wf)
  = !leaksWf(introduces, sanitizes, isSink, t0, wf)   // no taint leak to a sink
  && !reachesTargetWf(isTarget, wf);                  // no guarded target reachable
```

and the theorem's `ensures`, in full:

```
verifyWf(introduces, sanitizes, isSink, isTarget, t0, wf)
  ==> ( !leaksWfConcrete(introduces, sanitizes, isSink, chooseThen, t0, wf)
        && !reachesTargetWfConcrete(isTarget, chooseThen, wf) )
```

with **all** of `introduces, sanitizes, isSink, isTarget, chooseThen, t0, wf` universally
quantified. In words:

> For **every** workflow, **every** assignment of which tools are sources / sanitizers /
> sinks / guarded targets, **every** starting taint, and **every** way the conditionals
> branch at runtime (`chooseThen`) — if the static check `verifyWf` passes, that execution
> neither feeds tainted data into a sink nor fires a guarded tool.

Quantifying `chooseThen` is what makes "safe" hold on **every path**, not just a sampled
one. The proof is a pure carrier composing `leaksWfSound` and `reachesTargetWfSound`.

---

## 6. Why this is significant — and the honest boundaries

**A proof says something tests can't.** 100 passing tests show the checker is right on 100
workflows. `verifyWfSound` shows it is right on *all* of them — every AST shape, every
policy, every runtime path — and Dafny re-checks that mechanically in CI. The interesting
failure mode of a static security checker is the input nobody thought to test; a
universally-quantified, machine-checked soundness theorem is exactly the tool for that.

**Sound over-approximation is the right bias.** Every theorem here proves
`concrete ⟹ abstract` — the checker may be *too* cautious (reject a safe workflow) but
never too lax (admit an unsafe one). For security that asymmetry is a feature: a false
alarm costs a rejected plan; a missed leak costs the breach.

**The two repos are complementary, not redundant.** Python is the runnable system and the
behavioral **oracle**; this repo proves a faithful abstraction of its core checks is
sound. [`compare/`](compare/) closes the loop by differentially testing this repo's
verdicts against real Python Guardians, so the *model* is empirically tied to the
*implementation* it abstracts.

It is just as important to be precise about what the proof does **not** cover — the
trust hasn't vanished, it has *moved* to three smaller, namable places:

1. **A thin slice of the adapter is still unverified.** A real `Workflow`/`Policy` reaches
   the proved cores through [`src/verify.ts`](src/verify.ts). The *decisions* (`leaksWf`,
   `provAfter`, `reachesErrorAbstract`) **and** the *marshalling* onto the `Wf` AST
   (`buildWf`, proved verdict-faithful by `leaksSrcFaithful`) are now both proved. What
   remains trusted is the logic-free hop in between: the 1:1 transcription of `verify.ts`'s
   `Step[]` into the source datatype and the string→int interning of tool names — a shape
   copy with no decisions — plus the `taintPrecise` lineage tracing. The unverified surface
   is now small enough to read by eye, not a whole reimplementation.
2. **Model fidelity is assumed, not proved.** The proofs are airtight *about the model*.
   Whether the model faithfully captures Guardians' real semantics is a separate question,
   validated only empirically (by `compare/`). Notably, `leaksWf` is *order/control-based*
   taint — a sound over-approximation of data-flow taint that can flag more than Python's
   provenance analysis (e.g. a sink that runs after a source but does not consume its
   data). Sound, but coarser.
3. **Some checks aren't modeled at all.** Z3 preconditions / postconditions / frame
   conditions, the allowlist, and scope checks live only in Python. Frame conditions in
   particular — the paper's frame-problem fix (`delete_file("*.txt")` satisfying the
   postcondition too cheaply) — are arguably its subtlest idea and are untouched here; a
   natural target for the next round of proofs.

In short: this repo proves the *heart* of the Guardians safety argument — taint
(single-bit, per-source, nested, and looping) and security automata — is sound for all
inputs, and is honest about the seams where unverified glue and unmodeled checks remain.

---

## 7. Reproduce it yourself

```sh
# one-time: get the LemmaScript toolchain next to this repo
git clone https://github.com/midspiral/LemmaScript.git ../LemmaScript
cd ../LemmaScript/tools && npm ci && cd -

# regenerate the .dfy.gen from each .ts, then verify every .dfy with Dafny
for f in taint_core prov_core automaton_core wf_core loop_core; do
  node ../LemmaScript/tools/dist/lsc.js regen --backend=dafny src/$f.ts
done
../LemmaScript/tools/check.sh dafny
```

A green run means Dafny has re-checked every proof in this document from scratch. To see
the abstraction tested against the Python reference end-to-end, see
[`compare/`](compare/) and the "diffing against Python" section of the [`README`](README.md).

### Where to look next

| you want to… | open |
|---|---|
| see the simplest complete proof | `taintMonotone` in [`src/taint_core.ts`](src/taint_core.ts) |
| see what a generated inductive proof looks like | diff `src/taint_core.dfy.gen` against `src/taint_core.dfy` |
| read the capstone | `verifyWfSound` in [`src/wf_core.ts`](src/wf_core.ts) |
| see the fixpoint argument | `satPrefixpoint` / `loopExitSound` in [`src/loop_core.ts`](src/loop_core.ts) |
| see the marshalling proved faithful | `leaksSrcFaithful` in [`src/wf_core.ts`](src/wf_core.ts) |
| see the proofs meet a real workflow | [`src/verify.ts`](src/verify.ts) (the thin adapter) |
