# DESIGN — frame conditions for the Guardians checker

> **The thing that must never break.** A tool that declares a frame ("I only touch
> files matching pattern `P`") cannot quietly change a file outside `P` — and a
> *vacuous* frame (pattern `*`, which protects nothing) is provably rejected, not
> silently accepted. The `delete_file("foo.txt", "bar.txt")` → `delete_file("*")`
> catastrophe is ruled out by the checker, with a machine-checked reason.

**Status:** _Phases A + B done._ Phase A spike verified (7/0); Phase B landed —
`src/frame_core.ts` is the TS-sourced core, regenerated and verified by Dafny
(`frame_core.dfy`, 11 verified / 0 errors), wired into `LemmaScript-files.txt`, the
README verify loop, and `demo.ts`; the throwaway spike is retired to `../bak/`.
Stages 2–3 below remain. (The full `check.sh dafny` run is green across all six cores.)
**Category:** a **coverage increment** to [guardians-lemmascript](README.md) — a new
verified core `frame_core`, in the same pure-functional, HOF-parametric idiom as
[`loop_core`](src/loop_core.ts) and [`taint_core`](src/taint_core.ts). It models the
one part of Erik Meijer's *"Guardians of the Agents"* (CACM Jan 2026) the existing
cores skip, and the part the reference Python explicitly lists as **not
implemented** (its `DESIGN.md` names `old()` state, set membership, and Dafny
integration as future work). This is where a Dafny-backed proof has the most to add.

---

## 1. Motivation — the frame problem (McCarthy & Hayes, 1969)

An agent is told to delete `foo.txt` and `bar.txt`. The LLM, satisfying the
postcondition as cheaply as it can, emits `delete_file("*.txt")` — or worse,
`delete_file("*")` — and wipes files nobody asked it to touch. The postcondition
("`foo.txt` and `bar.txt` are gone") is *met*; the damage is everything else.

A **postcondition says what must become true; a frame condition says what is allowed
to change.** The fix Guardians wants is

```
forall file . file ∉ glob(pattern) ⟹ file unchanged
```

with a crucial side check: the frame itself must be **non-vacuous**. A frame whose
pattern matches *everything* (`*`) constrains nothing — `file ∉ glob("*")` is never
true, so the implication is vacuously satisfied by any post-state, including one that
deleted the whole disk. So the checker has two jobs: enforce the frame, **and**
refuse a frame that protects nothing.

That pairing — *enforce* + *reject-the-vacuous* — is exactly the shape of the
"sound, and the obvious shortcut isn't" results elsewhere in this portfolio
(`Strictness`/`Domination` in the ESLint rule, `FixedWindowLeaks` in the rate
limiter, the `scopeNaive` `OR`-leak). It is a genuine plausible-but-wrong a machine
should catch, not a tautology.

## 2. The pure-functional move — "old is identity"

The frame problem is classically stated with `old()`: compare the post-execution
state to the state *before* the call. The imperative reflex is to model the file
system as a mutable object and reach for Dafny's heap `old()` with `reads`/`modifies`
clauses — which is both the ugly corner of Dafny **and** not what LemmaScript emits
(LS generates *pure* functions; `\old(x)` is not expressible in a `//@` spec — see
`[[feedback_no_old_in_ls_annotations]]`).

We sidestep all of it. In a pure model there is no temporal indirection: the
pre-state is just a **value**, threaded as a parameter, exactly the way
[`loop_core`](src/loop_core.ts) threads `t0` and `iterTaint(.., n)` carries "the
state after `n` iterations" as a plain argument. `old(state)` collapses to the
identity on the value we are already holding — we name it `pre` and never invoke
`old()`. The frame condition becomes a first-order relation between two values,
`pre` and `post`, with no heap, no `reads`/`modifies`, and no toolchain gap.

(One could literally define `function old<T>(x: T): T { x }` so the spec text mirrors
the paper. It buys nothing but confusion — skip it; just name the parameter `pre`.)

## 3. The verified core — `frame_core`

Abstract just enough to make the theorem load-bearing and nothing more, matching the
opaque-HOF style of the existing cores (`introduces`/`sanitizes` are uninterpreted;
so is the glob here):

- **File universe** — `files: number[]`, the finite set of files in play (a workflow
  references finitely many). Modelling the universe as a `seq` keeps every predicate
  a **recursive fold** (like `taintAfter`), hence executable *and* `//@`-verifiable —
  no unbounded `forall f` ghost predicate, no `.dfy`-only spec migration.
- **State** — `state: (file: number) => number`, the content of each file (`0` = absent).
  `pre`, `post` are two such functions. "`f` unchanged" is just `pre(f) === post(f)`,
  which covers deletion (content → `0`) and modification uniformly.
- **Frame** — `inFrame: (file: number) => boolean`, the uninterpreted glob membership
  (`glob(pattern)` abstracted to a predicate; the string-pattern → predicate mapping is
  the *adapter's* job, named in §6).

```ts
// Outside the frame, nothing changed. Recursive fold over the file universe.
export function framePreserved(
  pre: (file: number) => number,
  post: (file: number) => number,
  inFrame: (file: number) => boolean,
  files: number[],
): boolean {
  //@ verify
  //@ decreases files.length
  if (files.length === 0) return true;
  const f = files[0];
  const ok = inFrame(f) ? true : pre(f) === post(f);
  return ok && framePreserved(pre, post, inFrame, files.slice(1));
}

// The frame actually protects at least one file (¬ "matches everything").
export function nonVacuous(inFrame: (file: number) => boolean, files: number[]): boolean {
  //@ verify
  //@ decreases files.length
  if (files.length === 0) return false;
  return !inFrame(files[0]) || nonVacuous(inFrame, files.slice(1));
}
```

## 4. Theorems

The load-bearing pair (both parametric, both `//@`-expressible, both pure carriers
with the induction in the generated `_ensures` lemma — the `[[reference_ls_pure_carrier_lemma]]`
shape):

1. **Vacuity protects nothing (T1).** If every file in the universe is in the frame
   (`pattern == "*"`), then `framePreserved` holds for **any** `pre`/`post` — so the
   frame proves nothing and the checker must reject it.
   `requires forall(i, 0<=i<files.length ==> inFrame(files[i]))`,
   `ensures framePreserved(pre, post, inFrame, files)`.
2. **Out-of-frame change is caught (T2).** If some file is out of frame and changed,
   `framePreserved` is `false` — the over-deletion is flagged.
   `requires !inFrame(files[k]) && pre(files[k]) !== post(files[k])` (with `0<=k<len`),
   `ensures !framePreserved(pre, post, inFrame, files)`.

T1 + T2 *are* the dominance result: a vacuous frame catches nothing, a scoped frame
catches every out-of-frame change. The checker is sound **and** the shortcut (accept
a `*` frame) provably fails.

3. **Dominance, machine-checked (T3 — `frameDominance`).** Shipped not as a hardcoded
   trace but as a *parametric* theorem: for **any** `(pre, post, files)` and witness
   index `k`, if `star` matches everything and `scoped` excludes a changed file
   `files[k]`, then `star` `framePreserved`-passes (waved through — via T1) while
   `scoped` fails (caught — via T2). The `delete_file("*")` story as a theorem; the
   concrete foo/bar trace is the runnable demonstration in `demo.ts`.

**Stage 2 — frame ∧ postcondition.** Model the tool's postcondition as a predicate
`wants(post, files)` ("`foo` is absent"). Prove: `wants(post) && framePreserved(scoped)`
pins `bar` to `pre` (the unintended file survives), while `wants(post) &&
framePreserved(star)` does **not** — the formal version of "the LLM picks `*` because
it satisfies the postcondition more cheaply." This is the increment that ties frames
to the postconditions the rest of Guardians already reasons about.

**Stage 3 — capstone integration (deferred).** Thread a per-tool frame declaration
through the `Wf` AST and extend `verifyWfSound` so a clean verdict *also* rules out
out-of-frame mutation on every path — the analogue of folding general automata into
the capstone (TODO.md). Heavier (needs frame decls in the AST); standalone core first,
exactly as `loop_core` landed standalone before any capstone wiring.

## 5. Dafny-first workflow (the prototyping path)

The proofs here are quantifier/induction reasoning over a new datatype shape, and we
don't yet know which obligations Dafny discharges automatically vs. which need an
explicit witness or `_ensures` recursion. So we settle the math in **raw Dafny first**,
where the edit/verify loop is seconds and there is no generation or merge friction —
*then* back-port the (now-known-good) model to TypeScript. The shipped artifact stays
TS-sourced (verification means LemmaScript — `[[feedback_verification_means_lemmascript]]`);
Dafny is scaffolding, not the deliverable.

**Phase A — spike in `src/frame_spike.dfy` (hand-written, throwaway).** Mirror the
`loop_core.dfy` conventions (HOFs as `(int) -> bool`, `seq<int>`, pure-carrier +
`lemma`). Iterate with `dafny verify src/frame_spike.dfy` until green:

```dafny
function framePreserved(pre: (int)->int, post: (int)->int, inFrame: (int)->bool, files: seq<int>): bool
  decreases |files|
{
  if |files| == 0 then true
  else (if inFrame(files[0]) then true else pre(files[0]) == post(files[0]))
       && framePreserved(pre, post, inFrame, files[1..])
}

function nonVacuous(inFrame: (int)->bool, files: seq<int>): bool
  decreases |files|
{ if |files| == 0 then false else !inFrame(files[0]) || nonVacuous(inFrame, files[1..]) }

// T1 — a "*" frame protects nothing: any post passes.
lemma vacuousProtectsNothing(pre: (int)->int, post: (int)->int, inFrame: (int)->bool, files: seq<int>)
  requires forall i :: 0 <= i < |files| ==> inFrame(files[i])
  ensures framePreserved(pre, post, inFrame, files)
  decreases |files|
{ if |files| == 0 {} else { vacuousProtectsNothing(pre, post, inFrame, files[1..]); } }

// T2 — any out-of-frame change is caught.
lemma outOfFrameChangeCaught(pre: (int)->int, post: (int)->int, inFrame: (int)->bool, files: seq<int>, k: int)
  requires 0 <= k < |files| && !inFrame(files[k]) && pre(files[k]) != post(files[k])
  ensures !framePreserved(pre, post, inFrame, files)
  decreases |files|
{ if k == 0 {} else { outOfFrameChangeCaught(pre, post, inFrame, files[1..], k - 1); } }

// T3 — delete_file("*") catastrophe, concretely. foo=1, bar=2; both wiped.
lemma deleteStarCatastrophe()
{
  var pre    := (f: int) => (if f == 1 || f == 2 then 1 else 0);
  var post   := (f: int) => 0;          // wiped BOTH
  var star   := (f: int) => true;       // pattern "*"
  var scoped := (f: int) => f == 1;     // frame = {foo}
  var files  := [1, 2];
  vacuousProtectsNothing(pre, post, star, files);
  assert framePreserved(pre, post, star, files);      // WAVED THROUGH
  outOfFrameChangeCaught(pre, post, scoped, files, 1); // bar (index 1) changed, ∉ scoped
  assert !framePreserved(pre, post, scoped, files);    // CAUGHT
}
```

(These empty bodies **verify as-is** — `dafny verify src/frame_spike.dfy` →
7 verified, 0 errors, no hints. Should a future variation need a nudge, the usual fix
is an explicit witness `assert !inFrame(files[k]);` to instantiate the `exists`, and
spell hand-written proof vars clear of reserved names — `[[reference_dafny_reserved_words_in_proofs]]`.)

**Phase B — back-port to `src/frame_core.ts` + regen.** Once the spike is green,
transcribe the model into TS (§3) with `//@ verify`/`//@ ensures` (quantifiers as
`forall(i, P)` / `exists(i, P)` — `[[reference_lemmascript_quantifier_syntax]]`), the
theorems as pure carriers (`return true`, induction in the generated `_ensures`).
Then, from inside the case-study dir (`[[reference_lsc_invocation]]`):

```sh
node ../LemmaScript/tools/dist/lsc.js regen --backend=dafny src/frame_core.ts
../LemmaScript/tools/check.sh dafny
```

Use `regen` (merges proof additions), never `rm`+`gen` (`[[feedback_use_regen_not_rm]]`).
The only hand-added content in `frame_core.dfy` is the three `_ensures` proof bodies
(the T1/T2 inductions copied from the spike, each with `decreases |files|` per
`loop_core`'s convention; T3's `frameDominance_ensures` just composes them) —
**additions** to the generated file, the sanctioned model
(`[[feedback_prove_long_way_over_ugly_ls_feature]]`), not orphan Dafny. The back-port
*generalized* the spike's concrete `deleteStarCatastrophe` into the parametric
`frameDominance` carrier, with the concrete trace becoming the `demo.ts` scenario.
Mind the pure-carrier regen gotcha: a function-body shape change breaks the merge —
`cp .gen → .dfy` and reapply (`[[reference_ls_pure_carrier_lemma]]`). Finally add
`src/frame_core.ts` to `LemmaScript-files.txt`, the README `Verify` loop, and a
`demo.ts` section (the concrete foo/bar trace); retire `frame_spike.dfy` to `../bak/`.

## 6. Trust boundary — verified vs. trusted

- **Verified** (pure, over the file universe): `framePreserved` / `nonVacuous`, T1
  (vacuity protects nothing), T2 (out-of-frame change caught), T3 (concrete
  catastrophe), and Stage 2's frame ∧ postcondition.
- **Trusted (named, not hidden):**
  - **Glob fidelity.** `inFrame` is uninterpreted; that a real pattern string maps to
    the right membership predicate (`glob("*.txt")` ⟷ `inFrame`) is the dominant
    assumption — the same kind of unverified adapter glue as the rest of guardians
    (`src/verify.ts`'s interning / lineage), and the analogue of graph-extraction in
    the ESLint rule. The proof is about the *frame logic*, not the globber.
  - **File-universe completeness.** We reason over the `files` actually in play; a
    file the model never lists is outside the claim. The shell must supply the
    universe honestly.
  - **State abstraction.** Content as `(file) => number` models presence/edit; richer
    effects (permissions, partial writes) are out of scope.

No "verified end-to-end." The proven artifact is: *given a faithful glob predicate and
the files in play, a declared frame cannot hide an out-of-frame change, and a frame
that protects nothing is rejected.*

## 7. Architecture

```
  (frame_spike.dfy)     Phase A. Hand-written Dafny prototype of T1–T3. RETIRED to ../bak/.
  src/frame_core.ts     Phase B. VERIFIED. State/glob model, framePreserved,
                        nonVacuous, T1/T2 carriers, (T3). Pure. //@-annotated.
  src/frame_core.dfy.gen / .dfy   generated + hand-added _ensures proof bodies.
```

## 8. Staged plan

| Stage | Lands | Status |
|---|---|---|
| **A — Dafny spike** | `frame_spike.dfy`: `framePreserved`/`nonVacuous` + T1, T2, T3 green | ✅ **done** (7 VCs, 0 errors) |
| **B — TS back-port** | `frame_core.ts` + regen; T1/T2/T3 as `//@` carriers; wired into Verify loop + demo | ✅ **done** (11 VCs, 0 errors) |
| **2 — frame ∧ postcondition** | `wants(post)` + the "cheaper postcondition picks `*`" theorem | _planned_ |
| **3 — capstone integration** | per-tool frame decl threaded through `Wf`; `verifyWfSound` extended | _deferred_ |

**Spike gate:** Stage A — **passed.** The pitch rested on "enforce the frame *and*
reject the vacuous one, both proven"; T1+T2+T3 are green clean in raw Dafny with no
hints, so the spine holds and Phase B is a mechanical transcription.
