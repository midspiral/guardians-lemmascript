// Verified frame conditions for the Guardians checker.
//
// Guardians (Meijer, "Guardians of the Agents", CACM Jan 2026) checks an agent's
// workflow before any tool runs. A POSTCONDITION says what must become true; a
// FRAME condition says what is allowed to CHANGE. Without it, an LLM told to delete
// foo.txt and bar.txt may emit delete_file("*") — the postcondition is met, but
// every other file is gone. The frame the paper wants is
//   forall file. file not-in glob(pattern) ==> file unchanged
// with one essential side check: the frame must be NON-VACUOUS. A pattern that
// matches everything ("*") makes `file not-in glob` never hold, so it is satisfied
// by ANY post-state, including one that wiped the disk. The checker must enforce the
// frame AND refuse a frame that protects nothing. This file proves both.
//
// "old is identity": the frame problem is classically stated with old() — compare
// the post-state to the pre-state. We never reach for heap old()/reads/modifies
// (the ugly corner of Dafny, and not what LS emits — \old isn't //@-expressible).
// In a pure model the pre-state is just a VALUE, threaded as a parameter exactly the
// way loop_core threads `t0`. So `pre` and `post` are two ordinary functions and the
// frame condition is a first-order relation between them.
//
// Model: the file universe is a finite `files` list (a workflow touches finitely
// many), so every predicate is a recursive FOLD (like taintAfter) — executable and
// //@-verifiable, no unbounded-forall ghost predicate. State is `(file) => number`
// content (0 = absent), so "unchanged" (pre(f) === post(f)) covers deletion and edit
// uniformly. `inFrame` is the uninterpreted glob membership — the string-pattern ->
// predicate mapping is the (named) trusted adapter, as elsewhere in guardians.

// Outside the frame, nothing changed. Fold over the file universe.
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

// The frame protects at least one file (it is not the "matches everything" pattern).
export function nonVacuous(inFrame: (file: number) => boolean, files: number[]): boolean {
  //@ verify
  //@ decreases files.length
  if (files.length === 0) return false;
  return !inFrame(files[0]) || nonVacuous(inFrame, files.slice(1));
}

// T1 — a "*" frame protects nothing: if every file in the universe is in the frame,
// `framePreserved` holds for ANY pre/post. So a frame the checker can satisfy this
// way proves nothing, and must be rejected. Pure carrier; induction in _ensures.
export function vacuousProtectsNothing(
  pre: (file: number) => number,
  post: (file: number) => number,
  inFrame: (file: number) => boolean,
  files: number[],
): boolean {
  //@ verify
  //@ requires forall(i, 0 <= i && i < files.length ==> inFrame(files[i]))
  //@ ensures framePreserved(pre, post, inFrame, files)
  return true;
}

// T2 — any out-of-frame change is caught: if some file is outside the frame and its
// content changed, `framePreserved` is false. The over-deletion is flagged. Pure
// carrier; induction in _ensures.
export function outOfFrameChangeCaught(
  pre: (file: number) => number,
  post: (file: number) => number,
  inFrame: (file: number) => boolean,
  files: number[],
  k: number,
): boolean {
  //@ verify
  //@ requires 0 <= k && k < files.length
  //@ requires !inFrame(files[k])
  //@ requires pre(files[k]) !== post(files[k])
  //@ ensures !framePreserved(pre, post, inFrame, files)
  return true;
}

// T3 — the dominance: a vacuous frame is strictly dominated. On the SAME (pre, post,
// files), a "*"-frame (`star`, matching everything) accepts the change while a
// `scoped` frame that excludes a changed file `files[k]` rejects it. This is the
// delete_file("*") catastrophe in its general form — and the Strictness/Domination
// shape from the rest of the portfolio. Pure carrier; _ensures composes T1 + T2.
export function frameDominance(
  pre: (file: number) => number,
  post: (file: number) => number,
  star: (file: number) => boolean,
  scoped: (file: number) => boolean,
  files: number[],
  k: number,
): boolean {
  //@ verify
  //@ requires forall(f, star(f))
  //@ requires 0 <= k && k < files.length
  //@ requires !scoped(files[k])
  //@ requires pre(files[k]) !== post(files[k])
  //@ ensures framePreserved(pre, post, star, files)
  //@ ensures !framePreserved(pre, post, scoped, files)
  return true;
}
