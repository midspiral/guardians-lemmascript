// v-loops: sound over-approximation of taint through an UNBOUNDED loop.
//
// Guardians' AST has a LoopNode: a body that runs some number of times. Unlike a
// conditional (a finite union of branches), a loop needs a FIXPOINT argument —
// the static check must bound the taint reachable after any number of iterations.
//
// Key fact (single taint bit): with `bodyTaint` monotone in incoming taint,
//   sat := t0 || bodyTaint(t0, body)
// is a one-step PRE-FIXPOINT — `bodyTaint(sat) ==> sat` — so it soundly bounds
// the exit taint of the loop after ANY iteration count, with no iteration to a
// fixpoint required. The body here is a linear tool sequence (the essential new
// content is the unbounded iteration, orthogonal to nesting in the body).

// Taint after one pass of the body.
export function bodyTaint(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0: boolean,
  body: number[],
): boolean {
  //@ verify
  //@ decreases body.length
  if (body.length === 0) return t0;
  const next = sanitizes(body[0]) ? false : t0 || introduces(body[0]);
  return bodyTaint(introduces, sanitizes, next, body.slice(1));
}

// Does the body leak (reach a sink while tainted) in one pass?
export function leaksBody(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  isSink: (tool: number) => boolean,
  t0: boolean,
  body: number[],
): boolean {
  //@ verify
  //@ decreases body.length
  if (body.length === 0) return false;
  const here = isSink(body[0]) && t0;
  const next = sanitizes(body[0]) ? false : t0 || introduces(body[0]);
  return here || leaksBody(introduces, sanitizes, isSink, next, body.slice(1));
}

// Taint after running the body `n` times (the concrete loop exit taint for n iters).
export function iterTaint(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0: boolean,
  body: number[],
  n: number,
): boolean {
  //@ verify
  //@ type n nat
  //@ decreases n
  if (n === 0) return t0;
  return bodyTaint(introduces, sanitizes, iterTaint(introduces, sanitizes, t0, body, n - 1), body);
}

// Did any of the first `n` iterations leak? (concrete loop leak after n iters)
export function leaksUpTo(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  isSink: (tool: number) => boolean,
  t0: boolean,
  body: number[],
  n: number,
): boolean {
  //@ verify
  //@ type n nat
  //@ decreases n
  if (n === 0) return false;
  return (
    leaksBody(introduces, sanitizes, isSink, iterTaint(introduces, sanitizes, t0, body, n - 1), body) ||
    leaksUpTo(introduces, sanitizes, isSink, t0, body, n - 1)
  );
}

// bodyTaint is monotone in incoming taint. Pure carrier.
export function bodyMonotone(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0a: boolean,
  t0b: boolean,
  body: number[],
): boolean {
  //@ verify
  //@ requires t0a ==> t0b
  //@ ensures bodyTaint(introduces, sanitizes, t0a, body) ==> bodyTaint(introduces, sanitizes, t0b, body)
  return true;
}

// leaksBody is monotone in incoming taint. Pure carrier.
export function leaksBodyMonotone(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  isSink: (tool: number) => boolean,
  t0a: boolean,
  t0b: boolean,
  body: number[],
): boolean {
  //@ verify
  //@ requires t0a ==> t0b
  //@ ensures leaksBody(introduces, sanitizes, isSink, t0a, body) ==> leaksBody(introduces, sanitizes, isSink, t0b, body)
  return true;
}

// THE fixpoint fact: sat = t0 || bodyTaint(t0) is a pre-fixpoint of one body pass.
// Pure carrier (boolean case analysis on whether sat holds).
export function satPrefixpoint(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0: boolean,
  body: number[],
): boolean {
  //@ verify
  //@ ensures bodyTaint(introduces, sanitizes, t0 || bodyTaint(introduces, sanitizes, t0, body), body) ==> (t0 || bodyTaint(introduces, sanitizes, t0, body))
  return true;
}

// SOUND loop exit: the taint after ANY number of iterations is bounded by sat.
// Pure carrier; induction on n using bodyMonotone and satPrefixpoint.
export function loopExitSound(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  t0: boolean,
  body: number[],
  n: number,
): boolean {
  //@ verify
  //@ type n nat
  //@ ensures iterTaint(introduces, sanitizes, t0, body, n) ==> (t0 || bodyTaint(introduces, sanitizes, t0, body))
  return true;
}

// SOUND loop leak: if any iteration leaks, then the body leaks from sat — so the
// static check `leaksBody(sat, body)` rules out a leak on every iteration count.
// Pure carrier; induction on n using loopExitSound and leaksBodyMonotone.
export function loopLeakSound(
  introduces: (tool: number) => boolean,
  sanitizes: (tool: number) => boolean,
  isSink: (tool: number) => boolean,
  t0: boolean,
  body: number[],
  n: number,
): boolean {
  //@ verify
  //@ type n nat
  //@ ensures leaksUpTo(introduces, sanitizes, isSink, t0, body, n) ==> leaksBody(introduces, sanitizes, isSink, t0 || bodyTaint(introduces, sanitizes, t0, body), body)
  return true;
}
