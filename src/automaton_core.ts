// v3: security automata — Guardians' other static check.
//
// A security policy is a finite automaton over tool-call sequences; some
// guarded transitions lead to an error state (e.g. `send_email` to a recipient
// outside the allowed domain). At verification time the guard's truth is unknown
// (the recipient is a symbolic placeholder), so the static checker must consider
// BOTH outcomes of each guard — it reports "error reachable" if ANY path through
// the guard choices reaches an error state. The concrete run follows the actual
// guard value. The theorem: the static reachability OVER-approximates the
// concrete one, so a clean static verdict means no concrete path ever errors.
//
// Guards are higher-order parameters (`nextOn` takes the guard outcome,
// `guardHolds` is the concrete evaluation), so there is no condition DSL and the
// result holds for any automaton. States are ints; `isError` marks error states.

// Static reachability: a state is "error-reachable" if it is already an error
// state, or — exploring BOTH guard outcomes of the next tool — either successor
// is. This is the conservative analysis: no guard branch is ruled out.
export function reachesErrorAbstract(
  isError: (state: number) => boolean,
  nextOn: (state: number, tool: number, guard: boolean) => number,
  state: number,
  tools: number[],
): boolean {
  //@ verify
  //@ decreases tools.length
  if (isError(state)) return true;
  if (tools.length === 0) return false;
  return (
    reachesErrorAbstract(isError, nextOn, nextOn(state, tools[0], true), tools.slice(1)) ||
    reachesErrorAbstract(isError, nextOn, nextOn(state, tools[0], false), tools.slice(1))
  );
}

// Concrete execution: follow the single transition the actual guard selects.
export function reachesErrorConcrete(
  isError: (state: number) => boolean,
  nextOn: (state: number, tool: number, guard: boolean) => number,
  guardHolds: (state: number, tool: number) => boolean,
  state: number,
  tools: number[],
): boolean {
  //@ verify
  //@ decreases tools.length
  if (isError(state)) return true;
  if (tools.length === 0) return false;
  return reachesErrorConcrete(isError, nextOn, guardHolds, nextOn(state, tools[0], guardHolds(state, tools[0])), tools.slice(1));
}

// THE v3 THEOREM. The static analysis over-approximates concrete execution: if a
// concrete run reaches an error state, the static checker — which explores all
// guard choices — already found a path to error. Pure carrier; the induction
// case-splits on the concrete guard so the chosen successor matches one of the
// two abstract branches.
export function automatonSound(
  isError: (state: number) => boolean,
  nextOn: (state: number, tool: number, guard: boolean) => number,
  guardHolds: (state: number, tool: number) => boolean,
  state: number,
  tools: number[],
): boolean {
  //@ verify
  //@ ensures reachesErrorConcrete(isError, nextOn, guardHolds, state, tools) ==> reachesErrorAbstract(isError, nextOn, state, tools)
  return true;
}

// The usable form: a clean static verdict (no path reaches error) guarantees the
// concrete run never reaches an error state — for any guard valuation, i.e. any
// actual data. This is what lets Guardians admit a workflow before it runs.
export function automatonSafeVerdict(
  isError: (state: number) => boolean,
  nextOn: (state: number, tool: number, guard: boolean) => number,
  guardHolds: (state: number, tool: number) => boolean,
  state: number,
  tools: number[],
): boolean {
  //@ verify
  //@ requires !reachesErrorAbstract(isError, nextOn, state, tools)
  //@ ensures !reachesErrorConcrete(isError, nextOn, guardHolds, state, tools)
  return true;
}
