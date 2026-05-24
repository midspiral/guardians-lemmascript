# Runs the REAL Python guardians.verify() on the example's two scenarios and
# prints the verdict as JSON, in the same shape as scenarios.ts. Reuses the exact
# Workflow/Policy objects from examples/email_agent.py (its __main__ is guarded,
# so importing it just builds the objects).
import json
import os
import sys

here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, "..", "..", "guardians", "examples"))

import email_agent as ex  # noqa: E402
from guardians import verify  # noqa: E402


def summ(r):
    return {
        "ok": r.ok,
        "taint": any(v.category == "taint" for v in r.violations),
        "automaton": any(v.category == "automaton" for v in r.violations),
    }


out = {
    "safe": summ(verify(ex.safe_wf, ex.policy, ex.registry)),
    "malicious": summ(verify(ex.malicious_wf, ex.policy, ex.registry)),
}
print(json.dumps(out))
