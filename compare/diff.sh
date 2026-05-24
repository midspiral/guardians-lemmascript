#!/bin/sh
# Differential test: run our verified-core-backed verify() and the real Python
# guardians.verify() on the email-agent scenarios, and diff the verdicts.
#
# One-time setup for the Python side:
#   cd ../guardians && python3 -m venv .venv && .venv/bin/pip install -e .
set -e
cd "$(dirname "$0")/.."

node ../LemmaScript/node_modules/.bin/tsx compare/scenarios.ts > /tmp/gl_ts.json
../guardians/.venv/bin/python compare/dump_py.py > /tmp/gl_py.json

../guardians/.venv/bin/python compare/check.py
echo
echo "(Python also reports a 'precondition' category on external sends — the Z3"
echo " check this project does not model. Not a disagreement.)"
