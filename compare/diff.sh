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

echo "TS (verified cores): $(cat /tmp/gl_ts.json)"
echo "PY (real guardians): $(cat /tmp/gl_py.json)"
echo

python3 -m json.tool /tmp/gl_ts.json > /tmp/gl_ts_norm.json
python3 -m json.tool /tmp/gl_py.json > /tmp/gl_py_norm.json
if diff /tmp/gl_ts_norm.json /tmp/gl_py_norm.json > /dev/null; then
  echo "MATCH on {ok, taint, automaton}."
  echo "(Python additionally reports the 'precondition' category on the malicious"
  echo " workflow — the Z3 check this project does not model. Not a disagreement.)"
else
  echo "MISMATCH:"
  diff /tmp/gl_ts_norm.json /tmp/gl_py_norm.json
  exit 1
fi
