# Compares the TS (verified-core) verdicts against the real Python guardians.
# Checks: (1) the precise adapter matches Python on taint and automaton; (2) the
# PROVED leaksWf is sound (flags every taint Python flags) and reports where it
# is conservatively stronger (the sound superset).
import json
import sys

ts = json.load(open("/tmp/gl_ts.json"))
py = json.load(open("/tmp/gl_py.json"))

cols = f"{'scenario':<22}{'PY taint':>10}{'TS precise':>12}{'TS leaksWf':>12}{'PY auto':>9}{'TS auto':>9}"
print(cols)
print("-" * len(cols))

precise_taint_ok = True
automaton_ok = True
wf_sound = True
overapprox = []

for s in py:
    t, p = ts[s], py[s]
    print(f"{s:<22}{str(p['taint']):>10}{str(t['taintPrecise']):>12}{str(t['taintWf']):>12}{str(p['automaton']):>9}{str(t['automaton']):>9}")
    if t["taintPrecise"] != p["taint"]:
        precise_taint_ok = False
    if t["automaton"] != p["automaton"]:
        automaton_ok = False
    if p["taint"] and not t["taintWf"]:
        wf_sound = False  # a real Python taint flag that leaksWf missed — would be unsound
    if t["taintWf"] and not p["taint"]:
        overapprox.append(s)

print()
print(f"precise adapter taint == Python:      {'YES' if precise_taint_ok else 'NO'}")
print(f"automaton == Python:                  {'YES' if automaton_ok else 'NO'}")
print(f"leaksWf sound (flags >= Python taint): {'YES' if wf_sound else 'NO'}")
print(f"leaksWf conservative over-flags:      {overapprox if overapprox else 'none'}")

sys.exit(0 if (precise_taint_ok and automaton_ok and wf_sound) else 1)
