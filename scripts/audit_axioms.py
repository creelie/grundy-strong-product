"""Reads the output of `lake env lean Check.lean` and checks that every certificate rests only on the
standard axioms (no sorry, no native_decide, no ofReduceBool)."""
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = 25

text = open(sys.argv[1]).read()
if "sorryAx" in text or "error" in text:
    sys.exit("audit: sorry or error in the output")
found = re.findall(r"^'(\S+)' depends on axioms: \[([^\]]*)\]", text, re.M)
free = re.findall(r"^'(\S+)' does not depend on any axioms", text, re.M)
bad = 0
for name, axioms in found:
    used = {a.strip() for a in axioms.split(",") if a.strip()}
    extra = used - ALLOWED
    if extra:
        print(f"{name}: not allowed: {', '.join(sorted(extra))}")
    bad += bool(extra)
total = len(found) + len(free)
if total != EXPECTED:
    sys.exit(f"audit: expected {EXPECTED} theorems, found {total}")
if bad:
    sys.exit("audit: unexpected axioms")
print(f"axiom audit: {total} theorems, standard axioms only ({len(free)} use no axioms at all)")
