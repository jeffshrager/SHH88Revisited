#!/usr/bin/env python3
"""Check that every \\lean{...} and \\code{...} name cited in the paper is a declaration listed
in notes/CATALOG.md (regenerate it with tools/gen_catalog.py first)."""
import os, re, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
cat = open(os.path.join(ROOT, "notes", "CATALOG.md")).read()
names = set(re.findall(r"`([A-Za-z_][A-Za-z0-9_.']*)`", cat))
files = sys.argv[1:] or [os.path.join(ROOT, "paper", "paper.tex")]
missing = []
for f in files:
    for m in re.findall(r"\\lean\{([^}]*)\}", open(f).read()):
        n = m.replace("\\_", "_")
        if not any(x == n or x.endswith("." + n) or n.endswith("." + x) for x in names):
            missing.append(n)
for n in sorted(set(missing)):
    print("missing:", n)
print(f"{len(set(missing))} cited names not found")
sys.exit(1 if missing else 0)
