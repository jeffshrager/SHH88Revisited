#!/usr/bin/env python3
"""Check that every \\lean{...} name cited in the paper is a declaration in the SHH library,
by asking Lean (`#check @name` for each). Run `lake build` first."""
import os, re, subprocess, sys, tempfile
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ENV = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])
files = sys.argv[1:] or [os.path.join(ROOT, "paper", "paper.tex")]
names = sorted({m.replace("\\_", "_") for f in files for m in re.findall(r"\\lean\{([^}]*)\}", open(f).read())})
src = "import SHH\n" + "".join(f"#check @{n}\n" for n in names)
with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir=ROOT) as fh:
    fh.write(src); path = fh.name
try:
    out = subprocess.run(["lake", "env", "lean", path], cwd=ROOT, env=ENV, capture_output=True, text=True).stdout
finally:
    os.unlink(path)
missing = sorted({n for n in names if re.search(r"Unknown (constant|identifier) `@?" + re.escape(n) + "`", out)})
for n in missing:
    print("missing:", n)
print(f"{len(names)} cited names, {len(missing)} not found")
sys.exit(1 if missing else 0)
