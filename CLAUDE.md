# Working on SHH88Revisited

A self-contained CogLean-style formalization of Shrager, Hogg & Huberman (1988), aiming at a
paper, "SHH Revisited: Don't Just Run Models, Reason About Them". It depends on nothing from the
CogLean lab repository; `SHH/Phenomena/LearningCurve.lean` is copied from it with provenance.

## Build

- Lean 4.35.0 via elan (`export PATH=$HOME/.elan/bin:$PATH`); Mathlib v4.35.0 (`lake exe cache
  get` once, then `lake build`). One package, one library `SHH`; layering by imports:
  `Phenomena` ← `Walk` ← `GraphDynamics` (later `BitGame`, `Sims`).
- `Walk/` is over exact `ℚ` with `D : ℕ`; `GraphDynamics/` over `ℝ` (logs, real exponents).
- Every theorem fully proved: no `sorry`; `#print axioms` shows only `propext`, `Quot.sound`,
  `Classical.choice`.
- `python3 tools/walk_check.py` is the Python prototype with the same semantics as the Lean
  definitions; every number used as a Lean witness is printed there first.
- `python3 tools/gen_catalog.py` regenerates `notes/CATALOG.md`.
- The paper: `cd paper && make`; rebuild after every substantial edit; `tools/check_paper.py`
  checks cited names.

## Conventions

- Postulates, conditions, idealizations and phenomena are listed in `notes/POSTULATES.md` with
  page references; every claim of the 1988 paper and its status is in `notes/CLAIMS.md`. Keep
  both current. Mark `SIMPLIFIED:`, `NOT MODELED:`, `OPEN:` in docstrings.
- Headline docstrings begin in bold and say which premises are postulates, which are conditions
  and which are idealizations.
- Phenomena are targets, not premises: a theorem with a phenomenon among its hypotheses relates
  phenomena; say so.
- Commit after every successful major step. **Push at every major milestone without asking**
  (Jeff, 2026-11-13).
