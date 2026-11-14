# SHH88Revisited

*SHH Revisited: Don't Just Run Models, Reason About Them.* A self-contained Lean 4 + Mathlib
formalization of Shrager, Hogg & Huberman (1988), "A graph-dynamic model of the power law of
practice and the problem-solving fan-effect" (*Science* 242, 414–416), in the CogLean style:
the paper's mechanisms, conditions and idealizations stated as postulates with page references
(`notes/POSTULATES.md`), its phenomena stated without mechanism, and its claims proved,
refuted or reinterpreted (`notes/CLAIMS.md`). It depends on nothing from the
[CogLean lab repository](https://github.com/jeffshrager/CogLean); the theory-neutral
learning-curve predicates are copied from it with provenance.

Work in progress. Milestone 1 (theory tier, built): the theory tier, the one-dimensional walk of p. 416
and its regimes, over exact rationals and the reals. Milestone 2 (done): the bit game as an executable
model. Milestone 3: Figure 1 by simulation. Milestone 4: the paper.

## Layout

| Path | Contents |
|---|---|
| `SHH/Phenomena/` | Theory-neutral learning-curve predicates (power-law signatures; `Worsens`, the fan effect) |
| `SHH/Walk/` | The biased walk on 0..D: the linear system, the closed form, regimes |
| `SHH/GraphDynamics/` | The SHH parameterization p(μ, r), D(n, μ); the practice curve; the fan effect |
| `tools/walk_check.py` | Python prototype with the same semantics; the numbers the Lean witnesses use |
| `notes/` | Postulates, claims and their status, the generated catalog |
| `paper/` | The paper |

## Build

Lean 4.35.0 and Mathlib v4.35.0:

```
lake exe cache get
lake build
python3 tools/walk_check.py
```

Every theorem is fully proved, with no `sorry`, and depends only on Lean's standard axioms.
