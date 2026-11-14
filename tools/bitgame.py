#!/usr/bin/env python3
"""Exact prototype of the bit game (SHH 1988, pp. 414-415), with the semantics of SHH/BitGame/.

A state is a tuple of B bits. An operator is a tuple of B entries, each None (don't care) or a
pair (a, b): the position must hold a, and becomes b. It applies when every specified position
matches. The initial operators are the 2B one-bit operators (bit i: 0->1 and 1->0). Chunking a
solved game start->goal gives the operator with (start_i, goal_i) where they differ and None
where they agree. The decision procedure with parameter r: among applicable operators, the
"good" ones minimize the Hamming distance to the goal after application; each "bad" one is
removed with probability r; one operator is chosen uniformly from what remains.

Everything is exact (Fractions): the one-step distribution, the expected number of steps to the
goal (by solving the absorbing chain), and the probability of solving within k steps.

    python3 tools/bitgame.py
"""
from fractions import Fraction as F
from itertools import product
from math import comb


def apply(op, s):
    if any(e is not None and s[i] != e[0] for i, e in enumerate(op)):
        return None
    return tuple(e[1] if e is not None else s[i] for i, e in enumerate(op))


def initial_ops(B):
    ops = []
    for i in range(B):
        for a in (False, True):
            ops.append(tuple((a, not a) if j == i else None for j in range(B)))
    return ops


def chunk(s, g):
    return tuple(None if s[i] == g[i] else (s[i], g[i]) for i in range(len(s)))


def ham(x, y):
    return sum(a != b for a, b in zip(x, y))


def step_dist(ops, r, g, x):
    """Distribution over next states: {state: prob}. Duplicate successors merged."""
    succ = [y for y in (apply(o, x) for o in ops) if y is not None]
    if not succ:
        return {x: F(1)}
    best = min(ham(y, g) for y in succ)
    good = [y for y in succ if ham(y, g) == best]
    bad = [y for y in succ if ham(y, g) != best]
    G, b = len(good), len(bad)
    r = F(r)
    # number K of bad ones kept ~ Binomial(b, 1-r); choice uniform among G + K
    pk = lambda n, k: comb(n, k) * (1 - r) ** k * r ** (n - k)
    p_good = sum(pk(b, k) / (G + k) for k in range(b + 1))
    p_bad = (1 - r) * sum(pk(b - 1, k) / (G + 1 + k) for k in range(b)) if b else F(0)
    d = {}
    for y in good:
        d[y] = d.get(y, F(0)) + p_good
    for y in bad:
        d[y] = d.get(y, F(0)) + p_bad
    assert sum(d.values()) == 1, sum(d.values())
    return d


def expected_steps(ops, r, B, s, g):
    """Exact expected steps from s to g (absorbing at g), by Gaussian elimination."""
    states = list(product((False, True), repeat=B))
    idx = {x: i for i, x in enumerate(states)}
    n = len(states)
    A = [[F(0)] * n for _ in range(n)]
    rhs = [F(0)] * n
    for x in states:
        i = idx[x]
        A[i][i] = F(1)
        if x == g:
            continue
        rhs[i] = F(1)
        for y, p in step_dist(ops, r, g, x).items():
            A[i][idx[y]] -= p
    for i in range(n):
        piv = next(k for k in range(i, n) if A[k][i] != 0)
        A[i], A[piv] = A[piv], A[i]
        rhs[i], rhs[piv] = rhs[piv], rhs[i]
        for k in range(n):
            if k != i and A[k][i] != 0:
                f = A[k][i] / A[i][i]
                A[k] = [a - f * c for a, c in zip(A[k], A[i])]
                rhs[k] -= f * rhs[i]
    return rhs[idx[s]] / A[idx[s]][idx[s]]


def solved_within(ops, r, g, s, k):
    d = {s: F(1)}
    for _ in range(k):
        nd = {}
        for x, p in d.items():
            if x == g:
                nd[x] = nd.get(x, F(0)) + p
                continue
            for y, q in step_dist(ops, r, g, x).items():
                nd[y] = nd.get(y, F(0)) + p * q
        d = nd
    return d.get(g, F(0))


def bits(sx):
    return tuple(c == "1" for c in sx)


def show(op):
    return "".join("?" if e is None else str(int(e[0])) for e in op) + "->" + \
           "".join("?" if e is None else str(int(e[1])) for e in op)


def mean_over_games(ops, r, B):
    states = list(product((False, True), repeat=B))
    tot = F(0)
    for s in states:
        for g in states:
            if s != g:
                tot += expected_steps(ops, r, B, s, g)
    return tot / (len(states) * (len(states) - 1))


def main():
    # the paper's example
    c = chunk(bits("01110"), bits("10101"))
    print("chunk(01110 -> 10101) =", show(c), " applies to",
          [ "".join(str(int(b)) for b in x) for x in product((False, True), repeat=5) if apply(c, x) is not None])

    B = 3
    ops = initial_ops(B)
    print(f"\nB={B}, initial operators only: mean expected steps over all games")
    for r in [F(0), F(1, 2), F(1)]:
        print(f"  r={r}: {mean_over_games(ops, r, B)} = {float(mean_over_games(ops, r, B)):.4f}")

    print(f"\nB={B}: add one chunked operator; does a fixed game get slower? (search)")
    states = list(product((False, True), repeat=B))
    found = {}
    for r in [F(0), F(1, 2)]:
        for s in states:
            for g in states:
                if s == g:
                    continue
                base = expected_steps(ops, r, B, s, g)
                for a in states:
                    for b in states:
                        if a == b:
                            continue
                        new = chunk(a, b)
                        if new in ops:
                            continue
                        e = expected_steps(ops + [new], r, B, s, g)
                        if e > base and (r not in found or e - base > found[r][0]):
                            found[r] = (e - base, s, g, a, b, base, e)
    for r, (dlt, s, g, a, b, base, e) in found.items():
        f = lambda x: "".join(str(int(t)) for t in x)
        print(f"  r={r}: game {f(s)}->{f(g)}: adding {show(chunk(a, b))} raises E[steps] {base} -> {e}  (+{float(dlt):.3f})")

    print(f"\nB={B}: mean over all games, initial ops vs + each single chunk (r = 0, 1/2, 1)")
    for r in [F(0), F(1, 2), F(1)]:
        base = mean_over_games(ops, r, B)
        worse = 0
        tot = 0
        for a in states:
            for b in states:
                if a == b:
                    continue
                new = chunk(a, b)
                if new in ops:
                    continue
                tot += 1
                if mean_over_games(ops + [new], r, B) > base:
                    worse += 1
        print(f"  r={r}: {worse} of {tot} single chunks raise the mean expected steps")

    # greedy (r = 1) is not always optimal once chunks exist
    print(f"\nB=4: r = 1 with chunks: greedy vs shortest path (search)")
    B4 = 4
    ops4 = initial_ops(B4)
    st4 = list(product((False, True), repeat=B4))
    from collections import deque
    def shortest(ops, s, g):
        dist = {s: 0}; q = deque([s])
        while q:
            x = q.popleft()
            for o in ops:
                y = apply(o, x)
                if y is not None and y not in dist:
                    dist[y] = dist[x] + 1; q.append(y)
        return dist[g]
    shown = 0
    for a in st4:
        for b in st4:
            if a == b or shown:
                continue
            ops_ = ops4 + [chunk(a, b)]
            for s in st4:
                for g in st4:
                    if s != g and not shown:
                        e = expected_steps(ops_, 1, B4, s, g)
                        sp = shortest(ops_, s, g)
                        if e > sp:
                            f = lambda x: "".join(str(int(t)) for t in x)
                            print(f"  with {show(chunk(a, b))}: game {f(s)}->{f(g)}: r=1 expects {e}, shortest path {sp}")
                            shown = 1


if __name__ == "__main__":
    main()
