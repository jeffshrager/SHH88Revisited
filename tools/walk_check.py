#!/usr/bin/env python3
"""Prototype of the SHH88 theory tier, with semantics identical to the Lean definitions.

The one-dimensional walk of Shrager, Hogg & Huberman (1988), p. 416: states 0..D, the goal 0
absorbing; from k (1 <= k < D) a step toward the goal with probability p and away with
probability 1-p; at D forced reflection to D-1 (the paper's convention: it gives s = D^2 in the
symmetric case). `exact` solves the linear system for the expected number of steps from D;
`closed` is the closed form proved in SHH/Walk/ClosedForm.lean. `exact_stay` is the other
boundary convention (stay at D with probability 1-p), for comparison.

Then the SHH parameterization: p = 1/(1 + (mu-1)(1-r)), D = ln n / ln mu, and the curves the
paper discusses, including the numbers used as witnesses in the Lean files.

    python3 tools/walk_check.py
"""
from fractions import Fraction as F
import math


def solve(A, b):
    n = len(b)
    A = [row[:] for row in A]
    b = b[:]
    for i in range(n):
        piv = next(r for r in range(i, n) if A[r][i] != 0)
        A[i], A[piv] = A[piv], A[i]
        b[i], b[piv] = b[piv], b[i]
        for r in range(n):
            if r != i and A[r][i] != 0:
                f = A[r][i] / A[i][i]
                A[r] = [x - f * y for x, y in zip(A[r], A[i])]
                b[r] -= f * b[i]
    return [b[i] / A[i][i] for i in range(n)]


def system(p, D, stay=False):
    """T_0 = 0; T_k = 1 + p T_{k-1} + (1-p) T_{k+1} for 1 <= k < D;
    forced reflection: T_D = 1 + T_{D-1}; stay: T_D = 1 + p T_{D-1} + (1-p) T_D."""
    q = 1 - p
    n = D + 1
    A = [[F(0)] * n for _ in range(n)]
    b = [F(0)] * n
    A[0][0] = F(1)
    for k in range(1, D):
        A[k][k] = F(1); A[k][k - 1] = -p; A[k][k + 1] = -q; b[k] = F(1)
    if stay:
        A[D][D] = F(1) - q; A[D][D - 1] = -p; b[D] = F(1)
    else:
        A[D][D] = F(1); A[D][D - 1] = F(-1); b[D] = F(1)
    return A, b


def exact(p, D, stay=False):
    """Expected steps from D, by solving the system exactly."""
    if D == 0:
        return F(0)
    A, b = system(F(p), D, stay)
    return solve(A, b)[D]


def closed(p, D):
    """The closed form (forced reflection): SHH.Walk.s."""
    p = F(p)
    q = 1 - p
    if p == F(1, 2):
        return F(D * D)
    return F(D) / (2 * p - 1) - 2 * p * q * (1 - (q / p) ** D) / (2 * p - 1) ** 2


def closed_real(p, D):
    """The closed form with a real exponent (SHH.GD.sR)."""
    q = 1 - p
    if abs(2 * p - 1) < 1e-12:
        return D * D
    return D / (2 * p - 1) - 2 * p * q * (1 - (q / p) ** D) / (2 * p - 1) ** 2


def p_of(mu, r):
    return 1 / (1 + (mu - 1) * (1 - r))


def D_of(n, mu):
    return math.log(n) / math.log(mu)


def s_gd(n, mu, r):
    return closed_real(p_of(mu, r), D_of(n, mu))


def main():
    print("Closed form against the exact system (forced reflection), and the stay convention:")
    ok = True
    for p in [F(1), F(9, 10), F(2, 3), F(1, 2), F(1, 3), F(1, 5), F(1, 10)]:
        for D in [0, 1, 2, 4, 5, 6, 8]:
            e, c = exact(p, D), closed(p, D)
            ok &= (e == c)
            if D in (5, 8) or e != c:
                print(f"  p={str(p):5} D={D}: exact={e} closed={c} {'' if e == c else 'MISMATCH'}"
                      f"   stay-convention exact={exact(p, D, stay=True)}")
    print("  all agree" if ok else "  DISAGREEMENT")

    print("\nValues used as Lean witnesses (SHH.Walk):")
    for p, D in [(F(1, 3), 8), (F(1, 5), 6), (F(9, 10), 5), (F(2, 3), 5),
                 (p_of(F(3), F(1, 2)), 8), (p_of(F(10), F(1, 2)), 4)]:
        print(f"  s({p}, {D}) = {closed(p, D)}  (= {float(closed(p, D)):.4f})")
    print(f"  fan in the walk: s(1/5, 6) = {closed(F(1,5),6)} > s(1/3, 8) = {closed(F(1,3),8)}")

    print("\nSHH curves s(mu; n, r), continuous D = ln n / ln mu (SHH.GD.sGD):")
    for r in [0, 0.5, 1]:
        print(f"  r = {r}, n = 10^4:")
        for mu in [3, 4, 5, 7, 10, 15, 20, 40, 100]:
            extra = f"   paper's Eq. 5 approx 2n/mu = {2e4/mu:8.1f}" if r == 0 else ""
            print(f"    mu={mu:4d}  s={s_gd(1e4, mu, r):10.3f}{extra}")

    print("\nPower-of-two family (D exact): n = 2^16, r = 0:")
    for mu in [2, 4, 16, 256]:
        D = int(round(D_of(2 ** 16, mu)))
        print(f"    mu={mu:4d} D={D:3d}  s={closed(p_of(F(mu), F(0)), D)}  (= {float(closed(p_of(F(mu), F(0)), D)):.3f})")

    print("\nThe r = 1 curve s(t) = ln n / ln(mu0 + c t), n = 2^5 nodes... use n = 10^4, mu0 = 2, c = 1:")
    T = lambda t: math.log(1e4) / math.log(2 + t)
    for t in [1, 2, 4, 8, 16, 32, 64, 128, 1024, 2 ** 20]:
        print(f"    t={t:8d}  s={T(t):8.4f}   s(2t)/s(t)={T(2*t)/T(t):.4f}")
    # best-fit power law over trials 1..100 on log-log, and the max relative deviation
    ts = list(range(1, 101))
    xs = [math.log(t) for t in ts]; ys = [math.log(T(t)) for t in ts]
    xm, ym = sum(xs) / len(xs), sum(ys) / len(ys)
    b = sum((x - xm) * (y - ym) for x, y in zip(xs, ys)) / sum((x - xm) ** 2 for x in xs)
    a = math.exp(ym - b * xm)
    dev = max(abs(T(t) - a * t ** b) / T(t) for t in ts)
    print(f"    best power law on trials 1..100: {a:.3f} * t^({b:.3f}); max relative deviation {dev:.3%}")


if __name__ == "__main__":
    main()
