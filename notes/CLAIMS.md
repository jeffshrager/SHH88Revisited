# The claims of Shrager, Hogg & Huberman (1988), and their status

Each claim the paper makes, restated, with its status in this repository. Status values:
**proved** (a theorem, named), **refuted** (a theorem contradicts it), **reinterpreted** (true
under a different statement, named), **supported numerically** (prototype only), **untested**.
Page numbers are the paper's. Kept current as the work proceeds.

## The theory (p. 416)

| # | Claim | Status |
|---|---|---|
| T1 | Eq. 1: a step toward the goal with probability P₋ = 1/(1 + (μ−1)(1−r)). | untested (definition `SHH.GD.pOf`; a consequence of idealizations I1–I2, not derived here) |
| T2 | Eq. 2: the expected steps s from distance D, "by standard techniques". | **proved** for the walk as stated: the closed form `SHH.Walk.s` solves the system (`SHH.Walk.term_sys`), the system has one solution (`SHH.Walk.sys_unique`), so `SHH.Walk.sys_eq_s`. The printed Eq. 2 (transcribed in `notes/equations.txt`) is exactly this function for every p ∉ {0, ½} (`SHH.Walk.eq2_printed`): the paper's formula is right. |
| T3 | Eq. 3: when P₋ > P₊, drift, s ≈ D/(P₋ − P₊). | **proved, sharpened**: `D/(2p−1) − 2p(1−p)/(2p−1)² ≤ s ≤ D/(2p−1)` (`SHH.Walk.drift_bounds`); Eq. 3 is the upper bound, off by at most a constant. |
| T4 | When P₊ = P₋, s = D². | **proved** (`SHH.Walk.s_half`). It fixes the boundary convention: forced reflection at D; the stay convention gives D² + D (`SHH.Walk.stay_half_sys`, `stay_half_value`). |
| T5 | Eq. 4: when P₊ > P₋, s grows exponentially with D. | **proved**: printed Eq. 4 is Eq. 2's exponential term, and `s` minus Eq. 4 is the term 2(p² + p(D−1) − D/2)/(2p−1)², linear in D (`SHH.Walk.eq4_remainder`). Exactly,  s = 2p(1−p)(((1−p)/p)^D − 1)/(1−2p)² − D/(1−2p). Also: s strictly increases with D for every 0 < p < 1 (`SHH.Walk.s_strictMono_D`). |
| T6 | Eq. 5: with a weak decision procedure and μ(1−r) ≫ 1, s ≈ (2n/μ)(1−r)^{ln n/ln μ − 1}. | **inexact where it is applied**: the step replaces (μ−1)^D by μ^D = n; the omitted factor is ((μ−1)/μ)^D ≤ exp(−D/μ) (`SHH.GD.eq5_error_factor`, `SHH.GD.eq5_error_bound`), ≈ 0.06 at μ = 3, n = 10⁴. |
| T7 | "When r = 0, increasing the number of edges reduces the time to solve the problem." | **refuted within the paper's own idealized model**: at n = 2¹⁶, r = 0, raising μ from 2 to 4 raises s from 256 to 9,824; it falls only from μ = 16 on (`SHH.GD.fan_pow2_zero`, `SHH.GD.fan_pow2_worsens`; D exact by `SHH.GD.DOf_2_4` etc.). Numerically the same at n = 10⁴ (1,307 at μ = 3 → 2,469 at μ = 5). The paper's simulation at r = 0 (Fig. 1A) improves, so the idealization, not the simulation, is at fault there. |
| T8 | With r > 0 but μ(1−r) ≫ 1, there is a range in which adding links increases s: the fan effect; "s will increase as links are added when \|ln(1−r)\| ln n > (ln μ)²". | **proved** for the first part at exact settings: n = 2¹⁶, r = ½, μ 2 → 4 → 16 gives s 44.0 → 255.5 → 1117.75 (`SHH.GD.fan_pow2_half`); also inside the walk (`SHH.Walk.fan_witness_walk`, `fan_witness_half`). The stated condition: untested (OPEN). |
| T9 | Eq. 6: with a strong decision procedure (r near 1), s ≈ ln n / ln μ, and "one obtains a power-law decay". | **reinterpreted, proved**: at r = 1, s = D exactly (`SHH.Walk.s_one`), so with μ linear in trials (condition C3) the curve is `SHH.GD.curveGD` = ln n / ln(μ₀ + ct). It improves (`curveGD_improves`) with strictly diminishing relative returns (`curveGD_diminishingRelative`), but for any r, ε with (1+ε)r < 1 approximate scale invariance fails on long ranges (`curveGD_not_powerLaw`). Numerically: which with μ linear in trials is logarithmic in trials: every qualitative signature of a power law (`Improves`, `DiminishingReturns`, `DiminishingRelativeReturns`) and approximately a power law over trials 1–100 (best fit t^{−0.29}, within 12%), but not a power law over long ranges (the doubling ratio tends to 1). |
| T10 | Fig. 2: Eq. 2 "produces the range of behaviors observed in the bit game experiments" (improvement at r = 0 and 1, initial degradation at r = 0.5). | **refuted at r = 0**: the idealized walk shows a fan effect at r = 0 (`SHH.GD.fan_pow2_zero`, T7) while the bit game itself improves on average at r = 0 (`SHH.BitGame.figure1_pattern_three`). The tree idealization I1, not the game, produces the r = 0 fan effect. |

## The simulations (pp. 414–415)

| # | Claim | Status |
|---|---|---|
| S1 | Fig. 1A, C (r = 0, 1): solution rates "consistent with the power law — approximately straight on a log-log plot" over trials 1–100. | improvement **proved** for one learning step on the three-bit game: the chunk `00?→11?` lowers the mean expected steps over all 56 games at r = 0 (58/7 → 2603/315) and r = 1 (12/7 → 23/14) (`SHH.BitGame.figure1_pattern_three`); the same for all 32 single chunks numerically (`tools/bitgame.py`). The curve's shape over 100 trials: milestone 3. |
| S2 | Fig. 1B (r = 0.5): performance initially degrades: the fan effect. | **proved** for one learning step on the three-bit game: the same chunk raises the mean expected steps at r = ½ (128/35 → ≈3.682) (`SHH.BitGame.figure1_pattern_three`); all 32 single chunks do so numerically. Also per game: `SHH.BitGame.chunk_slows_game` (game 000→001 slows at r = 0 and r = ½). |
| S3 | At r = 1 the heuristic "comes very close to the optimal path". | **proved for the initial operators**, for every number of bits: every move the r = 1 procedure can make is one bit closer to the goal (`SHH.BitGame.r1_moves_closer`), so every run takes exactly the Hamming distance. With learned operators, an exception: with the chunk `0000→1111` on the four-bit game, game 0001→1110 takes 15/4 expected steps at r = 1 against a shortest path of 3 (`tools/bitgame.py`); the paper says only "approximates", so not a refutation. Lean certificate: to come. |
| S4 | The learned operator "connects two pairs of states", i.e. adds 2 edges for one don't-care bit (2^k for k). | **proved** for the paper's example (`SHH.BitGame.chunk_paper`, `chunk_paper_applies`); in general a chunk takes its start to its goal (`SHH.BitGame.chunk_apply`). |

## The comparison (p. 416)

| # | Claim | Status |
|---|---|---|
| D1 | ACT* obtains the power law by a strengthening mechanism that itself follows a power law; here the power law is not built in. | reinterpreted in prospect: what is not built in is a *logarithmic* curve that looks like a power law over the plotted range (T9). |
| D2 | A power law is predicted "for any sort of operator addition (in the appropriate decision-procedure regimes)". | untested; its exact content depends on T9 |
