# The claims of Shrager, Hogg & Huberman (1988), and their status

Each claim the paper makes, restated, with its status in this repository. Status values:
**proved** (a theorem, named), **refuted** (a theorem contradicts it), **reinterpreted** (true
under a different statement, named), **supported numerically** (prototype only), **untested**.
Page numbers are the paper's. Kept current as the work proceeds.

## The theory (p. 416)

| # | Claim | Status |
|---|---|---|
| T1 | Eq. 1: a step toward the goal with probability P₋ = 1/(1 + (μ−1)(1−r)). | untested (definition `SHH.GD.pOf`; a consequence of idealizations I1–I2, not derived here) |
| T2 | Eq. 2: the expected steps s from distance D, "by standard techniques". | untested (the closed form is derived and will be proved: `SHH.Walk.s`; comparison with the printed Eq. 2 awaits a transcription of the printed formula, which the OCR garbled) |
| T3 | Eq. 3: when P₋ > P₊, drift, s ≈ D/(P₋ − P₊). | untested (to be proved as two-sided exact bounds `SHH.Walk.drift_bounds`) |
| T4 | When P₊ = P₋, s = D². | supported numerically (`walk_check.py`; `SHH.Walk.s_half` to come). Note: this value fixes the boundary convention as forced reflection at D; the stay convention gives D² + D. |
| T5 | Eq. 4: when P₊ > P₋, s grows exponentially with D. | untested (`SHH.Walk.diffusion_lower`) |
| T6 | Eq. 5: with a weak decision procedure and μ(1−r) ≫ 1, s ≈ (2n/μ)(1−r)^{ln n/ln μ − 1}. | **supported numerically as inexact**: the step replaces (μ−1)^D by μ^D = n; the omitted factor (1 − 1/μ)^D is 0.06 at μ = 3, n = 10⁴. `SHH.GD.eq5_error_factor` to come. |
| T7 | "When r = 0, increasing the number of edges reduces the time to solve the problem." | **supported numerically as false in the paper's own idealized model**: at r = 0, n = 10⁴, s rises from 1,307 (μ = 3) to 2,469 (μ = 5) before falling. Over exact integer D: s(μ=2, D=16) = 256 < s(μ=4, D=8) = 9,824 at n = 2¹⁶ (`walk_check.py`; Lean witnesses to come). The paper's simulation at r = 0 (Fig. 1A) improves, so the idealization, not the simulation, is at fault there. |
| T8 | With r > 0 but μ(1−r) ≫ 1, there is a range in which adding links increases s: the fan effect; "s will increase as links are added when \|ln(1−r)\| ln n > (ln μ)²". | supported numerically for the first part (r = ½, n = 10⁴: s rises to μ ≈ 10 then falls); the stated condition untested |
| T9 | Eq. 6: with a strong decision procedure (r near 1), s ≈ ln n / ln μ, and "one obtains a power-law decay". | untested; expected **reinterpreted**: at r = 1, s = D = ln n / ln μ exactly, which with μ linear in trials is logarithmic in trials: every qualitative signature of a power law (`Improves`, `DiminishingReturns`, `DiminishingRelativeReturns`) and approximately a power law over trials 1–100 (best fit t^{−0.29}, within 12%), but not a power law over long ranges (the doubling ratio tends to 1). |
| T10 | Fig. 2: Eq. 2 "produces the range of behaviors observed in the bit game experiments" (improvement at r = 0 and 1, initial degradation at r = 0.5). | untested; partly contradicted by T7 within the model |

## The simulations (pp. 414–415)

| # | Claim | Status |
|---|---|---|
| S1 | Fig. 1A, C (r = 0, 1): solution rates "consistent with the power law — approximately straight on a log-log plot" over trials 1–100. | untested (milestone 3) |
| S2 | Fig. 1B (r = 0.5): performance initially degrades: the fan effect. | untested (milestone 3) |
| S3 | At r = 1 the heuristic "comes very close to the optimal path". | untested (milestone 2: at r = 1 with the initial operators, steps = Hamming distance) |
| S4 | The learned operator "connects two pairs of states", i.e. adds 2 edges for one don't-care bit (2^k for k). | untested (milestone 2) |

## The comparison (p. 416)

| # | Claim | Status |
|---|---|---|
| D1 | ACT* obtains the power law by a strengthening mechanism that itself follows a power law; here the power law is not built in. | reinterpreted in prospect: what is not built in is a *logarithmic* curve that looks like a power law over the plotted range (T9). |
| D2 | A power law is predicted "for any sort of operator addition (in the appropriate decision-procedure regimes)". | untested; its exact content depends on T9 |
