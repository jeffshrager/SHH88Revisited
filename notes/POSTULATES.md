# The postulates of Shrager, Hogg & Huberman (1988), as CogLean reads them

Shrager, J., Hogg, T., & Huberman, B. A. (1988). A graph-dynamic model of the power law of
practice and the problem-solving fan-effect. *Science, 242*, 414–416. Page numbers below are
the paper's.

Each item is marked by its kind. **Mechanism**: a process the theory posits. **Condition**: a
circumstance a result depends on, not part of the theory. **Idealization**: an approximation
the analysis makes to the mechanism. **Phenomenon**: a regularity of behavior, stated without
mechanism. **Result at a setting**: a number or a curve at particular parameters.

## The task and its mechanisms (the executable tier; milestone 2)

| | Postulate | Where |
|---|---|---|
| P1 | **States and operators** (mechanism). A state is a B-bit vector; an operator is a pattern→result pair over the B positions with don't-care bits, applicable when its fixed bits match, flipping the bits that differ; it "connects two pairs of states" per don't-care bit. | p. 414, col. 1–2 |
| P2 | **The initial operators** (condition). Play begins with the 2B one-bit operators, "a B-dimensional hypercube", so every state is reachable from every other. | p. 414–415 |
| P3 | **The decision procedure with parameter r** (mechanism). At a state, order the applicable operators by the Hamming distance to the goal after application; the "good" ones minimize it; each "bad" one is removed with probability r; one operator is chosen uniformly from what remains. r = 1 approximates optimal search; r = 0 is a random walk. | p. 415, col. 2 |
| P4 | **Operator learning by chunking** (mechanism). After each trial, add the operator that most generally summarizes the solution: start→goal with `?` where a bit did not change; it solves that game in one step and adds 2^k directed edges for k unchanged bits. | p. 415, col. 1 |
| C1 | **Trials** (condition). Each trial draws a start and a goal uniformly among the 2^B states; performance is the number of edges traversed; learning between trials. | p. 415 |
| C2 | **Regimes** (condition). r ∈ {0, 0.5, 1}; B = 5; 16,384 observations per point. | p. 415, Fig. 1 |

## The theory (the analytic tier; milestone 1)

| | Postulate | Where |
|---|---|---|
| I1 | **The random-graph idealization** (idealization). A typical problem space is a random graph on n nodes with edge probability p; learning raises p. Assume every node has the mean degree μ = (n−1)p, cycles are long (tree-like), start and goal are about the diameter D = ln n / ln μ apart, and at each node one edge leads toward the goal and μ−1 away. | p. 415, col. 3; p. 416, col. 1 |
| I2 | **The decision procedure in the idealization** (idealization). Each bad edge is eliminated with probability r, leaving (μ−1)(1−r) effective bad choices, so a step goes toward the goal with probability P₋ = 1/(1 + (μ−1)(1−r)) and away with P₊ = 1 − P₋ (Eq. 1). | p. 416, col. 1 |
| W | **The walk** (mechanism of the idealized model). A one-dimensional walk on distance 0..D from the goal, absorbed at 0, "constrained to remain within distance D": forced reflection at D (the paper reports s = D² for the symmetric case, which is this convention; the stay-with-probability-P₊ convention gives D² + D). Expected steps s from D by "standard techniques" (van Kampen 1981): Eq. 2. | p. 416, col. 1–2 |
| C3 | **Links grow with trials** (condition, implicit). Each trial adds a bounded number of edges, so μ grows about linearly in trials. Needed to read s(μ) as a learning curve. | p. 415 ("As new operators are learned … p will correspondingly increase") |

## The phenomena

| | Phenomenon | Where |
|---|---|---|
| Φ1 | **The power law of practice**: speed improves as a power of the number of trials. In CogLean: the graded predicates `Improves`, `DiminishingReturns`, `DiminishingRelativeReturns`, `ApproxScaleRatio` (over a range), `ScaleRatio` (exact). | p. 414 |
| Φ2 | **The problem-solving fan effect**: performance becomes slower as more operators are learned, in certain situations. In CogLean: `Worsens`. | p. 414, 415 |

## Results at settings

| | Result | Where |
|---|---|---|
| R1 | Fig. 1: log-log solution rates, trials 1–100, for r = 0, 0.5, 1. A and C "approximately straight"; B initially degrades. | p. 414 |
| R2 | Fig. 2: Eq. 2 against p for the three r regimes, n = 10,000. | p. 416 |

## Claims derived from the theory (see CLAIMS.md for status)

Eq. 3 (drift, P₋ > P₊: s ≈ D/(P₋ − P₊)); symmetric s = D²; Eq. 4 (P₊ > P₋: exponential in D);
Eq. 5 (weak decision procedure: s ≈ (2n/μ)(1−r)^{ln n/ln μ − 1}); the fan-effect condition
"|ln(1−r)| ln n > (ln μ)²"; Eq. 6 (strong decision procedure: s ≈ ln n / ln μ) and "a power-law
decay"; the comparison with ACT* and Rosenbloom (p. 416).
