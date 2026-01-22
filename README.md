# Formalizing Mathematics in Lean 2025 Class Projects

# Bannai-Bannai-Stanton Theorem
Formalising Mathematics in Lean - ETH Zurich

> **Note:** Please refer to the provided PDF report

 Potential improvement/remark: After reflection, I noticed that one can maybe reduce the number of lines of this proof by removing at least the lemma `finite_distance_set_imp_finite_set` and related parts, using the following trick:

We first show that `S.Finite` implies $|S| \leq\binom{d + |D(S)|}{d}$ (so we do the exact proof of the Bannai-Bannai-Stanton bound but we assume $S$ to be finite). Then we use a standard compactness argument to extend the result to any $S$ by the following: if $S$ is finite we are already done; otherwise, $S$ is infinite, we show this leads to a contradiction.

There must exist a finite subset $S' \subset S$ such that $|D(S')| = |D(S)|$ (otherwise, if every finite subset missed at least one distance, we could iteratively pick pairs of points from $S$ realizing the "missing" distances; since $D(S)$ is finite, this process must terminate, yielding a finite subset that realizes all distances).

Then, since $S'$ is finite and $S$ is infinite, we can add sufficiently many points from $S \setminus S'$ to $S'$ to obtain a finite subset $S' \subset S'' \subset S$ with more than $\binom{d + |D(S)|}{d}$ points. This set must satisfy $D(S') \subseteq D(S'') \subseteq D(S)$, and since $|D(S')| = |D(S)|$, we must have $|D(S'')| = |D(S)|$. Thus we have found a finite subset $S''$ with more than $\binom{d + |D(S'')|}{d}$ points, which is a contradiction of our first claim about finite sets.

Alternatively, if the objective of the library includes building general-purpose tools, the lines currently serving `finite_distance_set_imp_finite_set` could be replaced by code of independent value: **in any finite-dimensional normed vector space, a set which gives rise to a finite distance set must be finite.**