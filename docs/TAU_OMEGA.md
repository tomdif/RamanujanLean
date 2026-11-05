# `τ(n) = Ω(n^{11/2})`

Lean: `RamanujanTau/TauOmega/Main.lean`. **Evidence level (1): Lean, axiom-clean, unconditional.**

* `TauOmega.tau_sq_ge_infinitely_often`: ∃ c > 0 such that τ(n)² ≥ c·n¹¹ for infinitely many n.
* `TauOmega.tau_omega`: ∃ c > 0 such that |τ(n)| ≥ c·n^{11/2} for infinitely many n.
* `TauOmega.tau_not_isBigO`: for every δ > 0, τ(n) is **not** O(n^{11/2−δ}).

So the exponent 11/2 in Deligne's bound |τ(n)| ≤ d(n)n^{11/2} is optimal (Deligne itself is not
used or proved). The proof is the classical one: if τ(n)²/n¹¹ < c₁/2 for all large n, then
Σ_{n≤N} τ(n)²/n¹¹ ≤ B + c₁N/2. That contradicts the unconditional lower bound
Σ_{n≤N} τ(n)²/n¹¹ ≥ c₁N from `RankinSelberg.rankinSelberg_two_sided`.

## Every nonzero level-one cusp form

`RamanujanTau/TauOmega/General.lean`, evidence level (1). For f ∈ S_k(SL₂(ℤ)) with f ≠ 0 and
k ≥ 1:
* `TauOmega.coeffSq_ge_infinitely_often`: |a_f(n)|² ≥ c·n^{k−1} infinitely often;
* `TauOmega.coeff_omega`: |a_f(n)| ≥ c·n^{(k−1)/2} infinitely often;
* `TauOmega.coeff_not_isBigO`: a_f(n) ≠ O(n^{(k−1)/2−δ}) for every δ > 0.

These follow from `RankinSelbergGeneral.rankinSelberg_two_sided`.
