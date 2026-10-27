# Plan: Atkin–O'Brien congruences for powers of 13

**Target** (Atkin–O'Brien 1967, Trans. AMS 126, Thm 1.1 as quoted by Garvan–Shomanov, arXiv:2504.10824).
Put `P(N) = p(n)` if `N = 24n − 1`, and `0` otherwise. For every `α ≥ 1` there is an integer `K_α` with
`13 ∤ K_α` such that, for all `N`, `P(13^{α+2}N) ≡ K_α · P(13^α N) (mod 13^α)`.

This is a proportionality statement, not a divisibility one: 13 is not a Ramanujan prime.

## Structure (mirrors `Atkin11*`)
* `g = (η(13τ)/η(τ))² = q∏(1−q^{13n})²/(1−qⁿ)²` is the Hauptmodul of `Γ₀(13)`, and `φ = η(169τ)/η(τ)`.
* There are two alternating stages:
  * `L_{2α−1} = U₁₃(φ·L_{2α−2})`, with `U(φgᵏ) = Σ d_{k,r} gʳ`;
  * `L_{2α} = U₁₃(L_{2α−1})`, with `U(gᵏ) = Σ c_{k,r} gʳ`.
* 13-adic valuation bounds (A–O Lemma 4.1):
  * `π(c_{k,r}) ≥ ⌊(13r−k−1)/14⌋` and `π(d_{k,r}) ≥ ⌊(13r−k−8)/14⌋`;
  * `π(k_{α,r}) ≥ ⌊(13r−9)/14⌋` and `π(ℓ_{α,r}) ≥ ⌊(13r−2)/14⌋`, with the `r = 1` coefficients 13-adic units.
* Proportionality comes from 2×2 minors. Put `y_α` = the coefficient vector of stage `α` and
  `μ_α = y_{α+1} ∧ y_α`. Then `μ_{α+1} = Λ²M μ_α`, and the minors of the stage matrices gain 13-adic valuation.
  Since `y_{α,1}` is a unit, `y_{α+1} ≡ (y_{α+1,1}/y_{α,1}) y_α`, which is `K_α`.

## Numerics (2026-10-27, `scripts/atkin13/`)
* `U₁₃(gᵏ)` is a polynomial in `g` of degree `13k`, with lowest term `g^{⌈k/13⌉}`. The bound
  `π(c_{k,r}) ≥ ⌊(13r−k−1)/14⌋` holds for every `k ≤ 14` and `r ≤ 39` computed. For example,
  `U(g) = 1165g + ⋯ + 13¹¹g¹³`.
* The modular equation is `Y¹³ = Σ_{j=1}^{13} ±σ_j(x) Y^{13−j}`, where `Y = g((τ+λ)/13)` and `x = g(τ)`. Each
  `σ_j` has degree `14−j` and lowest term `x¹`, giving 91 integer coefficients. `σ₁₃ = c·x` because
  `∏_λ g((τ+λ)/13) ∝ g(τ)`.

## Lean route
1. A 13-dissection of `E(q)`. Its components are 6 theta quotients plus `−q⁷E(q¹⁶⁹)` (residues with
   `24r+1 ≡ □ mod 13`). The analogue of `Atkin11Dissect` is a norm identity
   `∏_λ E(ζ^λ q^{1/13}) = E(q)^{14}/E(q^{13})`.
2. Certified polynomial identities among the components, which give `U(gᵏ)` for `k ≤ 13` and `U(φgᵏ)` for
   `k ≤ 12` (seeds). The `Atkin11Cert` pipeline is the template.
3. The modular-equation recurrence gives all `c_{k,r}` and `d_{k,r}`, then the valuation bounds by induction,
   as in `Atkin11Bound`.
4. The `Λ²` minor argument, then `K_α`.

Estimated scale: comparable to the 11^k development (several sessions). The main risk is step 1–2: the
relations among the six theta components.
