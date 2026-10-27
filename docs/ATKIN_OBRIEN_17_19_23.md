# Atkin–O'Brien congruences for ℓ = 17, 19, 23: reduction and evidence

Notation follows Boylan–Webb (BW, Trans. AMS 365 (2013)):
* `L(0) = 1`;
* `L(b) = L(b−1)|D` for `b` odd, `L(b) = L(b−1)|U` for `b` even, where `D(f) = (Φf)|U` and
  `Φ = η(ℓ²z)/η(z)`;
* `L(b) = η(ℓz)P_ℓ(b)` (b odd) or `η(z)P_ℓ(b)` (b even), with `P_ℓ(b) = Σ p((ℓ^b n+1)/24) q^{n/24}`;
* `b_ℓ(m)` is the stability threshold mod `ℓ^m`.

BW prove `b_ℓ(m) ≤ 2m − 1` (given `d_ℓ = 0`, which they verify for `ℓ ≤ 1300`). For `13 ≤ ℓ ≤ 31` the
stable modules have rank 1, so `L(b+2) ≡ K L(b) (mod ℓ^m)` for `b ≥ b_ℓ(m)`.

**Conjecture.** If `dim S_{ℓ−1}(SL₂ℤ) = 1`, i.e. `ℓ ∈ {13, 17, 19, 23}`, then `b_ℓ(m) = m` for all `m ≥ 1`.
`ℓ = 13` is Atkin–O'Brien (1967). For `ℓ ≥ 29` BW observe that `2m − 1` is sharp.

## Proposition (reduction; proved)
Let `ℓ ∈ {13, 17, 19, 23}`, `m ≥ 1`, `b ≥ m`, and suppose `L(b+2) ≡ K L(b) (mod ℓ^m)`. Let
`ε = (L(b+2) − K L(b))/ℓ^m (mod ℓ)`, a cusp form mod `ℓ`. If the Serre filtration satisfies
`w(ε) ≤ 2(ℓ − 1)`, then `L(b+3) ≡ (K + ℓ^m c) L(b+1) (mod ℓ^{m+1})` for some `c ∈ ℤ`.

*Proof.*
1. Let `T ∈ {U, D}` be the operator taking `L(b) ↦ L(b+1)`, which also takes `L(b+2) ↦ L(b+3)`. Then
   `L(b+3) − K L(b+1) = ℓ^m · ε̃|T`, where `ε̃ ∈ ℤ_(ℓ)((q))` reduces to `ε`.
2. **U-step.** By Serre (BW Lemma 2.2), `w(ε|U) ≤ ℓ + (w(ε) − 1)/ℓ < ℓ + 2`. Filtrations here are multiples
   of `ℓ − 1`, so `w(ε|U) ≤ ℓ − 1`.
3. **D-step.** Mod `ℓ`, `Φ ≡ Δ^{(ℓ²−1)/24}`, so
   `w(ε|D) ≤ ℓ + ((ℓ²−1)/2 + 2ℓ − 3)/ℓ < 2(ℓ − 1)` for `ℓ ≥ 11`. Hence again `w(ε|D) ≤ ℓ − 1`.
4. In both cases `ε|T ∈ S_{ℓ−1} ⊗ 𝔽_ℓ`, which is one-dimensional.
5. `L(b+1) ≢ 0 (mod ℓ)` spans the same line: by BW, the stable module mod `ℓ` has rank 1, `b_ℓ(1) = 1`, and
   `X` is an isomorphism on it.
6. So `ε|T ≡ c L(b+1) (mod ℓ)`, which gives the claim. ∎

**Corollary.** By induction on `m` (base case `b_ℓ(1) = 1`, BW), `b_ℓ(m) = m` for all `m` follows from:

**(★) Key lemma (open).** For every `m ≥ 1`, the first error digit
`ε_m := (L(m+2) − K_m L(m))/ℓ^m (mod ℓ)` has `w(ε_m) ≤ 2(ℓ − 1)`.

Sharpness: proportionality fails mod `ℓ^{m+1}` at `b = m`, as observed.

## Evidence (scripts in `scripts/frontier/`, `p(n)` mod prime powers to `n = 10⁸` via FLINT)
* **Proportionality at `b = m`, exact exponent `m`:**
  * ℓ = 17: m ≤ 4;
  * ℓ = 19, 23: m ≤ 3;
  * ℓ = 13 control: Atkin–O'Brien's `K₂ = 45` is reproduced.
  * It fails at `b = m` for 29 and 31, and fails mod ℓ for `ℓ ≥ 37`.
* **(★) numerically** (`filt2.py`): `w(ε_m) = 2(ℓ − 1)` exactly.
  * ℓ = 17: m = 1, 2, 3 (value 32);
  * ℓ = 19: m = 1, 2 (36);
  * ℓ = 23: m = 1, 2 (44).
* **Digit structure (new observation)** (`digits.py`). Write `L(b) mod ℓ^{j+1}` as
  `Σ_i ℓ^i F_i E_{ℓ−1}^{a_i}` with `F_i` classical. Then the `i`-th ℓ-adic digit has filtration exactly
  `(i+1)(ℓ − 1)`, for `i = 0, 1, 2`, `b = 1, 2, 3`, `ℓ ∈ {17, 19, 23, 29, 31}`. This linear growth is far below
  BW's a-priori `ℓ^i(ℓ − 1)`, and it holds for 29 and 31 as well. So the dichotomy `b = m` vs `2m − 1` comes
  only from `dim S_{ℓ−1}`, as the Proposition predicts.

## Why (★) should hold, and a route to a proof
Linear digit growth is the hallmark of overconvergence with a definite radius. In Katz expansions
`f = Σ_i b_i/E_{ℓ−1}^i`, digit `j` only involves `i ≤ j + 1`. Katz/Coleman/Lauder show that `U_ℓ` improves
overconvergence: Katz-basis matrix entries have valuation `≥ ⌊(ℓ i − j)/(ℓ+1)⌋`, the same shape as
Atkin–O'Brien's Lemma 4.1. Hence:
1. An error whose digit 0 lies in filtration `2(ℓ − 1)`, and whose digits obey the shifted envelope
   `(j+2)(ℓ − 1)`, keeps that envelope under one `T`-step.
   * For `U` this is the computation
     `w' ≤ max(ℓ + (w_{d+1} − 1)/ℓ, w_0, …, w_d)` together with `U ≡ T_ℓ (mod ℓ^{k−1})` in weight `k`.
   * For `D` it also needs the overconvergence of `Φ`.
2. Combined with the Proposition, this proves the conjecture.
3. A computer-assisted proof per prime is possible in the style of Atkin–O'Brien / Garvan–Shomanov, at level 1
   (Katz basis), which avoids level-ℓ modular equations: kernel-check the valuation bounds of the `U`/`D`
   matrices on a periodic box, then run the `Λ²` minor argument.
