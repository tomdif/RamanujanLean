# Stepanov's method: Hasse–Weil for `y² = f(x)` over `𝔽_p`, and Salié's bound (`RamanujanTau/Stepanov/`)

**Status (2026-11-04).** Both goals are done and axiom-clean. There are no named hypotheses, no `sorry`, and no
`native_decide`.

* **Goal A.** Stepanov's elementary Hasse–Weil-type bound for quadratic-character sums of polynomials over the prime
  field. Mathlib does not have this, not even Hasse's theorem for elliptic curves.
* **Goal B.** Salié's bound `|S(1,b;p)| ≪ p^{2/3}`, i.e. `WeilKloosterman.SaliePrimeBound`, proved. Hence
  **`τ(n) = O(n^{35/6+ε})` unconditionally**.

Every `#print axioms` prints `[propext, Classical.choice, Quot.sound]`.

Build (only these files):
`nice -n 10 lake build RamanujanTau.Stepanov.Salie`. This builds Basic, Aux, Main and SalieCount, and imports
`TauBound/KlPrime` and `WeilKloosterman/Main` unchanged. The root `RamanujanTau.lean` does not import any of it.

| File | Lines | Content |
|---|---|---|
| `Stepanov/Basic.lean` | 238 | base-`X^p` digit uniqueness, `NotConstSq`, squarefree ⟹ `NotConstSq`, **nonvanishing lemma** |
| `Stepanov/Aux.lean` | 311 | derivative formula, auxiliary polynomial, dimension count, multiplicity, **one-sided bound** |
| `Stepanov/Main.lean` | 305 | parameter choice, real one-sided bound, two-sided bound, all-`p` bound, point count, **Hasse** |
| `Stepanov/SalieCount.lean` | 412 | fibre count `M(u,v)` of the sixth moment, reduction to a **quartic** (genus 1), `|M−p| ≪ √p` |
| `Stepanov/Salie.lean` | 290 | sixth-moment identity, orbit argument, **`saliePrimeBound`**, **`tau_isBigO_35_6_unconditional`** |
| `scripts/stepanov/check_stepanov.py` | | numerical validation (see (4) below) |

## (1) Lean, axiom-clean, unconditional

`F = ZMod p` with `p` an odd prime, `c = (p−1)/2`, `m = natDegree f`, and `χ = quadraticChar F`.

`NotConstSq f` means `∀ a ≠ 0, ∀ u v, f·u² = C a·v² → u = 0`. It follows from either of these:
* `Squarefree f ∧ 0 < deg f` (`notConstSq_of_squarefree`, by infinite descent);
* a simple root (`notConstSq_of_rootMultiplicity_one`).

| Theorem | Statement |
|---|---|
| `eq_zero_of_eval_X_pow` | if every digit `P.coeff i ∈ R[X]` of `P ∈ R[X][Y]` has degree `< q`, then `P(X^q) = 0 → P = 0` |
| **`stepanov_nonvanish`** | `NotConstSq f`, `deg r_j, s_j < A`, `2(A−1)+m < p`, `J+m ≤ p`, and `∑_{j<J}(r_j + s_j f^c) X^{pj} = 0` ⟹ all `r_j = s_j = 0` |
| `derivative_formula` | `f^k (s f^c)^{(k)} = u_k(s) f^c`, where `u_{k+1} = f u_k' + (c−k) f' u_k` |
| `iterate_derivative_mul_X_pow_p` | `(P X^{pj})^{(k)} = P^{(k)} X^{pj}` in characteristic `p` |
| `natDegree_qLin_lt` | `deg Q_k < D := A+J−1+(ℓ−1)(m−1)` for `k < ℓ` |
| **`stepanov_card_le`** | (combinatorial one-sided bound) `ε ≠ 0`, `2 ≤ A`, `ℓ ≤ A`, `ℓ ≤ p`, `2(A−1)+m < p`, `J+m ≤ p`, and `ℓ·D < 2JA` ⟹ `ℓ·#{x : f(x)^c = ε} ≤ A−1 + cm + p(J−1)` |
| **`stepanov_card_le_real`** | `p ≥ 144m²` ⟹ `#{x : f(x)^c = ε} ≤ p/2 + 2m√m√p` |
| **`stepanov_charSum_le`** | `p ≥ 144m²` ⟹ `|∑_x χ(f(x))| ≤ 4m√m√p + m` |
| **`hasseWeil_charSum_le`** | **every** odd prime `p`, `f` squarefree with `deg f ≥ 1`: `|∑_x χ(f(x))| ≤ 12m²√p` (`…_of_notConstSq` is the general form) |
| **`hasseWeil_pointCount`** | `|#{(x,y) : y² = f(x)} − p| ≤ 12m²√p` |
| **`hasse_elliptic`** | squarefree cubic: `|#{(x,y) : y² = f(x)} − p| ≤ 108√p` (Hasse 1933, up to the constant) |
| `notConstSq_fUV`, `M3_sub_p_le`, `M3_sub_p_sq_le` | sixth-moment fibres (see below) |
| `sum_norm_kl_pow_six` | `∑_{a,b}|S(a,b;p)|⁶ = p² N₆` |
| `card_pairs_eq_sum_sq` | `#{(x,y) : g x = g y} = ∑_b #g⁻¹(b)²` |
| `sum_M3_sub_sq_le` | `∑_{u,v}(M(u,v) − p)² ≤ (196²+18) p³` |
| **`norm_kl_prime_pow_six_le`** | odd `p`: `|S(1,b;p)|⁶ ≤ 2(196²+18) p⁴` |
| **`saliePrimeBound`** | `WeilKloosterman.SaliePrimeBound` (`C = max((2(196²+18))^{1/6}, 2)`, about 6.6) |
| **`tau_isBigO_35_6_unconditional`** | `∀ε>0, τ(n) = O(n^{35/6+ε})` |

### How the Stepanov proof works (formalised exactly this way)

1. **Auxiliary polynomial.**
   * Set `T = ∑_{j<J}(r_j + s_j g) X^{pj}`, where `g = f^c` and `deg r_j, s_j < A`. The unknown coefficients are
     a vector in `F^{J×2×A}`.
   * In characteristic `p`, derivatives pass through `X^{pj}`. The derivative formula then gives
     `f(x)^k T^{(k)}(x) = Q_k(x)` for every `x ∈ S_ε = {f(x)^c = ε}`, because `x^p = x` and `g(x) = ε`. Here
     `Q_k = ∑_j (f^k r_j^{(k)} + ε u_k(s_j)) X^j` is linear in the unknowns and has degree `< D`.
   * The coefficient map `F^{2JA} → F^{ℓD}` has a nonzero kernel vector when `ℓD < 2JA`. This is
     `LinearMap.ker_ne_bot_of_finrank_lt`.
2. **Multiplicity.** For `x ∈ S_ε` we have `f(x) ≠ 0`, so `T^{(k)}(x) = 0` for all `k < ℓ`. Since `(ℓ−1)! ≠ 0` in
   `F` (`ℓ ≤ p`), Mathlib's `lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors` gives
   multiplicity `≥ ℓ`.
3. **Nonvanishing.**
   * Suppose `T = 0`. Then `U = −f^c V`, so `f U² = f^p V² = f(X^p) V²` (`ZMod.expand_card`).
   * Read this in `F[X][Y]` with `Y = X^p`. All digits have degree `< p` (because `2(A−1)+m < p`), so
     `f(X) r(X,Y)² = f(Y) s(X,Y)²`.
   * Specialise `Y = y` for each `y` with `f(y) ≠ 0`. Then `NotConstSq` gives `r(X,y) = s(X,y) = 0`.
   * There are `≥ p−m > J−1` such `y`, so `r = s = 0`.

   This specialisation trick avoids bivariate valuations.
4. **Counting.** `ℓ|S_ε| ≤ #roots(T) ≤ deg T ≤ A−1+cm+p(J−1)`.
5. **Parameters.** Take `A = c−m+1`, `J ≈ √p/(4√m)` and `ℓ = 2J−1`. This gives
   `|S_ε| ≤ p/2 + pm/(2(2J−1)) ≤ p/2 + 2m√m√p`.
6. **Two-sided bound.** `N₊ + N₋ ≥ p − m` turns the one-sided bounds into a two-sided one. Small `p < 144m²`
   use the trivial bound `|∑χ| ≤ p < 12m√p`.

### How Salié follows (a correction to `docs/WEIL_KLOOSTERMAN.md`)

1. `M(u,v) = #{x ∈ (𝔽_p^×)³ : Σx = u, Σx⁻¹ = v}`. Fibring over `x₁ = x`, with `s = u−x` and `r = v−x⁻¹`, gives
   `M₂(s,r) = 1 + χ(s² − 4s/r)` for `s, r ≠ 0`. This is proved via root pairs of `z² − sz + s/r` and
   completing the square.
2. Then `χ(s² − 4s/r) = χ(f_{u,v}(x))`, where `f_{u,v}(x) = A(A−4x)` and `A = (u−x)(vx−1)`.
   **This is a quartic (genus 1), not a quintic.** The factor `x` in `WEIL_KLOOSTERMAN.md` §G1 step 5 cancels as
   the square `x²`. So Salié only needs Hasse-type bounds (elliptic curves).
3. `x = u` is a simple root of `f_{u,v}` whenever `u ≠ 0` and `uv ≠ 1`. This avoids any discriminant computation.
4. So for all but `≤ 2p` pairs, `|M − p| ≤ 4 + 192√p`, and `|M − p| ≤ 3p` always. Hence
   `∑(M−p)² ≤ (196²+18)p³`.
5. Let `q = p−1`. Combining `p²N₆ = p²∑(M−p)² + 2p³q³ − p⁶` with the orbit bound
   `(p−1)|S(1,b)|⁶ + q⁶ ≤ p²N₆` gives `(p−1)|S|⁶ ≤ p²∑(M−p)² − (p³−q³)² ≤ C₀p⁵`.

## (4) Numerical (`scripts/stepanov/check_stepanov.py`, done before the Lean work)

1. The parameter choice satisfies all the side conditions and `bound ≤ p/2 + 2m^{3/2}√p` for every `m ≤ 12` and
   every prime `144m² ≤ p < 40000`.
2. For random squarefree `f` with `deg f ≤ 6` and `p < 400`, `max |∑χ(f)|/(m²√p) = 0.22`. The proved constant is 12.
3. The auxiliary polynomial was built explicitly by linear algebra mod `p` for `p = 61, 67, 97, 151` and
   `m = 3, 4`. In every case `T ≠ 0`, every `x ∈ S_ε` is a root of multiplicity `≥ ℓ`, and `ℓ|S| ≤ deg T`.
4. For `p = 5, 7, 11, 13`, the exact fibre inequality `|M−p| ≤ 4 + |∑χ(f_{u,v})| + (p−1)[uv=1]` holds for all
   `(u,v)`, and `∑(M−p)²/p³ ≈ 3–4.3`.

## Remarks, limits, reuse

* The constants are crude: `12m²` against the sharp `2⌊(m−1)/2⌋`, and `C ≈ 6.6` for Salié. They could be improved
  with a better choice of `ℓ` and `J` and a sharper `deg u_k`, but nothing downstream needs that.
* **Over general finite fields.** Steps 1, 2 and 4 use only characteristic `p`, `x^q = x` and `(ℓ−1)! ≠ 0`. They
  carry over verbatim to `GaloisField p r` with `q = p^r` in place of `p` (replace `ZMod.pow_card` and
  `ZMod.expand_card` by `FiniteField.pow_card` and `FiniteField.expand_card`). The nonvanishing step needs
  `X^q`-digits of degree `< q` and specialisation at `q − m` points; both also carry over. The present files are
  written for `ZMod p` only. A port is mechanical: about 100 lines of edits, mostly changing `F := ZMod p` to a
  variable `[Field K] [Fintype K] [CharP K p]`.
* Not needed for τ and not done: the Artin–Schreier analogue (Weil's `2√p`), which is being done separately.

## Literature

* S. A. Stepanov, *On the number of points of a hyperelliptic curve over a finite prime field*, Izv. AN SSSR 33
  (1969).
* W. M. Schmidt, *Equations over Finite Fields*, Ch. I–II.
* Iwaniec–Kowalski, *Analytic Number Theory*, §11.
* H. Hasse (1933/36).
* H. Salié, Math. Z. 34 (1932).
* H. Davenport, J. reine angew. Math. 169 (1933).
