> **Update (2026-11-04):** `WeilPrimeBound` is proved (`StepanovAS.weilPrimeBound`), so τ(n) = O(n^{23/4+ε}) holds unconditionally (`StepanovAS.tau_isBigO_23_4_unconditional`); see [STEPANOV_ARTIN_SCHREIER](STEPANOV_ARTIN_SCHREIER.md).
> **Update (2026-11-04):** `SaliePrimeBound` is proved (`Stepanov.saliePrimeBound`), giving τ(n) = O(n^{35/6+ε}) unconditionally. Correction: the fibre character sum in the sixth moment is a quartic (genus 1), not a quintic; see [STEPANOV](STEPANOV.md).

# Salié and Weil exponents for τ via Kloosterman sums (`RamanujanTau/WeilKloosterman/`)

**Status (2026-11-04).** Everything is proved except the bound for **prime moduli**:

* `τ(n) = O(n^{35/6+ε})` (Salié 1931/32, Davenport 1933) is proved assuming `SaliePrimeBound`.
* `τ(n) = O(n^{23/4+ε})` (Weil 1948) is proved assuming `WeilPrimeBound`.

All prime-power and composite-modulus work is done and axiom-clean, and so is the reduction from a
Kloosterman exponent to a τ exponent. Neither prime-modulus bound has been proved yet; the assessment
below explains what each one would cost.

Files (new; nothing in `TauBound/` was modified, and nothing is imported by the root `RamanujanTau.lean`):

| File | Lines | Content |
|---|---|---|
| `WeilKloosterman/Assembly.lean` | ~180 | from local bounds to `KloostermanBound (α+δ)`, then to `τ = O(n^{(11+α)/2+ε})` |
| `WeilKloosterman/OddPrimePow.lean` | ~330 | sharp odd prime-power bound by stationary phase |
| `WeilKloosterman/Main.lean` | ~210 | named prime hypotheses and the G1/G2 headlines |
| `scripts/weilkloosterman/check_bounds.py` | | numerical sanity check |

Build (only these files):
`nice -n 10 lake build RamanujanTau.WeilKloosterman.Assembly RamanujanTau.WeilKloosterman.OddPrimePow`, then
`nice -n 10 lake env lean RamanujanTau/WeilKloosterman/Main.lean`. The `#print axioms` lines at the end of
`Main.lean` all print `[propext, Classical.choice, Quot.sound]`.

## Evidence levels

### (1) Lean, axiom-clean, no hypotheses

| Theorem | File | Statement |
|---|---|---|
| `qsum_normSq` | OddPrimePow | `|∑_t ψ(tA+t²B)|² = N ∑_{h: 2hB=0} ψ(hA+h²B)` on `ZMod N` |
| **`norm_kl_primePow_odd_le`** | OddPrimePow | for `p` an odd prime, `k = 2j+1`, `j ≥ 1`, and any `b`: `|S(1,b;p^k)| ≤ 4√(p^k)` |
| **`norm_kloosterman_primePow_le_sqrt`** | Main | for every prime `p` (including 2), `k ≥ 2`, and any `n`: `|S(1,n;p^k)| ≤ 6√(p^k)` |
| `norm_kl_prime_zero_le` | Main | `S(1,0;p) = −1` |
| `const_pow_omega_le` | Assembly | `C^{ω(c)} ≤ K_δ c^δ` (for any `C ≥ 1`) |
| `norm_kloosterman_le_major` | Assembly | `LocalKlBound α C ⟹ |S(1,n;c)| ≤ C^{ω(c)} c^α` (twisted multiplicativity) |
| **`kloostermanBound_of_local`** | Assembly | `LocalKlBound α C ⟹ ∀δ>0, KloostermanBound (α+δ)` |
| **`tau_isBigO_of_kloostermanFamily`** | Assembly | `0 ≤ α`, `∀δ>0, KloostermanBound(α+δ)` ⟹ `∀ε>0, τ(n) = O(n^{(11+α)/2+ε})`, using the unconditional `PoincareFormula` from `TauBound` |
| `localKlBound_half`, `localKlBound_twoThirds` | Main | `PrimeKlBound (1/2)` resp. `(2/3)` ⟹ `LocalKlBound` with the same exponent |

Sanity check: the `example` in `Assembly.lean` recovers the existing `47/8` result from
`kloostermanBound_three_quarters`.

How the odd prime-power proof works. It is elementary and needs no Gauss-sum evaluation.

1. Put `x = p^j`. Then `x³ = 0` and `(1+xt)⁻¹ = 1 − xt + x²t²`.
2. Averaging over `u ↦ u(1+xt)` gives `p^k S = ∑_u ψ(f(u)) Q(x(u−bū), x²bū)`.
3. Shifting by `t = s + h` gives `|Q|² = p^k ∑_{x²h=0} ψ(hA)`. This uses that `2` and `bū` are units.
4. That sum is invariant under `h ↦ h+p`. So it vanishes unless `p^{j+1}(u−bū) = 0`, and it has at most
   `p^{k−1}` terms.
5. Combining with `card_sqrt_le` (at most `4p^{j+1}` such `u`) gives `|S| ≤ 4p^{k/2}`.
6. If `p | b`, the set of such `u` is empty, so `S = 0`.

For `p = 2` and odd `k`, the existing bound `4·2^{⌈k/2⌉}` is already within a constant (`4√2 ≤ 6`) of `2^{k/2}`.
For even `k`, the existing bound `4p^{k/2}` is already sharp.

### (2) Lean, conditional on named hypotheses (axiom-clean)

The named hypotheses are statements about prime moduli only, and both are true theorems in the literature:

* `PrimeKlBound α := ∃ C, ∀ p prime, ∀ b : ZMod p, b ≠ 0 → |kl p 1 b| ≤ C p^α`;
* `SaliePrimeBound := PrimeKlBound (2/3)`;
* `WeilPrimeBound := ∀ p prime, ∀ b ≠ 0, |kl p 1 b| ≤ 2√p`. This is exactly Weil's statement for `p ∤ ab`
  with `a = 1`.

| Theorem | Statement |
|---|---|
| `kloostermanBound_twoThirds_of_salie` | `SaliePrimeBound → ∀δ>0, KloostermanBound (2/3+δ)` (**G1 Kloosterman part**) |
| **`tau_isBigO_35_6_of_salie`** | `SaliePrimeBound → ∀ε>0, τ(n) = O(n^{35/6+ε})` (**G1**) |
| `kloostermanBound_half_of_weil` | `WeilPrimeBound → ∀δ>0, KloostermanBound (1/2+δ)` (**G2 Kloosterman part**) |
| **`tau_isBigO_23_4_of_weil`** | `WeilPrimeBound → ∀ε>0, τ(n) = O(n^{23/4+ε})` (**G2**, Weil 1948) |
| `tau_isBigO_23_4_of_primeKlBound` | the same conclusion from `|S(1,b;p)| ≤ C√p` with any constant `C` |

Not formalized in the exact sharp form: `|S(a,b;c)| ≤ τ(c) gcd(a,b,c)^{1/2} c^{1/2}`. It is not needed for τ,
because the `C^{ω(c)} ≪ c^δ` form is enough. With the pieces above, the remaining gaps would be the factor
`6` (the sharp constant is `2`, and `p = 2` needs `2√2`) and the `gcd` bookkeeping.

### (4) Numerical

`scripts/weilkloosterman/check_bounds.py` computes `max_b |S(1,b;q)|/√q`:

* `q = p` for `p ≤ 101`: at most 1.92, which is below 2;
* `q = p³` and `3⁵`: at most 2.000;
* `q = 2^k`, `k = 3, …, 9`: at most 2.83, which is below `2√2` and below 6.

## What remains: the prime modulus

### G1 (`SaliePrimeBound`): assessment

The natural route is the sixth moment. It works exactly like the fourth-moment proof in `TauBound/KlPrime.lean`:

1. `∑_{a,b}|S(a,b;p)|⁶ = p² N₆`, where `N₆ = #{x,y ∈ (F_p^×)³ : Σx = Σy, Σx⁻¹ = Σy⁻¹}`.
2. The orbit argument gives `(p−1)|S(1,t)|⁶ ≤ p²N₆ − (p−1)⁶ − 2(p−1)`.
3. So it suffices to show `N₆ − (p−1)⁶/p² ≪ p³`.
4. Write `N₆ = ∑_{u,v} M(u,v)²`, where `M(u,v) = #{x ∈ (F^×)³ : Σx = u, Σx⁻¹ = v}`.
5. Fibre over `x₃`. For `s = u − x₃ ≠ 0` and `r = v − 1/x₃ ≠ 0`, the pair `(x₁, x₂)` is a root pair of
   `z² − sz + s/r`. This gives `M(u,v) = p + E(u,v) + O(1) + (p−1)[uv=1]`, where
   `E(u,v) = ∑_x χ(x(u−x)(vx−1)((u−x)(vx−1) − 4x))`.
6. `E(u,v)` is a quadratic-character sum of a **quintic**, that is, a genus-2 curve.
7. So `N₆ − (p−1)⁶/p² ≪ p³` follows from the pointwise bound `|E(u,v)| ≪ √p` for all but `O(p)` pairs
   `(u,v)`.

I could not find an elementary shortcut. Computing `∑_{u,v}E²` directly leads to 2-variable sums of
characters of quartics, which again need a Hasse-type bound.

**Needed input:** the Riemann hypothesis for hyperelliptic curves `y² = f(x)` over the prime field `F_p`.

* It is not in Mathlib. There is no Hasse bound even for elliptic curves. Mathlib does have
  `Polynomial.hasseDeriv`, Gauss sums, and Jacobi sums.
* Stepanov's method over `F_p` itself needs no extension fields and no zeta function. It gives
  `|#{y²=f} − p| ≤ C_m √p` for `p ≫ m`, and the small `p` go into the constant.
* The nondegeneracy (squarefreeness) of the quintic for generic `(u,v)` must also be checked.

**Estimate:**

| Piece | Lines of Lean |
|---|---|
| Stepanov for hyperelliptic curves (auxiliary polynomial, Hasse-derivative vanishing, the linear-algebra dimension count) | ~1200–1800 |
| Sixth moment, fibration, degenerate cases | ~600–900 |
| **Total** | **~2000–2700**, several agent-days |

This is also the natural ceiling of the method. For the `2k`-th moment with `k ≥ 4`, fibring down to curves
loses too much: square-root cancellation on the whole `(k−2)`-dimensional variety (Deligne) would be needed.
So the elementary moment method stops at `2/3`, which matches the history.

### G2 (`WeilPrimeBound`): assessment

There is no route that stays over `F_p`. A Stepanov-type bound over `F_p` alone is trivial for the
Kloosterman curve, whose genus is about `p`. The standard route has two parts.

1. **Rationality.** `exp(∑_r K_r T^r/r) = 1 + K₁T + pT²`, where `K_r` is the Kloosterman sum over `F_{p^r}`
   with `ψ∘Tr`. The proof is elementary:
   * write `λ(f) = ψ(−c₁ ± c_{d−1}/c_d)` on monic `f`;
   * show `λ` is multiplicative;
   * show `∑_{deg f = d} λ(f) = 0` for `d ≥ 3`;
   * then match the Euler product over irreducible polynomials against point counts over `F_{p^r}`.

   This needs unique factorization over `F_p[X]`, the roots of irreducible polynomials in `GaloisField p r`,
   and trace compatibility. Estimate: ~1500–2500 lines.
2. **Stepanov for Artin–Schreier.** Prove `|K_r| ≤ C p^{r/2}` for all even `r` (or all large `r`), using
   Stepanov's auxiliary polynomial for `y^p − y = x + b/x` over `F_{p^r}`, or Bombieri–Stepanov. Estimate:
   ~1500–3000 lines.
3. **Amplification (cheap).** `K_r = −(α^r+β^r)` with `αβ = p` and `|K_r| ≤ Cp^{r/2}` for all `r` give
   `|α| = |β| = √p`, hence `|K₁| ≤ 2√p`.

Total: **~4000–7000 lines**, a multi-week project.

There is no shortcut through Mathlib's Gauss and Jacobi sums: the Mellin expansion
`K = (1/(p−1)) Σ_χ g(χ)² χ̄` only gives the trivial bound. Hasse–Davenport does not apply directly, because
Kloosterman sums are not monomials in Gauss sums.

**Recommendation.** Do G1's hyperelliptic Stepanov first. It is a reusable Mathlib-level result (Hasse–Weil
for `y² = f(x)` over `F_p`), and it immediately gives `35/6`. G2 is better done as a separate project:
"rationality of Kloosterman L-functions plus Stepanov over `F_q`".

## Literature

* Salié, *Über die Kloostermanschen Summen S(u,v;q)*, Math. Z. 34 (1932).
* Davenport, *On certain exponential sums*, J. reine angew. Math. 169 (1933).
* Weil, *On some exponential sums*, PNAS 34 (1948).
* Stepanov (1969–72). Schmidt, *Equations over Finite Fields: An Elementary Approach*, Ch. I–II.
* Iwaniec–Kowalski, *Analytic Number Theory*, Ch. 11. This covers Stepanov's method, Kloosterman sums, and
  §11.7 on the elementary prime-power evaluation.
* Iwaniec, *Topics in Classical Automorphic Forms*, §4.3.
