# The twisted second moment of `L(Δ, s)` (2026-11-06)

**Status.** Level 1: Lean, axiom-clean, no hypotheses.

    nice -n 10 lake build RamanujanTau.TwistedMoment.Main      # exit 0

* Every `#print axioms` in `TwistedMoment/Main.lean` (9 names) gives `[propext, Classical.choice, Quot.sound]`.
* `grep` finds no `sorry`, `admit`, `native_decide` or `axiom` in `RamanujanTau/TwistedMoment/`.
* There are 18 files, about 3.4k lines. No committed file was modified.

## Headline

```lean
theorem twisted_moment : ∃ C : ℝ, 0 ≤ C ∧ ∀ (h k : ℕ), 1 ≤ h → 1 ≤ k → ∀ X : ℝ, 2 ^ (300 : ℕ) ≤ X →
    ‖TwAv h k X (X ^ (299 / 300 : ℝ)) - MainTw h k X (X ^ (299 / 300 : ℝ))‖ ≤
      C * ((h * k : ℕ) : ℝ) ^ 33 * X ^ (599 / 600 : ℝ)
```

Here `H = X^{299/300}`, and:

* `TwAv h k X H = (1/H) ∫_X^{X+H} ∫_{16}^u |L(Δ,6+it)|² ((h/k)^{it} + (k/h)^{it}) dt du`.
  This is the **symmetrised** twist `2|L|² cos(t log(h/k))`, averaged in the upper limit.
* `MainTw h k X H = 2√(hk) Σ_m ι_k(m+1) ι_h(m+1) (m+1)^{−1} P̃(2 log(m+1) − log hk, 0, X, H)`.
  * `ι_a(x) = [a ∣ x] λ(x/a)`.
  * `P̃(Λ, 0, X, H) = ∫_{16}^X V(Λ − 2log(t/2π)) dt + (1/H)∫_X^{X+H} (X+H−t) V(…) dt` is the
    averaged smoothed diagonal weight.
  * So `MainTw` is exactly the contribution of the diagonal `kM = hN`. For coprime `h, k` it is
    `(2/√(hk)) Σ_r λ(hr)λ(kr) r^{−1} P̃(log(hk r²) − log hk, 0, X, H)`.
* Coprimality is **not** assumed. The error is `O((hk)^{33} X^{1−1/600})`, so `δ = 1/600` with the
  polynomial `(hk)^{33}`.

**Sharp-cutoff and weighted forms.** `TwAv(X₂) − TwAv(X₁)` is the moment against a trapezoid weight
that is 1 on `[X₁ + H₁, X₂]`. Since `|L|² ≥ 0`, these give majorants of `∫_{X₁}^{X₂}` for upper bounds,
which is all (MV2) needs.

## Method

1. **Generic Good machinery** (`Defs`, `Rankin2` … `OffTotal`, `GParam`).
   * The whole off-diagonal analysis of `GoodSecondTerm2` was re-run for an arbitrary sequence `g`
     with `[GoodSeq g]`. That class asks for:
     * `g 0 = 0`;
     * the Rankin bound `Σ_{n≤N} g² ≤ N`;
     * the shifted-convolution bound `|Σ_{n≤N} g(n)g(n+ℓ)| ≤ (N+ℓ)^{20/21} ℓ^{1/21}`;
     * a `V`-shift `c ≥ 0`.
   * Constants are normalised to 1 and are uniform over all instances.
   * `gavgOff_le` gives `‖Σ_p zz g T₁ H p‖ ≤ C e^{8c} T^{599/600}`, with `C` absolute.
   * The shift `c` enters through `Dfac(Λ − c, T') = Dfac(Λ, T'e^{c/2})` and a factor `e^{6c}`.
2. **Twisting** (`TwAFE.twist_reindex`).
   * Put `x = kM` and `y = hN`. Then
     `(Σ_{M,N} b_t(M,N)) (h/k)^{it} = √(hk) Σ_{x,y} ι_k(x) ι_h(y) (xy)^{−1/2} (y/x)^{it} V(log xy − log hk − L_t)`.
   * The twisted moment is therefore a Good-type double sum with coefficients `(ι_k, ι_h)` and shift `c = log hk`.
3. **Polarisation** (`polarise`, `twist_pointwise`).
   * `α(x)β(y) + β(x)α(y) = ((α+β)(x)(α+β)(y) − (α−β)(x)(α−β)(y))/2`.
   * So the symmetrised twist reduces to two single-sequence sums with `g_± = r(ι_k ± ι_h)`.
   * `r = S^{−1/2}`, where `S = 4(A + C + 1)(hk)^{24}`.
4. **SCS input** (`TwCoef.prefix_eq`, `TwSeq.iota_scs`, `goodSeq_gS`).
   * A prefix sum `Σ_{x≤N} ι_a(x) ι_b(x+ℓ)` equals `HeckeAFE.shiftSum2 b a ℓ N_t` with `N_t ≤ N + ℓ`.
     The truncation `N_t = max(⌊N/a⌋, ⌊(a⌊N/a⌋+ℓ)/b⌋)` is exact.
   * So `SCS2Coprime.scs2_general` gives `≪ (N+ℓ)^{20/21} ℓ^{1/21} (ab)^{12}`.
   * Rankin along multiples gives `Σ ι_a² ≤ A N`.
   * Hence `g_±` are `GoodSeq`s.
5. **Averaging and diagonal** (`GAvg.gavg_eq`, `TwMain`).
   * `(1/H)∫∫ Σ_q bG2 g g = Σ_q zzF g`. The diagonal is split off, and `g₊² − g₋² = 4r² ι_k ι_h`
     yields `MainTw`.
   * The AFE error `O(t^{−1/2})` contributes `O(X^{1/2})`.
   * The total error is `√(hk)·S·C·(hk)^8·X^{599/600} ≪ (hk)^{33} X^{599/600}`.

## Files (`RamanujanTau/TwistedMoment/`)

| file | content |
|---|---|
| `Defs` | `GoodSeq` class, generic `shiftSum` |
| `Rankin2`, `SCSAbel`, `Pair`, `NonS`, `Sums`, `Regions`, `SPart`, `OffBound`, `OffTotal` | generic copies of `GoodSecondTerm2`. `Pair.norm_zz_le` and `OffTotal.off_avg_bound` carry the shift `c` and uniform constants |
| `GParam` | `gavgOff_le` (parameters `H = T^{299/300}`, `M₀ = ⌊H⌋`, `h₂ = ⌊T^{1/150}⌋`, `ε = 1/600`) |
| `TwCoef` | `iota`, `sum_dvd`, `iota_rankin`, `inner_m`, **`prefix_eq`** |
| `TwSeq` | `iota_scs`, `Ssz`, `gS`, **`goodSeq_gS`** |
| `TwAFE` | `wq`, `bG2`, **`twist_reindex`**, `polarise` |
| `GAvg` | `zzF`, `vq`, **`gavg_eq`** |
| `TwFinal` | `ph`, `twist_pointwise`, the averaging operator `Av`, `MainTw`, `TwAv` |
| `TwMain` | **`twisted_moment`** |
| `Main` | headlines, `#print axioms` |

## What (MV2) needs, and gaps

* **Shape for Hafner (MV2).** `∫_T^{3T} |L M²|² ≪ T` with **real** mollifier coefficients `c = b ∗ b`.
  Expanding `|M²|² = Σ_{h,k≤y²} c(h)c(k)(hk)^{−1/2}(k/h)^{it}` is symmetric in `(h, k)`. So only the
  **symmetrised** twist `(h/k)^{it} + (k/h)^{it}` enters, which is exactly what is proved.
  * Only an upper bound is needed, so the trapezoid-weighted form suffices.
  * Summing over `h, k ≤ y² = T^{2θ}` costs `T^{136θ}`. The error stays power-saving for
    **`θ < 1/81600`**, giving `∫ |LM²|² w = Σ_{h,k} c(h)c(k)(hk)^{−1/2} MainTw(h,k) + O(T^{1−1/600+136θ})`.
* **Gap 1 (Laurent data, not formalised).** `MainTw` is given exactly as the smoothed diagonal series.
  * Its asymptotic evaluation needs `D_{h,k}(s) = Σ_r λ(hr)λ(kr) r^{−s} = R(s) ρ(h₁)ρ(k₁)` (Hecke
    multiplicativity). That gives `MainTw ≈ (2/√(hk)) ρ(h)ρ(k) r₀ [X log X + …]`.
  * It also needs a contour shift of the Mellin weight, as in `GoodSecondTerm`.
  * This, and the quadratic form (QF) of `docs/SELBERG_COEFFS.md` §3, remain open for (MV2).
* **Gap 2.** The antisymmetric part `(h/k)^{it} − (k/h)^{it}` is not covered: the polarisation uses
  real sequences. It would need a Hermitian (complex-coefficient) version of the generic machinery,
  and it is not needed for (MV2).
* The exponents `33` and `1/600` are not optimised.
