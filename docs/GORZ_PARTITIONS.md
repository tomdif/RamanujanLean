# Griffin–Ono–Rolen–Zagier for the partition function, in every degree

**Result.** For every degree `d ≥ 0`, the Jensen polynomial

```
J^{d,n}(X) = Σ_{j=0}^{d} C(d,j) p(n+j) X^j        (JensenThreshold.jensen d n)
```

is hyperbolic (all roots real) for all sufficiently large `n`. The stronger GORZ statement is also proved. After
renormalization, `Ĵ^{d,n}(X) = J^{d,n}(e^{−A}(δX − 1)) / (Mmain(n)·δ^d)` converges to `H_d(X/2)`, both
coefficientwise and pointwise. Here `H_d` is the physicists' Hermite polynomial.

Reference: M. Griffin, K. Ono, L. Rolen, D. Zagier, *Jensen polynomials for the Riemann zeta function and other
sequences*, PNAS 116 (2019) 11103–11110. The theorem formalized here is their Theorem 1 (with Theorem 3 as the
analytic input), specialised to `p(n)`. For `p(n)` the result is also their Theorem 5 / Corollary, first
conjectured by Chen–Jia–Wang.

## Evidence levels

| Statement | Lean name | Level |
|---|---|---|
| `H_d` takes strict alternating signs at `d+1` increasing points | `GORZ.H_alternating` | **(1)** axiom-clean |
| `H_d = Π_{i<d}(X − r_i)` with `r_0 < … < r_{d−1}` (simple real roots) | `GORZ.H_simple_roots`, `GORZ.H_hyperbolic` | **(1)** |
| Newton forward-difference identity in **every** degree (previously only `d = 6, 7`) | `GORZ.newtonId` | **(1)** |
| `γ_k(n) = Δ^k w(0)/δ^k → c_k` (GORZ Thm 3 for `p(n)`) | `GORZ.tendsto_gam` | **(1)** |
| `Ĵ^{d,n}(x) → H_d(x/2)` for every real `x` | `GORZ.tendsto_Gn` | **(1)** |
| `coeff_i Ĵ^{d,n} → coeff_i H_d(X/2)` for every `i` | `GORZ.tendsto_coeff_Jhat` | **(1)** |
| **`∀ d, ∀ᶠ n in atTop, Hyperbolic (jensen d n)`** | **`GORZ.jensen_eventually_hyperbolic`** | **(1)** |
| `∀ d, ∃ N, JensenTail d N` | `GORZ.jensen_hyperbolic_from` | **(1)** |

`#print axioms` for each of these (`RamanujanTau/GORZ/Main.lean`) gives `[propext, Classical.choice, Quot.sound]`.
The files contain no `sorry`, no new `axiom`, no `native_decide`, and no named hypotheses. The only
analytic input about `p(n)` is the repo's own `Rademacher.p_sub_main_le`, used through
`JensenThreshold.Tail.rel_err`.

The result is **not effective as stated**. The proof produces explicit constants (`gam_close`), but the
final step uses `Filter.Tendsto` and no explicit `N(d)` is extracted. For effective thresholds at fixed `d`, see
`docs/JENSEN_THRESHOLDS.md` (`N(6) = 610`, `N(7) = 908`).

## Headline statements

```lean
theorem GORZ.jensen_eventually_hyperbolic (d : ℕ) :
    ∀ᶠ n in atTop, JensenThreshold.Hyperbolic (JensenThreshold.jensen d n)

theorem GORZ.tendsto_coeff_Jhat (d i : ℕ) :
    Tendsto (fun n : ℕ => (Jhat d n).coeff i) atTop (𝓝 ((H d).coeff i))
-- Jhat d n = C ((Mmain n * δ^d)⁻¹) * (jensen d n).comp (C (exp (-A)) * (C δ * X - 1)),
--   δ = δv (uk 1 n) = √(−f''(0)/2),  A = Av (uk 1 n) = f'(0),  f(s) = log Mmain(n+s) + const.

theorem GORZ.tendsto_Gn (d : ℕ) (x : ℝ) :
    Tendsto (fun n : ℕ => Gn d n x) atTop (𝓝 ((H d).eval x))
-- Gn d n x = Σ_k C(d,k) γ_k x^{d−k} (δx−1)^k = (jensen d n).eval (e^{−A}(δx−1)) / (Mmain n δ^d)

theorem GORZ.tendsto_gam (k : ℕ) : Tendsto (fun n : ℕ => gamv n k) atTop (𝓝 (cH k))
-- cH 0 = 1, cH 1 = 0, cH (k+2) = −2(k+1) cH k   ( = (d/dy)^k e^{−y²} at 0 )

theorem GORZ.H_alternating (d : ℕ) : ∃ y : ℕ → ℝ, (∀ i < d, y i < y (i + 1)) ∧
    ∀ i ≤ d, 0 < (-1 : ℝ) ^ (d - i) * (H d).eval (y i)
-- H d = Σ_{k≤d} C(d,k) cH k X^{d−k} = H_d(X/2);  H 6 = X⁶−30X⁴+180X²−120, H 7 = X⁷−42X⁵+420X³−840X (checked)
```

## Proof outline (as formalized)

1. **Hermite (`Hermite.lean`).** `H d` is defined in Appell form. Then `H_{d+1}' = (d+1)H_d` and
   `H_{d+1} = X H_d − 2H_d'`. The recursion is proved by showing that `D_d = H_{d+1} − XH_d + 2H_d'` satisfies
   `D_d' = d·D_{d−1}` and `D_d(0) = c_{d+1} + 2d c_{d−1} = 0`. `H d` is monic of degree `d`, with parity
   `H_d(−x) = (−1)^d H_d(x)`. Interlacing goes by induction on `d`. The IVT gives roots `r_i` between the
   alternation points, so `H_d = Π(X − r_i)` (`roots_of_alternating`), hence `(−1)^{d−1−i} H_d'(r_i) > 0`
   (`prod_derivative_sign`, by induction on the product), hence `(−1)^{d−i}H_{d+1}(r_i) = 2(−1)^{d−1−i}H_d'(r_i) > 0`.
   Adding the points `±Y` (Y large, from `tendsto_atTop_of_leadingCoeff_nonneg` and parity) gives `d+2` alternation points.
2. **Newton identity (`Newton.lean`).** Mathlib's Gregory–Newton formula (`shift_eq_sum_fwdDiff_iter`) gives
   `w_j = Σ_k C(j,k)Δ^k w(0)`. Combined with `C(d,j)C(j,k) = C(d,k)C(d−k,j−k)` and the binomial theorem, this
   yields `NewtonId d` for all `d`. So `J(e^{−A}(δx−1)) = Mmain(n)·δ^d·Ĝ(x)` (`eval_jensen_eq'`).
3. **Uniform derivative bounds (`Bounds.lean`).** Every monomial `U^{-p}(U−1)^{-q}` of the repo's generic
   derivative data `Pz m` has `p+q ≥ 2m−1` (`Pz_degOK`, by induction through `dZ`/`normZ`). Hence
   `|f^{(m)}(s)| ≤ (a/2)^m B_m U₀^{1−2m}` for all `m ≥ 1` and `s ≥ 0` (`fch_bound`). From the explicit `Pz 2`,
   `f''(0) ≤ −(a/2)²U₀^{-3}/2`, so `(a/4)t³ ≤ δ ≤ (a/2)(B₂+1)t³` with `t = U₀^{-1/2}`. Consequently
   `|Φ_m(s)| ≤ 2^m B_m t^{m−2}` for `m ≥ 2`, `|Φ₁| ≤ X a B₂` and `Φ₀ ≤ (a/2)²B₂X²/2` on `[0,X]`.
4. **Leibniz chain.** The repo's `gs` is the Leibniz chain for `(e^φ)^{(k)}`. It is dominated by the chain of
   the constant majorants (`gs_abs_le`) and is continuous in its inputs (`gs_tendsto`). At the limit inputs
   `Φ₂ = −2`, `Φ_m = 0` otherwise, it equals `c_k` (`gs_Φinf`).
5. **Main estimate (`Limit.lean`, `gam_close`).** For `n ≥ 2` and `U₀ ≥ 12`:
   `|γ_k − gs(Φ)_k(0)| ≤ 2^k M_{k+1} k^{k+1} δ + 2^k e^{ψ₀} · 4(2k+3)! 2^{2k+3} (4/a)^k t^{k+2}`.
   This combines four facts:
   * Taylor's theorem for `e^φ` to order `k+1` (the repo's `taylor_bounds`);
   * `Σ_j (−1)^{k−j}C(k,j) jⁱ = 0` for `i < k` and `= k!` for `i = k` (Mathlib `fwdDiff_iter_pow_eq_zero_of_lt`, `fwdDiff_iter_eq_factorial`);
   * the Rademacher bound `|ε_j| ≤ 2U³e^{−U/2}/(U−1) ≤ 4N!2^N U₀^{2−N}` with `N = 2k+3`;
   * `δ^k ≥ (a/4)^k t^{3k}`.

   Since `δ → 0`, `t → 0` and `gs(Φ)_k(0) → c_k`, this gives `γ_k → c_k`.
6. **Hyperbolicity.** By step 5, `Ĝ_n(y_i) → H_d(y_i)` at the `d+1` alternation points of step 1. So eventually
   `Ĝ_n` alternates in sign at those points. Since `x ↦ e^{−A}(δx−1)` is increasing, `J^{d,n}` alternates at
   the image points, and `JensenThreshold.hyperbolic_of_alternating` concludes.

## Files (`RamanujanTau/GORZ/`)

| File | Contents |
|---|---|
| `Hermite.lean` | `cH`, `H`, `derivative_H`, `H_succ`, `H_monic`, `natDegree_H`, `eval_H_neg`, `prod_derivative_sign`, `roots_of_alternating`, **`H_alternating`**, `H_simple_roots`, `H_hyperbolic` |
| `Newton.lean` | `fd`, `gregory_newton`, `choose_sum`, **`newtonId`** (all `d`) |
| `Bounds.lean` | `Pz_degOK`, `Bz`, `abs_evalZ_le`, `fch_bound`, `fch2_zero_le`, `δ_lower`, `δ_upper`, `Φ_bound_ge2`, `Φ1_bound`, `Φ0_le`, `Φ2_zero`, `gs_abs_le`, `gs_tendsto`, `Φinf`, `gs_Φinf` |
| `Limit.lean` | `wv_eq'`, `eps_le`, `alt_pow_sum_*`, `psi`, `gsΦ_bound`, `taylor_e`, **`gam_close`**, `tendsto_uk`, `tendsto_δ`, `tendsto_gsΦ`, **`tendsto_gam`**, `Gn`, `eval_jensen_eq'`, **`tendsto_Gn`**, **`jensen_eventually_hyperbolic`** |
| `Coeff.lean` | `Jhat`, `Gpoly`, `Jhat_eq_Gpoly`, `coeff_lin_pow`, **`tendsto_coeff_Jhat`** |
| `Main.lean` | `jensen_hyperbolic_from`, sanity checks `H 6`, `H 7`, `#print axioms` |

Dependencies: `JensenThreshold.Basic`, `JensenThreshold.Tail.{Calculus, Model, Setup, Link, Box2}` (definitions
`jensen`, `Hyperbolic`, `hyperbolic_of_alternating`, `fch`, `Pz`, `δv`, `Φv`, `gs`, `taylor_bounds`, `wv`,
`gamv`, `rel_err`). None of those files is modified. Nothing is added to the root `RamanujanTau.lean`.

Build (one process, this machine):

```
lake build RamanujanTau.GORZ.Main
```

Each module takes 6–15 s (Hermite ~6 s, Newton ~11 s, Bounds ~15 s, Limit and Coeff each well under a minute).
This assumes the `JensenThreshold.Tail` oleans are already built. `Main` takes 13 s.

## Remaining / possible extensions

* **Effective `N(d)` for all `d`.** The constants in `gam_close` are explicit, but `M_{k+1} = gs(ψ)_{k+1}(0)` and
  `B_m = Bz(Pz m)` grow super-exponentially. Turning the `Tendsto` arguments into an explicit `n₀(d)` would need
  an explicit quantitative version of the Hermite sign margins at the alternation points (step 1 is
  non-constructive: `Y` and the `r_i` come from the IVT and `atTop`). Not attempted.
* **The general GORZ Theorem 3** (arbitrary sequences with `log α(n+j) = log α(n) + A(n)j − δ(n)²j² + o(δ^d)`)
  is not stated abstractly. The proof here is specific to `p(n)` through `Mmain` and the `Pz` data. The same
  structure (Taylor + `gs` domination + `gs_tendsto` + `H_alternating`) would abstract with moderate effort.
* Riemann ξ / Taylor coefficients of `Ξ` (the other GORZ application) is not touched.
