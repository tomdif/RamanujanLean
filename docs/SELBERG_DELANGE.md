# Toward Selberg–Delange for `R(s)^{−1/2}`, and the Q⁰ bound

Lean: `RamanujanTau/SelbergDelange/` (6 files plus `Main.lean`). There is no `sorry`, no new
axiom and no `native_decide`. Build with `nice -n 10 lake build RamanujanTau.SelbergDelange.Main`.
The module is not imported from `RamanujanTau.lean`.

**Status (checkpoint, 2026-11-06).**

* Task 1 (bounds in the region) is **done**, in the `log²` form.
* A new, unconditional **Rankin–Selberg prime number theorem with de la Vallée-Poussin error** is
  **done**. It is the arithmetic input for the Selberg–Delange step.
* Task 2 (Selberg–Delange for the coefficients of `R^{−1/2}`) is **not done**. §3 explains why, and
  gives the route chosen instead.
* Task 3 (Q⁰ ≪ 1/log y) is **not done**. §4 maps what remains.

## 1. Statements (level 1 unless marked)

Notation:

* `KK(s) = (s−1)ζ(2s)R(s) = (s−1)ζ(s)L(Sym²Δ,s)`; this is `TauPNTUncond.KK`.
* `negLogDerivK = −KK'/KK`.
* `vR(p^k) = (α_p^k+β_p^k)² log p ≥ 0` is the von Mangoldt function of `ζ(2s)R(s)`. In particular
  `vR(p) = λ(p)² log p`.

```lean
-- LogDeriv.lean
theorem logDerivKK_bound : ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 400 ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re →
      KK s ≠ 0 ∧ ‖deriv KK s / KK s‖ ≤ C * Real.log (|s.im| + 2) ^ 2
-- Perron.lean
theorem perron_shiftK (hreg : RegK c C₀) (hc : 0 ≤ c) (hC₀ : 0 ≤ C₀) {x : ℝ} (hx : 1 ≤ x) :
    (2 * π : ℂ) * ∑' n, (vR n : ℂ) * (phi 1 (n / x) : ℂ) =
      (∫ y : ℝ, gK x (1 + y * I)) + ((π * x * (1 - 1 / x) ^ 2 : ℝ) : ℂ)
-- Smoothed.lean
theorem smoothed_boundK : ∃ a > 0, a ≤ 1/64 ∧ ∃ K ≥ 0, ∀ x ≥ 3,
    ‖∑' n, (vR n : ℂ) * phi 1 (n / x) - x (1 - 1/x)^2 / 2‖ ≤ K * x * exp (-a * √(log x))
-- Unsmooth.lean
theorem psiR_error : ∃ b : ℝ, 0 < b ∧ ∃ K X₀ : ℝ, 0 ≤ K ∧ ∀ x : ℝ, X₀ ≤ x →
    |psiR x - x| ≤ K * x * Real.exp (-b * Real.sqrt (Real.log x))   -- psiR x = Σ_{n≤x} vR n
-- PrimeDeligne.lean  (level 2, [DeligneBound], only for the prime powers)
theorem rs_prime_PNT_error [DeligneBound] : ∃ b > 0, ∃ K X₀, 0 ≤ K ∧ ∀ x ≥ X₀,
    |∑ p ∈ Icc 1 ⌊x⌋₊ with p.Prime, lam p ^ 2 * log p - x| ≤ K * x * exp (-b * √(log x))
```

Supporting results:

* `norm_KK_le`: `‖KK z‖ ≤ A(‖z‖+1)²` on `Re z ≥ 0.61`.
* `logDerivKK_right`, `regK_exists`, `pole_integral`, `contour_boundK`.
* `FR_bound`: `Σ_{n≤x} vR(n)(x−n) = (x−1)²/2 + O(x²e^{−a√log x})`.
* `diff_sandwich`: `hψ_R(x) ≤ F(x+h) − F(x) ≤ hψ_R(x+h)`.

## 2. Proofs in brief

### 2.1 The log-derivative bound (`LogDeriv.lean`)

This follows Titchmarsh §3.11, with `TauPNTError.LogDerivBound` as the template. The disc has to
be small, because `KK` has growth bounds only on `Re > 3/5`, through the Abel continuation
`KK = ζ(2·)·R1`.

* **Disc.** The centre is `z₀ = 33/32 + it` and the radius is `21/50`, so the disc lies in
  `Re ≥ 0.611`. The point `s` lies within `r/12`.
* **Lower bound at the centre.** `‖KK(z₀)‖ ≥ e^{−B₁}/32`, from `HH = exp(Σ cR n^{−s})`.
* **Landau.** `landau_pf` gives `‖KK'/KK(z) − Σ n_u/(z−u)‖ ≤ 24M/r`.
* **Counting zeros at `z₀`.** There `Re 1/(z₀−u) ≥ 1`.
* **The terms at `s`.** The zeros satisfy `Re u ≤ 1 − c₀/(2L)` by
  `Sym2ZeroFree.KK_zero_free_region_uniform`, so `|1/(s−u)| ≤ 4L/c₀`.

### 2.2 Perron with the pole (`Perron.lean`)

The pole of `−H'/H = −KK'/KK + 1/(s−1)` is removed explicitly. Since `P₁(s)/(s−1) = P₂(s−1)/2`,
Mellin inversion of the Riesz kernel (`RankinError.mellinInv_Pk`, k = 2) gives

    ∫_{Re s=2} x^s P₁(s)/(s−1) dy = π x (1−1/x)².

The remaining integrand `x^s P₁(s)(−KK'/KK)(s)` is holomorphic in the region. The rest of
`TauPNTError.Contour` / `Smoothed` then applies verbatim.

### 2.3 Unsmoothing (`Unsmooth.lean`)

Because `vR ≥ 0`, unsmoothing needs **no short-interval input**:

* `F1_diff` gives `hψ_R(x) ≤ F(x+h) − F(x) ≤ hψ_R(x+h)`.
* Take `h = x·exp(−(a/4)√log x)` and compare the two-sided differences at `x ± h`.
* For `x − h` use `√log(x−h) ≥ √log x / 2`.

### 2.4 Primes (`PrimeDeligne.lean`)

Under Deligne `|A_k(p)| ≤ 2`, so `vR ≤ 4Λ`. Mathlib's `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`
bounds the prime powers by `8√x log x`.

Without Deligne, the prime-square terms `Σ_{p≤√x}(λ(p)²−2)² log p` need fourth moments of `λ(p)`.
The repo has no such bound. Rankin–Selberg alone gives only `≪ x`, which is not enough.

## 3. Task 2: why the Hankel-contour route was not taken, and what replaces it

The contour route for `G(s) = R(s)^{−1/2} = (ζ(2s)/H(s))^{1/2}` needs four things.

1. **A holomorphic branch of `log KK` on the region `σ > 1 − c/log(|t|+2)`.** This region is not
   convex, because the boundary `1 − c/log(|t|+2)` is concave in t. Mathlib only provides
   primitives on balls and on `univ` (`Analysis/Complex/HasPrimitives`: `isExactOn_ball`,
   `isExactOn_univ`). The region *is* star-shaped about `s = 2`. A branch could be built by
   integrating `KK'/KK` along rays, but that needs a holomorphy-of-parametric-integral argument:
   new infrastructure, roughly 400–600 lines.
2. **Growth of `KK^{±1/2}`.** From the `log²` bound and `−KK'/KK = Σ vR n^{−s} − 1/(s−1)` on
   `Re > 1`, we get `|log KK(s)| ≤ C log(|t|+2)`. So `|KK(s)^{±1/2}| ≤ (|t|+2)^{C}` grows
   **polynomially**, with an ineffective `C`. The classical `|log ζ| ≤ log log t + O(1)` instead
   uses `|ζ(1+it)| ≪ log t`. The analogue for `H = L(Δ×Δ)` would need a near-convexity bound
   `|H(1+it)| ≪ (log t)^A`, which is not in the repo; the repo has only `≪ |t|` from Abel
   summation. Consequently the Perron kernel must be a Riesz mean of order `k > C+1`, and the
   unsmoothing then goes through `k` differencing steps.
3. **Hankel's formula `1/Γ(z) = (1/2πi)∫_H e^w w^{−z} dw`.** This produces the main-term constant
   `1/Γ(1/2)`. It is **not in Mathlib**.
4. The truncated Hankel contour and its error terms.

Items 1 and 3 are new library work. Estimate for the full contour route: 2.5–4k lines.

**The replacement: a real-variable Selberg–Delange theorem.** Granville–Koukoulopoulos, *Beyond
the LSD method for the partial sums of multiplicative functions*, Ramanujan J. (2019), prove the
following:

> If `f` is multiplicative, `|Λ_f| ≤ kΛ`, and `Σ_{p≤x} f(p) log p = κx + O(x/(log x)^A)`, then
> `Σ_{n≤x} f(n) = x Σ_{j<J} c_j (log x)^{κ−1−j} + O(x(log x)^{k−1−J}…)`.

The proof is an elementary iteration of `f·log = f ∗ Λ_f`. It uses no contour, no complex
logarithm and no Γ-function. That suits Lean much better.

**The arithmetic input is exactly `rs_prime_PNT_error`, now proved.** Here are the shapes needed:

* For `α` (coefficients of `L^{−1/2}`): `α(p) = −λ(p)/2`. This needs a PNT for `λ(p)` itself,
  which the repo has as `TauPNTError.tau_PNT_error_uncond`. Then κ = 0, but the second moment is
  driven by `λ(p)²`.
* For the generating function of `c·ρ` in (QF), the prime values are
  `f(p) ≈ −λ(p)²/2 + O(1/p)`, so `Σ_{p≤x} f(p) log p = −x/2 + O(x e^{−b√log x})`. This uses
  `rs_prime_PNT_error` under Deligne, so κ = −1/2.

## 4. Task 3 (Q⁰ ≪ 1/log y): what remains

See `docs/SELBERG_COEFFS.md` §§3, 6, 7 for the form. In order:

1. **The ρ-weighted diagonalization** `Q⁰(c) = Σ_d w(d)·y_d²` (paper, `SELBERG_COEFFS` §3). The
   repo has the unweighted `selberg_diag`. The weighted version needs care at primes with
   `λ(p) = 0`. Estimate 0.3–0.5k lines.
2. **The real-variable LSD theorem above**, for κ = −1/2, with the log-weighted variants
   `Σ f(n)/n·(log(x/n))^j`. Since only log means are needed, the first two terms suffice
   (`J = 2`). Estimate 1.5–2.5k lines. Level 2: `|Λ_f| ≤ kΛ` uses `|α(p^k)| ≤ 1` (Deligne).
3. **Selberg's smoothing** `b = α(1 − log n/log y)`. This converts the LSD main terms
   `(log x)^{−1/2}` into `y_d ≪ g(d)/log y` with `Σ_d w(d)g(d)² ≪ log y`; that is the
   Titchmarsh §10.13–10.16 bookkeeping. Estimate 1–1.5k lines.
4. **The companions** (log-weighted forms ≪ 1). These use the same LSD output with `j = 1, 2`.

Total estimate: 3–5k lines at level 2 on `[DeligneBound]`. The analytic inputs are all present
after this checkpoint: the zero-free region, `KK'/KK` bounds, and the RS-PNT with error.

## 5. Gaps and remarks

* **`log²` instead of `log`.** The bound is `KK'/KK ≪ log²(|t|+2)`, not `log`. That is enough
  for PNT-type contour shifts, and these are proved. For a contour Selberg–Delange it gives only
  polynomial growth of `KK^{±1/2}` (§3, item 2).
* **No prime form without Deligne.** `rs_prime_PNT_error` is level 2. Without Deligne the
  prime-square terms are uncontrolled; the `ψ_R` form is level 1.
* **Ineffective constants.** All constants (`c`, `C`, `b`, `K`, `X₀`) are ineffective, inherited
  from `Sym2ZeroFree`.
* **Not done:** Selberg–Delange (Task 2), and Q⁰ with its companions (Task 3).

## 6. Literature

* Titchmarsh, *The Theory of the Riemann Zeta-Function*, §§3.9–3.11 and §§10.9–10.22.
* Iwaniec–Kowalski, Thm 5.13 (PNT for `L(f×f̄)` with de la Vallée-Poussin error). The theorem
  number is from memory and has not been checked.
* Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, II.5 (Selberg–Delange).
* Granville–Koukoulopoulos, *Beyond the LSD method for the partial sums of multiplicative
  functions*, Ramanujan J. 49 (2019).
* Hafner, Math. Ann. 264 (1983); Selberg (1942).
