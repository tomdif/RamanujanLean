# The prime number theorem for `τ` with the de la Vallée-Poussin error term

Lean: `RamanujanTau/TauPNTError/` (9 files, about 2140 lines, no `sorry`, no new axiom, no
`native_decide`). Build with `nice -n 10 lake build RamanujanTau.TauPNTError.Main`; it exits 0.
The module is not imported from `RamanujanTau.lean`.

**Evidence level (1).** All results are unconditional and axiom-clean. Every headline prints
`[propext, Classical.choice, Quot.sound]`. Deligne's bound is **not** used by the final
statements. A first version used `[DeligneBound]` (`psiDelta_error`, `tau_PNT_error`,
`tau_PNT_tau_error`); it is superseded by the `_uncond` versions below, which replace Deligne with
Rankin–Selberg.

Notation: `L(s) = Lnorm s = L(Δ, s + 11/2)`, `λ(p) = τ(p)p^{−11/2}` (`EdgeNonvanishing.lam`),
`Λ_Δ = TauPNT.vM` with `−L'/L(s) = Σ Λ_Δ(n) n^{−s}` (`TauPNT.negLogDeriv_eq_LSeries`).

## Headline statements

```lean
-- Uncond.lean
theorem tau_PNT_error_uncond : ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 256 ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ N : ℕ, 3 ≤ N →
    |∑ p ∈ Finset.range (N + 1) with p.Prime, lam p * Real.log p| ≤
      K * N * Real.exp (-b * Real.sqrt (Real.log N))
theorem psiDelta_error_uncond : ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 256 ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ x : ℝ, 3 ≤ x →
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vM n| ≤ K * x * Real.exp (-b * Real.sqrt (Real.log x))
theorem tau_PNT_tau_error_uncond : ∃ b : ℝ, 0 < b ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 9 ≤ N →
    |∑ p ∈ Finset.range N with p.Prime, ((tau p : ℤ) : ℝ) * Real.log p| ≤
      K * (N : ℝ) ^ (13 / 2 : ℝ) * Real.exp (-b * Real.sqrt (Real.log N))
```

These say the following:

- `Σ_{p≤N} τ(p)p^{−11/2} log p ≪ N exp(−b√log N)`;
- `ψ_Δ(x) = Σ_{n≤x} Λ_Δ(n) ≪ x exp(−b√log x)`;
- `Σ_{p<N} τ(p) log p ≪ N^{13/2} exp(−b√log N)`.

### Intermediate results (all unconditional)

```lean
-- LandauGen.lean: Landau's lemma, partial-fraction form (any analytic f)
theorem landau_pf {f : ℂ → ℂ} {c : ℂ} {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hfc : f c ≠ 0)
    (hbd : ∀ z ∈ closedBall c r, ‖f z‖ ≤ Real.exp M * ‖f c‖) :
    ∃ (S : Finset ℂ) (n : ℂ → ℕ), (∀ u ∈ S, dist u c ≤ r / 3 ∧ f u = 0) ∧
      ∀ z ∈ closedBall c (r / 12), f z ≠ 0 →
        ‖deriv f z / f z - ∑ u ∈ S, (n u : ℂ) * (1 / (z - u))‖ ≤ 24 * M / r
-- LogDerivBound.lean: L'/L ≪ log² in the de la Vallée-Poussin region
theorem negLogDeriv_bound : ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 32 ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re →
      Lnorm s ≠ 0 ∧ ‖negLogDeriv s‖ ≤ C * Real.log (|s.im| + 2) ^ 2
-- Smoothed.lean: the Riesz-smoothed PNT with error term
theorem smoothed_bound : ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 64 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 3 ≤ x →
    ‖∑' n : ℕ, (vM n : ℂ) * (phi 1 (n / x) : ℂ)‖ ≤ K * x * Real.exp (-a * Real.sqrt (Real.log x))
-- UncondH.lean: higher prime powers p^k, k ≥ 2
theorem sum_abs_vH_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Finset.Icc 1 N, |vH n| ≤ C * (N : ℝ) ^ (9 / 10 : ℝ)
```

Further results:

- `perron_shift` and `contour_bound` (`Contour.lean`) are the Perron identity and the explicit
  three-piece contour estimate.
- `F1_bound_vM`, `F1_bound_vP` and `A_vP_error` (`Unsmooth.lean`, `Uncond.lean`) are the Riesz-sum
  and prime-part bounds.
- `tau_form_of_prime_bound` (`PrimeForm.lean`) is partial summation from the `λ(p)` form to the
  `τ(p)` form.

## Proof

1. **Landau's lemma, partial fractions** (`landau_pf`). The proof is the factorization from
   `ZeroFreeRegion.landau`:
   - divide out the zeros in `|z−c| ≤ r/3` (`extract_zeros_poles`);
   - apply the maximum principle;
   - take a logarithm `H` of the quotient.

   `H'` is then bounded off the centre. Borel–Carathéodory gives `|H| ≤ 2M` on `|w−c| ≤ r/6`, and
   Cauchy's estimate on circles of radius `r/12` gives `|H'(z)| ≤ 24M/r`.
2. **`L'/L ≪ log²`** (`negLogDeriv_bound`). Put `z₀ = 17/16 + it` and `r = 3/2`.
   - The disc maps to unnormalized `5 ≤ Re ≤ 9`, so `tauL_poly_bound` gives `|L| ≤ A(10+|t|)²` there.
   - `tauL_norm_lower` gives `|L(z₀)| ≥ e^{−K}`. Hence `M ≪ log(|t|+2)`.
   - **Zero count:** at `z = z₀`, every zero has `Re(1/(z₀−u)) ≥ 1/4`, and `|L'/L(z₀)| ≤ B₀` from the
     Dirichlet series. So `Σ n_u ≤ 4(B₀ + 16M)`.
   - **Distances:** every zero `u` in the disc has `|Im u − t| ≤ 1/2`. By the uniform zero-free region
     `Re u ≤ 1 − c₀/(2 log(|t|+2))`. If `Re s ≥ 1 − c₀/(4 log)`, then `|1/(s−u)| ≤ 4 log/c₀`.
   - Together these give `‖L'/L(s)‖ ≤ 16M + Σ n_u·4 log/c₀ ≪ log²`. For `Re s ≥ 17/16` the trivial
     Dirichlet-series bound applies.
3. **Perron + shift to `Re s = 1`** (`perron_shift`).
   - Use `MeanSquare.perron_c` with `k = 1` on `Re s = 2`:
     `2π Σ Λ_Δ(n)(1−n/x)₊ = ∫ x^s P₁(s) (−L'/L)(s)`, where `P₁ = 1/(s(s+1))`.
   - The integrand is holomorphic on `1 ≤ Re ≤ 2`, since `L ≠ 0` there.
   - It is `≪ (1+|t|)^{−3/2}` by step 2 and `log² ≤ 32(1+|t|)^{1/2}`.
   - `Stirling.integral_line_eq_rpow` moves the line to `Re s = 1`.
4. **Contour** (`contour_bound`). Cut `Re s = 1` at `|t| = T`. Move the segment to
   `σ₀ = 1 − c/log(T+2)` by Cauchy's theorem for rectangles
   (`integral_boundary_rect_eq_zero_of_differentiableOn`). There are no zeros in `[σ₀,1]×[−T,T]`,
   by step 2. The pieces are bounded as follows:
   - left side: `≤ x^{σ₀}·16C₀ log²(T+2)·∫(1+|y|)^{−2}`;
   - horizontal sides: `≤ x·16C₀ log²(T+2)/(1+T)²`;
   - tails: `≤ 512C₀ x(1+T)^{−1/4}∫(1+|y|)^{−5/4}`.
5. **Optimization** (`smoothed_bound`). Take `T = exp(√log x) − 2`, so `log(T+2) = ℓ = √log x`.
   - `x^{σ₀} = x e^{−cℓ}`, `(1+T)^{−2} ≤ 4e^{−cℓ}` and `(1+T)^{−1/4} ≤ 2e^{−cℓ}`.
   - These give `≪ xℓ²e^{−cℓ} ≪ x e^{−(c/2)ℓ}`.
6. **Higher prime powers** (`sum_abs_vH_le`, no Deligne).
   - For `p²`: `|Λ_Δ(p²)| = |λ(p)²−2| log p` with `λ(p)² = τ(p)²/p¹¹` (`lam_sq_eq`). Rankin gives
     `Σ_{m≤√N} τ(m)²/m¹¹ ≪ √N`.
   - For `p^k` with `k ≥ 3`: `|Λ_Δ| ≤ 2‖α_p‖^k log p ≤ 2√N log N`, using `‖α_p‖² ≤ p`
     (`TauPNT.norm_sa_sq_le`). There are `≤ (N^{1/3}+1) log₂N` such pairs (`p, k`).
   - The pairs are indexed through the injective map `(p,j) ↦ p^{j+2}` (`Nat.Prime.pow_inj`). The
     total is `≪ √N log N + N^{5/6} log²N ≪ N^{9/10}`.
7. **Unsmoothing without Deligne** (`A_vP_error`).
   - Let `vP = Λ_Δ·1_{primes}`. Then `F₁(vP)(x) = Σ_{n≤x} vP(n)(x−n)` equals `F₁(Λ_Δ) − F₁(vH)`,
     which is `≪ x² e^{−aℓ} + x^{19/10} ≪ x²e^{−aℓ}`.
   - Apply Landau differencing (`TauPartialSums.main_ineq`) with `h = x e^{−(a/2)ℓ}`.
   - Short sums use `|vP(p)| = √(τ(p)²/p¹¹)·log p`, Cauchy–Schwarz and Rankin's
     `|Σ_{n≤N} τ(n)²/n¹¹ − cN| ≤ CN^{3/5}` (`EdgeNonvanishing.rs_partial`). This gives
     `Σ_{x<n≤x+h} |vP(n)| ≤ D log(2x)(h + (2x)^{3/5})`.
   - The result is `Σ_{n≤x} vP(n) ≪ x e^{−(a/4)ℓ}`. This is the prime sum, which gives
     `tau_PNT_error_uncond`. Adding `vH` gives `psiDelta_error_uncond`.
8. **`τ(p)` form** (`tau_form_of_prime_bound`). Use Abel summation (`TauPNT.abel_identity`) with
   `w(n) = n^{11/2}`. The partial sums are bounded by `B ≪ N e^{−(b/2)ℓ}` uniformly on `m ≤ N`:
   - for `m > √N`: `√log m ≥ ℓ/2`;
   - for `m ≤ √N`: the trivial bound `K√N`, and `√N ≤ 4Ne^{−(b/2)ℓ}`.

## Files

| file | content |
|---|---|
| `LandauGen.lean` | `landau_pf` |
| `LogDerivBound.lean` | `negLogDeriv_bound` |
| `Contour.lean` | `gx`, `Reg`, `logsq_le`, `norm_gx_le`, `perron_shift`, `contour_bound` |
| `Smoothed.lean` | `sq_mul_exp_le`, `smoothed_bound` |
| `Unsmooth.lean` | `F1_bound_vM`, `sqrt_log_le`; Deligne versions `psiDelta_error`, `tau_PNT_error` |
| `PrimeForm.lean` | `abel_bound`, `tau_form_of_prime_bound`; Deligne version `tau_PNT_tau_error` |
| `UncondH.lean` | `vP`, `vH`, `lam_sq_eq`, `abs_vH_pow_le`, `sum_abs_vH_le` |
| `Uncond.lean` | `F1_bound_vP`, `short_rs`, `A_vP_error`, `tau_PNT_error_uncond`, `psiDelta_error_uncond`, `tau_PNT_tau_error_uncond` |
| `Main.lean` | `#print axioms` for all 15 headlines |

## Gaps and remarks

- **The constants are ineffective.** `b`, `K` and `c` are existential. They inherit the uniform
  zero-free-region constant, which uses a compactness argument and finiteness of the low zeros, and
  the constants in `tauL_poly_bound`, `Kconst` and Rankin's `O(N^{3/5})`. The exponent `b` is a
  fixed fraction of the zero-free-region constant: `c ≤ c₀/4`, `a = c/2`, `b = a/4`, and `b/2` in
  the `τ(p)` form. It is not optimized.
- **Range of validity.** The statements are for `x ≥ 3` (`N ≥ 3`, or `N ≥ 9` in the `τ(p)` form).
  The `τ(p)` form sums over `p < N`; the `λ(p)` form sums over `p ≤ N`.
- **Method.** The proof uses a Riesz-smoothed (order 1) Perron formula. There is no truncated Perron
  formula, so no truncation-error analysis is needed. There is also no explicit formula over zeros
  and no Riemann–von Mangoldt input: only the local zero count `Σ n_u ≪ log`, which comes from the
  same Landau decomposition.
- The Wiener–Ikehara hypothesis of `TauPNT.tau_PNT` is not needed here. The unconditional
  `tau_PNT_error_uncond` implies `tau_PNT` in a much stronger form, but no bridging corollary is
  stated.
- **Not done:** a zero-density or Vinogradov–Korobov region (exponent `(log x)^{3/5}`), and an
  effective version.

## Literature

- de la Vallée Poussin (1899).
- Landau, *Handbuch* (1909).
- Titchmarsh, *Theory of the Riemann zeta-function*, §3.9–3.11 (Lemma α, the `ζ'/ζ ≪ log` bound)
  and §3.12.
- Iwaniec–Kowalski, *Analytic Number Theory*, Prop. 5.7, Thm 5.10 and Thm 5.13 (the PNT for
  `L(f,s)` with the classical error term).
- Montgomery–Vaughan, *Multiplicative Number Theory I*, Lemma 6.3 and §6.2.
- Moreno, "Prime number theorems for the coefficients of modular forms" (1972/74).
- Rankin (1939).
