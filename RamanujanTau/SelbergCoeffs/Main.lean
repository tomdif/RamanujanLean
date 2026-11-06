/-
# Arithmetic side of Selberg's mollifier for `L(Δ,s)`: headlines

See `docs/SELBERG_COEFFS.md`.  `λ(n) = τ(n)n^{−11/2}`; `L(Δ,s) = Σ λ(n)n^{−s}` (analytic
normalization, critical line `Re s = 1/2`, the repo's `Re s = 6`).

Level 1 (axiom-clean, unconditional):
* `alphaLoc_sq_sum` — the local square identity `(Σ_k α(p^k)X^k)² = 1 − λ(p)X + X²`;
* `lamN_mul_alpha_mul_alpha` — `λ ∗ α ∗ α = δ`: `α` are the coefficients of `L(Δ,s)^{−1/2}`
  (also `alpha_mul_alpha : α ∗ α = μ_Δ`, `lamN_mul_muD : λ ∗ μ_Δ = δ`);
* `abs_alphaLoc_le_pow` — `|α(p^k)| ≤ R^k` for any Satake pair with `‖a‖,‖b‖ ≤ R`;
* `alpha_sq_le_self` — `α(n)² ≤ n` for all `n` (no Deligne; Satake `‖a_p‖² ≤ p` from Rankin);
* `bSel_one`, `norm_bSel_le_sqrt` — Selberg's `b(n) = α(n)(1 − log n/log y)` has `b(1) = 1`,
  `|b(n)| ≤ n^{1/2}`;
* `selbergHyp_of_moll_uncond`, `tauL_positive_proportion_of_moll` — (MV2)+(SK) for Selberg's
  mollifier (`SelbergMollHyp`) imply `HafnerProportion.SelbergHyp`, hence the proportion;
* `selberg_diag`, `selberg_form_nonneg` — `Σ x_h x_k/[h,k] = Σ_d φ(d)(Σ_{d|h} x_h/h)² ≥ 0`;
* `lamN_mul_trunc_mul_trunc` — `(λ ∗ b₀ ∗ b₀)(N) = δ(N)` for `N ≤ y`, `b₀ = α·1_{≤y}`.

Level 2 (conditional on the class `[DeligneBound]`, `τ(p)² ≤ 4p^{11}`):
* `abs_alpha_le_one` — `|α(n)| ≤ 1` for **all** `n` (sharper than `d(n)`);
* `norm_bSel_le_one`, `selbergHyp_of_moll` — the size clauses with `β = 1, η = 0`;
* `sum_alpha_sq_div_le` — Selberg's lemma `Σ_{n≤N} α(n)²/n ≤ C (log N + 1)^{1/4}`.
-/
import RamanujanTau.SelbergCoeffs.Local
import RamanujanTau.SelbergCoeffs.Global
import RamanujanTau.SelbergCoeffs.Mollifier
import RamanujanTau.SelbergCoeffs.SelbergSum
import RamanujanTau.SelbergCoeffs.Quadratic

open RamanujanTau.SelbergCoeffs

-- Level 1
#print axioms RamanujanTau.SelbergCoeffs.alphaLoc_sq_sum
#print axioms RamanujanTau.SelbergCoeffs.abs_alphaLoc_le_pow
#print axioms RamanujanTau.SelbergCoeffs.abs_alphaLoc_le_one
#print axioms RamanujanTau.SelbergCoeffs.alpha_mul_alpha
#print axioms RamanujanTau.SelbergCoeffs.lamN_mul_muD
#print axioms RamanujanTau.SelbergCoeffs.lamN_mul_alpha_mul_alpha
#print axioms RamanujanTau.SelbergCoeffs.alpha_prime
#print axioms RamanujanTau.SelbergCoeffs.alpha_sq_le_self
#print axioms RamanujanTau.SelbergCoeffs.abs_alpha_le_sqrt
#print axioms RamanujanTau.SelbergCoeffs.bSel_one
#print axioms RamanujanTau.SelbergCoeffs.norm_bSel_le_sqrt
#print axioms RamanujanTau.SelbergCoeffs.selbergHyp_of_moll_uncond
#print axioms RamanujanTau.SelbergCoeffs.tauL_positive_proportion_of_moll
#print axioms RamanujanTau.SelbergCoeffs.selberg_diag
#print axioms RamanujanTau.SelbergCoeffs.selberg_form_nonneg
#print axioms RamanujanTau.SelbergCoeffs.lamN_mul_trunc_mul_trunc
#print axioms RamanujanTau.SelbergCoeffs.rs_real_le
-- Level 2 ([DeligneBound])
#print axioms RamanujanTau.SelbergCoeffs.abs_alpha_le_one
#print axioms RamanujanTau.SelbergCoeffs.norm_bSel_le_one
#print axioms RamanujanTau.SelbergCoeffs.selbergHyp_of_moll
#print axioms RamanujanTau.SelbergCoeffs.sum_alpha_sq_div_le
