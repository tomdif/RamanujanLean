/-
# `ZetaMeanSquare`: the mean square of `ζ` off the critical line, and Rankin–Selberg Ω±(x^{1/4−ε})

See `docs/ZETA_MEAN_SQUARE.md`.

1. `zeta_mean_value_uniform` / `zeta_mean_value_dyadic`: uniformly for `1/2 < σ₀ ≤ σ ≤ 1`, `T ≥ 1`,
   `|∫ |ζ(σ+it)|² − ζ(2σ)T| ≤ C (T^{3/2−σ} + T^{2−2σ}(1+log T)²)` on `[1,T]` and on `[T,2T]`.
2. `zeta_mean_square_tendsto` (`1/2 < σ ≤ 1`, from `1`) and `zeta_mean_square_tendsto_zero`
   (`1/2 < σ < 1`, from `0`): `(1/T)∫|ζ(σ+it)|² dt → ζ(2σ)`.
3. `tau_rankin_omega_pm_quarter`: `∑_{n≤x} τ(n)²/n¹¹ − c₀x = Ω±(x^β)` for every `β < 1/4`
   (`cuspForm_rankin_omega_pm_quarter` for every nonzero level-one cusp form,
   `rs_omega_pm_quarter` for abstract Rankin–Selberg data).
-/
import RamanujanTau.ZetaMeanSquare.Zeta
import RamanujanTau.ZetaMeanSquare.Rankin

-- ζ mean square
#print axioms RamanujanTau.ZetaMeanSquare.zeta_mean_value_uniform
#print axioms RamanujanTau.ZetaMeanSquare.zeta_mean_value_dyadic
#print axioms RamanujanTau.ZetaMeanSquare.zeta_mean_square_tendsto
#print axioms RamanujanTau.ZetaMeanSquare.zeta_mean_square_tendsto_zero
#print axioms RamanujanTau.ZetaMeanSquare.riemannZeta_two_mul_real
#print axioms RamanujanTau.ZetaMeanSquare.mean_value_minus
#print axioms RamanujanTau.ZetaMeanSquare.riemannZeta_conj
#print axioms RamanujanTau.ZetaMeanSquare.tail_L2
#print axioms RamanujanTau.ZetaMeanSquare.err_L2
#print axioms RamanujanTau.ZetaMeanSquare.norm_zeta_fe_le
#print axioms RamanujanTau.ZetaMeanSquare.zeta_dyadic_upper
#print axioms RamanujanTau.ZetaMeanSquare.zeta_two_s_mean_sq
-- Rankin–Selberg Ω±
#print axioms RamanujanTau.ZetaMeanSquare.tau_rankin_omega_pm_quarter
#print axioms RamanujanTau.ZetaMeanSquare.cuspForm_rankin_omega_pm_quarter
#print axioms RamanujanTau.ZetaMeanSquare.cuspForm_omega_pm_quarter_of_bound
#print axioms RamanujanTau.ZetaMeanSquare.rs_omega_pm_quarter
#print axioms RamanujanTau.ZetaMeanSquare.false_of_conv_quarter
#print axioms RamanujanTau.ZetaMeanSquare.gamma_ratio_lower'
#print axioms RamanujanTau.ZetaMeanSquare.Zf_first_moment'
