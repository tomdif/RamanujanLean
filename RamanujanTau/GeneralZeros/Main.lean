/-
# Zeros of `L(f,s)` for every nonzero level-one cusp form `f`

See `docs/GENERAL_ZEROS.md`.

* Zero counting (`Count`): `N_f(T+1) − N_f(T) ≪ log T`, `N_f(T) ≪ T log T`, finiteness.
* Riemann–von Mangoldt (`RvMFinal`): `N_f(T) = (T/π) log(T/(2π e n₀)) + O(log T)`, `n₀` the first
  index with `a_f(n₀) ≠ 0`; `= (T/π) log(T/(2πe)) + O(log T)` when `a_f(1) ≠ 0`.
* Zero-free region (`ZFREigen`): for every normalized Hecke eigenform,
  `Re ρ ≤ (k+1)/2 − c/log|Im ρ|` and `Re ρ ≥ (k−1)/2 + c/log|Im ρ|` for `|Im ρ| ≥ t₀`
  (unconditional); at all heights under the real edge point `L(f,(k+1)/2) ≠ 0`.
* Sanity checks: `f = Δ`.
-/
import RamanujanTau.GeneralZeros.RvMFinal
import RamanujanTau.GeneralZeros.ZFREigen
import RamanujanTau.Basic

set_option autoImplicit false

namespace RamanujanTau.GeneralZeros

open Complex ModularForm
open RamanujanTau.HeckeConvexGeneral
open scoped Real MatrixGroups

/-- **Sanity check `f = Δ`**: `N_Δ(T) = (T/π) log(T/(2πe)) + O(log T)` from the general theorem
(here `N_Δ` counts the zeros of `HeckeConvexGeneral.heckeLambda Δ`, equivalently of `L(Δ,s)`, with
`0 < Im ≤ T`). -/
theorem riemann_von_mangoldt_discriminant :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
      |(zeroCount (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) T : ℝ) -
        T / π * Real.log (T / (2 * π * Real.exp 1))| ≤ C * Real.log T := by
  apply riemann_von_mangoldt_of_coef_one
  rw [coef_discriminant]
  simp [RamanujanTau.tauC, RamanujanTau.tau_one]

end RamanujanTau.GeneralZeros

#print axioms RamanujanTau.GeneralZeros.riemann_von_mangoldt_gen
#print axioms RamanujanTau.GeneralZeros.riemann_von_mangoldt_of_coef_one
#print axioms RamanujanTau.GeneralZeros.riemann_von_mangoldt_discriminant
#print axioms RamanujanTau.GeneralZeros.zeroCount_ge_T_log_T_gen
#print axioms RamanujanTau.GeneralZeros.rvm_nonordinate_gen
#print axioms RamanujanTau.GeneralZeros.window_count
#print axioms RamanujanTau.GeneralZeros.window_right
#print axioms RamanujanTau.GeneralZeros.zeroSet_finite
#print axioms RamanujanTau.GeneralZeros.zeroCountAB_add
#print axioms RamanujanTau.GeneralZeros.zeroCount_window
#print axioms RamanujanTau.GeneralZeros.zeroCount_le
#print axioms RamanujanTau.GeneralZeros.zeroSet_eq_fL
#print axioms RamanujanTau.GeneralZeros.ord_eq_fL
#print axioms RamanujanTau.GeneralZeros.exists_sigma_normalized
#print axioms RamanujanTau.GeneralZeros.order_reflect
#print axioms RamanujanTau.GeneralZeros.fL_growth
#print axioms RamanujanTau.GeneralZeros.backlund_gen
#print axioms RamanujanTau.GeneralZeros.rectInt_phi_symm_gen
#print axioms RamanujanTau.GeneralZeros.pi_count_eq_gen
#print axioms RamanujanTau.GeneralZeros.phi_eq_gen
#print axioms RamanujanTau.GeneralZeros.integral_re_digamma_nat
#print axioms RamanujanTau.GeneralZeros.gamma_cauchy_gen
#print axioms RamanujanTau.GeneralZeros.fL_zero_free_region
#print axioms RamanujanTau.GeneralZeros.fL_zero_free_region_left
#print axioms RamanujanTau.GeneralZeros.fL_zero_free_region_uniform
#print axioms RamanujanTau.GeneralZeros.fL_discriminant_zero_free_region
#print axioms RamanujanTau.GeneralZeros.ZFR.L_zero_free_region
#print axioms RamanujanTau.GeneralZeros.ZFR.core
#print axioms RamanujanTau.GeneralZeros.ZFR.norm_Psi_le
#print axioms RamanujanTau.GeneralZeros.ZFR.norm_Fval_antitone
