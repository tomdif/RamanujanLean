/-
# Non-vacuity of the remaining hypotheses, and the headline with `PoincareUnfolding` discharged

* `summable_poincareTerm`: the double series defining `poincare z` converges absolutely for every
  `z ∈ ℍ` (so `poincare` is the genuine Poincaré series, not a `tsum`-junk value);
* `summable_firstCoeff`: the series in `PoincareFirstCoeffNeZero` is absolutely summable (so that
  hypothesis is not trivially true by `tsum = 0`);
* `tau_isBigO_47_8_of_cusp_and_coeff`: `τ(n) = O(n^{47/8+ε})` from `PoincareIsCuspForm` and
  `PoincareFirstCoeffNeZero` only.
-/
import RamanujanTau.TauBound.Unfold

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Complex Filter Asymptotics
open scoped Real

theorem summable_poincareTerm (z : UpperHalfPlane) :
    Summable (fun p : ℕ × ℤ => poincareTerm (p.1 + 1) p.2 z) := by
  refine Summable.of_norm_bounded
    (summable_majorant.mul_left (EisensteinSeries.r z ^ (-12 : ℝ))) (fun p => ?_)
  refine (norm_poincareTerm_le (p.1 + 1) (by omega) p.2 z.coe_im_pos).trans ?_
  have h := EisensteinSeries.summand_bound z (k := 12) (by norm_num)
    (![((p.1 + 1 : ℕ) : ℤ), p.2] : Fin 2 → ℤ)
  refine le_of_eq_of_le ?_ h
  congr 2

/-- Hence `poincare z = e(z) + ∑_{(c,d)} T(c,d,z)` as an absolutely convergent double sum. -/
theorem poincare_eq_tsum_prod (z : UpperHalfPlane) :
    poincare z = ee z + ∑' p : ℕ × ℤ, poincareTerm (p.1 + 1) p.2 z := by
  rw [poincare, (summable_poincareTerm z).tsum_prod' (fun c => (summable_poincareTerm z).prod_factor c)]

theorem summable_firstCoeff :
    Summable (fun c : ℕ => ((c + 1 : ℕ) : ℂ) ^ (-12 : ℤ) * kloosterman 1 1 (c + 1) *
      kInt 1 (c + 1) 1) := by
  have hs : Summable (fun c : ℕ => kConst 0 * ((c + 1 : ℕ) : ℝ) ^ (-11 : ℝ)) := by
    refine Summable.mul_left _ ?_
    have := Real.summable_nat_rpow.mpr (show (-11 : ℝ) < -1 by norm_num)
    exact ((summable_nat_add_iff 1).mpr this).congr fun c => by push_cast; rfl
  refine Summable.of_norm_bounded hs (fun c => ?_)
  have hC : (0 : ℝ) < ((c + 1 : ℕ) : ℝ) := by positivity
  have h3 := norm_kInt_inv_le (r := 0) le_rfl (by norm_num) 1 (c + 1) le_rfl (by omega)
  simp only [Nat.cast_one, div_one, Real.one_rpow, one_mul, mul_zero, Real.rpow_zero,
    mul_one] at h3
  have h2 := norm_kloosterman_le 1 1 (c + 1)
  rw [norm_mul, norm_mul, norm_zpow, Complex.norm_natCast]
  have hk := kConst_nonneg 0
  calc ((c + 1 : ℕ) : ℝ) ^ (-12 : ℤ) * ‖kloosterman 1 1 (c + 1)‖ * ‖kInt 1 (c + 1) 1‖
      ≤ ((c + 1 : ℕ) : ℝ) ^ (-12 : ℤ) * ((c + 1 : ℕ) : ℝ) * kConst 0 := by gcongr
    _ = kConst 0 * ((c + 1 : ℕ) : ℝ) ^ (-11 : ℝ) := by
      have e : ((c + 1 : ℕ) : ℝ) ^ (-12 : ℤ) * ((c + 1 : ℕ) : ℝ) = ((c + 1 : ℕ) : ℝ) ^ (-11 : ℝ) := by
        rw [show ((c + 1 : ℕ) : ℝ) ^ (-11 : ℝ) =
          ((c + 1 : ℕ) : ℝ) ^ (((-12 : ℤ) : ℝ) + 1) by norm_num, Real.rpow_add hC,
          Real.rpow_intCast, Real.rpow_one]
      rw [e]; ring

/-- **Headline with the unfolding discharged.** -/
theorem tau_isBigO_47_8_of_cusp_and_coeff (hA : PoincareIsCuspForm)
    (hC : PoincareFirstCoeffNeZero) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (tau n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((47 / 8 : ℝ) + ε) :=
  tau_isBigO_47_8_of_poincare_hyps hA poincareUnfolding hC ε hε

end RamanujanTau.TauBound
