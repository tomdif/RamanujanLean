/-
# Weight-`k` Tauberian chain, part 2: exponential-Riesz formula and the quadratic Riesz mean

Weight-`k` copies of `SCSSharp.laplace_rieszK`, `SCSSharp.Rmean2_le`, `SCSSharp.Rmean2_bound`.
The pointwise bound for `G^f_h` is an explicit hypothesis `hpt` (weight-`k` `pointwise_G'`).
-/
import RamanujanTau.SubconvexGeneral2.TauBasic

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral2

open MeasureTheory Complex Filter
open RamanujanTau.HeckeConvexGeneral RamanujanTau.SubconvexGeneral
open RamanujanTau.RankinError RamanujanTau.SCSProof RamanujanTau.SCSSharp
open scoped MatrixGroups Real

variable {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ))

/-- The term function on the line. -/
noncomputable def ktermT (j : ℕ) (h : ℕ) (x L : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  (aT f h n : ℂ) * (((Real.exp ((n - x) / L) : ℝ) : ℂ) ^ (-((L / x : ℝ) + y * I)) *
    Pk j ((L / x : ℝ) + y * I))

lemma norm_ktermT (j : ℕ) (h : ℕ) {x L : ℝ} (hx : 0 < x) (hL : 0 < L) (n : ℕ) (y : ℝ) :
    ‖ktermT f j h x L n y‖ = aabsT f h n * Real.exp (-n * (1 / x)) * Real.exp 1 *
      ‖Pk j ((L / x : ℝ) + y * I)‖ := by
  unfold ktermT
  rw [norm_mul, norm_mul, cpow_exp_neg, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_aT]
  have hre : (-((L / x : ℝ) + y * I) * (((n - x) / L : ℝ) : ℂ)).re = -(L / x) * ((n - x) / L) := by
    simp [Complex.mul_re]
  rw [hre]
  have : -(L / x) * ((n - x) / L) = -n * (1 / x) + 1 := by field_simp; ring
  rw [this, Real.exp_add]; ring

lemma integral_ktermT {j : ℕ} (hj : 1 ≤ j) (h : ℕ) {x L : ℝ} (hx : 0 < x) (hL : 0 < L) (n : ℕ) :
    ∫ y, ktermT f j h x L n y = (aT f h n : ℂ) * (2 * π * (phi j (Real.exp ((n - x) / L)) : ℂ)) := by
  have hinv := mellinInv_Pk (k := j) hj (σ := L / x) (by positivity)
    (u := Real.exp ((n - x) / L)) (Real.exp_pos _)
  unfold mellinInv at hinv
  rw [Complex.real_smul] at hinv
  unfold ktermT
  rw [integral_const_mul]
  congr 1
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  rw [← hinv]
  push_cast
  field_simp
  congr 1; funext y; simp only [smul_eq_mul]; ring_nf

lemma integrable_ktermT {j : ℕ} (hj : 1 ≤ j) (h : ℕ) {x L : ℝ} (hx : 0 < x) (hL : 0 < L) (n : ℕ) :
    Integrable (ktermT f j h x L n) := by
  have hP := integrable_Pk_line (k := j) hj (σ := L / x) (by positivity)
  have hmeas : AEStronglyMeasurable (ktermT f j h x L n) := by
    refine Continuous.aestronglyMeasurable ?_
    unfold ktermT
    have hc1 := continuous_Pk_line j (σ := L / x) (by positivity)
    refine continuous_const.mul (Continuous.mul ?_ ?_)
    · exact Continuous.const_cpow (by fun_prop) (Or.inl (by
        exact_mod_cast (Real.exp_pos _).ne'))
    · push_cast at hc1 ⊢; exact hc1
  refine (hP.norm.const_mul (aabsT f h n * Real.exp (-n * (1 / x)) * Real.exp 1)).mono' hmeas
    (Eventually.of_forall fun y => ?_)
  rw [norm_ktermT f j h hx hL]

/-- **The exponential-Riesz formula**, weight `k`. -/
theorem laplace_rieszT (hreal : ∀ n, (coef f n).im = 0) {j : ℕ} (hj : 1 ≤ j) (h : ℕ) {x L : ℝ}
    (hx : 0 < x) (hL : 0 < L)
    (hsum : Summable fun n : ℕ => aabsT f h n * Real.exp (-n * (1 / x))) :
    (2 * π : ℂ) * ∑' n : ℕ, (aT f h n : ℂ) * (phi j (Real.exp ((n - x) / L)) : ℂ) =
      ∫ y : ℝ, cexp (x * ((L / x : ℝ) + y * I) / L) * Pk j ((L / x : ℝ) + y * I) *
        GhF f h (((L / x : ℝ) + y * I) / L) := by
  have hint := integrable_ktermT f hj h hx hL
  have hsumI : Summable fun n => ∫ y, ‖ktermT f j h x L n y‖ := by
    simp_rw [norm_ktermT f j h hx hL, integral_const_mul]
    exact (hsum.mul_right (Real.exp 1)).mul_right _
  have key := integral_tsum_of_summable_integral_norm hint hsumI
  simp_rw [integral_ktermT f hj h hx hL] at key
  rw [← tsum_mul_left]
  have e1 : ∀ n : ℕ, (2 * π : ℂ) * ((aT f h n : ℂ) * (phi j (Real.exp ((n - x) / L)) : ℂ)) =
      (aT f h n : ℂ) * (2 * π * (phi j (Real.exp ((n - x) / L)) : ℂ)) := fun n => by ring
  simp_rw [e1, key]
  congr 1
  funext y
  unfold ktermT
  rw [GhF_eq f hreal, ← tsum_mul_left]
  congr 1
  funext n
  rw [cpow_exp_neg]
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have e : -(((L / x : ℝ) : ℂ) + y * I) * (((n - x) / L : ℝ) : ℂ) =
      x * (((L / x : ℝ) : ℂ) + y * I) / L + (-(n : ℂ) * ((((L / x : ℝ) : ℂ) + y * I) / L)) := by
    push_cast; field_simp; ring
  rw [e, Complex.exp_add]
  push_cast
  ring

/-- The quadratic exponential-Riesz mean. -/
noncomputable def RmeanT (h : ℕ) (x L : ℝ) : ℝ :=
  ∑' n : ℕ, aT f h n * phi 2 (Real.exp ((n - x) / L))

set_option maxHeartbeats 2000000 in
/-- **Bound for the quadratic exponential-Riesz mean**, weight `k`. -/
theorem RmeanT_le (hreal : ∀ n, (coef f n).im = 0) (K : ℝ) (hK : 0 ≤ K)
    (hpt : ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 → (h : ℝ) * σ ≤ 1 →
      ‖GhF f h ((σ : ℂ) + v * I)‖ ≤
        K * Real.sqrt h * (|2 * v / σ| + 3) * σ ^ (-(k : ℝ) + 12 / 125))
    (h : ℕ) (hh : 1 ≤ h) {x : ℝ} (hx : 1 ≤ x) (hhx : (h : ℝ) ≤ x) {σ₀ : ℝ} (hσ0 : 0 < σ₀) :
    2 * π * |RmeanT f h x (x * σ₀)| ≤
      Real.exp 1 * (48 / σ₀) * I2 * (K * Real.sqrt h * x ^ ((k : ℝ) - 12 / 125)) := by
  have hx0 : 0 < x := by linarith
  set L := x * σ₀ with hLdef
  have hL : 0 < L := by positivity
  have hLx : L / x = σ₀ := by rw [hLdef]; field_simp
  have hsum := summable_aabsT f h (σ := 1 / x) (by positivity)
  have hR := laplace_rieszT f hreal (j := 2) (by norm_num) h hx0 hL hsum
  rw [hLx] at hR
  set Gm := K * Real.sqrt h * x ^ ((k : ℝ) - 12 / 125)
  have hGm0 : 0 ≤ Gm := by positivity
  have hbound : ∀ y : ℝ, ‖cexp (x * ((σ₀ : ℂ) + y * I) / L) * Pk 2 ((σ₀ : ℂ) + y * I) *
      GhF f h (((σ₀ : ℂ) + y * I) / L)‖ ≤
        Real.exp 1 * Gm * (48 / σ₀ * (1 + ‖y‖) ^ (-(2 : ℝ))) := by
    intro y
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have hre : (x * ((σ₀ : ℂ) + y * I) / L).re = 1 := by
      rw [hLdef]; simp [Complex.div_re]; field_simp
    rw [hre]
    have hW : ((σ₀ : ℂ) + y * I) / L = ((1 / x : ℝ) : ℂ) + ((y / L : ℝ) : ℂ) * I := by
      have hσC : (σ₀ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
      have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
      rw [hLdef]; push_cast; field_simp
    rw [hW]
    have hG := hpt h hh (1 / x) (y / L) (by positivity) (by rw [div_le_one hx0]; exact hx)
      (by rw [mul_one_div, div_le_one hx0]; exact hhx)
    have hθ : 2 * (y / L) / (1 / x) = 2 * y / σ₀ := by rw [hLdef]; field_simp
    have hxp : (1 / x) ^ (-(k : ℝ) + 12 / 125) = x ^ ((k : ℝ) - 12 / 125) := by
      rw [one_div, Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le]
      congr 1; ring
    rw [hxp, hθ] at hG
    have hk := Pk2_mul_le hσ0 y
    calc Real.exp 1 * ‖Pk 2 ((σ₀ : ℂ) + y * I)‖ *
          ‖GhF f h (((1 / x : ℝ) : ℂ) + ((y / L : ℝ) : ℂ) * I)‖
        ≤ Real.exp 1 * ‖Pk 2 ((σ₀ : ℂ) + y * I)‖ *
            (K * Real.sqrt h * (|2 * y / σ₀| + 3) * x ^ ((k : ℝ) - 12 / 125)) := by gcongr
      _ = Real.exp 1 * Gm * (‖Pk 2 ((σ₀ : ℂ) + y * I)‖ * (|2 * y / σ₀| + 3)) := by ring
      _ ≤ _ := by gcongr
  have hint : Integrable fun y : ℝ => Real.exp 1 * Gm * (48 / σ₀ * (1 + ‖y‖) ^ (-(2 : ℝ))) :=
    (int2.const_mul _).const_mul _
  have hnorm := norm_integral_le_of_norm_le hint (Eventually.of_forall hbound)
  rw [← hR] at hnorm
  rw [integral_const_mul, integral_const_mul] at hnorm
  have hRe : ‖(2 * π : ℂ) * ∑' n : ℕ, (aT f h n : ℂ) * (phi 2 (Real.exp ((n - x) / L)) : ℂ)‖ =
      2 * π * |RmeanT f h x L| := by
    unfold RmeanT
    rw [norm_mul]
    have : (∑' n : ℕ, (aT f h n : ℂ) * (phi 2 (Real.exp ((n - x) / L)) : ℂ)) =
        ((∑' n : ℕ, aT f h n * phi 2 (Real.exp ((n - x) / L)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]; push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    congr 1
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [hRe] at hnorm
  refine hnorm.trans (le_of_eq ?_)
  unfold I2
  ring

set_option maxHeartbeats 2000000 in
/-- `|RmeanT h x (x^{19/20})| ≤ C √h x^{k − 1/22}` for `1 ≤ h ≤ x`. -/
theorem RmeanT_bound (hreal : ∀ n, (coef f n).im = 0)
    (hpw : ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 → (h : ℝ) * σ ≤ 1 →
      ‖GhF f h ((σ : ℂ) + v * I)‖ ≤
        K * Real.sqrt h * (|2 * v / σ| + 3) * σ ^ (-(k : ℝ) + 12 / 125)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℕ, 1 ≤ h → ∀ x : ℝ, 1 ≤ x → (h : ℝ) ≤ x →
      |RmeanT f h x (x * x ^ (-(1 / 20 : ℝ)))| ≤ C * Real.sqrt h * x ^ ((k : ℝ) - ηs) := by
  obtain ⟨K, hK0, hK⟩ := hpw
  refine ⟨Real.exp 1 * 48 * I2 * K, by have := I2_nonneg; positivity, fun h hh x hx hhx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hσ0 : 0 < x ^ (-(1 / 20 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hR := RmeanT_le f hreal K hK0 hK h hh hx hhx hσ0
  have hI2 := I2_nonneg
  have e : 48 / x ^ (-(1 / 20 : ℝ)) * x ^ ((k : ℝ) - 12 / 125) =
      48 * x ^ ((k : ℝ) - 12 / 125 + 1 / 20) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hx0.le, neg_neg, mul_assoc, ← Real.rpow_add hx0]
    rw [show (1 / 20 : ℝ) + ((k : ℝ) - 12 / 125) = (k : ℝ) - 12 / 125 + 1 / 20 by ring]
  have hpow : x ^ ((k : ℝ) - 12 / 125 + 1 / 20) ≤ x ^ ((k : ℝ) - ηs) :=
    Real.rpow_le_rpow_of_exponent_le hx (by unfold ηs; linarith)
  have h2π : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
  have hRn : 0 ≤ |RmeanT f h x (x * x ^ (-(1 / 20 : ℝ)))| := abs_nonneg _
  have hfin : Real.exp 1 * (48 / x ^ (-(1 / 20 : ℝ))) * I2 *
      (K * Real.sqrt h * x ^ ((k : ℝ) - 12 / 125))
      ≤ Real.exp 1 * 48 * I2 * K * Real.sqrt h * x ^ ((k : ℝ) - ηs) := by
    have : Real.exp 1 * (48 / x ^ (-(1 / 20 : ℝ))) * I2 *
        (K * Real.sqrt h * x ^ ((k : ℝ) - 12 / 125))
        = Real.exp 1 * I2 * K * Real.sqrt h *
          (48 / x ^ (-(1 / 20 : ℝ)) * x ^ ((k : ℝ) - 12 / 125)) := by
      ring
    rw [this, e]
    have h0 : 0 ≤ Real.exp 1 * I2 * K * Real.sqrt h := by positivity
    calc Real.exp 1 * I2 * K * Real.sqrt h * (48 * x ^ ((k : ℝ) - 12 / 125 + 1 / 20))
        ≤ Real.exp 1 * I2 * K * Real.sqrt h * (48 * x ^ ((k : ℝ) - ηs)) := by gcongr
      _ = _ := by ring
  have := hR.trans hfin
  nlinarith

end RamanujanTau.SubconvexGeneral2
