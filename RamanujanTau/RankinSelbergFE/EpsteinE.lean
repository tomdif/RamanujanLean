/-
# `E*(z,s)` is the completed real-analytic Eisenstein series

For real `σ > 1` (primitive decomposition `ℤ² ∖ 0 = ℕ_{≥1} · {coprime}`, `nzEquiv`):

    ∑_{v ≠ 0} Q_z(v)^{−σ} = ζ(2σ) · ∑_{(c,d) coprime} y^σ |cz+d|^{−2σ} = 2 ζ(2σ) E(z,σ),

hence (`EpsteinStar_ofReal`)

    E*(z,σ) = 2 π^{−σ} Γ(σ) ζ(2σ) E(z,σ),

where `E(z,σ) = ½ ∑_{gcd(c,d)=1} y^σ |cz+d|^{−2σ}` is the repo's `EisensteinReal.E`. Together with
`EpsteinStar_one_sub` this is the continuation and functional equation of
`π^{−s} Γ(s) ζ(2s) E(z,s)`.
-/
import RamanujanTau.RankinSelbergFE.Epstein
import Mathlib.NumberTheory.LSeries.RiemannZeta

set_option autoImplicit false

namespace RamanujanTau.RankinSelbergFE

open Real Filter Topology Set EisensteinSeries
open RamanujanTau.EisensteinReal.Horo
open UpperHalfPlane hiding I
open scoped ENNReal

/-- `copSet ≃ gammaSet 1 1 0`, `(a, c) ↦ (−c, a)`. -/
def copGamma : copSet ≃ gammaSet 1 1 0 where
  toFun p := ⟨![-p.1.2, p.1.1], by
    rw [gammaSet_one_mem_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [Int.neg_gcd, Int.gcd_comm]
    exact p.2⟩
  invFun v := ⟨(v.1 1, -v.1 0), by
    have h := (gammaSet_one_mem_iff 1 v.1).1 v.2
    show Int.gcd _ _ = 1
    rw [Int.gcd_neg, Int.gcd_comm]
    exact h⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp

lemma summable_shift_zeta {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * σ) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_rpow.2 (by linarith : 1 < 2 * σ))
  refine h.congr fun n => ?_
  push_cast; rfl

lemma rpow_scale {σ : ℝ} (k : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    1 / (((k : ℝ) + 1) ^ 2 * q) ^ σ = 1 / ((k : ℝ) + 1) ^ (2 * σ) * (1 / q ^ σ) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  rw [Real.mul_rpow (by positivity) hq, ← Real.rpow_natCast, ← Real.rpow_mul hk]
  push_cast
  rw [one_div_mul_one_div]

/-- `∑_{v ≠ 0} Q_z(v)^{−σ} = ζ(2σ) · 2E(z,σ)` for real `σ > 1`. -/
theorem tsum_lq_rpow (z : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    ∑' v : ℤ × ℤ, (if v = 0 then (0 : ℝ) else 1) / lq z v ^ σ =
      (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 * σ)) * (2 * EisensteinReal.E z σ) := by
  have hnn : ∀ v : ℤ × ℤ, 0 ≤ (if v = 0 then (0 : ℝ) else 1) / lq z v ^ σ := fun v => by
    by_cases hv : v = 0
    · simp [hv]
    · simp only [hv, if_false]; exact div_nonneg zero_le_one (Real.rpow_nonneg (lq_nonneg z v) _)
  have hE : 2 * EisensteinReal.E z σ = ∑' v : gammaSet 1 1 0, EisensteinReal.eSummand σ z v := by
    unfold EisensteinReal.E; ring
  have hEnn : ∀ v : gammaSet 1 1 0, 0 ≤ EisensteinReal.eSummand σ z v := fun v =>
    EisensteinReal.eSummand_nonneg _ _ _
  have hζnn : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 1) ^ (2 * σ) := fun n => by positivity
  rw [← ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hnn)
    (mul_nonneg (tsum_nonneg hζnn) (by rw [hE]; exact tsum_nonneg hEnn)),
    ENNReal.ofReal_tsum_of_nonneg hnn (summable_lq_rpow z hσ), tsum_decomp,
    ENNReal.ofReal_mul (tsum_nonneg hζnn), ENNReal.ofReal_tsum_of_nonneg hζnn (summable_shift_zeta hσ),
    hE, ENNReal.ofReal_tsum_of_nonneg hEnn ((EisensteinReal.summable_E hσ z)),
    ← ENNReal.tsum_mul_right]
  simp only [if_true, zero_div, ENNReal.ofReal_zero, zero_add]
  refine tsum_congr fun k => ?_
  rw [← ENNReal.tsum_mul_left, ← copGamma.tsum_eq]
  refine tsum_congr fun p => ?_
  rw [if_neg (scaleMap_ne_zero (k, p)), lq_scale, rpow_scale k (lq_nonneg z p.1),
    ENNReal.ofReal_mul (hζnn k), one_div_lq_rpow z (copSet_ne_zero p)]
  rfl

/-- **`E*(z,σ) = 2 π^{−σ} Γ(σ) ζ(2σ) E(z,σ)`** for real `σ > 1`. -/
theorem EpsteinStar_ofReal (z : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    EpsteinStar z σ = 2 * (π : ℂ) ^ (-(σ : ℂ)) * Complex.Gamma σ * riemannZeta (2 * σ) *
      (EisensteinReal.E z σ : ℂ) := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have h1 := hasSum_EpsteinStar z hs
  have hζ : riemannZeta (2 * σ) = ((∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 * σ) : ℝ) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; linarith), Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity)]
    push_cast; rfl
  set c : ℝ := Real.Gamma σ * (π ^ σ)⁻¹
  have h2 : HasSum (fun v : ℤ × ℤ => c * ((if v = 0 then (0 : ℝ) else 1) / lq z v ^ σ))
      (c * ((∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 * σ)) * (2 * EisensteinReal.E z σ))) := by
    rw [← tsum_lq_rpow z hσ]
    exact (summable_lq_rpow z hσ).hasSum.mul_left c
  have h3 := h2.mapL Complex.ofRealCLM
  simp only [Complex.ofRealCLM_apply] at h3
  have e : ∀ v : ℤ × ℤ, Complex.Gamma σ * (if v = 0 then (0 : ℂ) else 1) /
      ((π * lq z v : ℝ) : ℂ) ^ (σ : ℂ) = ((c * ((if v = 0 then (0 : ℝ) else 1) / lq z v ^ σ) : ℝ) : ℂ) := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · simp only [hv, if_false, c]
      rw [← Complex.ofReal_cpow (mul_nonneg Real.pi_pos.le (lq_nonneg z v)),
        Real.mul_rpow Real.pi_pos.le (lq_nonneg z v), Complex.Gamma_ofReal]
      push_cast
      field_simp
  simp_rw [e] at h1
  rw [h1.unique h3, hζ]
  simp only [c]
  rw [Complex.cpow_neg, ← Complex.ofReal_cpow Real.pi_pos.le, Complex.Gamma_ofReal]
  push_cast
  ring

end RamanujanTau.RankinSelbergFE
