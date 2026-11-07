/-
# The `(log x)^κ` form, and the Selberg-smoothed sum for `R^{−1/2}`

* `rpow_shift_diff`: `|(t − c₀)^κ − t^κ| ≤ |κ| M_κ |c₀| t^{κ−1}` for `t ≥ 2|c₀| + 2`.
* `logmean_LSD_log`: `logmean_LSD` with main term `C₁ (log x)^κ`.
* `logmean_fR_log`: `Σ_{n≤x} fR(n)/n = C₁ (log x)^{−1/2} + O((1+log(1+log x)) (log x)^{−3/2})`.
-/
import RamanujanTau.SelbergDelange3.Apply

set_option autoImplicit false

namespace RamanujanTau.SelbergDelange3

open Finset Set Filter Topology ArithmeticFunction
open RamanujanTau.SelbergDelange2

lemma rpow_interval_le (a : ℝ) {t u : ℝ} (ht : 0 < t) (hu1 : t / 2 ≤ u) (hu2 : u ≤ 3 / 2 * t) :
    u ^ a ≤ ((1 / 2) ^ a + (3 / 2) ^ a) * t ^ a := by
  have e1 : (t / 2) ^ a = (1 / 2) ^ a * t ^ a := by
    rw [div_eq_mul_inv, mul_comm, Real.mul_rpow (by norm_num) ht.le]; norm_num
  have e2 : (3 / 2 * t) ^ a = (3 / 2) ^ a * t ^ a := Real.mul_rpow (by norm_num) ht.le
  have p1 : 0 ≤ (1 / 2 : ℝ) ^ a * t ^ a := by positivity
  have p2 : 0 ≤ (3 / 2 : ℝ) ^ a * t ^ a := by positivity
  rcases le_or_gt 0 a with hk | hk
  · have := Real.rpow_le_rpow (by linarith) hu2 hk
    rw [e2] at this; nlinarith
  · have := Real.rpow_le_rpow_of_nonpos (by positivity) hu1 hk.le
    rw [e1] at this; nlinarith

lemma rpow_shift_diff (κ : ℝ) {c₀ t : ℝ} (ht : 2 * |c₀| + 2 ≤ t) :
    |(t - c₀) ^ κ - t ^ κ| ≤
      |κ| * ((1 / 2) ^ (κ - 1) + (3 / 2) ^ (κ - 1)) * |c₀| * t ^ (κ - 1) := by
  have hc := le_abs_self c₀
  have hc' := neg_abs_le c₀
  have ht0 : 0 < t := by linarith [abs_nonneg c₀]
  set s : Set ℝ := Icc (t / 2) (3 / 2 * t) with hs
  have hconv : Convex ℝ s := convex_Icc _ _
  set M : ℝ := |κ| * ((1 / 2) ^ (κ - 1) + (3 / 2) ^ (κ - 1)) * t ^ (κ - 1) with hM
  have hder : ∀ u ∈ s, HasDerivWithinAt (fun u : ℝ => u ^ κ) (κ * u ^ (κ - 1)) s u := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    exact (Real.hasDerivAt_rpow_const (Or.inl hu0.ne')).hasDerivWithinAt
  have hbd : ∀ u ∈ s, ‖κ * u ^ (κ - 1)‖ ≤ M := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu0 _), hM, mul_assoc]
    exact mul_le_mul_of_nonneg_left (rpow_interval_le (κ - 1) ht0 hu.1 hu.2) (abs_nonneg κ)
  have hx : t ∈ s := ⟨by linarith, by linarith⟩
  have hy : t - c₀ ∈ s := ⟨by linarith, by linarith⟩
  have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd hx hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs, show t - c₀ - t = -c₀ by ring, abs_neg] at this
  calc |(t - c₀) ^ κ - t ^ κ| ≤ M * |c₀| := this
    _ = _ := by rw [hM]; ring

/-- **`logmean_LSD` with main term `C₁ (log x)^κ`.** -/
theorem logmean_LSD_log (f g : ArithmeticFunction ℝ) {κ c₀ σ B K : ℝ} (hκ : -1 < κ) (hσ0 : 0 < σ)
    (hσ1 : σ < 1) (hσκ : σ ≤ 1 + κ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hconv : ∀ n : ℕ, 0 < n → f n * Real.log n = (g * f) n)
    (hM : ∀ y : ℝ, 1 ≤ y → |Err g κ c₀ y| ≤ B / (1 + Real.log y))
    (hC : ∀ y : ℝ, 1 ≤ y → ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, |f n| ≤ K * y * (1 + Real.log y) ^ (σ - 1)) :
    ∃ C₁ K₂ X₁ : ℝ, ∀ x : ℝ, X₁ ≤ x →
      |Ssum f x - C₁ * Real.log x ^ κ| ≤
        K₂ * (1 + Real.log (1 + Real.log x)) * Real.log x ^ (κ - 1) := by
  obtain ⟨C₁, K₁, X₀, h⟩ := logmean_LSD f g hκ hσ0 hσ1 hσκ hB hK hconv hM hC
  set Mk : ℝ := |κ| * ((1 / 2) ^ (κ - 1) + (3 / 2) ^ (κ - 1)) * |c₀| with hMk
  refine ⟨C₁, |K₁| + |C₁| * Mk, max X₀ (Real.exp (2 * |c₀| + 2)), fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) (le_trans (le_max_right _ _) hx)
  set t := Real.log x with ht
  have hta : 2 * |c₀| + 2 ≤ t := by
    rw [ht, Real.le_log_iff_exp_le hx0]; exact le_trans (le_max_right _ _) hx
  have ht0 : 0 < t := by linarith [abs_nonneg c₀]
  have h1 := h x (le_trans (le_max_left _ _) hx)
  have h2 := rpow_shift_diff κ hta
  have hL : 1 ≤ 1 + Real.log (1 + t) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + t by linarith); linarith
  have hp : 0 ≤ t ^ (κ - 1) := by positivity
  have hMk0 : 0 ≤ Mk := by positivity
  have e : Ssum f x - C₁ * t ^ κ = (Ssum f x - C₁ * (t - c₀) ^ κ) + C₁ * ((t - c₀) ^ κ - t ^ κ) := by
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have h3 : |C₁| * |(t - c₀) ^ κ - t ^ κ| ≤ |C₁| * Mk * t ^ (κ - 1) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by rw [hMk]; exact h2) (abs_nonneg _)
  have h4 : K₁ * (1 + Real.log (1 + t)) * t ^ (κ - 1) ≤ |K₁| * (1 + Real.log (1 + t)) * t ^ (κ - 1) := by
    gcongr; exact le_abs_self K₁
  have h5 : |C₁| * Mk * t ^ (κ - 1) ≤ |C₁| * Mk * (1 + Real.log (1 + t)) * t ^ (κ - 1) := by
    have : 0 ≤ |C₁| * Mk * t ^ (κ - 1) := by positivity
    nlinarith
  nlinarith

/-- **`Σ_{n≤x} fR(n)/n = C₁ (log x)^{−1/2} + O(log log x · (log x)^{−3/2})`** (unconditional). -/
theorem logmean_fR_log : ∃ C₁ K₂ X₁ : ℝ, ∀ x : ℝ, X₁ ≤ x →
    |Ssum fR x - C₁ * Real.log x ^ (-(1 / 2 : ℝ))| ≤
      K₂ * (1 + Real.log (1 + Real.log x)) * Real.log x ^ (-(1 / 2 : ℝ) - 1) := by
  obtain ⟨c, B, hB, hM⟩ := mertens_LamR_err
  obtain ⟨K, hK, hC⟩ := density_fR
  have hM' : ∀ y : ℝ, 1 ≤ y → |Err (toA gR gR_zero) (-(1 / 2)) (-(c / 2)) y| ≤
      (B / 2) / (1 + Real.log y) := by
    intro y hy
    have h := hM y hy
    have e : Err (toA gR gR_zero) (-(1 / 2)) (-(c / 2)) y =
        -(1 / 2) * (Msum SelbergCoeffs2.LamR y - Real.log y - c) := by
      unfold Err Msum
      rw [mul_sub, mul_sub, mul_sum]
      have : ∑ m ∈ Finset.Ioc 0 ⌊y⌋₊, (toA gR gR_zero) m / m =
          ∑ m ∈ Finset.Ioc 0 ⌊y⌋₊, -(1 / 2) * (SelbergCoeffs2.LamR m / m) :=
        sum_congr rfl fun m _ => by simp only [toA, coe_mk, gR]; ring
      rw [this]; ring
    rw [e, abs_mul]
    have : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num
    rw [this]
    calc 1 / 2 * |Msum SelbergCoeffs2.LamR y - Real.log y - c| ≤ 1 / 2 * (B / (1 + Real.log y)) := by
          gcongr
      _ = B / 2 / (1 + Real.log y) := by ring
  exact logmean_LSD_log (recFA gR) (toA gR gR_zero) (κ := -(1 / 2)) (c₀ := -(c / 2))
    (σ := 1 / 2) (B := B / 2) (K := K) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) hK fR_log hM' (fun y hy => hC y hy)

end RamanujanTau.SelbergDelange3
