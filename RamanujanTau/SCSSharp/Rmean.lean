/-
# The quadratic exponential-Riesz mean and its bound

`Rmean2 h x L = Σ_n a_n φ₂(e^{(n−x)/L})`, `φ₂(u) = (1−u)₊²`, `a_n = τ(n)τ(n+h)`.

* `Pk2_mul_le`: `|P₂(σ₀+iy)| (|2y/σ₀|+3) ≤ 48 σ₀^{−1} (1+|y|)^{−2}` (the kernel `P₂(s) = 2/(s(s+1)(s+2))`
  absorbs the *linear* `θ`-loss of `pointwise_G'` at the cost of one factor `σ₀^{−1}` only);
* `Rmean2_le`: `2π |Rmean2 h x (xσ₀)| ≤ e (48/σ₀) I₂ K √h x^{1488/125}`;
* `Rmean2_bound`: with `σ₀ = x^{−1/20}`: `|Rmean2| ≤ C √h x^{12 − 1/22}` for `1 ≤ h ≤ x`.
-/
import RamanujanTau.SCSSharp.RieszK

set_option autoImplicit false

namespace RamanujanTau.SCSSharp

open MeasureTheory Complex Filter
open RamanujanTau.RankinError RamanujanTau.SCSProof
open scoped Real

/-- The quadratic exponential-Riesz mean. -/
noncomputable def Rmean2 (h : ℕ) (x L : ℝ) : ℝ :=
  ∑' n : ℕ, aR h n * phi 2 (Real.exp ((n - x) / L))

lemma norm_ge_avg (s : ℂ) : (|s.re| + |s.im|) / 2 ≤ ‖s‖ := by
  have := Complex.abs_re_le_norm s; have := Complex.abs_im_le_norm s; linarith

lemma Pk2_eq (s : ℂ) : Pk 2 s = 2 / (s * (s + 1) * (s + 2)) := by
  unfold Pk
  simp [Finset.prod_range_succ, Nat.factorial]

lemma Pk2_mul_le {σ₀ : ℝ} (h0 : 0 < σ₀) (y : ℝ) :
    ‖Pk 2 ((σ₀ : ℂ) + y * I)‖ * (|2 * y / σ₀| + 3) ≤ 48 / σ₀ * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  set s : ℂ := (σ₀ : ℂ) + y * I with hs
  have hre : s.re = σ₀ := by simp [s]
  have him : s.im = y := by simp [s]
  have ha : (σ₀ + |y|) / 2 ≤ ‖s‖ := by
    have := norm_ge_avg s; rwa [hre, him, abs_of_pos h0] at this
  have hb : (1 + |y|) / 2 ≤ ‖s + 1‖ := by
    have := norm_ge_avg (s + 1)
    simp only [add_re, one_re, add_im, one_im, add_zero] at this
    rw [hre, him, abs_of_pos (by linarith)] at this; linarith
  have hc : (1 + |y|) / 2 ≤ ‖s + 2‖ := by
    have := norm_ge_avg (s + 2)
    have e1 : (s + 2).re = σ₀ + 2 := by rw [add_re, hre]; norm_num
    have e2 : (s + 2).im = y := by rw [add_im, him]; norm_num
    rw [e1, e2, abs_of_pos (by linarith)] at this; linarith
  have hy0 := abs_nonneg y
  have hA0 : 0 < (σ₀ + |y|) / 2 := by positivity
  have hB0 : 0 < (1 + |y|) / 2 := by positivity
  have hnorm : ‖Pk 2 s‖ = 2 / (‖s‖ * ‖s + 1‖ * ‖s + 2‖) := by
    rw [Pk2_eq, norm_div, norm_mul, norm_mul]; norm_num
  have hP : ‖Pk 2 s‖ ≤ 2 / ((σ₀ + |y|) / 2 * ((1 + |y|) / 2) * ((1 + |y|) / 2)) := by
    rw [hnorm]
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    gcongr
  have hθ : |2 * y / σ₀| + 3 ≤ 3 * (σ₀ + |y|) / σ₀ := by
    rw [abs_div, abs_mul, abs_two, abs_of_pos h0, div_add' _ _ _ h0.ne']
    gcongr; linarith
  have hr : (1 + ‖y‖) ^ (-(2 : ℝ)) = 1 / (1 + |y|) ^ 2 := by
    rw [Real.rpow_neg (by positivity), Real.norm_eq_abs, one_div]; norm_cast
  rw [hr]
  calc ‖Pk 2 s‖ * (|2 * y / σ₀| + 3)
      ≤ 2 / ((σ₀ + |y|) / 2 * ((1 + |y|) / 2) * ((1 + |y|) / 2)) * (3 * (σ₀ + |y|) / σ₀) := by
        gcongr
    _ = 48 / σ₀ * (1 / (1 + |y|) ^ 2) := by field_simp; ring

set_option maxHeartbeats 2000000 in
/-- **Bound for the quadratic exponential-Riesz mean.** -/
theorem Rmean2_le (K C₀ : ℝ) (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hpt : ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 → (h : ℝ) * σ ≤ 1 →
      ‖Gh h ((σ : ℂ) + v * I)‖ ≤ K * Real.sqrt h * (|2 * v / σ| + 3) * σ ^ (-(1488 / 125 : ℝ)))
    (hlap : ∀ (h : ℕ) (σ : ℝ), 0 < σ →
      Summable (fun n : ℕ => aabs h n * Real.exp (-n * σ)) ∧
        ∑' n : ℕ, aabs h n * Real.exp (-n * σ) ≤ (1 + Real.exp (h * σ)) / 2 * (C₀ * σ ^ (-(12 : ℝ))))
    (h : ℕ) (hh : 1 ≤ h) {x : ℝ} (hx : 1 ≤ x) (hhx : (h : ℝ) ≤ x) {σ₀ : ℝ} (hσ0 : 0 < σ₀) :
    2 * π * |Rmean2 h x (x * σ₀)| ≤
      Real.exp 1 * (48 / σ₀) * I2 * (K * Real.sqrt h * x ^ (1488 / 125 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  set L := x * σ₀ with hLdef
  have hL : 0 < L := by positivity
  have hLx : L / x = σ₀ := by rw [hLdef]; field_simp
  obtain ⟨hsum, -⟩ := hlap h (1 / x) (by positivity)
  have hR := laplace_rieszK (k := 2) (by norm_num) h hx0 hL hsum
  rw [hLx] at hR
  set Gm := K * Real.sqrt h * x ^ (1488 / 125 : ℝ)
  have hGm0 : 0 ≤ Gm := by positivity
  have hbound : ∀ y : ℝ, ‖cexp (x * ((σ₀ : ℂ) + y * I) / L) * Pk 2 ((σ₀ : ℂ) + y * I) *
      Gh h (((σ₀ : ℂ) + y * I) / L)‖ ≤
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
    have hxp : (1 / x) ^ (-(1488 / 125 : ℝ)) = x ^ (1488 / 125 : ℝ) := by
      rw [one_div, Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le, neg_neg]
    rw [hxp, hθ] at hG
    have hk := Pk2_mul_le hσ0 y
    calc Real.exp 1 * ‖Pk 2 ((σ₀ : ℂ) + y * I)‖ * ‖Gh h (((1 / x : ℝ) : ℂ) + ((y / L : ℝ) : ℂ) * I)‖
        ≤ Real.exp 1 * ‖Pk 2 ((σ₀ : ℂ) + y * I)‖ *
            (K * Real.sqrt h * (|2 * y / σ₀| + 3) * x ^ (1488 / 125 : ℝ)) := by gcongr
      _ = Real.exp 1 * Gm * (‖Pk 2 ((σ₀ : ℂ) + y * I)‖ * (|2 * y / σ₀| + 3)) := by ring
      _ ≤ _ := by gcongr
  have hint : Integrable fun y : ℝ => Real.exp 1 * Gm * (48 / σ₀ * (1 + ‖y‖) ^ (-(2 : ℝ))) :=
    (int2.const_mul _).const_mul _
  have hnorm := norm_integral_le_of_norm_le hint (Eventually.of_forall hbound)
  rw [← hR] at hnorm
  rw [integral_const_mul, integral_const_mul] at hnorm
  have hRe : ‖(2 * π : ℂ) * ∑' n : ℕ, (aR h n : ℂ) * (phi 2 (Real.exp ((n - x) / L)) : ℂ)‖ =
      2 * π * |Rmean2 h x L| := by
    unfold Rmean2
    rw [norm_mul]
    have : (∑' n : ℕ, (aR h n : ℂ) * (phi 2 (Real.exp ((n - x) / L)) : ℂ)) =
        ((∑' n : ℕ, aR h n * phi 2 (Real.exp ((n - x) / L)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]; push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    congr 1
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [hRe] at hnorm
  refine hnorm.trans (le_of_eq ?_)
  unfold I2
  ring

/-- The saving exponent of the sharp chain: `η = 1/22`. -/
noncomputable def ηs : ℝ := 1 / 22

set_option maxHeartbeats 2000000 in
/-- `|Rmean2 h x (x^{19/20})| ≤ C √h x^{12 − 1/22}` for `1 ≤ h ≤ x`. -/
theorem Rmean2_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℕ, 1 ≤ h → ∀ x : ℝ, 1 ≤ x → (h : ℝ) ≤ x →
    |Rmean2 h x (x * x ^ (-(1 / 20 : ℝ)))| ≤ C * Real.sqrt h * x ^ (12 - ηs) := by
  obtain ⟨K, hK0, hK⟩ := pointwise_G'
  obtain ⟨C₀, hC₀, hT⟩ := abs_laplace_le
  refine ⟨Real.exp 1 * 48 * I2 * K, by have := I2_nonneg; positivity, fun h hh x hx hhx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hσ0 : 0 < x ^ (-(1 / 20 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hR := Rmean2_le K C₀ hK0 hC₀ hK hT h hh hx hhx hσ0
  have hI2 := I2_nonneg
  have e : 48 / x ^ (-(1 / 20 : ℝ)) * x ^ (1488 / 125 : ℝ) = 48 * x ^ (5977 / 500 : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hx0.le, neg_neg, mul_assoc, ← Real.rpow_add hx0]
    norm_num
  have hpow : x ^ (5977 / 500 : ℝ) ≤ x ^ (12 - ηs) :=
    Real.rpow_le_rpow_of_exponent_le hx (by unfold ηs; norm_num)
  have h2π : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
  have hRn : 0 ≤ |Rmean2 h x (x * x ^ (-(1 / 20 : ℝ)))| := abs_nonneg _
  have hfin : Real.exp 1 * (48 / x ^ (-(1 / 20 : ℝ))) * I2 * (K * Real.sqrt h * x ^ (1488 / 125 : ℝ))
      ≤ Real.exp 1 * 48 * I2 * K * Real.sqrt h * x ^ (12 - ηs) := by
    have : Real.exp 1 * (48 / x ^ (-(1 / 20 : ℝ))) * I2 * (K * Real.sqrt h * x ^ (1488 / 125 : ℝ))
        = Real.exp 1 * I2 * K * Real.sqrt h * (48 / x ^ (-(1 / 20 : ℝ)) * x ^ (1488 / 125 : ℝ)) := by
      ring
    rw [this, e]
    have h0 : 0 ≤ Real.exp 1 * I2 * K * Real.sqrt h := by positivity
    calc Real.exp 1 * I2 * K * Real.sqrt h * (48 * x ^ (5977 / 500 : ℝ))
        ≤ Real.exp 1 * I2 * K * Real.sqrt h * (48 * x ^ (12 - ηs)) := by gcongr
      _ = _ := by ring
  have := hR.trans hfin
  nlinarith

end RamanujanTau.SCSSharp
