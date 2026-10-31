import RamanujanTau.ThetaLift.KernelSummable
import RamanujanTau.ThetaLift.TaylorExtract

/-!
# The Taylor coefficients of the Poincaré seed

The coefficient of `σⁿ/n!` in `𝔾_g(z;σ)` is a theta series with a Hermite polynomial in its summand.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex Polynomial
open scoped Real

noncomputable section

/-- The coefficient of the `x`-th Gaussian in the seed. -/
def sv (ξ y : ℝ) (g : ℤ) (z : ℂ) (x : ℤ) : ℂ :=
  cexp (-(6 * π * g ^ 2 * y ^ 2 / z.im)) * (chiZ x : ℂ) *
    cexp (2 * π * I * (x ^ 2 * z / 24 + x * (g * ξ)))

/-- The linear coefficient of the `x`-th Gaussian in the seed. -/
def sA (y : ℝ) (g : ℤ) (z : ℂ) (x : ℤ) : ℂ := x + 6 * g * y / z.im

/-- The width of the Gaussian in the seed. -/
def sB (z : ℂ) : ℂ := ((√(3 / (π * z.im)) : ℝ) : ℂ)

lemma sB_sq {z : ℂ} (hz : 0 < z.im) : sB z ^ 2 = 3 / (π * z.im) := by
  have h : 0 ≤ 3 / (π * z.im) := by
    have := Real.pi_pos
    positivity
  unfold sB
  rw [← ofReal_pow, Real.sq_sqrt h]
  push_cast
  rfl

lemma sB_ne {z : ℂ} (hz : 0 < z.im) : sB z ≠ 0 := by
  have h : 0 < 3 / (π * z.im) := by
    have := Real.pi_pos
    positivity
  unfold sB
  exact_mod_cast (Real.sqrt_pos.mpr h).ne'

/-- One term of the seed. -/
def sF (ξ y : ℝ) (g : ℤ) (z : ℂ) (x : ℤ) (σ : ℂ) : ℂ :=
  sv ξ y g z x * cexp (sA y g z x * σ - sB z ^ 2 * σ ^ 2 / 2)

lemma seed_term (ξ y : ℝ) (g : ℤ) {z : ℂ} (hz : 0 < z.im) (x : ℤ) (σ : ℂ) :
    cexp (6 * g * y * σ / z.im - 3 * σ ^ 2 / (2 * π * z.im) - 6 * π * g ^ 2 * y ^ 2 / z.im) *
      ((chiZ x : ℂ) * jacobiTheta₂_term x (g * ξ + σ / (2 * π * I)) (z / 12)) =
    sF ξ y g z x σ := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hv : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have h : cexp (6 * g * y * σ / z.im - 3 * σ ^ 2 / (2 * π * z.im) - 6 * π * g ^ 2 * y ^ 2 / z.im) *
      cexp (2 * π * I * (x ^ 2 * z / 24 + x * (g * ξ + σ / (2 * π * I)))) =
      cexp (-(6 * π * g ^ 2 * y ^ 2 / z.im)) * cexp (2 * π * I * (x ^ 2 * z / 24 + x * (g * ξ))) *
        cexp (sA y g z x * σ - sB z ^ 2 * σ ^ 2 / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, sB_sq hz]
    congr 1
    unfold sA
    field_simp
    ring
  unfold sF sv
  rw [term_eq]
  linear_combination (chiZ x : ℂ) * h

lemma seed_eq_tsum (ξ y : ℝ) (g : ℤ) {z : ℂ} (hz : 0 < z.im) (σ : ℂ) :
    seed ξ y g z σ = ∑' x : ℤ, sF ξ y g z x σ := by
  unfold seed chiTheta
  rw [← tsum_mul_left]
  exact tsum_congr fun x => seed_term ξ y g hz x σ

lemma chiZ_abs_le (x : ℤ) : |(chiZ x : ℝ)| ≤ 1 := by
  unfold chiZ
  split_ifs <;> norm_num

/-- The dominating series for the seed on a ball. -/
lemma norm_sF_le (ξ y : ℝ) (g : ℤ) {z : ℂ} (hz : 0 < z.im) {R : ℝ} (hR : 0 < R) (x : ℤ) {σ : ℂ}
    (hσ : σ ∈ Metric.ball (0 : ℂ) R) :
    ‖sF ξ y g z x σ‖ ≤ Real.exp (-(6 * π * g ^ 2 * y ^ 2 / z.im) +
        ‖(6 * g * y / z.im : ℂ)‖ * R + ‖sB z ^ 2‖ * R ^ 2 / 2) *
      (hG (π * z.im / 12) R x + hG (π * z.im / 12) (-R) x) := by
  have hσ' : ‖σ‖ ≤ R := by
    have : ‖σ‖ < R := by simpa using hσ
    exact this.le
  set C := ‖(6 * g * y / z.im : ℂ)‖
  set B := ‖sB z ^ 2‖
  have hC : 0 ≤ C := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hre : (sA y g z x * σ - sB z ^ 2 * σ ^ 2 / 2).re ≤ (|(x : ℝ)| + C) * R + B * R ^ 2 / 2 := by
    have h1 : (sA y g z x * σ - sB z ^ 2 * σ ^ 2 / 2).re ≤
        ‖sA y g z x * σ - sB z ^ 2 * σ ^ 2 / 2‖ := Complex.re_le_norm _
    have h2 : ‖sA y g z x * σ - sB z ^ 2 * σ ^ 2 / 2‖ ≤
        ‖sA y g z x‖ * ‖σ‖ + B * ‖σ‖ ^ 2 / 2 := by
      refine (norm_sub_le _ _).trans ?_
      simp [B]
    have h3 : ‖sA y g z x‖ ≤ |(x : ℝ)| + C := by
      unfold sA
      refine (norm_add_le _ _).trans ?_
      simp [C]
    have hσ0 := norm_nonneg σ
    have hx0 := abs_nonneg (x : ℝ)
    have h4 : ‖sA y g z x‖ * ‖σ‖ ≤ (|(x : ℝ)| + C) * R :=
      mul_le_mul h3 hσ' hσ0 (by positivity)
    have h5 : B * ‖σ‖ ^ 2 / 2 ≤ B * R ^ 2 / 2 := by
      have : ‖σ‖ ^ 2 ≤ R ^ 2 := by gcongr
      have := mul_le_mul_of_nonneg_left this hB
      linarith
    linarith
  have hsv : ‖sv ξ y g z x‖ ≤ Real.exp (-(6 * π * g ^ 2 * y ^ 2 / z.im)) *
      Real.exp (-(π * z.im / 12) * (x : ℝ) ^ 2) := by
    unfold sv
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
    have he1 : (-(6 * π * g ^ 2 * y ^ 2 / z.im : ℂ)).re = -(6 * π * g ^ 2 * y ^ 2 / z.im) := by
      have : (-(6 * π * g ^ 2 * y ^ 2 / z.im : ℂ)) =
          ((-(6 * π * g ^ 2 * y ^ 2 / z.im) : ℝ) : ℂ) := by push_cast; ring
      rw [this, ofReal_re]
    have he2 : (2 * π * I * (x ^ 2 * z / 24 + x * (g * ξ)) : ℂ).re =
        -(π * z.im / 12) * (x : ℝ) ^ 2 := by
      have : (2 * π * I * (x ^ 2 * z / 24 + x * (g * ξ)) : ℂ) =
          I * ((2 * π * (x ^ 2 / 24) : ℝ) : ℂ) * z + I * ((2 * π * (x * (g * ξ)) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [this]
      simp only [add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_im]
      ring
    rw [he1, he2]
    have hχ : ‖(chiZ x : ℂ)‖ ≤ 1 := by
      have := chiZ_abs_le x
      simpa [Complex.norm_intCast] using this
    have hp1 := Real.exp_pos (-(6 * π * g ^ 2 * y ^ 2 / z.im))
    have hp2 := Real.exp_pos (-(π * z.im / 12) * (x : ℝ) ^ 2)
    calc _ ≤ Real.exp (-(6 * π * g ^ 2 * y ^ 2 / z.im)) * 1 *
          Real.exp (-(π * z.im / 12) * (x : ℝ) ^ 2) := by gcongr
      _ = _ := by ring
  have hsum : Real.exp (-(π * z.im / 12) * (x : ℝ) ^ 2 + |(x : ℝ)| * R) ≤
      hG (π * z.im / 12) R x + hG (π * z.im / 12) (-R) x := by
    unfold hG
    rcases abs_cases (x : ℝ) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h, mul_comm (x : ℝ) R]
      have := Real.exp_pos (-(π * z.im / 12) * (x : ℝ) ^ 2 + -R * x)
      linarith
    · rw [h]
      have := Real.exp_pos (-(π * z.im / 12) * (x : ℝ) ^ 2 + R * x)
      have e : -(π * z.im / 12) * (x : ℝ) ^ 2 + -(x : ℝ) * R = -(π * z.im / 12) * (x : ℝ) ^ 2 + -R * x := by
        ring
      rw [e]
      linarith
  unfold sF
  rw [norm_mul, Complex.norm_exp]
  have hex : Real.exp (sA y g z x * σ - sB z ^ 2 * σ ^ 2 / 2).re ≤
      Real.exp ((|(x : ℝ)| + C) * R + B * R ^ 2 / 2) := Real.exp_le_exp.mpr hre
  calc _ ≤ (Real.exp (-(6 * π * g ^ 2 * y ^ 2 / z.im)) *
        Real.exp (-(π * z.im / 12) * (x : ℝ) ^ 2)) *
        Real.exp ((|(x : ℝ)| + C) * R + B * R ^ 2 / 2) := by gcongr
    _ = Real.exp (-(6 * π * g ^ 2 * y ^ 2 / z.im) + C * R + B * R ^ 2 / 2) *
        Real.exp (-(π * z.im / 12) * (x : ℝ) ^ 2 + |(x : ℝ)| * R) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by gcongr

lemma summable_seed_bound {K : ℝ} (hK : 0 < K) (L : ℝ) : Summable fun x : ℤ => hG K L x := by
  obtain ⟨_, _, h⟩ := gauss_uniform hK L
  simpa only [add_zero] using (h 0).1

lemma sF_differentiable (ξ y : ℝ) (g : ℤ) (z : ℂ) (x : ℤ) : Differentiable ℂ (sF ξ y g z x) := by
  unfold sF
  fun_prop

/-- **Taylor coefficients of the seed.** -/
theorem seed_iteratedDeriv (ξ y : ℝ) (g : ℤ) {z : ℂ} (hz : 0 < z.im) (n : ℕ) :
    HasSum (fun x : ℤ => sv ξ y g z x *
        (sB z ^ n * aeval (sA y g z x / sB z) (hermite n)))
      (iteratedDeriv n (seed ξ y g z) 0) := by
  have hK : 0 < π * z.im / 12 := by
    have := Real.pi_pos
    positivity
  have hu : Summable fun x : ℤ => Real.exp (-(6 * π * g ^ 2 * y ^ 2 / z.im) +
        ‖(6 * g * y / z.im : ℂ)‖ * 1 + ‖sB z ^ 2‖ * 1 ^ 2 / 2) *
      (hG (π * z.im / 12) 1 x + hG (π * z.im / 12) (-1) x) :=
    ((summable_seed_bound hK 1).add (summable_seed_bound hK (-1))).mul_left _
  have h := hasSum_iteratedDeriv (F := sF ξ y g z) hu Metric.isOpen_ball
    (sF_differentiable ξ y g z) (fun x σ hσ => norm_sF_le ξ y g hz one_pos x hσ) n
    (Metric.mem_ball_self one_pos)
  have hseed : seed ξ y g z = fun τ => ∑' x : ℤ, sF ξ y g z x τ :=
    funext fun σ => seed_eq_tsum ξ y g hz σ
  rw [hseed]
  convert h using 2 with x
  have hF : sF ξ y g z x = fun τ => sv ξ y g z x * cexp (sA y g z x * τ - sB z ^ 2 * τ ^ 2 / 2) := rfl
  have hg : ContDiffAt ℂ n (fun τ : ℂ => cexp (sA y g z x * τ - sB z ^ 2 * τ ^ 2 / 2)) 0 := by
    fun_prop
  rw [hF, iteratedDeriv_const_mul_field, iteratedDeriv_gauss _ _ (sB_ne hz)]
  simp

end

end RamanujanTau.ThetaLift
