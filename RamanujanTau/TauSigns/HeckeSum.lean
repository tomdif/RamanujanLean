/-
# Hecke's bound for partial sums of τ

`hecke_partial_sum : 0 < ε → ε ≤ 1 → ∃ C, ∀ M ≥ 1, |∑_{n ≤ M} τ(n)| ≤ C · M^{6+ε}`.

(Hecke's classical form is `O(M⁶ log M)`; any `M^{6+ε}` suffices for the sign-change
application.)  Proof: by Mathlib's coefficient integral,
`∑_{n≤M} τ(n) = ∫₀¹ K(x) Δ(x+iy) dx`,  `K(x) = ∑_{n≤M} w(x)ⁿ`,  `w = 1/q = e^{2πy}e^{-2πix}`.
Take `y = 1/M`.  Then `|Δ(x+iy)| ≤ C y^{-6} = C M⁶` (Mathlib's `CuspFormClass.exists_bound`),
`|K| ≤ (M+1)e^{2π}` and `|K|·|w−1| = |w^{M+1} − 1| ≤ 2e^{4π}`, with `|w − 1| ≥ 2 sin πx`.
Interpolating, `|K| ≤ c M^ε (sin πx)^{ε−1} ≤ c M^ε (x^{ε−1} + (1−x)^{ε−1})`, which is integrable.
-/
import RamanujanTau.TauSigns.Qualitative

set_option autoImplicit false

namespace RamanujanTau.TauSigns

open Complex ModularForm Finset Filter MeasureTheory
open UpperHalfPlane hiding I
open scoped MatrixGroups Real
open RamanujanTau.RankinSelberg

local notation "𝕢" => Function.Periodic.qParam

/-- `|e^{a+ib} − 1|² ≥ 4 sin²(b/2)` for `a ≥ 0`. -/
lemma normSq_exp_sub_one_ge {a b : ℝ} (ha : 0 ≤ a) :
    4 * Real.sin (b / 2) ^ 2 ≤ Complex.normSq (Complex.exp ((a : ℂ) + (b : ℂ) * I) - 1) := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.exp_re,
    Complex.exp_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp only [mul_zero, sub_zero, mul_one, zero_add, add_zero, sub_self]
  have hE : 1 ≤ Real.exp a := Real.one_le_exp ha
  have hc : Real.cos b ≤ 1 := Real.cos_le_one b
  have hsc := Real.sin_sq_add_cos_sq b
  have hhalf : Real.sin (b / 2) ^ 2 = (1 - Real.cos b) / 2 := by
    have h1 := Real.cos_two_mul (b / 2)
    rw [show 2 * (b / 2) = b by ring] at h1
    have h2 := Real.sin_sq_add_cos_sq (b / 2)
    linarith
  rw [hhalf]
  have hid : Real.exp a ^ 2 * (Real.sin b ^ 2 + Real.cos b ^ 2) = Real.exp a ^ 2 := by
    rw [hsc, mul_one]
  nlinarith [mul_nonneg (sub_nonneg.mpr hE) (show 0 ≤ Real.exp a + 1 - 2 * Real.cos b by linarith)]

lemma inv_qParam_eq (x y : ℝ) :
    1 / 𝕢 1 ((x : ℂ) + y * I) = Complex.exp (((2 * π * y : ℝ) : ℂ) + ((-2 * π * x : ℝ) : ℂ) * I) := by
  unfold Function.Periodic.qParam
  rw [one_div, ← Complex.exp_neg]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]; ring

lemma norm_inv_qParam (x y : ℝ) : ‖1 / 𝕢 1 ((x : ℂ) + y * I)‖ = Real.exp (2 * π * y) := by
  rw [inv_qParam_eq, Complex.norm_exp]
  simp

lemma norm_w_sub_one_ge {x y : ℝ} (hy : 0 ≤ y) :
    2 * |Real.sin (π * x)| ≤ ‖1 / 𝕢 1 ((x : ℂ) + y * I) - 1‖ := by
  rw [inv_qParam_eq]
  have h := normSq_exp_sub_one_ge (a := 2 * π * y) (b := -2 * π * x) (by positivity)
  rw [Complex.normSq_eq_norm_sq] at h
  have e : Real.sin (-2 * π * x / 2) ^ 2 = |Real.sin (π * x)| ^ 2 := by
    rw [sq_abs, show -2 * π * x / 2 = -(π * x) by ring, Real.sin_neg, neg_sq]
  rw [e] at h
  have h0 : 0 ≤ ‖Complex.exp (((2 * π * y : ℝ) : ℂ) + ((-2 * π * x : ℝ) : ℂ) * I) - 1‖ :=
    norm_nonneg _
  nlinarith [abs_nonneg (Real.sin (π * x))]

/-- Interpolation: `a ≤ A`, `a t ≤ B` give `a ≤ A^ε B^{1−ε} t^{ε−1}`. -/
lemma interp {a A B t ε : ℝ} (ha : 0 ≤ a) (hA : a ≤ A) (hB : a * t ≤ B) (ht : 0 < t)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : a ≤ A ^ ε * B ^ (1 - ε) * t ^ (ε - 1) := by
  have hat : a ≤ B / t := by rw [le_div_iff₀ ht]; exact hB
  have hB0 : 0 ≤ B := le_trans (mul_nonneg ha ht.le) hB
  have e : a = a ^ ε * a ^ (1 - ε) := by
    rw [← Real.rpow_add' ha (by norm_num)]; simp
  have h1 : a ^ ε ≤ A ^ ε := Real.rpow_le_rpow ha hA hε0
  have h2 : a ^ (1 - ε) ≤ (B / t) ^ (1 - ε) := Real.rpow_le_rpow ha hat (by linarith)
  have h3 : (B / t) ^ (1 - ε) = B ^ (1 - ε) * t ^ (ε - 1) := by
    rw [Real.div_rpow hB0 ht.le, div_eq_mul_inv, ← Real.rpow_neg ht.le, neg_sub]
  calc a = a ^ ε * a ^ (1 - ε) := e
    _ ≤ A ^ ε * (B / t) ^ (1 - ε) := by
        apply mul_le_mul h1 h2 (Real.rpow_nonneg ha _) (Real.rpow_nonneg (le_trans ha hA) _)
    _ = A ^ ε * B ^ (1 - ε) * t ^ (ε - 1) := by rw [h3]; ring

/-- `sin(πx)^{ε−1} ≤ x^{ε−1} + (1−x)^{ε−1}` on `(0,1)`. -/
lemma sin_rpow_le {x ε : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hε1 : ε ≤ 1) :
    Real.sin (π * x) ^ (ε - 1) ≤ x ^ (ε - 1) + (1 - x) ^ (ε - 1) := by
  have hz : ε - 1 ≤ 0 := by linarith
  have hp := Real.pi_pos
  rcases le_total x (1 / 2) with h | h
  · have hj := Real.mul_le_sin (x := π * x) (by positivity) (by nlinarith)
    have hx2 : x ≤ Real.sin (π * x) := by
      have : 2 / π * (π * x) = 2 * x := by field_simp
      linarith
    have := Real.rpow_le_rpow_of_nonpos hx0 hx2 hz
    linarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (ε - 1)]
  · have hs : Real.sin (π * x) = Real.sin (π * (1 - x)) := by
      rw [show π * (1 - x) = π - π * x by ring, Real.sin_pi_sub]
    have hj := Real.mul_le_sin (x := π * (1 - x)) (by nlinarith) (by nlinarith)
    have hx2 : 1 - x ≤ Real.sin (π * x) := by
      have : 2 / π * (π * (1 - x)) = 2 * (1 - x) := by field_simp
      rw [hs]; linarith
    have := Real.rpow_le_rpow_of_nonpos (by linarith) hx2 hz
    linarith [Real.rpow_nonneg hx0.le (ε - 1)]

/-- The kernel bound: on `(0,1)`, with `y = 1/M`,
`|∑_{n≤M} wⁿ| ≤ 2e^{6π} M^ε (x^{ε−1} + (1−x)^{ε−1})`. -/
lemma kernel_bound {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {M : ℕ} (hM : 1 ≤ M) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    ‖∑ n ∈ range (M + 1), (1 / 𝕢 1 ((x : ℂ) + ((1 / (M : ℝ) : ℝ) : ℂ) * I)) ^ n‖ ≤
      2 * Real.exp (6 * π) * (M : ℝ) ^ ε * (x ^ (ε - 1) + (1 - x) ^ (ε - 1)) := by
  set y : ℝ := 1 / (M : ℝ)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hy : 0 < y := by positivity
  set w := 1 / 𝕢 1 ((x : ℂ) + (y : ℂ) * I)
  set K := ∑ n ∈ range (M + 1), w ^ n
  have hw : ‖w‖ = Real.exp (2 * π * y) := norm_inv_qParam x y
  have hp := Real.pi_pos
  -- (a) trivial bound
  have ha : ‖K‖ ≤ 2 * M * Real.exp (2 * π) := by
    calc ‖K‖ ≤ ∑ n ∈ range (M + 1), ‖w ^ n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range (M + 1), Real.exp (2 * π) := by
          refine sum_le_sum fun n hn => ?_
          rw [norm_pow, hw, ← Real.exp_nat_mul]
          apply Real.exp_le_exp.mpr
          have hn : (n : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hn)
          have : (n : ℝ) * (2 * π * y) = 2 * π * ((n : ℝ) / M) := by simp only [y]; ring
          rw [this]
          have : (n : ℝ) / M ≤ 1 := (div_le_one hMpos).mpr hn
          nlinarith
      _ = (M + 1) * Real.exp (2 * π) := by simp
      _ ≤ 2 * M * Real.exp (2 * π) := by
          gcongr; linarith
  -- (b) geometric bound
  have hgeom : K * (w - 1) = w ^ (M + 1) - 1 := geom_sum_mul w (M + 1)
  have hb2 : ‖K‖ * ‖w - 1‖ ≤ 2 * Real.exp (4 * π) := by
    rw [← norm_mul, hgeom]
    calc ‖w ^ (M + 1) - 1‖ ≤ ‖w ^ (M + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = Real.exp (2 * π * y) ^ (M + 1) + 1 := by rw [norm_pow, hw, norm_one]
      _ ≤ Real.exp (4 * π) + Real.exp (4 * π) := by
          gcongr
          · rw [← Real.exp_nat_mul]
            apply Real.exp_le_exp.mpr
            have : ((M + 1 : ℕ) : ℝ) * (2 * π * y) = 2 * π * (1 + 1 / (M : ℝ)) := by
              simp only [y]; push_cast; field_simp
            rw [this]
            have : 1 / (M : ℝ) ≤ 1 := by rw [div_le_one hMpos]; exact hM1
            nlinarith
          · exact Real.one_le_exp (by positivity)
      _ = 2 * Real.exp (4 * π) := by ring
  have hsin : 0 < Real.sin (π * x) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have hwl := norm_w_sub_one_ge (x := x) hy.le
  rw [abs_of_pos hsin] at hwl
  have hb : ‖K‖ * Real.sin (π * x) ≤ Real.exp (4 * π) := by
    have := mul_le_mul_of_nonneg_left hwl (norm_nonneg K)
    linarith
  have hI := interp (norm_nonneg K) ha hb hsin hε0.le hε1
  -- simplify the constants
  have hA : (2 * M * Real.exp (2 * π)) ^ ε ≤ 2 * Real.exp (2 * π) * (M : ℝ) ^ ε := by
    rw [show 2 * (M : ℝ) * Real.exp (2 * π) = (2 * Real.exp (2 * π)) * M by ring,
      Real.mul_rpow (by positivity) hMpos.le]
    gcongr
    have h1 : 1 ≤ 2 * Real.exp (2 * π) := by
      have := Real.one_le_exp (show 0 ≤ 2 * π by positivity); linarith
    calc (2 * Real.exp (2 * π)) ^ ε ≤ (2 * Real.exp (2 * π)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 hε1
      _ = 2 * Real.exp (2 * π) := Real.rpow_one _
  have hB : Real.exp (4 * π) ^ (1 - ε) ≤ Real.exp (4 * π) := by
    calc Real.exp (4 * π) ^ (1 - ε) ≤ Real.exp (4 * π) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (by positivity)) (by linarith)
      _ = Real.exp (4 * π) := Real.rpow_one _
  have hS := sin_rpow_le hx0 hx1 hε1
  have hS0 : 0 ≤ Real.sin (π * x) ^ (ε - 1) := Real.rpow_nonneg hsin.le _
  have he : Real.exp (2 * π) * Real.exp (4 * π) = Real.exp (6 * π) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖K‖ ≤ (2 * M * Real.exp (2 * π)) ^ ε * Real.exp (4 * π) ^ (1 - ε) *
        Real.sin (π * x) ^ (ε - 1) := hI
    _ ≤ (2 * Real.exp (2 * π) * (M : ℝ) ^ ε) * Real.exp (4 * π) *
        (x ^ (ε - 1) + (1 - x) ^ (ε - 1)) := by
        apply mul_le_mul (mul_le_mul hA hB (Real.rpow_nonneg (by positivity) _) (by positivity))
          hS hS0 (by positivity)
    _ = 2 * Real.exp (6 * π) * (M : ℝ) ^ ε * (x ^ (ε - 1) + (1 - x) ^ (ε - 1)) := by
        rw [← he]; ring

/-- **Hecke-type bound for partial sums of τ**: `|∑_{n≤M} τ(n)| ≤ C M^{6+ε}`. -/
theorem hecke_partial_sum {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ M : ℕ, 1 ≤ M → |∑ n ∈ range (M + 1), (tau n : ℝ)| ≤ C * (M : ℝ) ^ (6 + ε) := by
  obtain ⟨C₀, hC₀⟩ := CuspFormClass.exists_bound (CuspForm.discriminant : CuspForm 𝒮ℒ 12)
  set g : ℝ → ℝ := fun x => x ^ (ε - 1) + (1 - x) ^ (ε - 1)
  have hg : IntervalIntegrable g volume 0 1 := by
    have h1 : IntervalIntegrable (fun x : ℝ => x ^ (ε - 1)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have h2 : IntervalIntegrable (fun x : ℝ => x ^ (ε - 1)) volume 1 0 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have h3 := h2.comp_sub_left 1
    simp only [sub_self, sub_zero] at h3
    exact h1.add h3
  set I₀ := ∫ x in (0 : ℝ)..1, g x
  set C₁ := max C₀ 0
  refine ⟨C₁ * (2 * Real.exp (6 * π)) * I₀, fun M hM => ?_⟩
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  set y : ℝ := 1 / (M : ℝ)
  have hy : 0 < y := by positivity
  set w : ℝ → ℂ := fun x => 1 / 𝕢 1 ((x : ℂ) + (y : ℂ) * I)
  set F : ℝ → ℂ := fun x => (∑ n ∈ range (M + 1), w x ^ n) * Δf (hp hy x)
  have hcontf : Continuous (fun x : ℝ => Δf (hp hy x)) :=
    (ModularFormClass.holo (CuspForm.discriminant : CuspForm 𝒮ℒ 12)).continuous.comp
      (continuous_hp hy)
  have hcontq : Continuous (fun x : ℝ => 𝕢 1 ((x : ℂ) + y * I)) := by
    unfold Function.Periodic.qParam; fun_prop
  have hcontw : Continuous w :=
    continuous_const.div hcontq fun x => Complex.exp_ne_zero _
  -- the coefficient integral
  have hcoef : ∀ n, ((tau n : ℤ) : ℂ) = ∫ x in (0 : ℝ)..1, w x ^ n * Δf (hp hy x) := by
    intro n
    have h := ModularFormClass.qExpansion_coeff_eq_intervalIntegral
      (CuspForm.discriminant : CuspForm 𝒮ℒ 12) one_pos one_mem_strictPeriods_SL n hy
    rw [TauBound.qExpansion_discriminant_coeff_tau] at h
    rw [h]
    simp only [w, one_div_pow]
    simp [hp]
  have hsum : ((∑ n ∈ range (M + 1), (tau n : ℝ) : ℝ) : ℂ) = ∫ x in (0 : ℝ)..1, F x := by
    push_cast
    simp_rw [hcoef]
    rw [← intervalIntegral.integral_finsetSum]
    · congr 1 with x
      simp only [F, Finset.sum_mul]
    · intro n _
      exact ((hcontw.pow n).mul hcontf).intervalIntegrable _ _
  -- pointwise bound
  have hΔ : ∀ x, ‖Δf (hp hy x)‖ ≤ C₁ * (M : ℝ) ^ 6 := by
    intro x
    have h := hC₀ (hp hy x)
    rw [hp_im, show (((12 : ℤ) : ℝ) / 2) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    have : C₀ / y ^ 6 = C₀ * (M : ℝ) ^ 6 := by simp only [y]; field_simp
    rw [this] at h
    exact le_trans h (by gcongr; exact le_max_left _ _)
  have hptw : ∀ᵐ x ∂volume, x ∈ Set.Ioc (0 : ℝ) 1 →
      ‖F x‖ ≤ C₁ * (2 * Real.exp (6 * π)) * (M : ℝ) ^ (6 + ε) * g x := by
    have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with x hx1 hx
    obtain ⟨hx0, hx1'⟩ := hx
    have hxl : x < 1 := lt_of_le_of_ne hx1' hx1
    have hk := kernel_bound hε0 hε1 hM hx0 hxl
    have hpow : (M : ℝ) ^ (6 + ε) = (M : ℝ) ^ ε * (M : ℝ) ^ 6 := by
      rw [Real.rpow_add hMpos, mul_comm]; norm_cast
    have hg0 : 0 ≤ g x := by
      exact add_nonneg (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg (by linarith) _)
    simp only [F, norm_mul]
    calc ‖∑ n ∈ range (M + 1), w x ^ n‖ * ‖Δf (hp hy x)‖
        ≤ (2 * Real.exp (6 * π) * (M : ℝ) ^ ε * g x) * (C₁ * (M : ℝ) ^ 6) :=
          mul_le_mul hk (hΔ x) (norm_nonneg _) (by positivity)
      _ = C₁ * (2 * Real.exp (6 * π)) * (M : ℝ) ^ (6 + ε) * g x := by rw [hpow]; ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1) hptw
    (hg.const_mul (C₁ * (2 * Real.exp (6 * π)) * (M : ℝ) ^ (6 + ε)))
  rw [← hsum, Complex.norm_real, Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hint
  calc |∑ n ∈ range (M + 1), (tau n : ℝ)| ≤ C₁ * (2 * Real.exp (6 * π)) * (M : ℝ) ^ (6 + ε) * I₀ :=
        hint
    _ = C₁ * (2 * Real.exp (6 * π)) * I₀ * (M : ℝ) ^ (6 + ε) := by ring

end RamanujanTau.TauSigns

#print axioms RamanujanTau.TauSigns.hecke_partial_sum
