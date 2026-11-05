/-
# Wilton's uniform bound for additively twisted partial sums of τ

`wilton_bound : ∃ C, ∀ α : ℝ, ∀ M ≥ 1, ‖∑_{n ≤ M} τ(n) e(nα)‖ ≤ C · M⁶ · log(1 + 2M)`,

uniformly in the real frequency `α` (Wilton 1929).  In normalized form
`∑_{n≤M} λ(n) e(nα) ≪ M^{1/2} log M` after partial summation: square-root cancellation,
uniform in `α`.

Proof (the twisted version of `TauSigns.hecke_partial_sum`).  Put `y = 1/M`,
`w(x) = 1/𝕢(x+iy) = e^{2πy} e^{−2πix}`.  Mathlib's coefficient integral gives
`τ(n) = ∫₀¹ w(x)ⁿ Δ(x+iy) dx`; the integrand is `1`-periodic, so translating by `α` and using
`w(x+α) = w(x) e(−α)`:

    τ(n) e(nα) = ∫₀¹ w(x)ⁿ Δ(x + α + iy) dx.

Summing, `∑_{n≤M} τ(n)e(nα) = ∫₀¹ K(x) Δ(x+α+iy) dx` with `K = ∑_{n≤M} wⁿ`.  Now
`|Δ| ≤ C y^{−6} = C M⁶` everywhere (Mathlib's `CuspFormClass.exists_bound`), and
`|K| ≤ 2e^{2π}M`, `|K| sin(πx) ≤ e^{4π}`, hence `|K| ≤ (2e^{2π}+e^{4π}) M / (1 + M sin πx)`,
and `sin πx ≥ 2 min(x, 1−x)` gives `∫₀¹ M/(1+M sin πx) dx ≤ log(1+2M)`.
-/
import RamanujanTau.TauSigns.HeckeSum

set_option autoImplicit false

namespace RamanujanTau.Subconvexity

open Complex ModularForm Finset Filter MeasureTheory
open UpperHalfPlane hiding I
open scoped MatrixGroups Real
open RamanujanTau.RankinSelberg RamanujanTau.TauSigns

local notation "𝕢" => Function.Periodic.qParam

/-- The additive character `e(θ) = exp(2πiθ)`. -/
noncomputable def eC (θ : ℝ) : ℂ := Complex.exp (2 * π * I * θ)

lemma norm_eC (θ : ℝ) : ‖eC θ‖ = 1 := by
  unfold eC
  rw [show (2 * π * I * θ : ℂ) = ((2 * π * θ : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `1/𝕢(x+α+iy) = 1/𝕢(x+iy) · e(−α)`. -/
lemma inv_qParam_add (x α y : ℝ) :
    1 / 𝕢 1 (((x + α : ℝ) : ℂ) + y * I) = 1 / 𝕢 1 ((x : ℂ) + y * I) * eC (-α) := by
  unfold Function.Periodic.qParam eC
  rw [one_div, one_div, ← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `Δ(x+iy)` is `1`-periodic in `x`. -/
lemma Δf_hp_periodic {y : ℝ} (hy : 0 < y) : Function.Periodic (fun x => Δf (hp hy x)) 1 := by
  intro x
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) one_mem_strictPeriods_SL
  have h := hper ((x : ℂ) + y * I)
  have e1 : ∀ u : ℝ, ofComplex ((u : ℂ) + y * I) = hp hy u := by
    intro u
    rw [ofComplex_apply_of_im_pos (by simpa using hy)]
    rfl
  simp only [Function.comp_apply] at h
  show Δf (hp hy (x + 1)) = Δf (hp hy x)
  rw [← e1 x, ← e1 (x + 1), show ((x + 1 : ℝ) : ℂ) + y * I = (x : ℂ) + y * I + 1 by
    push_cast; ring]
  simpa using h

/-- **Twisted coefficient integral**: `τ(n) e(nα) = ∫₀¹ w(x)ⁿ Δ(x+α+iy) dx`. -/
lemma tau_twist_integral (n : ℕ) {y : ℝ} (hy : 0 < y) (α : ℝ) :
    ((tau n : ℤ) : ℂ) * eC (n * α) =
      ∫ x in (0 : ℝ)..1, (1 / 𝕢 1 ((x : ℂ) + y * I)) ^ n * Δf (hp hy (x + α)) := by
  set G : ℝ → ℂ := fun x => (1 / 𝕢 1 ((x : ℂ) + y * I)) ^ n * Δf (hp hy x)
  have hcoef : ((tau n : ℤ) : ℂ) = ∫ x in (0 : ℝ)..1, G x := by
    have h := ModularFormClass.qExpansion_coeff_eq_intervalIntegral
      (CuspForm.discriminant : CuspForm 𝒮ℒ 12) one_pos one_mem_strictPeriods_SL n hy
    rw [TauBound.qExpansion_discriminant_coeff_tau] at h
    rw [h]
    simp only [G, one_div_pow]
    simp [hp]
  have hGper : Function.Periodic G 1 := by
    intro x
    simp only [G]
    rw [show Δf (hp hy (x + 1)) = Δf (hp hy x) from Δf_hp_periodic hy x]
    congr 2
    have := inv_qParam_add x 1 y
    rw [this]
    unfold eC
    rw [show (2 * π * I * ((-1 : ℝ) : ℂ)) = -(2 * π * I) by push_cast; ring, Complex.exp_neg,
      Complex.exp_two_pi_mul_I, inv_one, mul_one]
  have hshift : ∫ x in (0 : ℝ)..1, G x = ∫ x in (0 : ℝ)..1, G (x + α) := by
    rw [intervalIntegral.integral_comp_add_right G α, zero_add,
      show (1 : ℝ) + α = α + 1 by ring, hGper.intervalIntegral_add_eq α 0, zero_add]
  rw [hcoef, hshift, ← intervalIntegral.integral_mul_const]
  congr 1 with x
  simp only [G]
  rw [inv_qParam_add, mul_pow]
  have h1 : eC (-α) ^ n * eC (n * α) = 1 := by
    unfold eC
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    rw [show (n : ℂ) * (2 * π * I * ((-α : ℝ) : ℂ)) + 2 * π * I * (((n : ℝ) * α : ℝ) : ℂ) = 0 by
      push_cast; ring, Complex.exp_zero]
  calc (1 / 𝕢 1 ((x : ℂ) + y * I)) ^ n * eC (-α) ^ n * Δf (hp hy (x + α)) * eC (n * α)
      = (1 / 𝕢 1 ((x : ℂ) + y * I)) ^ n * Δf (hp hy (x + α)) * (eC (-α) ^ n * eC (n * α)) := by
        ring
    _ = _ := by rw [h1, mul_one]

/-- The kernel bound: `‖∑_{n≤M} wⁿ‖ ≤ (2e^{2π} + e^{4π}) M / (1 + M sin πx)` on `(0,1)`. -/
lemma kernel_bound_log {M : ℕ} (hM : 1 ≤ M) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ‖∑ n ∈ range (M + 1), (1 / 𝕢 1 ((x : ℂ) + ((1 / (M : ℝ) : ℝ) : ℂ) * I)) ^ n‖ ≤
      (2 * Real.exp (2 * π) + Real.exp (4 * π)) * M / (1 + M * Real.sin (π * x)) := by
  set y : ℝ := 1 / (M : ℝ)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hy : 0 < y := by positivity
  set w := 1 / 𝕢 1 ((x : ℂ) + (y : ℂ) * I)
  set K := ∑ n ∈ range (M + 1), w ^ n
  have hw : ‖w‖ = Real.exp (2 * π * y) := norm_inv_qParam x y
  have hp := Real.pi_pos
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
  have hden : 0 < 1 + M * Real.sin (π * x) := by positivity
  rw [le_div_iff₀ hden]
  have hMb : (M : ℝ) * (‖K‖ * Real.sin (π * x)) ≤ M * Real.exp (4 * π) :=
    mul_le_mul_of_nonneg_left hb hMpos.le
  nlinarith

/-- `1/(1 + M sin πx) ≤ 1/(1+2Mx) + 1/(1+2M(1−x))` on `(0,1)`. -/
lemma inv_sin_le {M : ℝ} (hM : 0 ≤ M) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    1 / (1 + M * Real.sin (π * x)) ≤ 1 / (1 + 2 * M * x) + 1 / (1 + 2 * M * (1 - x)) := by
  have hp := Real.pi_pos
  have h1 : 0 < 1 + 2 * M * x := by positivity
  have h2 : 0 < 1 + 2 * M * (1 - x) := by nlinarith
  have hpos1 : 0 ≤ 1 / (1 + 2 * M * x) := by positivity
  have hpos2 : 0 ≤ 1 / (1 + 2 * M * (1 - x)) := by positivity
  rcases le_total x (1 / 2) with h | h
  · have hj := Real.mul_le_sin (x := π * x) (by positivity) (by nlinarith)
    have hx2 : 2 * x ≤ Real.sin (π * x) := by
      have : 2 / π * (π * x) = 2 * x := by field_simp
      linarith
    have : 1 / (1 + M * Real.sin (π * x)) ≤ 1 / (1 + 2 * M * x) := by
      apply one_div_le_one_div_of_le h1
      nlinarith
    linarith
  · have hs : Real.sin (π * x) = Real.sin (π * (1 - x)) := by
      rw [show π * (1 - x) = π - π * x by ring, Real.sin_pi_sub]
    have hj := Real.mul_le_sin (x := π * (1 - x)) (by nlinarith) (by nlinarith)
    have hx2 : 2 * (1 - x) ≤ Real.sin (π * x) := by
      have : 2 / π * (π * (1 - x)) = 2 * (1 - x) := by field_simp
      rw [hs]; linarith
    have : 1 / (1 + M * Real.sin (π * x)) ≤ 1 / (1 + 2 * M * (1 - x)) := by
      apply one_div_le_one_div_of_le h2
      nlinarith
    linarith

/-- `∫₀¹ dx/(1+2Mx) = log(1+2M)/(2M)`. -/
lemma integral_inv_lin {M : ℝ} (hM : 0 < M) :
    ∫ x in (0 : ℝ)..1, 1 / (1 + 2 * M * x) = Real.log (1 + 2 * M) / (2 * M) := by
  have h := intervalIntegral.integral_comp_mul_add (fun u : ℝ => u⁻¹) (a := 0) (b := 1)
    (show (2 * M) ≠ 0 by positivity) 1
  simp only at h
  have e : ∀ x : ℝ, 1 / (1 + 2 * M * x) = (2 * M * x + 1)⁻¹ := by intro x; rw [one_div]; ring_nf
  simp_rw [e]
  rw [h, mul_zero, zero_add, mul_one, integral_inv]
  · rw [div_one, smul_eq_mul, add_comm]; field_simp
  · rw [Set.mem_uIcc]; push Not
    constructor <;> intro h0 <;> linarith

/-- The reflected integral `∫₀¹ dx/(1+2M(1−x)) = log(1+2M)/(2M)`. -/
lemma integral_inv_lin' {M : ℝ} (hM : 0 < M) :
    ∫ x in (0 : ℝ)..1, 1 / (1 + 2 * M * (1 - x)) = Real.log (1 + 2 * M) / (2 * M) := by
  have h := intervalIntegral.integral_comp_sub_left (fun x : ℝ => 1 / (1 + 2 * M * x))
    (a := 0) (b := 1) 1
  simp only [sub_zero, sub_self] at h
  rw [h, ← integral_inv_lin hM]

/-- **Wilton's uniform bound** for additively twisted partial sums of `τ`:
`‖∑_{n ≤ M} τ(n) e(nα)‖ ≤ C M⁶ log(1+2M)` for every real `α` and every `M ≥ 1`. -/
theorem wilton_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : ℝ) (M : ℕ), 1 ≤ M →
    ‖∑ n ∈ range (M + 1), ((tau n : ℤ) : ℂ) * eC (n * α)‖ ≤
      C * (M : ℝ) ^ 6 * Real.log (1 + 2 * M) := by
  obtain ⟨C₀, hC₀⟩ := CuspFormClass.exists_bound (CuspForm.discriminant : CuspForm 𝒮ℒ 12)
  set C₁ := max C₀ 0
  set A : ℝ := 2 * Real.exp (2 * π) + Real.exp (4 * π)
  have hA : 0 ≤ A := by positivity
  refine ⟨C₁ * A, mul_nonneg (le_max_right _ _) hA, fun α M hM => ?_⟩
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  set y : ℝ := 1 / (M : ℝ)
  have hy : 0 < y := by positivity
  set w : ℝ → ℂ := fun x => 1 / 𝕢 1 ((x : ℂ) + (y : ℂ) * I)
  set F : ℝ → ℂ := fun x => (∑ n ∈ range (M + 1), w x ^ n) * Δf (hp hy (x + α))
  have hcontf : Continuous (fun x : ℝ => Δf (hp hy (x + α))) :=
    (ModularFormClass.holo (CuspForm.discriminant : CuspForm 𝒮ℒ 12)).continuous.comp
      ((continuous_hp hy).comp (continuous_id.add continuous_const))
  have hcontq : Continuous (fun x : ℝ => 𝕢 1 ((x : ℂ) + y * I)) := by
    unfold Function.Periodic.qParam; fun_prop
  have hcontw : Continuous w :=
    continuous_const.div hcontq fun x => Complex.exp_ne_zero _
  have hsum : ∑ n ∈ range (M + 1), ((tau n : ℤ) : ℂ) * eC (n * α) = ∫ x in (0 : ℝ)..1, F x := by
    simp_rw [fun n => tau_twist_integral n hy α]
    rw [← intervalIntegral.integral_finsetSum]
    · congr 1 with x
      simp only [F, w, Finset.sum_mul]
    · intro n _
      exact ((hcontw.pow n).mul hcontf).intervalIntegrable _ _
  have hΔ : ∀ x, ‖Δf (hp hy (x + α))‖ ≤ C₁ * (M : ℝ) ^ 6 := by
    intro x
    have h := hC₀ (hp hy (x + α))
    rw [hp_im, show (((12 : ℤ) : ℝ) / 2) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    have : C₀ / y ^ 6 = C₀ * (M : ℝ) ^ 6 := by simp only [y]; field_simp
    rw [this] at h
    exact le_trans h (by gcongr; exact le_max_left _ _)
  set g : ℝ → ℝ := fun x => 1 / (1 + 2 * M * x) + 1 / (1 + 2 * M * (1 - x))
  have hgc : ContinuousOn g (Set.uIcc 0 1) := by
    apply ContinuousOn.add
    · apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx; rw [Set.uIcc_of_le zero_le_one] at hx; nlinarith [hx.1]
    · apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx; rw [Set.uIcc_of_le zero_le_one] at hx; nlinarith [hx.2]
  have hg : IntervalIntegrable g volume 0 1 := hgc.intervalIntegrable
  have hptw : ∀ᵐ x ∂volume, x ∈ Set.Ioc (0 : ℝ) 1 →
      ‖F x‖ ≤ C₁ * A * (M : ℝ) ^ 7 * g x := by
    have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with x hx1 hx
    obtain ⟨hx0, hx1'⟩ := hx
    have hxl : x < 1 := lt_of_le_of_ne hx1' hx1
    have hk := kernel_bound_log hM hx0 hxl
    have hi := inv_sin_le hMpos.le hx0 hxl
    have hk' : ‖∑ n ∈ range (M + 1), w x ^ n‖ ≤ A * M * g x := by
      refine hk.trans ?_
      rw [show A * M / (1 + M * Real.sin (π * x)) = A * M * (1 / (1 + M * Real.sin (π * x))) by
        ring]
      gcongr
    simp only [F, norm_mul]
    calc ‖∑ n ∈ range (M + 1), w x ^ n‖ * ‖Δf (hp hy (x + α))‖
        ≤ (A * M * g x) * (C₁ * (M : ℝ) ^ 6) :=
          mul_le_mul hk' (hΔ x) (norm_nonneg _) (by
            have : 0 ≤ g x := by
              simp only [g]
              have : 0 < 1 + 2 * (M : ℝ) * (1 - x) := by nlinarith
              positivity
            positivity)
      _ = C₁ * A * (M : ℝ) ^ 7 * g x := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1) hptw
    (hg.const_mul (C₁ * A * (M : ℝ) ^ 7))
  rw [← hsum, intervalIntegral.integral_const_mul] at hint
  have hgI : ∫ x in (0 : ℝ)..1, g x = Real.log (1 + 2 * M) / M := by
    have h1 : IntervalIntegrable (fun x : ℝ => 1 / (1 + 2 * M * x)) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx; rw [Set.uIcc_of_le zero_le_one] at hx; nlinarith [hx.1]
    have h2 : IntervalIntegrable (fun x : ℝ => 1 / (1 + 2 * M * (1 - x))) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx; rw [Set.uIcc_of_le zero_le_one] at hx; nlinarith [hx.2]
    simp only [g]
    rw [intervalIntegral.integral_add h1 h2, integral_inv_lin hMpos, integral_inv_lin' hMpos]
    field_simp
    ring
  rw [hgI] at hint
  calc ‖∑ n ∈ range (M + 1), ((tau n : ℤ) : ℂ) * eC (n * α)‖
      ≤ C₁ * A * (M : ℝ) ^ 7 * (Real.log (1 + 2 * M) / M) := hint
    _ = C₁ * A * (M : ℝ) ^ 6 * Real.log (1 + 2 * M) := by
        field_simp

end RamanujanTau.Subconvexity
