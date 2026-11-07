import RamanujanTau.ThetaLift.KernelOne

/-!
# Cauchy–Riemann for the obstruction

The obstruction `α(w) = y'^(1-λ) - (6w+1)^(2λ) y^(1-λ)` is not holomorphic at `w₀ = -1/6 + i`, when `λ ≥ 2`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex
open UpperHalfPlane hiding I
open scoped Real MatrixGroups Topology
open Rademacher

noncomputable section

/-- The matrix `[1, 0; 6, 1]`. -/
def g6 : SL(2, ℤ) := ⟨!![1, 0; 6, 1], by simp [Matrix.det_fin_two_of]⟩

lemma g6_10 : g6 1 0 = 6 * ((1 : ℕ) : ℤ) * 1 := rfl

lemma lin_g6 (w : ℂ) : lin g6 w = 6 * w + 1 := by
  simp [lin, g6]

lemma mob_g6 (w : ℂ) : mob g6 w = w / (6 * w + 1) := by
  simp [mob, g6]

/-- The base point. -/
def w₀ : ℂ := -1 / 6 + I

lemma w₀_im : w₀.im = 1 := by simp [w₀]

lemma rY_one_div (μ : ℕ) {M : ℝ} (hM : 0 < M) : rY (μ + 1) (1 / M) = M ^ μ := by
  unfold rY
  rw [div_pow, one_pow, one_div, inv_inv, one_div, pow_succ]
  field_simp

lemma alpha_line1 (μ : ℕ) (t : ℝ) :
    alphaF (μ + 1) g6 (w₀ + t) =
      (36 * (t : ℂ) ^ 2 + 36) ^ μ - (6 * (t : ℂ) + 6 * I) ^ (2 * (μ + 1)) := by
  have hj : 6 * (w₀ + (t : ℂ)) + 1 = 6 * (t : ℂ) + 6 * I := by
    unfold w₀
    ring
  have him : (w₀ + (t : ℂ)).im = 1 := by simp [w₀]
  have hpos : 0 < (w₀ + (t : ℂ)).im := by rw [him]; norm_num
  have hn : Complex.normSq (6 * (t : ℂ) + 6 * I) = 36 * t ^ 2 + 36 := by
    rw [Complex.normSq_apply]
    simp
    ring
  have hM : 0 < 36 * t ^ 2 + 36 := by positivity
  have hmob : (mob g6 (w₀ + (t : ℂ))).im = 1 / (36 * t ^ 2 + 36) := by
    have h := mob_im' g6 hpos
    rw [him, lin_g6, hj, hn] at h
    exact h
  unfold alphaF
  rw [hmob, him, rY_one_div μ hM, lin_g6, hj]
  have hr1 : rY (μ + 1) 1 = 1 := by simp [rY]
  rw [hr1]
  push_cast
  ring

lemma alpha_line2 (μ : ℕ) {t : ℝ} (ht : -1 < t) :
    alphaF (μ + 1) g6 (w₀ + (t : ℂ) * I) =
      36 ^ μ * (1 + (t : ℂ)) ^ μ - (6 * I) ^ (2 * (μ + 1)) * (1 + (t : ℂ)) ^ (μ + 2) := by
  have hy : 0 < 1 + t := by linarith
  have hyC : (1 + (t : ℂ)) ≠ 0 := by exact_mod_cast hy.ne'
  have hj : 6 * (w₀ + (t : ℂ) * I) + 1 = 6 * I * (1 + (t : ℂ)) := by
    unfold w₀
    ring
  have him : (w₀ + (t : ℂ) * I).im = 1 + t := by simp [w₀]
  have hpos : 0 < (w₀ + (t : ℂ) * I).im := by rw [him]; exact hy
  have hn : Complex.normSq (6 * I * (1 + (t : ℂ))) = 36 * (1 + t) ^ 2 := by
    have e : 6 * I * (1 + (t : ℂ)) = ((0 : ℝ) : ℂ) + ((6 * (1 + t) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [e, Complex.normSq_add_mul_I]
    ring
  have hmob : (mob g6 (w₀ + (t : ℂ) * I)).im = 1 / (36 * (1 + t)) := by
    have h := mob_im' g6 hpos
    rw [him, lin_g6, hj, hn] at h
    rw [h]
    field_simp
  have hM : 0 < 36 * (1 + t) := by positivity
  unfold alphaF
  rw [hmob, him, rY_one_div μ hM, lin_g6, hj]
  unfold rY
  push_cast
  rw [mul_pow]
  have hpow : ((1 + (t : ℂ)) ^ (2 * (μ + 1))) * (((1 + (t : ℂ)) ^ (μ + 1))⁻¹ * (1 + (t : ℂ))) =
      (1 + (t : ℂ)) ^ (μ + 2) := by
    have e : 2 * (μ + 1) = (μ + 1) + (μ + 1) := by ring
    rw [e, pow_add, show μ + 2 = (μ + 1) + 1 by ring, pow_succ (1 + (t : ℂ)) (μ + 1)]
    field_simp
  calc _ = 36 ^ μ * (1 + (t : ℂ)) ^ μ - (6 * I) ^ (2 * (μ + 1)) * (((1 + (t : ℂ)) ^ (2 * (μ + 1))) *
        (((1 + (t : ℂ)) ^ (μ + 1))⁻¹ * (1 + (t : ℂ)))) := by
        rw [mul_pow]
        ring
    _ = _ := by rw [hpow]

/-- **The obstruction is not holomorphic at the base point.** -/
theorem alpha_not_diff (μ : ℕ) (hμ : μ ≠ 0) : ¬ DifferentiableAt ℂ (alphaF (μ + 1) g6) w₀ := by
  intro hd
  have hD := hd.hasDerivAt
  set D := deriv (alphaF (μ + 1) g6) w₀ with hDdef
  -- the horizontal line
  have h1 : HasDerivAt (fun s : ℂ => alphaF (μ + 1) g6 (w₀ + s)) D 0 := by
    have hs : HasDerivAt (fun s : ℂ => w₀ + s) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_add w₀
    have hD' : HasDerivAt (alphaF (μ + 1) g6) D (w₀ + 0) := by rwa [add_zero]
    simpa using hD'.comp (0 : ℂ) hs
  have hP1 : HasDerivAt (fun s : ℂ => (36 * s ^ 2 + 36) ^ μ - (6 * s + 6 * I) ^ (2 * (μ + 1)))
      (-(((2 * (μ + 1) : ℕ) : ℂ) * (6 * I) ^ (2 * μ + 1) * 6)) 0 := by
    have hA : HasDerivAt (fun s : ℂ => (36 * s ^ 2 + 36) ^ μ) 0 0 := by
      have h0 := (((hasDerivAt_id (0 : ℂ)).pow 2).const_mul 36).add_const 36
      have h3 := h0.pow μ
      convert h3 using 1
      simp
    have hB : HasDerivAt (fun s : ℂ => (6 * s + 6 * I) ^ (2 * (μ + 1)))
        (((2 * (μ + 1) : ℕ) : ℂ) * (6 * I) ^ (2 * μ + 1) * 6) 0 := by
      have h0 := ((hasDerivAt_id (0 : ℂ)).const_mul 6).add_const (6 * I)
      have h3 := h0.pow (2 * (μ + 1))
      convert h3 using 1
      simp [show 2 * (μ + 1) - 1 = 2 * μ + 1 by omega]
    simpa using hA.sub hB
  have hfun1 : (fun t : ℝ => alphaF (μ + 1) g6 (w₀ + (t : ℂ))) =
      fun t : ℝ => (36 * (t : ℂ) ^ 2 + 36) ^ μ - (6 * (t : ℂ) + 6 * I) ^ (2 * (μ + 1)) :=
    funext fun t => alpha_line1 μ t
  have hDval : D = -(((2 * (μ + 1) : ℕ) : ℂ) * (6 * I) ^ (2 * μ + 1) * 6) := by
    have hzero : (((0 : ℝ) : ℂ)) = 0 := ofReal_zero
    have a1 : HasDerivAt (fun t : ℝ => alphaF (μ + 1) g6 (w₀ + (t : ℂ))) D (0 : ℝ) := by
      refine HasDerivAt.comp_ofReal (e := fun s : ℂ => alphaF (μ + 1) g6 (w₀ + s)) ?_
      rwa [hzero]
    have a2 : HasDerivAt (fun t : ℝ => (36 * (t : ℂ) ^ 2 + 36) ^ μ - (6 * (t : ℂ) + 6 * I) ^ (2 * (μ + 1)))
        (-(((2 * (μ + 1) : ℕ) : ℂ) * (6 * I) ^ (2 * μ + 1) * 6)) (0 : ℝ) := by
      refine HasDerivAt.comp_ofReal (e := fun s : ℂ =>
        (36 * s ^ 2 + 36) ^ μ - (6 * s + 6 * I) ^ (2 * (μ + 1))) ?_
      rwa [hzero]
    rw [hfun1] at a1
    exact a1.unique a2
  -- the vertical line
  have h2 : HasDerivAt (fun s : ℂ => alphaF (μ + 1) g6 (w₀ + s * I)) (D * I) 0 := by
    have hs : HasDerivAt (fun s : ℂ => w₀ + s * I) I 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).mul_const I).const_add w₀
      simpa using this
    have hD' : HasDerivAt (alphaF (μ + 1) g6) D (w₀ + 0 * I) := by
      rwa [zero_mul, add_zero]
    simpa using hD'.comp (0 : ℂ) hs
  have hP2 : HasDerivAt (fun s : ℂ => 36 ^ μ * (1 + s) ^ μ - (6 * I) ^ (2 * (μ + 1)) * (1 + s) ^ (μ + 2))
      (36 ^ μ * (μ : ℂ) - (6 * I) ^ (2 * (μ + 1)) * ((μ + 2 : ℕ) : ℂ)) 0 := by
    have h0 : HasDerivAt (fun s : ℂ => 1 + s) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_add 1
    have hA := (h0.pow μ).const_mul ((36 : ℂ) ^ μ)
    have hB := (h0.pow (μ + 2)).const_mul ((6 * I) ^ (2 * (μ + 1)))
    convert hA.sub hB using 1
    simp
  have hDI : D * I = 36 ^ μ * (μ : ℂ) - (6 * I) ^ (2 * (μ + 1)) * ((μ + 2 : ℕ) : ℂ) := by
    have hzero : (((0 : ℝ) : ℂ)) = 0 := ofReal_zero
    have a1 : HasDerivAt (fun t : ℝ => alphaF (μ + 1) g6 (w₀ + (t : ℂ) * I)) (D * I) (0 : ℝ) := by
      refine HasDerivAt.comp_ofReal (e := fun s : ℂ => alphaF (μ + 1) g6 (w₀ + s * I)) ?_
      rwa [hzero]
    have a2 : HasDerivAt (fun t : ℝ => (36 : ℂ) ^ μ * (1 + (t : ℂ)) ^ μ -
        (6 * I) ^ (2 * (μ + 1)) * (1 + (t : ℂ)) ^ (μ + 2))
        (36 ^ μ * (μ : ℂ) - (6 * I) ^ (2 * (μ + 1)) * ((μ + 2 : ℕ) : ℂ)) (0 : ℝ) := by
      refine HasDerivAt.comp_ofReal (e := fun s : ℂ =>
        36 ^ μ * (1 + s) ^ μ - (6 * I) ^ (2 * (μ + 1)) * (1 + s) ^ (μ + 2)) ?_
      rwa [hzero]
    have hev : (fun t : ℝ => alphaF (μ + 1) g6 (w₀ + (t : ℂ) * I)) =ᶠ[𝓝 (0 : ℝ)] fun t : ℝ =>
        (36 : ℂ) ^ μ * (1 + (t : ℂ)) ^ μ - (6 * I) ^ (2 * (μ + 1)) * (1 + (t : ℂ)) ^ (μ + 2) := by
      filter_upwards [Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 0)] with t ht
      exact alpha_line2 μ ht
    exact (a1.congr_of_eventuallyEq hev.symm).unique a2
  -- the contradiction
  have hμC : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  have hpow : (6 * I) ^ (2 * (μ + 1)) = (6 * I) ^ (2 * μ + 1) * (6 * I) := by
    rw [show 2 * (μ + 1) = (2 * μ + 1) + 1 by ring, pow_succ]
  have hmain : (μ : ℂ) * (36 ^ μ + (6 * I) ^ (2 * (μ + 1))) = 0 := by
    rw [hDval] at hDI
    push_cast at hDI ⊢
    rw [hpow] at hDI ⊢
    linear_combination -hDI
  have heq : (36 : ℂ) ^ μ = -(6 * I) ^ (2 * (μ + 1)) := by
    have := (mul_eq_zero.mp hmain).resolve_left hμC
    linear_combination this
  have hnorm := congrArg norm heq
  rw [norm_neg, norm_pow, norm_pow, norm_mul, Complex.norm_I, mul_one] at hnorm
  have e6 : ‖(6 : ℂ)‖ = 6 := by simp
  have e36 : ‖(36 : ℂ)‖ = 36 := by simp
  rw [e6, e36, pow_mul] at hnorm
  norm_num at hnorm

variable {k' : ℤ} (G : CuspForm 𝒮ℒ k') (j : ℕ)

/-- The obstruction at the base point is nonzero. -/
lemma alpha_base_ne (μ : ℕ) : alphaF (μ + 1) g6 w₀ ≠ 0 := by
  intro h
  have h1 := alpha_line1 μ 0
  simp only [ofReal_zero, add_zero] at h1
  rw [h] at h1
  have h2 : (36 : ℂ) ^ μ = (6 * I) ^ (2 * (μ + 1)) := by
    have : (0 : ℂ) = (36 * 0 ^ 2 + 36) ^ μ - (6 * 0 + 6 * I) ^ (2 * (μ + 1)) := h1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add] at this
    linear_combination -this
  have hnorm := congrArg norm h2
  rw [norm_pow, norm_pow, norm_mul, Complex.norm_I, mul_one] at hnorm
  have e6 : ‖(6 : ℂ)‖ = 6 := by simp
  have e36 : ‖(36 : ℂ)‖ = 36 := by simp
  rw [e6, e36, pow_mul] at hnorm
  norm_num at hnorm

/-- **The covariance law for `t = 1`.** -/
theorem defect_one (μ : ℕ) (hμ : μ ≠ 0) (hj : j < 24) (hNj : (24 : ℤ) ∣ ((1 : ℕ) : ℤ) * j + 1)
    (htj : 24 ∣ 1 + j) {w : ℕ} (hjw : j + 1 = 2 * w) (hk : k' = ((μ + 1 + w : ℕ) : ℤ))
    (hneg : ∀ g, jN 1 (-g) = (-1) ^ (μ + 1) * jN 1 g)
    (hT : ∀ t : ℂ, 0 < t.im → DifferentiableAt ℂ
      (fun t : ℂ => lamSum G j (N := 1) (jN 1) (μ + 1) t.re t.im) t)
    (γ : SL(2, ℤ)) {E : ℤ} (hE : γ 1 0 = 6 * ((1 : ℕ) : ℤ) * E) {t : ℂ} (ht : 0 < t.im) :
    defectT G j (N := 1) (μ + 1) γ t = 0 := by
  have h1 : (0 : ℕ) < 1 := one_pos
  have ht2 : ¬ 2 ∣ 1 := by norm_num
  have ht3 : ¬ 3 ∣ 1 := by norm_num
  have hw₀ : 0 < w₀.im := by rw [w₀_im]; norm_num
  have ha₀ := alpha_base_ne μ
  have hcross : ∀ (γ' : SL(2, ℤ)) {E' : ℤ} (_ : γ' 1 0 = 6 * ((1 : ℕ) : ℤ) * E') {t' : ℂ} (_ : 0 < t'.im),
      defectT G j (N := 1) (μ + 1) γ' t' =
        (defectT G j (N := 1) (μ + 1) g6 w₀ / alphaF (μ + 1) g6 w₀) * alphaF (μ + 1) γ' t' := by
    intro γ' E' hE' t' ht'
    have h := alpha_cross G j h1 (μ + 1) (Nat.succ_ne_zero μ) hj hNj ht2 ht3 htj hjw hk hneg γ' g6 hE'
      g6_10 ht' hw₀
    field_simp
    linear_combination h
  set κ := defectT G j (N := 1) (μ + 1) g6 w₀ / alphaF (μ + 1) g6 w₀ with hκ
  have hκ0 : κ = 0 := by
    by_contra hne
    apply alpha_not_diff μ hμ
    have hmobd : DifferentiableAt ℂ (mob g6) w₀ := by
      have hne0 : 6 * w₀ + 1 ≠ 0 := by
        unfold w₀
        ring_nf
        simp
      have : mob g6 = fun w => w / (6 * w + 1) := funext mob_g6
      rw [this]
      exact differentiableAt_id.div (by fun_prop) hne0
    have hlind : DifferentiableAt ℂ (fun w => lin g6 w ^ (2 * (μ + 1))) w₀ := by
      have : lin g6 = fun w => 6 * w + 1 := funext lin_g6
      rw [this]
      fun_prop
    have hmob_pos : 0 < (mob g6 w₀).im := mob_im_pos g6 hw₀
    have hcomp : DifferentiableAt ℂ (fun w => lamSum G j (N := 1) (jN 1) (μ + 1) (mob g6 w).re
        (mob g6 w).im) w₀ := (hT _ hmob_pos).comp w₀ hmobd
    have hdef : DifferentiableAt ℂ (fun w => κ⁻¹ * defectT G j (N := 1) (μ + 1) g6 w) w₀ := by
      unfold defectT
      exact (hcomp.sub (hlind.mul (hT _ hw₀))).const_mul _
    refine hdef.congr_of_eventuallyEq ?_
    have hopen : {w : ℂ | 0 < w.im} ∈ 𝓝 w₀ :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hw₀
    filter_upwards [hopen] with w hw
    have := hcross g6 g6_10 hw
    rw [this]
    field_simp
  rw [hcross γ hE ht, hκ0, zero_mul]

end

end RamanujanTau.ThetaLift
