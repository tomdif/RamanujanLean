/-
# All `t`-derivatives of the AFE weight `V_t(ξ) = V(6+it, ξ)`

On a line `Re u = x` (`x ≥ −1`, `x ≠ 0`): `Vline x ξ t = ∫ R(t,y) K(y) dy` with
`K(y) = (2π)⁻¹ ξ^{−u} e^{u²}/u`.  Then

* `hasDerivAt_intRd`: `∂_t ∫ Rd_j K = ∫ Rd_{j+1} K` (dominated differentiation; `Rd_j = ∂_t^j R`);
* `iteratedDeriv_Vline`: `∂_t^j Vline = ∫ Rd_j K`;
* `norm_intRd_le`: `‖∫ Rd_j K‖ ≤ K_j (T(t)/ξ)^x / (1+|t|)^j`;
* **`V_iteratedDeriv_bound`**: for every `j ≥ 1` and `A ≥ 0`,
  `‖∂_t^j V(6+it, ξ)‖ ≤ C (1+|t|)^{−j} (1+ξ/(1+|t|))^{−A}`, uniformly in `t ∈ ℝ`, `ξ > 0`,
  and `∂_t^j V` is differentiable with derivative `∂_t^{j+1} V` (so `V` is `C^∞` in `t`).
-/
import RamanujanTau.HeckeAFE3.Leibniz

set_option autoImplicit false

namespace RamanujanTau.HeckeAFE3

open Complex MeasureTheory Set Metric Filter Topology RamanujanTau.HeckeAFE RamanujanTau.HeckeAFE2
  RamanujanTau.HeckeL
open scoped Real

/-- `K(y) = (2π)⁻¹ ξ^{−u} e^{u²}/u`, `u = x+iy`. -/
noncomputable def Kf (x ξ y : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ((ξ : ℂ) ^ (-((x : ℂ) + y * I)) * cexp (((x : ℂ) + y * I) ^ 2) / ((x : ℂ) + y * I))

lemma norm_two_pi_inv : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
  rw [norm_inv, show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

lemma norm_Kf_le {x ξ : ℝ} (hx0 : x ≠ 0) (hξ : 0 < ξ) (y : ℝ) :
    ‖Kf x ξ y‖ ≤ (2 * π)⁻¹ * (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹) * Real.exp (-1 * y ^ 2) := by
  unfold Kf
  rw [norm_mul, norm_two_pi_inv, mul_assoc]
  gcongr
  exact norm_K_le hx0 hξ y

lemma continuous_Kf {x ξ : ℝ} (hx0 : x ≠ 0) (hξ : 0 < ξ) : Continuous (Kf x ξ) :=
  continuous_const.mul (continuous_K hx0 hξ)

lemma continuous_Rf_y {x : ℝ} (hx : -1 ≤ x) (t : ℝ) : Continuous (fun y => Rf x t y) :=
  (continuous_Gamma_line (s := 6 + t * I) (c := x) (by simp; linarith)).div_const _

lemma continuous_elld_y {x : ℝ} (hx : -1 ≤ x) (i : ℕ) (t : ℝ) : Continuous (fun y => elld x i t y) := by
  unfold elld
  refine continuous_const.mul (Continuous.sub ?_ continuous_const)
  rw [continuous_iff_continuousAt]
  intro y
  exact ContinuousAt.comp (g := iteratedDeriv i digamma)
    (f := fun y : ℝ => (6 + t * I) + ((x : ℂ) + y * I))
    ((analyticOnNhd_iteratedDeriv_digamma i _ (line_mem_slit (by rw [re_u]; exact hx) t)).continuousAt)
    (Continuous.continuousAt (by fun_prop))

lemma continuous_Rd_y {x : ℝ} (hx : -1 ≤ x) (m : ℕ) (t : ℝ) : Continuous (fun y => Rd x m t y) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | m
    · simp only [Rd_zero]; exact continuous_Rf_y hx t
    · simp only [Rd_succ]
      refine continuous_finsetSum _ fun i _ => ?_
      exact (continuous_const.mul (continuous_elld_y hx i t)).mul (ih (m - i) (by omega))

lemma Rd_eq_iteratedDeriv {x : ℝ} (hx : -1 ≤ x) (j : ℕ) (y : ℝ) :
    (fun t => Rd x j t y) = iteratedDeriv j (fun t => Rf x t y) := by
  funext t; exact (iteratedDeriv_Rf hx y j t).symm

lemma hasDerivAt_Rd {x : ℝ} (hx : -1 ≤ x) (j : ℕ) (y t : ℝ) :
    HasDerivAt (fun t => Rd x j t y) (Rd x (j + 1) t y) t := by
  rw [Rd_eq_iteratedDeriv hx j y, ← iteratedDeriv_Rf hx y (j + 1) t, iteratedDeriv_succ]
  exact (((contDiff_Rf hx y (j + 1 : ℕ)).differentiable_iteratedDeriv' j) t).hasDerivAt

/-- Stirling lower bound on the line in the form needed for local domination. -/
lemma Gamma_line_lower (t : ℝ) :
    Real.sqrt π / 3 * Real.exp (-10) * Real.exp (-(π * |t|) / 2) ≤ ‖Gamma (6 + t * I)‖ := by
  have h := RamanujanTau.Stirling.stirling_le_norm_Gamma (σ := 6) (by norm_num) t
  have e2 : ((6 : ℝ) : ℂ) + (t : ℂ) * I = 6 + t * I := by push_cast; ring
  rw [e2] at h
  have hT := one_le_Tq t
  have hp : 1 ≤ Tq t ^ ((6 : ℝ) - 1 / 2) := Real.one_le_rpow hT (by norm_num)
  change Real.sqrt π / 3 * Real.exp (-10) * Tq t ^ ((6 : ℝ) - 1 / 2) *
    Real.exp (-(π * |t|) / 2) ≤ ‖Gamma (6 + t * I)‖ at h
  have ha : 0 ≤ Real.sqrt π / 3 * Real.exp (-10) := by positivity
  have he := Real.exp_pos (-(π * |t|) / 2)
  have : Real.sqrt π / 3 * Real.exp (-10) * 1 * Real.exp (-(π * |t|) / 2) ≤
      Real.sqrt π / 3 * Real.exp (-10) * Tq t ^ ((6 : ℝ) - 1 / 2) * Real.exp (-(π * |t|) / 2) := by
    gcongr
  rw [mul_one] at this
  linarith

/-- the norm of `R` is controlled by Gamma at the integer points (crude, local). -/
lemma norm_Rf_le_local {x : ℝ} (hx : -1 ≤ x) (t₀ : ℝ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ t ∈ ball t₀ 1, ∀ y : ℝ, ‖Rf x t y‖ ≤ G := by
  set a : ℝ := Real.sqrt π / 3 * Real.exp (-10) * Real.exp (-(π * (|t₀| + 1)) / 2)
  have ha : 0 < a := by have := Real.sqrt_pos.2 Real.pi_pos; positivity
  refine ⟨Real.Gamma (6 + x) / a, (div_pos (Real.Gamma_pos_of_pos (by linarith)) ha).le,
    fun t ht y => ?_⟩
  have htt : |t| ≤ |t₀| + 1 := by
    rw [mem_ball, Real.dist_eq] at ht
    have := abs_sub_abs_le_abs_sub t t₀; linarith
  have hlow : a ≤ ‖Gamma (6 + t * I)‖ := by
    refine le_trans ?_ (Gamma_line_lower t)
    have : Real.exp (-(π * (|t₀| + 1)) / 2) ≤ Real.exp (-(π * |t|) / 2) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    have hc : 0 ≤ Real.sqrt π / 3 * Real.exp (-10) := by positivity
    exact mul_le_mul_of_nonneg_left this hc
  unfold Rf
  rw [norm_div]
  exact div_le_div₀ (Real.Gamma_pos_of_pos (by linarith)).le (gamma_re_bound hx t y) ha hlow

lemma poly_gauss {N : ℕ} (y : ℝ) :
    (1 + |y|) ^ N * Real.exp (-1 * y ^ 2) ≤
      Real.exp (((N : ℝ) + π / 2) ^ 2 / 2) * Real.exp (-(1 / 2) * y ^ 2) := by
  have h := poly_exp_bound (q := (N : ℝ)) (by positivity) y
  rw [Real.rpow_natCast] at h
  have hpi : 1 ≤ Real.exp (π * |y| / 2) := Real.one_le_exp (by positivity)
  have h0 : 0 ≤ (1 + |y|) ^ N * Real.exp (-1 * y ^ 2) := by positivity
  calc (1 + |y|) ^ N * Real.exp (-1 * y ^ 2)
      ≤ (1 + |y|) ^ N * (Real.exp (π * |y| / 2) * Real.exp (-1 * y ^ 2)) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_pos _).le hpi) (by positivity)
    _ = (1 + |y|) ^ N * Real.exp (π * |y| / 2) * Real.exp (-1 * y ^ 2) := by ring
    _ ≤ _ := h

/-- local Gaussian domination of `Rd_j K`, uniformly for `t` near `t₀`. -/
lemma norm_RdK_le_local {x ξ : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (j : ℕ) (t₀ : ℝ) :
    ∃ M : ℝ, ∀ t ∈ ball t₀ 1, ∀ y : ℝ,
      ‖Rd x j t y * Kf x ξ y‖ ≤ M * Real.exp (-(1 / 2) * y ^ 2) := by
  obtain ⟨B, hB0, hB⟩ := norm_Rd_le hx j
  obtain ⟨G, hG0, hG⟩ := norm_Rf_le_local hx t₀
  set Q : ℝ := (2 * π)⁻¹ * (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹)
  have hQ : 0 ≤ Q := by positivity
  set E : ℝ := Real.exp (((3 * j : ℕ) + π / 2) ^ 2 / 2)
  refine ⟨B * G * Q * E, fun t ht y => ?_⟩
  rw [norm_mul]
  have h1 := hB t y
  have h2 := hG t ht y
  have h3 := norm_Kf_le hx0 hξ y
  have ht1 : 1 ≤ (1 + |t|) ^ j := one_le_pow₀ (one_le_one_add_abs t)
  have hpg := poly_gauss (N := 3 * j) y
  have hRd : ‖Rd x j t y‖ ≤ B * (1 + |y|) ^ (3 * j) * G := by
    refine h1.trans ?_
    calc B * (1 + |y|) ^ (3 * j) / (1 + |t|) ^ j * ‖Rf x t y‖
        ≤ B * (1 + |y|) ^ (3 * j) / 1 * G := by gcongr
      _ = _ := by ring
  calc ‖Rd x j t y‖ * ‖Kf x ξ y‖ ≤ (B * (1 + |y|) ^ (3 * j) * G) * (Q * Real.exp (-1 * y ^ 2)) :=
        mul_le_mul hRd (by simpa [Q, mul_assoc] using h3) (norm_nonneg _) (by positivity)
    _ = B * G * Q * ((1 + |y|) ^ (3 * j) * Real.exp (-1 * y ^ 2)) := by ring
    _ ≤ B * G * Q * (E * Real.exp (-(1 / 2) * y ^ 2)) := by gcongr
    _ = _ := by ring

lemma integrable_RdK {x ξ : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (j : ℕ) (t : ℝ) :
    Integrable (fun y => Rd x j t y * Kf x ξ y) := by
  obtain ⟨M, hM⟩ := norm_RdK_le_local hx hx0 hξ j t
  exact Integrable.mono' ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul M)
    ((continuous_Rd_y hx j t).mul (continuous_Kf hx0 hξ)).aestronglyMeasurable
    (Eventually.of_forall fun y => hM t (mem_ball_self one_pos) y)

theorem hasDerivAt_intRd {x ξ : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (j : ℕ) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ y : ℝ, Rd x j t y * Kf x ξ y)
      (∫ y : ℝ, Rd x (j + 1) t₀ y * Kf x ξ y) t₀ := by
  obtain ⟨M, hM⟩ := norm_RdK_le_local hx hx0 hξ (j + 1) t₀
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t₀)
    (F := fun t y => Rd x j t y * Kf x ξ y) (F' := fun t y => Rd x (j + 1) t y * Kf x ξ y)
    (bound := fun y => M * Real.exp (-(1 / 2) * y ^ 2)) (ball_mem_nhds t₀ one_pos)
    (Eventually.of_forall fun t =>
      ((continuous_Rd_y hx j t).mul (continuous_Kf hx0 hξ)).aestronglyMeasurable)
    (integrable_RdK hx hx0 hξ j t₀)
    ((continuous_Rd_y hx (j + 1) t₀).mul (continuous_Kf hx0 hξ)).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => hM t ht y)
    ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul M)
    (Eventually.of_forall fun y t _ => (hasDerivAt_Rd hx j y t).mul_const (Kf x ξ y))
  exact h.2

lemma Vline_eq_int (x ξ : ℝ) : Vline x ξ = fun t => ∫ y : ℝ, Rd x 0 t y * Kf x ξ y := by
  funext t
  unfold Vline
  simp only [Rd_zero]
  rw [mul_div_assoc, ← integral_div, ← integral_const_mul]
  congr 1; funext y
  rw [Fi_eq]; unfold Rf Kf; ring

theorem iteratedDeriv_Vline {x ξ : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (j : ℕ) :
    iteratedDeriv j (Vline x ξ) = fun t => ∫ y : ℝ, Rd x j t y * Kf x ξ y := by
  induction j with
  | zero => rw [iteratedDeriv_zero, Vline_eq_int]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext t; exact (hasDerivAt_intRd hx hx0 hξ j t).deriv

theorem norm_intRd_le {x : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ξ : ℝ, 0 < ξ →
      ‖∫ y : ℝ, Rd x j t y * Kf x ξ y‖ ≤ K * (Tq t / ξ) ^ x / (1 + |t|) ^ j := by
  obtain ⟨B, hB0, hB⟩ := norm_Rd_le hx j
  obtain ⟨C, hC0, hC⟩ := norm_Gamma_ratio_line (x := x) (by linarith)
  have hp0 : 0 ≤ 11 / 2 + x + 3 * j := by
    have := (Nat.cast_nonneg j : (0:ℝ) ≤ j); linarith
  set E : ℝ := Real.exp ((11 / 2 + x + 3 * j + π / 2) ^ 2 / 2)
  set J : ℝ := ∫ y : ℝ, Real.exp (-(1 / 2) * y ^ 2)
  have hJ : 0 ≤ J := integral_nonneg fun _ => (Real.exp_pos _).le
  set K : ℝ := B * C * E * ((2 * π)⁻¹ * (Real.exp (x ^ 2) * |x|⁻¹)) * J
  refine ⟨K, by positivity, fun t ξ hξ => ?_⟩
  have ht1 : 0 < (1 + |t|) ^ j := by positivity
  set P : ℝ := B / (1 + |t|) ^ j * C * Tq t ^ x * ((2 * π)⁻¹ * (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹)) * E
  have hTx : 0 ≤ Tq t ^ x := (Real.rpow_pos_of_pos (Tq_pos t) _).le
  have hGp : 0 < ‖Gamma (6 + t * I)‖ := norm_pos_iff.2 (Gamma_line_ne t)
  have hpt : ∀ y : ℝ, ‖Rd x j t y * Kf x ξ y‖ ≤ P * Real.exp (-(1 / 2) * y ^ 2) := by
    intro y
    rw [norm_mul]
    have hy1 : 0 < 1 + |y| := by positivity
    have hR : ‖Rf x t y‖ ≤ C * Tq t ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) := by
      unfold Rf; rw [norm_div, div_le_iff₀ hGp]; exact hC t y
    have h1 := hB t y
    have h3 := norm_Kf_le hx0 hξ y
    have hpe := poly_exp_bound hp0 y
    have hpow : (1 + |y|) ^ (3 * j) * (1 + |y|) ^ (11 / 2 + x) = (1 + |y|) ^ (11 / 2 + x + 3 * j) := by
      rw [show (11 / 2 + x + 3 * j : ℝ) = ((3 * j : ℕ) : ℝ) + (11 / 2 + x) by push_cast; ring,
        Real.rpow_add hy1 ((3 * j : ℕ) : ℝ) (11 / 2 + x), Real.rpow_natCast]
    calc ‖Rd x j t y‖ * ‖Kf x ξ y‖
        ≤ (B * (1 + |y|) ^ (3 * j) / (1 + |t|) ^ j *
            (C * Tq t ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)))) *
          ((2 * π)⁻¹ * (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹) * Real.exp (-1 * y ^ 2)) := by
          refine mul_le_mul (h1.trans ?_) h3 (norm_nonneg _) (by positivity)
          gcongr
      _ = B / (1 + |t|) ^ j * C * Tq t ^ x * ((2 * π)⁻¹ * (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹)) *
          (((1 + |y|) ^ (3 * j) * (1 + |y|) ^ (11 / 2 + x)) * Real.exp (π * |y| / 2) *
            Real.exp (-1 * y ^ 2)) := by ring
      _ ≤ B / (1 + |t|) ^ j * C * Tq t ^ x * ((2 * π)⁻¹ * (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹)) *
          (E * Real.exp (-(1 / 2) * y ^ 2)) := by rw [hpow]; gcongr
      _ = _ := by ring
  have hint := (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul P
  have hI := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
  rw [integral_const_mul, show (∫ a : ℝ, Real.exp (-(1 / 2) * a ^ 2)) = J from rfl] at hI
  refine hI.trans (le_of_eq ?_)
  have hdiv : (Tq t / ξ) ^ x = Tq t ^ x * ξ ^ (-x) := by
    rw [Real.div_rpow (Tq_pos t).le hξ.le, Real.rpow_neg hξ.le, div_eq_mul_inv]
  rw [hdiv]
  simp only [P, K]
  field_simp

/-- **All `t`-derivatives of the AFE weight**: for `j ≥ 1` and `A ≥ 0` there is `C` with
`‖∂_t^j V(6+it, ξ)‖ ≤ C (1+|t|)^{−j} (1 + ξ/(1+|t|))^{−A}` for all `t ∈ ℝ`, `ξ > 0`; moreover
`∂_t^j V` has derivative `∂_t^{j+1} V` everywhere (`V` is smooth in `t`). -/
theorem V_iteratedDeriv_bound {j : ℕ} (hj : 1 ≤ j) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, 0 < ξ →
      HasDerivAt (iteratedDeriv j (fun w : ℝ => V (6 + w * I) ξ))
        (iteratedDeriv (j + 1) (fun w : ℝ => V (6 + w * I) ξ) t) t ∧
      ‖iteratedDeriv j (fun w : ℝ => V (6 + w * I) ξ) t‖ ≤
        C / (1 + |t|) ^ j * (1 + ξ / (1 + |t|)) ^ (-A) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := norm_intRd_le (x := A + 1) (by linarith) (ne_of_gt (by linarith)) j
  obtain ⟨K₂, hK₂0, hK₂⟩ := norm_intRd_le (x := -1) le_rfl (by norm_num) j
  refine ⟨max (2 * K₂ * 2 ^ A) (K₁ * (3 / 2) ^ (A + 1) * 2 ^ A), by positivity,
    fun t ξ hξ => ?_⟩
  have hx1 : (0:ℝ) < A + 1 := by linarith
  have e1 : ∀ k : ℕ, iteratedDeriv k (fun w : ℝ => V (6 + w * I) ξ) =
      fun t => ∫ y : ℝ, Rd (A + 1) k t y * Kf (A + 1) ξ y := by
    intro k
    rw [V_eq_Vline_pos (x := A + 1) hx1 hξ, iteratedDeriv_Vline (by linarith) hx1.ne' hξ]
  have e2 : iteratedDeriv j (fun w : ℝ => V (6 + w * I) ξ) t =
      ∫ y : ℝ, Rd (-1) j t y * Kf (-1) ξ y := by
    rw [V_eq_one_add_Vline hξ, iteratedDeriv_const_add (by omega),
      iteratedDeriv_Vline le_rfl (by norm_num) hξ]
  refine ⟨?_, ?_⟩
  · rw [e1 j, e1 (j + 1)]
    exact hasDerivAt_intRd (by linarith) hx1.ne' hξ j t
  have h1t : 0 < 1 + |t| := by positivity
  have hpj : 0 < (1 + |t|) ^ j := by positivity
  set f : ℝ := ‖iteratedDeriv j (fun w : ℝ => V (6 + w * I) ξ) t‖ * (1 + |t|) ^ j
  have hf1 : f ≤ K₁ * (Tq t / ξ) ^ (A + 1) := by
    simp only [f]; rw [e1 j, ← le_div_iff₀ hpj]; exact hK₁ t ξ hξ
  have hf2 : f ≤ K₂ * (Tq t / ξ) ^ (-1 : ℝ) := by
    simp only [f]; rw [e2, ← le_div_iff₀ hpj]; exact hK₂ t ξ hξ
  have hc := combine_bound (w := 1 + |t|) hA hK₁0 hK₂0 h1t hξ (Tq_ge t) (Tq_le t) hf1 hf2
  rw [div_mul_eq_mul_div, le_div_iff₀ hpj]
  linarith

end RamanujanTau.HeckeAFE3
