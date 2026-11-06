/-
# Uniform bounds for the AFE weight `V_t(ξ) = V(6+it, ξ)`

Write `T(t) = ‖3/2 + it‖` (so `(1+|t|)/2 ≤ T(t) ≤ (3/2)(1+|t|)`).

* `WGam_shift`: the weight integral does not depend on the line `Re u = c > 0`;
* `WGam_residue`: crossing `u = 0` picks up `Γ(s)`: `W_s(ξ)|_{c} − W_s(ξ)|_{−c'} = Γ(s)`;
* `norm_Gamma_ratio_line`: from the two-sided Stirling bounds of `Stirling.Absolute`,
  `|Γ(6+it+x+iy)| ≤ C_x T(t)^x (1+|y|)^{11/2+x} e^{π|y|/2} |Γ(6+it)|` for `x ≥ −9/2`,
  uniformly in `t, y`;
* **`V_decay`**: `|V(6+it, ξ)| ≤ C_A ((1+|t|)/ξ)^A` for every `A > 0`;
* **`V_sub_one`**: `|V(6+it, ξ) − 1| ≤ C_c (ξ/(1+|t|))^c` for `0 < c ≤ 9/2`;
* **`V_bound`**: `|V(6+it, ξ)| ≤ C_A (1 + ξ/(1+|t|))^{−A}` for every `A ≥ 0`.
All constants are independent of `t ∈ ℝ` and `ξ > 0`.
-/
import RamanujanTau.HeckeAFE.Exact
import RamanujanTau.Stirling.Absolute

set_option autoImplicit false

namespace RamanujanTau.HeckeAFE

open Complex MeasureTheory Set Filter Topology RamanujanTau.HeckeL
open scoped Real

/-! ## Shifting the weight integral -/

lemma gamma_bdd_strip {s : ℂ} {a b : ℝ} (_hab : a ≤ b) (h : 0 < s.re + a) :
    ∃ M : ℝ, ∀ u ∈ strip a b, ‖Gamma (s + u)‖ ≤ M := by
  have hcont : ContinuousOn Real.Gamma (Icc (s.re + a) (s.re + b)) := by
    intro x hx
    refine (Real.differentiableAt_Gamma (fun m hm => ?_)).continuousAt.continuousWithinAt
    have := hx.1; rw [hm] at this; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  obtain ⟨M, hM⟩ := (isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨M, fun u hu => ?_⟩
  have hw : 0 < (s + u).re := by simp; linarith [hu.1]
  refine (RamanujanTau.RankinError.norm_Gamma_le_Gamma_re hw).trans ?_
  have := hM (s + u).re ⟨by simp; linarith [hu.1], by simp; linarith [hu.2]⟩
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)

lemma differentiableOn_Gamma_add {s : ℂ} {a b : ℝ} (h : 0 < s.re + a) :
    DifferentiableOn ℂ (fun u => Gamma (s + u)) (strip a b) := by
  intro u hu
  have hw : 0 < (s + u).re := by simp; linarith [hu.1]
  exact ((differentiableAt_Gamma _ (ne_neg_nat_of_re_pos hw)).comp u
    ((differentiable_const s).add differentiable_id).differentiableAt).differentiableWithinAt

lemma differentiableOn_W_integrand {s : ℂ} {ξ a b : ℝ} (hξ : 0 < ξ) (h : 0 < s.re + a)
    (h0 : (0:ℂ) ∉ strip a b) :
    DifferentiableOn ℂ (fun u => Gamma (s + u) * (ξ : ℂ) ^ (-u) * cexp (u ^ 2) / u)
      (strip a b) := by
  have hξ0 : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  refine DifferentiableOn.div ?_ differentiableOn_id (fun u hu h' => h0 (h' ▸ hu))
  refine ((differentiableOn_Gamma_add h).mul ?_).mul ?_
  · exact (differentiable_neg.const_cpow (Or.inl hξ0)).differentiableOn
  · exact (Complex.differentiable_exp.comp (differentiable_pow 2)).differentiableOn

/-- the weight integral is independent of the line `Re u = c > 0`. -/
theorem WGam_shift {s : ℂ} {ξ c₁ c₂ : ℝ} (hξ : 0 < ξ) (hc₁ : 0 < c₁) (h12 : c₁ ≤ c₂)
    (hs : 0 < s.re + c₁) : WGam s ξ c₁ = WGam s ξ c₂ := by
  unfold WGam
  congr 1
  obtain ⟨M, hM⟩ := gamma_bdd_strip h12 hs
  refine vline_shift h12 (differentiableOn_W_integrand hξ hs ?_) ?_
  · intro h; have := h.1; simp at this; linarith
  · refine ⟨M * (ξ ^ (-c₂) + ξ ^ (-c₁)) * Real.exp (c₂ ^ 2) * c₁⁻¹, fun x y hx1 hx2 => ?_⟩
    have hmem := mem_strip_line hx1 hx2 y
    have hG := hM _ hmem
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hG
    show ‖Gamma (s + ((x : ℂ) + y * I)) * (ξ : ℂ) ^ (-((x : ℂ) + y * I)) *
      cexp (((x : ℂ) + y * I) ^ 2) / ((x : ℂ) + y * I)‖ ≤
      M * (ξ ^ (-c₂) + ξ ^ (-c₁)) * Real.exp (c₂ ^ 2) * c₁⁻¹ * Real.exp (-(1 / 2) * y ^ 2)
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_ofReal_cpow hξ, norm_cexp_sq]
    have hr : (-((x : ℂ) + y * I)).re = -x := by simp
    rw [hr]
    have h1 := rpow_le_add_of_mem hξ (neg_le_neg hx2) (neg_le_neg hx1)
    have h2 : Real.exp (x ^ 2 - y ^ 2) ≤ Real.exp (c₂ ^ 2) * Real.exp (-(1 / 2) * y ^ 2) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith [sq_nonneg y]
    have h3 : ‖((x : ℂ) + y * I)⁻¹‖ ≤ c₁⁻¹ :=
      (norm_inv_line_le (by linarith) y).trans (inv_anti₀ hc₁ hx1)
    calc ‖Gamma (s + (↑x + ↑y * I))‖ * ξ ^ (-x) * Real.exp (x ^ 2 - y ^ 2) *
          ‖((x : ℂ) + y * I)⁻¹‖
        ≤ M * (ξ ^ (-c₂) + ξ ^ (-c₁)) * (Real.exp (c₂ ^ 2) * Real.exp (-(1 / 2) * y ^ 2)) *
          c₁⁻¹ := by gcongr
      _ = _ := by ring

/-- **Crossing the pole**: `W_s(ξ)|_{Re u = c} − W_s(ξ)|_{Re u = −c'} = Γ(s)` for
`0 < c' < Re s`, `c > 0`. -/
theorem WGam_residue {s : ℂ} {ξ c c' : ℝ} (hξ : 0 < ξ) (hc : 0 < c) (hc' : 0 < c')
    (hs : c' < s.re) : WGam s ξ c - WGam s ξ (-c') = Gamma s := by
  have hξ0 : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  have h0 : 0 < s.re + -c' := by linarith
  obtain ⟨M, hM⟩ := gamma_bdd_strip (by linarith : -c' ≤ c) h0
  have hF : DifferentiableOn ℂ (fun u => Gamma (s + u) * (ξ : ℂ) ^ (-u)) (strip (-c') c) :=
    (differentiableOn_Gamma_add h0).mul
      (differentiable_neg.const_cpow (Or.inl hξ0)).differentiableOn
  have hFb : ∃ M', ∀ u ∈ strip (-c') c, ‖Gamma (s + u) * (ξ : ℂ) ^ (-u)‖ ≤ M' := by
    refine ⟨M * (ξ ^ (-c) + ξ ^ c'), fun u hu => ?_⟩
    rw [norm_mul, norm_ofReal_cpow hξ]
    have hG := hM u hu
    have h1 := rpow_le_add_of_mem hξ (a := -c) (b := c') (x := (-u).re)
      (by simp; linarith [hu.2]) (by simp; linarith [hu.1])
    exact mul_le_mul hG h1 (by positivity) (le_trans (norm_nonneg _) hG)
  have hres := vline_residue (by linarith : -c' < 0) hc hF hFb
  unfold WGam
  rw [← mul_sub]
  have e : (fun u => Gamma (s + u) * (ξ : ℂ) ^ (-u) * cexp (u ^ 2) / u) =
      (fun u => (Gamma (s + u) * (ξ : ℂ) ^ (-u)) * cexp (u ^ 2) / u) := rfl
  rw [e, hres]
  simp only [add_zero, neg_zero, cpow_zero, mul_one]
  field_simp [two_pi_ne_zero]

/-! ## Stirling: the Gamma ratio on vertical lines -/

/-- `T(t) = ‖3/2 + it‖ ≍ 1 + |t|`. -/
noncomputable def Tq (t : ℝ) : ℝ := ‖(3 / 2 : ℂ) + t * I‖

lemma one_le_Tq (t : ℝ) : 1 ≤ Tq t :=
  RamanujanTau.Stirling.one_le_norm_of_re (by simp; norm_num)

lemma Tq_pos (t : ℝ) : 0 < Tq t := lt_of_lt_of_le one_pos (one_le_Tq t)

lemma Tq_add_le (t y : ℝ) : Tq (t + y) ≤ Tq t * (1 + |y|) := by
  unfold Tq
  have e : (3 / 2 : ℂ) + ((t + y : ℝ) : ℂ) * I = ((3 / 2 : ℂ) + t * I) + (y : ℂ) * I := by
    push_cast; ring
  rw [e]
  have h1 := norm_add_le ((3 / 2 : ℂ) + t * I) ((y : ℂ) * I)
  have h2 : ‖(y : ℂ) * I‖ = |y| := by simp
  have h3 := one_le_Tq t
  unfold Tq at h3
  rw [h2] at h1
  nlinarith [abs_nonneg y]

lemma Tq_le (t : ℝ) : Tq t ≤ 3 / 2 * (1 + |t|) := by
  unfold Tq
  have h1 := norm_add_le (3 / 2 : ℂ) ((t : ℂ) * I)
  have h2 : ‖(t : ℂ) * I‖ = |t| := by simp
  have h3 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
    rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
    norm_num
  rw [h2, h3] at h1
  nlinarith [abs_nonneg t]

lemma Tq_ge (t : ℝ) : (1 + |t|) / 2 ≤ Tq t := by
  unfold Tq
  have h1 := Complex.abs_re_le_norm ((3 / 2 : ℂ) + t * I)
  have h2 := Complex.abs_im_le_norm ((3 / 2 : ℂ) + t * I)
  simp at h1 h2
  rw [abs_of_pos (by norm_num : (0:ℝ) < 3 / 2)] at h1
  linarith

/-- **Gamma ratio on vertical lines** (uniform in `t, y`): for `x ≥ −9/2`,
`|Γ(6+it + x+iy)| ≤ C T(t)^x (1+|y|)^{11/2+x} e^{π|y|/2} |Γ(6+it)|`. -/
theorem norm_Gamma_ratio_line {x : ℝ} (hx : -9 / 2 ≤ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, ‖Gamma ((6 + t * I) + ((x : ℂ) + y * I))‖ ≤
      C * Tq t ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) *
        ‖Gamma (6 + t * I)‖ := by
  set n : ℕ := ⌈x + 9 / 2⌉₊
  have hn : (6 + x) - 3 / 2 ≤ n + 1 := by have := Nat.le_ceil (x + 9 / 2); linarith
  set A : ℝ := ((n + 1).factorial : ℝ) * Real.exp 10 * Real.sqrt (2 * π) with hA
  set a : ℝ := Real.sqrt π / 3 * Real.exp (-10) with ha
  have ha0 : 0 < a := by
    have := Real.sqrt_pos.2 Real.pi_pos; positivity
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A / a, by positivity, fun t y => ?_⟩
  have hup := RamanujanTau.Stirling.norm_Gamma_le_stirling (σ := 6 + x) (by linarith) n hn (t + y)
  have hlow := RamanujanTau.Stirling.stirling_le_norm_Gamma (σ := 6) (by norm_num) t
  have e1 : (6 + t * I) + ((x : ℂ) + y * I) = ((6 + x : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I := by
    push_cast; ring
  have e2 : ((6 : ℝ) : ℂ) + (t : ℂ) * I = 6 + t * I := by push_cast; ring
  rw [e1]; rw [e2] at hlow
  change ‖Gamma (((6 + x : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I)‖ ≤
    A * Tq (t + y) ^ (6 + x - 1 / 2) * Real.exp (-(π * |t + y|) / 2) at hup
  change a * Tq t ^ ((6 : ℝ) - 1 / 2) * Real.exp (-(π * |t|) / 2) ≤ ‖Gamma (6 + t * I)‖ at hlow
  have hp : (6 + x - 1 / 2 : ℝ) = 11 / 2 + x := by ring
  rw [hp] at hup
  have hp0 : 0 ≤ 11 / 2 + x := by linarith
  set T := Tq t with hTdef
  have hT0 : 0 < T := Tq_pos t
  have h1 : Tq (t + y) ^ (11 / 2 + x) ≤ T ^ x * T ^ ((6 : ℝ) - 1 / 2) * (1 + |y|) ^ (11 / 2 + x) := by
    calc Tq (t + y) ^ (11 / 2 + x) ≤ (T * (1 + |y|)) ^ (11 / 2 + x) :=
          Real.rpow_le_rpow (Tq_pos _).le (Tq_add_le t y) hp0
      _ = T ^ (11 / 2 + x) * (1 + |y|) ^ (11 / 2 + x) :=
          Real.mul_rpow hT0.le (by positivity)
      _ = _ := by
          rw [← Real.rpow_add hT0, show x + ((6:ℝ) - 1 / 2) = 11 / 2 + x by ring]
  have h2 : Real.exp (-(π * |t + y|) / 2) ≤ Real.exp (-(π * |t|) / 2) * Real.exp (π * |y| / 2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    have : |t| ≤ |t + y| + |y| := by
      have := abs_sub_le t (t + y) 0
      simp at this
      calc |t| = |(t + y) - y| := by ring_nf
        _ ≤ |t + y| + |y| := abs_sub _ _
    nlinarith [Real.pi_pos]
  have h3 : T ^ ((6 : ℝ) - 1 / 2) * Real.exp (-(π * |t|) / 2) ≤ ‖Gamma (6 + t * I)‖ / a := by
    rw [le_div_iff₀ ha0]; linarith
  calc ‖Gamma (((6 + x : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I)‖
      ≤ A * Tq (t + y) ^ (11 / 2 + x) * Real.exp (-(π * |t + y|) / 2) := hup
    _ ≤ A * (T ^ x * T ^ ((6 : ℝ) - 1 / 2) * (1 + |y|) ^ (11 / 2 + x)) *
          (Real.exp (-(π * |t|) / 2) * Real.exp (π * |y| / 2)) := by gcongr
    _ = A * T ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) *
          (T ^ ((6 : ℝ) - 1 / 2) * Real.exp (-(π * |t|) / 2)) := by ring
    _ ≤ A * T ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) *
          (‖Gamma (6 + t * I)‖ / a) := by gcongr
    _ = _ := by ring

lemma poly_exp_bound {q : ℝ} (hq : 0 ≤ q) (y : ℝ) :
    (1 + |y|) ^ q * Real.exp (π * |y| / 2) * Real.exp (-1 * y ^ 2) ≤
      Real.exp ((q + π / 2) ^ 2 / 2) * Real.exp (-(1 / 2) * y ^ 2) := by
  have h1 : (1 + |y|) ^ q ≤ Real.exp (q * |y|) := by
    rw [mul_comm, Real.exp_mul]
    exact Real.rpow_le_rpow (by positivity) (by linarith [Real.add_one_le_exp |y|]) hq
  calc (1 + |y|) ^ q * Real.exp (π * |y| / 2) * Real.exp (-1 * y ^ 2)
      ≤ Real.exp (q * |y|) * Real.exp (π * |y| / 2) * Real.exp (-1 * y ^ 2) := by gcongr
    _ = Real.exp ((q + π / 2) * |y| - y ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp ((q + π / 2) ^ 2 / 2 + -(1 / 2) * y ^ 2) := by
        apply Real.exp_le_exp.2
        nlinarith [sq_nonneg (|y| - (q + π / 2)), sq_abs y]
    _ = _ := by rw [Real.exp_add]

/-- **Bound on a single line** `Re u = x` (`x ≥ −9/2`, `x ≠ 0`), uniform in `t` and `ξ`. -/
theorem W_line_bound {x : ℝ} (hx : -9 / 2 ≤ x) (hx0 : x ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ξ : ℝ, 0 < ξ →
      ‖WGam (6 + t * I) ξ x‖ ≤ K * (Tq t / ξ) ^ x * ‖Gamma (6 + t * I)‖ := by
  obtain ⟨C, hC0, hC⟩ := norm_Gamma_ratio_line hx
  have hp0 : 0 ≤ 11 / 2 + x := by linarith
  set E : ℝ := Real.exp ((11 / 2 + x + π / 2) ^ 2 / 2)
  set J : ℝ := ∫ y : ℝ, Real.exp (-(1 / 2) * y ^ 2)
  have hJ : 0 ≤ J := integral_nonneg fun _ => (Real.exp_pos _).le
  have hx' : 0 < |x| := abs_pos.2 hx0
  set K : ℝ := (2 * π)⁻¹ * (C * E * Real.exp (x ^ 2) * |x|⁻¹ * J)
  refine ⟨K, by positivity, fun t ξ hξ => ?_⟩
  set G : ℝ := ‖Gamma (6 + t * I)‖
  have hG0 : 0 ≤ G := norm_nonneg _
  set B : ℝ := C * Tq t ^ x * G * ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹ * E
  have hB : ∀ y : ℝ, ‖Gamma ((6 + t * I) + ((x : ℂ) + y * I)) * (ξ : ℂ) ^ (-((x : ℂ) + y * I)) *
      cexp (((x : ℂ) + y * I) ^ 2) / ((x : ℂ) + y * I)‖ ≤ B * Real.exp (-(1 / 2) * y ^ 2) := by
    intro y
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_ofReal_cpow hξ, norm_cexp_sq]
    have hr : (-((x : ℂ) + y * I)).re = -x := by simp
    rw [hr]
    have hi : ‖((x : ℂ) + y * I)⁻¹‖ ≤ |x|⁻¹ := by
      rw [norm_inv]; exact inv_anti₀ hx' (norm_line_ge y)
    have he : Real.exp (x ^ 2 - y ^ 2) = Real.exp (x ^ 2) * Real.exp (-1 * y ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [he]
    have hpe := poly_exp_bound hp0 y
    have hTx : 0 ≤ Tq t ^ x := (Real.rpow_pos_of_pos (Tq_pos t) _).le
    have hξx : 0 ≤ ξ ^ (-x) := (Real.rpow_pos_of_pos hξ _).le
    calc ‖Gamma (6 + ↑t * I + (↑x + ↑y * I))‖ * ξ ^ (-x) *
          (Real.exp (x ^ 2) * Real.exp (-1 * y ^ 2)) * ‖((x : ℂ) + y * I)⁻¹‖
        ≤ (C * Tq t ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) * G) * ξ ^ (-x) *
          (Real.exp (x ^ 2) * Real.exp (-1 * y ^ 2)) * |x|⁻¹ := by
          gcongr
          exact hC t y
      _ = C * Tq t ^ x * G * ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹ *
          ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2) * Real.exp (-1 * y ^ 2)) := by ring
      _ ≤ C * Tq t ^ x * G * ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹ *
          (E * Real.exp (-(1 / 2) * y ^ 2)) := by gcongr
      _ = _ := by ring
  have hint := (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul B
  have hI := norm_integral_le_of_norm_le hint (Eventually.of_forall hB)
  rw [integral_const_mul] at hI
  unfold WGam vline
  rw [norm_mul]
  have h2pi : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [h2pi]
  have hdiv : (Tq t / ξ) ^ x = Tq t ^ x * ξ ^ (-x) := by
    rw [Real.div_rpow (Tq_pos t).le hξ.le, Real.rpow_neg hξ.le, div_eq_mul_inv]
  rw [hdiv]
  calc (2 * π)⁻¹ * ‖∫ y : ℝ, Gamma (6 + ↑t * I + (↑x + ↑y * I)) * (ξ : ℂ) ^ (-(↑x + ↑y * I)) *
        cexp ((↑x + ↑y * I) ^ 2) / (↑x + ↑y * I)‖
      ≤ (2 * π)⁻¹ * (B * J) := by gcongr
    _ = _ := by simp only [B, K]; ring

/-! ## The headline bounds for `V(6+it, ξ)` -/

lemma Gamma_line_ne_zero (t : ℝ) : Gamma (6 + t * I) ≠ 0 :=
  Gamma_ne_zero_of_re_pos (by simp)

/-- **Rapid decay of the weight**: `|V(6+it, ξ)| ≤ C_A ((1+|t|)/ξ)^A`, uniformly. -/
theorem V_decay {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, 0 < ξ → ‖V (6 + t * I) ξ‖ ≤ C * ((1 + |t|) / ξ) ^ A := by
  obtain ⟨K, hK0, hK⟩ := W_line_bound (x := A) (by linarith) hA.ne'
  refine ⟨K * (3 / 2) ^ A, by positivity, fun t ξ hξ => ?_⟩
  have hsre : (6 + t * I).re = 6 := by simp
  have hW : WGam (6 + t * I) ξ 2 = WGam (6 + t * I) ξ A := by
    rcases le_total A 2 with h | h
    · exact (WGam_shift hξ hA h (by rw [hsre]; linarith)).symm
    · exact WGam_shift hξ (by norm_num) h (by rw [hsre]; norm_num)
  have hG := Gamma_line_ne_zero t
  have hGp : 0 < ‖Gamma (6 + t * I)‖ := norm_pos_iff.2 hG
  unfold V
  rw [hW, norm_div, div_le_iff₀ hGp]
  refine (hK t ξ hξ).trans ?_
  have h1 : (Tq t / ξ) ^ A ≤ (3 / 2) ^ A * ((1 + |t|) / ξ) ^ A := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    apply Real.rpow_le_rpow (by have := Tq_pos t; positivity) _ hA.le
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (Tq_le t) hξ.le
  calc K * (Tq t / ξ) ^ A * ‖Gamma (6 + t * I)‖
      ≤ K * ((3 / 2) ^ A * ((1 + |t|) / ξ) ^ A) * ‖Gamma (6 + t * I)‖ := by gcongr
    _ = _ := by ring

/-- **The weight is `1 + O(ξ/|t|)` near the origin**: for `0 < c ≤ 9/2`,
`|V(6+it, ξ) − 1| ≤ C_c (ξ/(1+|t|))^c`, uniformly. -/
theorem V_sub_one {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 9 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, 0 < ξ →
      ‖V (6 + t * I) ξ - 1‖ ≤ C * (ξ / (1 + |t|)) ^ c := by
  obtain ⟨K, hK0, hK⟩ := W_line_bound (x := -c) (by linarith) (by linarith)
  refine ⟨K * 2 ^ c, by positivity, fun t ξ hξ => ?_⟩
  have hsre : (6 + t * I).re = 6 := by simp
  have hres := WGam_residue (s := 6 + t * I) hξ (by norm_num : (0:ℝ) < 2) hc0
    (by rw [hsre]; linarith)
  have hG := Gamma_line_ne_zero t
  have hGp : 0 < ‖Gamma (6 + t * I)‖ := norm_pos_iff.2 hG
  have hV : V (6 + t * I) ξ - 1 = WGam (6 + t * I) ξ (-c) / Gamma (6 + t * I) := by
    unfold V
    rw [eq_div_iff hG, sub_mul, div_mul_cancel₀ _ hG, one_mul]
    linear_combination hres
  rw [hV, norm_div, div_le_iff₀ hGp]
  refine (hK t ξ hξ).trans ?_
  have hT := Tq_pos t
  have h1 : (Tq t / ξ) ^ (-c) ≤ 2 ^ c * (ξ / (1 + |t|)) ^ c := by
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div,
      ← Real.mul_rpow (by norm_num) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ hc0.le
    rw [div_le_iff₀ hT]
    have := Tq_ge t
    have h1t : 0 < 1 + |t| := by positivity
    rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ h1t]
    nlinarith
  calc K * (Tq t / ξ) ^ (-c) * ‖Gamma (6 + t * I)‖
      ≤ K * (2 ^ c * (ξ / (1 + |t|)) ^ c) * ‖Gamma (6 + t * I)‖ := by gcongr
    _ = _ := by ring

/-- **The AFE weight bound**: for every `A ≥ 0`,
`|V(6+it, ξ)| ≤ C_A (1 + ξ/(1+|t|))^{−A}`, uniformly in `t ∈ ℝ`, `ξ > 0`. -/
theorem V_bound {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, 0 < ξ →
      ‖V (6 + t * I) ξ‖ ≤ C * (1 + ξ / (1 + |t|)) ^ (-A) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := V_sub_one (c := 1) one_pos (by norm_num)
  obtain ⟨C₂, hC₂0, hC₂⟩ := V_decay (A := A + 1) (by linarith)
  refine ⟨max ((1 + C₁) * 2 ^ A) (C₂ * 2 ^ A), by positivity, fun t ξ hξ => ?_⟩
  set r : ℝ := ξ / (1 + |t|) with hr
  have h1t : 0 < 1 + |t| := by positivity
  have hr0 : 0 < r := by positivity
  have h2A : (2:ℝ) ^ A * (2:ℝ) ^ (-A) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  rcases le_total r 1 with hr1 | hr1
  · -- near the origin
    have hV : ‖V (6 + t * I) ξ‖ ≤ 1 + C₁ := by
      have h := hC₁ t ξ hξ
      rw [← hr, Real.rpow_one] at h
      have := norm_le_norm_add_norm_sub' (V (6 + t * I) ξ) 1
      rw [norm_one] at this
      nlinarith
    have hlow : (2:ℝ) ^ (-A) ≤ (1 + r) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    calc ‖V (6 + t * I) ξ‖ ≤ (1 + C₁) * ((2:ℝ) ^ A * (2:ℝ) ^ (-A)) := by rw [h2A]; linarith
      _ ≤ (1 + C₁) * 2 ^ A * (1 + r) ^ (-A) := by
          rw [← mul_assoc]; gcongr
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · -- far range
    have h := hC₂ t ξ hξ
    have hinv : (1 + |t|) / ξ = r⁻¹ := by rw [hr, inv_div]
    rw [hinv] at h
    have hri : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
    have hri0 : 0 < r⁻¹ := inv_pos.2 hr0
    have h3 : r⁻¹ ^ (A + 1) ≤ r⁻¹ ^ A :=
      Real.rpow_le_rpow_of_exponent_ge hri0 hri (by linarith)
    have h4 : r⁻¹ ^ A ≤ 2 ^ A * (1 + r) ^ (-A) := by
      rw [Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le]
      have : r ^ (-A) ≤ ((1 + r) / 2) ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      refine this.trans (le_of_eq ?_)
      rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        div_inv_eq_mul, mul_comm]
    calc ‖V (6 + t * I) ξ‖ ≤ C₂ * r⁻¹ ^ (A + 1) := h
      _ ≤ C₂ * (2 ^ A * (1 + r) ^ (-A)) := by gcongr; exact h3.trans h4
      _ = C₂ * 2 ^ A * (1 + r) ^ (-A) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

end RamanujanTau.HeckeAFE
