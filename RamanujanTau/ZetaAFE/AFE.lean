/-
# The approximate functional equation for `|ζ(1/2+it)|²` (exact form)

For real `t ≠ 0` let `s± = 1/2 + z ± it` and `Φ_t(z) = Ξ(s₊)Ξ(s₋)`. `Φ_t` is entire and even
(`Ξ(1−s) = Ξ(s)`), so the contour identity `afe_line` gives `π Φ_t(0) = ∫_{(c)} Φ_t(z) e^{z²} dz/(iz)`.
On `Re z = c > 1/2` expand `ζ(s₊)ζ(s₋)` as a double Dirichlet series. With
`g(s) = s(1−s)Γ_ℝ(s)` and `R_t(z) = g(s₊)g(s₋)/(g(1/2+it)g(1/2−it))`:

    π |ζ(1/2+it)|² = Σ_{m,n ≥ 1} ∫_ℝ R_t(z) e^{z²}/z · m^{−s₊} n^{−s₋} dy,     z = c + iy.

No `χ` factor appears: the symmetry `z ↦ −z` of `Φ_t` replaces the functional equation of `ζ`.
-/
import RamanujanTau.ZetaAFE.Xi
import RamanujanTau.ZetaMeanSquare.Conj

set_option autoImplicit false

namespace RamanujanTau.ZetaAFE

open Complex MeasureTheory Set Filter Topology

noncomputable def sp (t : ℝ) (z : ℂ) : ℂ := 1 / 2 + z + t * I
noncomputable def sm (t : ℝ) (z : ℂ) : ℂ := 1 / 2 + z - t * I
noncomputable def Phi (t : ℝ) (z : ℂ) : ℂ := Xi (sp t z) * Xi (sm t z)
noncomputable def gfac (s : ℂ) : ℂ := s * (1 - s) * Gammaℝ s
noncomputable def G0 (t : ℝ) : ℂ := gfac (sp t 0) * gfac (sm t 0)
/-- `R_t(z) = g(s₊)g(s₋)/(g(1/2+it)g(1/2−it))`. -/
noncomputable def Rt (t : ℝ) (z : ℂ) : ℂ := gfac (sp t z) * gfac (sm t z) / G0 t

/-- The `(m,n)` term of the AFE (indices shifted by one). -/
noncomputable def afeTerm (t c : ℝ) (p : ℕ × ℕ) (y : ℝ) : ℂ :=
  Rt t (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I) *
    (1 / ((p.1 : ℂ) + 1) ^ sp t (c + y * I) * (1 / ((p.2 : ℂ) + 1) ^ sm t (c + y * I)))

lemma differentiable_Phi (t : ℝ) : Differentiable ℂ (Phi t) := by
  unfold Phi sp sm
  have := differentiable_Xi
  fun_prop

lemma Phi_neg (t : ℝ) (z : ℂ) : Phi t (-z) = Phi t z := by
  unfold Phi
  have h1 : sp t (-z) = 1 - sm t z := by unfold sp sm; ring
  have h2 : sm t (-z) = 1 - sp t z := by unfold sp sm; ring
  rw [h1, h2, Xi_one_sub, Xi_one_sub, mul_comm]

lemma norm_s_le (t x y : ℝ) (hx : |x| ≤ 1) (σ : ℝ) (hσ : |σ| = 1) :
    ‖(1 / 2 : ℂ) + ((x : ℂ) + y * I) + σ * t * I‖ ≤ 2 + |t| + |y| := by
  have h : (1 / 2 : ℂ) + ((x : ℂ) + y * I) + σ * t * I = ((1 / 2 + x : ℝ) : ℂ) + ((y + σ * t : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [h]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  simp only [mul_zero, sub_zero, mul_one, zero_mul, add_zero, zero_add]
  have h1 : |1 / 2 + x| ≤ 1 / 2 + 1 := (abs_add_le _ _).trans (by rw [abs_of_pos (by norm_num)]; linarith)
  have h2 : |y + σ * t| ≤ |y| + |t| := (abs_add_le _ _).trans (by rw [abs_mul, hσ, one_mul])
  linarith

lemma norm_Phi_le (t : ℝ) {c : ℝ} (hc1 : c ≤ 1) :
    ∃ K : ℝ, ∀ x y : ℝ, |x| ≤ c → ‖Phi t (x + y * I)‖ ≤ K * Real.exp (y ^ 2 / 2) := by
  set A : ℝ := 3 + |t| with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨(B0 + 1) ^ 2 * (8 * (A ^ 4 + 8)), fun x y hx => ?_⟩
  have hx1 : |x| ≤ 1 := hx.trans hc1
  have hb : ∀ s : ℂ, s.re = 1 / 2 + x → ‖s‖ ≤ 2 + |t| + |y| → ‖Xi s‖ ≤ (A + |y|) ^ 2 * (B0 + 1) := by
    intro s hre hn
    have hxr := abs_le.mp hx1
    have := norm_Xi_le (s := s) (by rw [hre]; linarith) (by rw [hre]; linarith)
    have hB := B0_nonneg
    have h1 : (1 + ‖s‖) ^ 2 ≤ (A + |y|) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) (by rw [hA]; linarith) 2
    have h2 : 1 ≤ (A + |y|) ^ 2 := by
      have : 1 ≤ A + |y| := by rw [hA]; have := abs_nonneg t; have := abs_nonneg y; linarith
      nlinarith
    nlinarith
  have hsp := hb (sp t (x + y * I)) (by simp [sp]) (by
    have := norm_s_le t x y hx1 1 (by simp); simpa [sp] using this)
  have hsm := hb (sm t (x + y * I)) (by simp [sm]) (by
    have := norm_s_le t x y hx1 (-1) (by simp)
    have e : (1 / 2 : ℂ) + ((x : ℂ) + y * I) + ((-1 : ℝ) : ℂ) * t * I = sm t (x + y * I) := by
      unfold sm; push_cast; ring
    rwa [e] at this)
  unfold Phi
  rw [norm_mul]
  have hP := poly_le_gauss hA0 y
  have hB := B0_nonneg
  calc ‖Xi (sp t (x + y * I))‖ * ‖Xi (sm t (x + y * I))‖
      ≤ ((A + |y|) ^ 2 * (B0 + 1)) * ((A + |y|) ^ 2 * (B0 + 1)) := by
        gcongr
    _ = (B0 + 1) ^ 2 * (A + |y|) ^ 4 := by ring
    _ ≤ (B0 + 1) ^ 2 * (8 * (A ^ 4 + 8) * Real.exp (y ^ 2 / 2)) := by gcongr
    _ = _ := by ring

lemma sp_zero (t : ℝ) : sp t 0 = 1 / 2 + t * I := by unfold sp; ring
lemma sm_zero (t : ℝ) : sm t 0 = (starRingEnd ℂ) (1 / 2 + t * I) := by
  unfold sm; apply Complex.ext <;> simp

lemma half_line_ne_one (t : ℝ) : (1 / 2 : ℂ) + t * I ≠ 1 := by
  intro h; have := congrArg Complex.re h; norm_num at this

lemma gfac_ne_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) : gfac s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  unfold gfac
  exact mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr (Ne.symm hs1))) (Gammaℝ_ne_zero_of_re_pos hs)

lemma G0_ne_zero (t : ℝ) : G0 t ≠ 0 := by
  unfold G0
  refine mul_ne_zero (gfac_ne_zero (by simp [sp]) ?_) (gfac_ne_zero (by simp [sm]) ?_)
  · rw [sp_zero]; exact half_line_ne_one t
  · intro h; have := congrArg Complex.re h; norm_num [sm] at this

lemma Phi_zero (t : ℝ) :
    Phi t 0 = G0 t * ((‖riemannZeta (1 / 2 + t * I)‖ ^ 2 : ℝ) : ℂ) := by
  unfold Phi G0
  have h1 : Xi (sp t 0) = gfac (sp t 0) * riemannZeta (sp t 0) := by
    rw [Xi_eq_zeta (by simp [sp]) (by rw [sp_zero]; exact half_line_ne_one t)]; rfl
  have hsm1 : sm t 0 ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num [sm] at this
  have h2 : Xi (sm t 0) = gfac (sm t 0) * riemannZeta (sm t 0) := by
    rw [Xi_eq_zeta (by simp [sm]) hsm1]; rfl
  rw [h1, h2, sm_zero, ZetaMeanSquare.riemannZeta_conj (half_line_ne_one t), sp_zero]
  have : riemannZeta (1 / 2 + t * I) * (starRingEnd ℂ) (riemannZeta (1 / 2 + t * I)) =
      ((‖riemannZeta (1 / 2 + t * I)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← this]; ring

lemma norm_one_div_cpow (n : ℕ) (s : ℂ) :
    ‖1 / ((n : ℂ) + 1) ^ s‖ = ((n : ℝ) + 1) ^ (-s.re) := by
  have h : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h, norm_div, norm_one, norm_cpow_eq_rpow_re_of_pos (by positivity), Real.rpow_neg (by positivity),
    one_div]

lemma summable_rpow_neg {σ : ℝ} (hσ : 1 < σ) : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-σ) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hσ)
  refine h.congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Real.rpow_neg (by positivity)]

lemma re_sp (t : ℝ) (c y : ℝ) : (sp t (c + y * I)).re = 1 / 2 + c := by simp [sp]
lemma re_sm (t : ℝ) (c y : ℝ) : (sm t (c + y * I)).re = 1 / 2 + c := by simp [sm]

lemma norm_afeTerm (t c : ℝ) (p : ℕ × ℕ) (y : ℝ) :
    ‖afeTerm t c p y‖ = ‖Rt t (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)‖ *
      (((p.1 : ℝ) + 1) ^ (-(1 / 2 + c)) * ((p.2 : ℝ) + 1) ^ (-(1 / 2 + c))) := by
  unfold afeTerm
  rw [norm_mul, norm_mul, norm_one_div_cpow, norm_one_div_cpow, re_sp, re_sm]

/-- **The exact AFE for `|ζ(1/2+it)|²`.** -/
theorem afe_exact {t : ℝ} {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1)
    (hRc : Continuous fun y : ℝ => Rt t (c + y * I)) {KR : ℝ}
    (hR : ∀ y : ℝ, ‖Rt t (c + y * I)‖ ≤ KR * Real.exp (y ^ 2 / 2)) :
    (Real.pi : ℂ) * ((‖riemannZeta (1 / 2 + t * I)‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : ℕ × ℕ, ∫ y : ℝ, afeTerm t c p y := by
  have hc0 : 0 < c := by linarith
  obtain ⟨K, hK⟩ := norm_Phi_le t hc1
  have hline := afe_line (differentiable_Phi t) (Phi_neg t) hc0 hK
  rw [Phi_zero] at hline
  -- integrability of the base integrand
  have hbase : Integrable fun y : ℝ =>
      Rt t (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I) :=
    integrable_line_gauss hc0 hRc hR
  have hsum1 : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-(1 / 2 + c)) := summable_rpow_neg (by linarith)
  have hsumP : Summable fun p : ℕ × ℕ =>
      ((p.1 : ℝ) + 1) ^ (-(1 / 2 + c)) * ((p.2 : ℝ) + 1) ^ (-(1 / 2 + c)) :=
    summable_mul_of_summable_norm (f := fun n : ℕ => ((n : ℝ) + 1) ^ (-(1 / 2 + c)))
      (g := fun n : ℕ => ((n : ℝ) + 1) ^ (-(1 / 2 + c)))
      (by simpa [Real.norm_eq_abs] using hsum1.abs)
      (by simpa [Real.norm_eq_abs] using hsum1.abs)
  have hint : ∀ p : ℕ × ℕ, Integrable (afeTerm t c p) := by
    intro p
    refine (hbase.norm.mul_const (((p.1 : ℝ) + 1) ^ (-(1 / 2 + c)) *
      ((p.2 : ℝ) + 1) ^ (-(1 / 2 + c)))).mono' ?_ (Eventually.of_forall fun y => (norm_afeTerm t c p y).le)
    refine Continuous.aestronglyMeasurable ?_
    unfold afeTerm
    refine Continuous.mul ?_ ?_
    · exact (hRc.mul (by fun_prop)).div (by fun_prop) fun y => line_ne_zero hc0.ne' y
    · refine Continuous.mul ?_ ?_
      · refine continuous_const.div ?_ (fun y => ?_)
        · exact Continuous.const_cpow (by unfold sp; fun_prop) (Or.inl (by
            intro h; have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) p.1]))
        · exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by
            intro h; have := congrArg Complex.re h; simp [sp] at this; linarith)).mpr (by
            intro h; have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) p.1])
      · refine continuous_const.div ?_ (fun y => ?_)
        · exact Continuous.const_cpow (by unfold sm; fun_prop) (Or.inl (by
            intro h; have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) p.2]))
        · exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by
            intro h; have := congrArg Complex.re h; simp [sm] at this; linarith)).mpr (by
            intro h; have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) p.2])
  have hsumI : Summable fun p : ℕ × ℕ => ∫ y : ℝ, ‖afeTerm t c p y‖ := by
    simp_rw [norm_afeTerm]
    simp_rw [integral_mul_const]
    exact hsumP.mul_left _
  rw [integral_tsum_of_summable_integral_norm hint hsumI]
  -- pointwise: Φ_t(z) e^{z²}/z = G0 · Σ_p afeTerm
  have hpt : ∀ y : ℝ, Phi t (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I) =
      G0 t * ∑' p : ℕ × ℕ, afeTerm t c p y := by
    intro y
    set z : ℂ := (c : ℂ) + y * I with hz
    have hre1 : 1 < (sp t z).re := by rw [hz, re_sp]; linarith
    have hre2 : 1 < (sm t z).re := by rw [hz, re_sm]; linarith
    have hne1 : sp t z ≠ 1 := by intro h; rw [h] at hre1; simp at hre1
    have hne2 : sm t z ≠ 1 := by intro h; rw [h] at hre2; simp at hre2
    have hz1 : Xi (sp t z) = gfac (sp t z) * riemannZeta (sp t z) := by
      rw [Xi_eq_zeta (by linarith) hne1]; rfl
    have hz2 : Xi (sm t z) = gfac (sm t z) * riemannZeta (sm t z) := by
      rw [Xi_eq_zeta (by linarith) hne2]; rfl
    have hzz : riemannZeta (sp t z) * riemannZeta (sm t z) =
        ∑' p : ℕ × ℕ, 1 / ((p.1 : ℂ) + 1) ^ sp t z * (1 / ((p.2 : ℂ) + 1) ^ sm t z) := by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre1, zeta_eq_tsum_one_div_nat_add_one_cpow hre2]
      refine tsum_mul_tsum_of_summable_norm ?_ ?_
      · simp_rw [norm_one_div_cpow]; rw [hz, re_sp]; exact hsum1
      · simp_rw [norm_one_div_cpow]; rw [hz, re_sm]; exact hsum1
    unfold afeTerm
    rw [← hz, tsum_mul_left, ← hzz]
    unfold Phi Rt
    rw [hz1, hz2]
    have := G0_ne_zero t
    field_simp
  simp_rw [hpt] at hline
  rw [integral_const_mul] at hline
  have hG := G0_ne_zero t
  have : G0 t * ((Real.pi : ℂ) * ((‖riemannZeta (1 / 2 + t * I)‖ ^ 2 : ℝ) : ℂ)) =
      G0 t * ∫ y : ℝ, ∑' p : ℕ × ℕ, afeTerm t c p y := by
    rw [hline]; ring
  exact mul_left_cancel₀ hG this

end RamanujanTau.ZetaAFE
