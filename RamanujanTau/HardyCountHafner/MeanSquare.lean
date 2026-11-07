/-
# Uniform mean square of `L(Δ, σ+it)` near the critical line

**Theorem** (`mean_square_uniform`). There is `C` such that for all `0 < x ≤ 1` and `T ≥ 1`

    ∫_T^{2T} |L(Δ, 6+x+it)|² dt ≤ C · T / x.

The constant does not depend on `x`: this is the uniformity that the fixed-`σ` Carlson–Potter
limit (`MeanSquareFull`) does not provide.  The order `T/x` is sharp for `x ≥ 1/log T`
(the true size is `≍ T · min(1/x, log T)`).

Proof (no approximate functional equation):
1. `F(t) = Λ(σ+it) e^{βt} = ∫ Φ_σ(−2πξ+iβ) e^{−2πiξt} dξ` (`Fourier.Fs_eq_fI`), with
   `Φ_σ(w) = 2π e^{σw} Δ(i e^w)`.
2. `|Δ(τ)| (Im τ)⁶ e^{π Im τ} ≤ M` on `ℍ`, so with `c = cos β`, `v = c e^u`:
   `|Φ_σ(u+iβ)| ≤ 2π M c^{−6} e^{xu} e^{−π c e^u} ≤ 6π M c^{−6−x} / (1 + (x(u + log c))²)`.
3. Schur (`Schur.integral_tri_norm_fI_sq_le_gen`): `∫ tri_T(t−3T/2)|F|² ≤ K (∫k) T` with
   `K (∫k) = (6πMc^{−6−x})²/(2x)`.
4. Stirling from below, `β = π/2 − 1/T`, `c = sin(1/T) ≥ 2/(πT)`: the powers of `T` cancel
   and leave `T/x`.
-/
import RamanujanTau.HardyCountHafner.Fourier
import RamanujanTau.HardyCount.Window

set_option autoImplicit false

namespace RamanujanTau.HardyCountHafner

open Complex MeasureTheory Set Filter Topology
open UpperHalfPlane hiding I
open RamanujanTau.HeckeL RamanujanTau.HardyZeros RamanujanTau.HardyCount
  RamanujanTau.HardyCountLinear
open scoped Real FourierTransform

/-- `‖Δ(τ)‖ (Im τ)⁶ e^{π Im τ}` is bounded on `ℍ`. -/
lemma exists_Delta_bound_exp :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : ℍ, ‖Δf p‖ * p.im ^ 6 * Real.exp (π * p.im) ≤ M := by
  obtain ⟨M, hM0, hM⟩ := exists_Delta_bound
  obtain ⟨A, Y, hA, hY, hcusp⟩ := Delta_cusp_bound
  have hMY : 0 ≤ M * Real.exp (π * Y) := by positivity
  refine ⟨M * Real.exp (π * Y) + 720 * A, by positivity, fun p => ?_⟩
  have hy := p.im_pos
  rcases le_or_gt p.im Y with h | h
  · have h1 := hM p
    have h2 : Real.exp (π * p.im) ≤ Real.exp (π * Y) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have : ‖Δf p‖ * p.im ^ 6 * Real.exp (π * p.im) ≤ M * Real.exp (π * Y) :=
      mul_le_mul h1 h2 (by positivity) hM0
    linarith
  · have h1 := hcusp p h.le
    have h2 : p.im ^ 6 ≤ 720 * Real.exp (π * p.im) := by
      have h4 := Real.pow_div_factorial_le_exp p.im hy.le 6
      have h3 : Real.exp p.im ≤ Real.exp (π * p.im) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
      have e : ((6 : ℕ).factorial : ℝ) = 720 := by norm_num [Nat.factorial]
      rw [e, div_le_iff₀ (by norm_num)] at h4
      linarith
    have hE : Real.exp (-(2 * π) * p.im) * Real.exp (π * p.im) * Real.exp (π * p.im) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf; simp
    calc ‖Δf p‖ * p.im ^ 6 * Real.exp (π * p.im)
        ≤ (A * Real.exp (-(2 * π) * p.im)) * (720 * Real.exp (π * p.im)) *
            Real.exp (π * p.im) := by gcongr
      _ = 720 * A * (Real.exp (-(2 * π) * p.im) * Real.exp (π * p.im) *
            Real.exp (π * p.im)) := by ring
      _ = 720 * A := by rw [hE, mul_one]
      _ ≤ _ := by linarith

/-- `‖G_σ(u+iβ)‖ ≤ M c^{−6} e^{(σ−6)u} e^{−π c e^u}` with `c = cos β`. -/
lemma norm_Gs_le {M : ℝ} (hM : ∀ p : ℍ, ‖Δf p‖ * p.im ^ 6 * Real.exp (π * p.im) ≤ M)
    (σ : ℝ) {u β : ℝ} (hβ : |β| < π / 2) :
    ‖Gs σ ((u : ℂ) + β * I)‖ ≤
      M / Real.cos β ^ 6 * (Real.exp ((σ - 6) * u) *
        Real.exp (-(π * Real.cos β * Real.exp u))) := by
  set w : ℂ := (u : ℂ) + β * I with hwdef
  have hwim : w.im = β := by simp [hwdef]
  have hwre : w.re = u := by simp [hwdef]
  have hw : w ∈ strip := by show |w.im| < π / 2; rw [hwim]; exact hβ
  have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le β], by linarith [le_abs_self β]⟩
  have hz := im_exp_mul_I_pos hw
  have e : (cexp w * I).im = Real.exp u * Real.cos β := by
    rw [← hwre, ← hwim]; simp [Complex.exp_re]
  have h := hM ⟨cexp w * I, hz⟩
  have him : (⟨cexp w * I, hz⟩ : ℍ).im = Real.exp u * Real.cos β := e
  rw [him] at h
  rw [Gs, norm_mul, Complex.norm_exp, Dc_of_im_pos hz]
  have hre : ((σ : ℂ) * w).re = σ * u := by rw [hwdef]; simp
  rw [hre]
  set D := ‖Δf ⟨cexp w * I, hz⟩‖ with hD
  set v := Real.exp u * Real.cos β with hv
  have hvpos : 0 < v := by positivity
  have hD0 : 0 ≤ D := norm_nonneg _
  have hE1 : Real.exp (σ * u) = Real.exp ((σ - 6) * u) * Real.exp u ^ 6 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have hE2 : Real.exp (-(π * Real.cos β * Real.exp u)) * Real.exp (π * v) = 1 := by
    rw [← Real.exp_add, hv]; ring_nf; simp
  have hX : 0 < Real.exp ((σ - 6) * u) := Real.exp_pos _
  have hcos6 : 0 < Real.cos β ^ 6 := by positivity
  rw [hE1, div_mul_eq_mul_div, le_div_iff₀ hcos6]
  calc Real.exp ((σ - 6) * u) * Real.exp u ^ 6 * D * Real.cos β ^ 6
      = Real.exp ((σ - 6) * u) * Real.exp (-(π * Real.cos β * Real.exp u)) *
          (D * v ^ 6 * Real.exp (π * v)) := by
        rw [hv, mul_pow]
        have := hE2
        calc Real.exp ((σ - 6) * u) * Real.exp u ^ 6 * D * Real.cos β ^ 6
            = Real.exp ((σ - 6) * u) * Real.exp u ^ 6 * D * Real.cos β ^ 6 *
                (Real.exp (-(π * Real.cos β * Real.exp u)) * Real.exp (π * v)) := by
              rw [hE2, mul_one]
          _ = _ := by rw [hv]; ring
    _ ≤ Real.exp ((σ - 6) * u) * Real.exp (-(π * Real.cos β * Real.exp u)) * M := by
        gcongr
    _ = _ := by ring

/-- `e^{−a} ≤ 3/(1+a²)` for `a ≥ 0`. -/
lemma exp_neg_le_three_div {a : ℝ} (ha : 0 ≤ a) : Real.exp (-a) ≤ 3 * (1 + a ^ 2)⁻¹ := by
  have h2 := Real.pow_div_factorial_le_exp a ha 2
  have e : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [e] at h2
  have h1 : 1 ≤ Real.exp a := Real.one_le_exp ha
  have hpos : 0 < 1 + a ^ 2 := by positivity
  rw [Real.exp_neg, ← div_eq_mul_inv, inv_le_iff_one_le_mul₀ (Real.exp_pos a),
    div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith

/-- The pointwise majorant: for `0 < c ≤ 1`, `0 ≤ x ≤ 1`,
`e^{xu} e^{−π c e^u} ≤ 3 c^{−x} / (1 + (x (u + log c))²)`. -/
lemma kf_le {x c : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hc0 : 0 < c) (u : ℝ) :
    Real.exp (x * u) * Real.exp (-(π * c * Real.exp u)) ≤
      3 * c ^ (-x) * (1 + (x * (u + Real.log c)) ^ 2)⁻¹ := by
  set w := u + Real.log c with hw
  have hcx : c ^ (-x) = Real.exp (-(x * Real.log c)) := by
    rw [Real.rpow_def_of_pos hc0]; ring_nf
  have hxu : Real.exp (x * u) = c ^ (-x) * Real.exp (x * w) := by
    rw [hcx, ← Real.exp_add]; congr 1; rw [hw]; ring
  have hcx0 : 0 < c ^ (-x) := Real.rpow_pos_of_pos hc0 _
  have hP : 0 < (1 + (x * w) ^ 2)⁻¹ := by positivity
  rcases le_or_gt w 0 with hw0 | hw0
  · -- left of the turning point
    have h1 : Real.exp (-(π * c * Real.exp u)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := mul_pos (mul_pos Real.pi_pos hc0) (Real.exp_pos u); linarith
    have h2 : Real.exp (x * w) ≤ 3 * (1 + (x * w) ^ 2)⁻¹ := by
      have := exp_neg_le_three_div (a := -(x * w)) (by nlinarith)
      rwa [neg_neg, neg_sq] at this
    calc Real.exp (x * u) * Real.exp (-(π * c * Real.exp u)) ≤ Real.exp (x * u) * 1 := by
          gcongr
      _ = c ^ (-x) * Real.exp (x * w) := by rw [mul_one, hxu]
      _ ≤ c ^ (-x) * (3 * (1 + (x * w) ^ 2)⁻¹) := by gcongr
      _ = _ := by ring
  · -- right of the turning point: `c e^u = e^w ≥ 1 + w`
    have hce : c * Real.exp u = Real.exp w := by
      rw [hw, Real.exp_add, Real.exp_log hc0]; ring
    have h1 : Real.exp (-(π * c * Real.exp u)) ≤ Real.exp (-(π * (1 + w))) := by
      apply Real.exp_le_exp.mpr
      have := Real.add_one_le_exp w
      rw [mul_assoc, hce]
      nlinarith [Real.pi_pos]
    have hπ : 1 ≤ π - 1 := by linarith [Real.pi_gt_three]
    have h2 : Real.exp (x * w) * Real.exp (-(π * (1 + w))) ≤ Real.exp (-((π - 1) * w)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
    have h3 : Real.exp (-((π - 1) * w)) ≤ 3 * (1 + (x * w) ^ 2)⁻¹ := by
      refine (exp_neg_le_three_div (by nlinarith)).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply inv_anti₀ (by positivity)
      have hxw : 0 ≤ x * w := by nlinarith
      have : (x * w) ^ 2 ≤ ((π - 1) * w) ^ 2 := pow_le_pow_left₀ hxw (by nlinarith) 2
      linarith
    calc Real.exp (x * u) * Real.exp (-(π * c * Real.exp u))
        ≤ c ^ (-x) * Real.exp (x * w) * Real.exp (-(π * (1 + w))) := by
          rw [hxu]; gcongr
      _ = c ^ (-x) * (Real.exp (x * w) * Real.exp (-(π * (1 + w)))) := by ring
      _ ≤ c ^ (-x) * (3 * (1 + (x * w) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) hcx0.le
      _ = _ := by ring

lemma lorentz_eq {x : ℝ} (a : ℝ) :
    (fun ξ : ℝ => (1 + (x * (-2 * π * ξ + a)) ^ 2)⁻¹) =
      fun ξ => (fun y : ℝ => (1 + y ^ 2)⁻¹) ((-2 * π * x) * (ξ + -a / (2 * π))) := by
  funext ξ
  have : (-2 * π * x) * (ξ + -a / (2 * π)) = x * (-2 * π * ξ + a) := by
    field_simp; ring
  rw [this]

/-- `∫ (1 + (x(−2πξ + a))²)⁻¹ dξ = 1/(2x)`. -/
lemma integral_lorentz {x : ℝ} (hx : 0 < x) (a : ℝ) :
    ∫ ξ : ℝ, (1 + (x * (-2 * π * ξ + a)) ^ 2)⁻¹ = 1 / (2 * x) := by
  rw [lorentz_eq a, integral_add_right_eq_self
    (fun ξ => (fun y : ℝ => (1 + y ^ 2)⁻¹) ((-2 * π * x) * ξ)) (-a / (2 * π)),
    Measure.integral_comp_mul_left (fun y : ℝ => (1 + y ^ 2)⁻¹), integral_univ_inv_one_add_sq]
  rw [abs_inv, abs_of_neg (by have := Real.pi_pos; nlinarith [mul_pos this hx]), smul_eq_mul]
  field_simp

lemma integrable_lorentz {x : ℝ} (hx : 0 < x) (a : ℝ) :
    Integrable fun ξ : ℝ => (1 + (x * (-2 * π * ξ + a)) ^ 2)⁻¹ := by
  have hc : (-2 * π * x : ℝ) ≠ 0 := by
    have := Real.pi_pos; intro h; nlinarith [mul_pos this hx]
  rw [lorentz_eq a]
  exact (integrable_inv_one_add_sq.comp_mul_left' hc).comp_add_right (-a / (2 * π))


/-- **Mean square of `F(t) = Λ(σ+it)e^{βt}`**, `σ = 6 + x`, uniformly in `0 < x ≤ 1`. -/
theorem mean_sq_Fs : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 < x → x ≤ 1 → ∀ β : ℝ, 0 ≤ β → β < π / 2 →
    ∀ T : ℝ, 0 < T → ∫ t in Icc T (2 * T), ‖Fs (6 + x) β t‖ ^ 2 ≤
      (6 * π * M / Real.cos β ^ 6 * Real.cos β ^ (-x)) ^ 2 / x := by
  obtain ⟨M, hM0, hM⟩ := exists_Delta_bound_exp
  refine ⟨M, hM0, fun x hx0 hx1 β hβ0 hβ T hT => ?_⟩
  set σ : ℝ := 6 + x with hσ
  have h6 : 6 ≤ σ := by rw [hσ]; linarith
  have h7 : σ ≤ 7 := by rw [hσ]; linarith
  set c : ℝ := Real.cos β with hcdef
  have hc0 : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ⟩
  have hβabs : |β| < π / 2 := by rw [abs_of_nonneg hβ0]; exact hβ
  set A : ℝ := 6 * π * M / c ^ 6 * c ^ (-x) with hA
  have hA0 : 0 ≤ A := by rw [hA]; have := Real.rpow_pos_of_pos hc0 (-x); positivity
  set k : ℝ → ℝ := fun ξ => A * (1 + (x * (-2 * π * ξ + Real.log c)) ^ 2)⁻¹ with hk
  have hki : Integrable k := (integrable_lorentz hx0 (Real.log c)).const_mul A
  have hkK : ∀ ξ, k ξ ≤ A := by
    intro ξ
    have : (1 + (x * (-2 * π * ξ + Real.log c)) ^ 2)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (x * (-2 * π * ξ + Real.log c))])
    calc k ξ = A * (1 + (x * (-2 * π * ξ + Real.log c)) ^ 2)⁻¹ := rfl
      _ ≤ A * 1 := by gcongr
      _ = A := mul_one A
  have hkint : ∫ ξ, k ξ = A / (2 * x) := by
    rw [hk, integral_const_mul, integral_lorentz hx0]; ring
  have hstrip : ∀ ξ : ℝ, (((-2 * π * ξ : ℝ) : ℂ) + β * I) ∈ strip := by
    intro ξ; show |(((-2 * π * ξ : ℝ) : ℂ) + β * I).im| < π / 2; simpa using hβabs
  have hgb : ∀ ξ, ‖gS σ β ξ‖ ≤ k ξ := by
    intro ξ
    rw [gS, Phis_eq_strip h6 h7 (hstrip ξ), norm_mul]
    have h2π : ‖(2 * π : ℂ)‖ = 2 * π := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h2π]
    have hG := norm_Gs_le hM σ (u := -2 * π * ξ) hβabs
    have hkf := kf_le (x := x) (c := c) hx0.le hx1 hc0 (-2 * π * ξ)
    have e : σ - 6 = x := by rw [hσ]; ring
    rw [e, ← hcdef] at hG
    have hMc : 0 ≤ M / c ^ 6 := by positivity
    calc 2 * π * ‖Gs σ (((-2 * π * ξ : ℝ) : ℂ) + β * I)‖
        ≤ 2 * π * (M / c ^ 6 * (Real.exp (x * (-2 * π * ξ)) *
            Real.exp (-(π * c * Real.exp (-2 * π * ξ))))) := by gcongr
      _ ≤ 2 * π * (M / c ^ 6 * (3 * c ^ (-x) *
            (1 + (x * (-2 * π * ξ + Real.log c)) ^ 2)⁻¹)) := by gcongr
      _ = k ξ := by rw [hk, hA]; ring
  have hgc : Continuous (gS σ β) := by
    unfold gS
    exact (differentiableOn_Phis h6 h7).continuousOn.comp_continuous (by fun_prop) hstrip
  have hgi : Integrable (gS σ β) := hki.mono' hgc.aestronglyMeasurable (Eventually.of_forall hgb)
  have hFeq : ∀ t, Fs σ β t = fI (gS σ β) t := Fs_eq_fI h6 h7 hβ0 hβ hgi
  have hmain := integral_tri_norm_fI_sq_le_gen hgc hki hgb hkK hT.le (3 * T / 2)
  rw [hkint] at hmain
  have hsq : ∀ t, ‖fI (gS σ β) t‖ ^ 2 = ‖Fs σ β t‖ ^ 2 := fun t => by rw [hFeq]
  simp only [hsq] at hmain
  set B : ℝ := ∫ ξ, ‖gS σ β ξ‖ with hB
  have hBd : ∀ t, ‖Fs σ β t‖ ≤ B := fun t => by rw [hFeq]; exact norm_fI_le t
  have hFc : Continuous fun t => ‖Fs σ β t‖ ^ 2 := ((continuous_Fs σ β).norm.pow 2)
  have hWI : Integrable fun t => tri T (t - 3 * T / 2) * ‖Fs σ β t‖ ^ 2 := by
    have h1 : Integrable fun t => tri T (t - 3 * T / 2) := (integrable_tri T).comp_sub_right _
    have h2 := h1.bdd_mul (f := fun t => ‖Fs σ β t‖ ^ 2) (c := B ^ 2)
      hFc.aestronglyMeasurable (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hBd t) 2)
    refine h2.congr (Eventually.of_forall fun t => ?_)
    simp only; ring
  have hpt : ∀ t ∈ Icc T (2 * T), ‖Fs σ β t‖ ^ 2 ≤
      2 / T * (tri T (t - 3 * T / 2) * ‖Fs σ β t‖ ^ 2) := by
    intro t ht
    have habs : |t - 3 * T / 2| ≤ T / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have htri : T / 2 ≤ tri T (t - 3 * T / 2) := by
      rw [tri_of_abs_le (by linarith)]; linarith
    have hsq0 := sq_nonneg ‖Fs σ β t‖
    rw [← mul_assoc]
    have : 1 ≤ 2 / T * tri T (t - 3 * T / 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hT]; linarith
    nlinarith
  calc ∫ t in Icc T (2 * T), ‖Fs σ β t‖ ^ 2
      ≤ ∫ t in Icc T (2 * T), 2 / T * (tri T (t - 3 * T / 2) * ‖Fs σ β t‖ ^ 2) :=
        setIntegral_mono_on (hFc.integrableOn_Icc) (hWI.const_mul _).integrableOn
          measurableSet_Icc hpt
    _ ≤ ∫ t, 2 / T * (tri T (t - 3 * T / 2) * ‖Fs σ β t‖ ^ 2) :=
        setIntegral_le_integral (hWI.const_mul _) (Eventually.of_forall fun t =>
          mul_nonneg (by positivity) (mul_nonneg (tri_nonneg _ _) (sq_nonneg _)))
    _ = 2 / T * ∫ t, tri T (t - 3 * T / 2) * ‖Fs σ β t‖ ^ 2 := integral_const_mul _ _
    _ ≤ 2 / T * (A * (A / (2 * x)) * T) := by gcongr
    _ = A ^ 2 / x := by field_simp

/-- The Stirling constant for the lower bound. -/
noncomputable def cH : ℝ := (2 * π) ^ (-7 : ℝ) * (Real.sqrt π / 3) * Real.exp (-12)

lemma cH_pos : 0 < cH := by unfold cH; positivity

/-- **Stirling from below**: `c_H T^{11/2} T^x |L(6+x+it)| ≤ |Λ(6+x+it)| e^{βt}` on `[T,2T]`,
`β = π/2 − 1/T`. -/
lemma Fs_lower {x T t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hT : 1 ≤ T) (ht : T ≤ t)
    (ht' : t ≤ 2 * T) :
    cH * (T ^ (11 / 2 : ℝ) * T ^ x) * ‖tauL (((6 + x : ℝ) : ℂ) + t * I)‖ ≤
      ‖Fs (6 + x) (π / 2 - 1 / T) t‖ := by
  set σ : ℝ := 6 + x with hσ
  have hTpos : 0 < T := by linarith
  have htpos : 0 < t := by linarith
  have hs : ∀ n : ℕ, ((σ : ℂ) + t * I : ℂ) ≠ -n :=
    RamanujanTau.HeckeZeros.ne_neg_nat_of_re_pos (by simp; linarith)
  rw [Fs, Zs, heckeLambda_eq_tauL hs, norm_mul, norm_mul, norm_mul, Complex.norm_exp]
  have hre : (((π / 2 - 1 / T : ℝ) : ℂ) * (t : ℂ)).re = (π / 2 - 1 / T) * t := by simp
  rw [hre]
  have h2π : (2 * π) ^ (-7 : ℝ) ≤ ‖(2 * π : ℂ) ^ (-((σ : ℂ) + t * I))‖ := by
    have e : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
    rw [e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [neg_re, add_re, mul_re, Complex.I_re, Complex.I_im, ofReal_re, ofReal_im,
      mul_zero, sub_zero, add_zero, mul_one]
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [Real.pi_gt_three]) (by linarith)
  have hΓ := RamanujanTau.Stirling.stirling_le_norm_Gamma (σ := σ) (by linarith) t
  have hTn : t ≤ ‖(3 / 2 : ℂ) + t * I‖ := by
    have := Complex.abs_im_le_norm ((3 / 2 : ℂ) + t * I)
    have e : ((3 / 2 : ℂ) + t * I).im = t := by simp
    rw [e] at this
    exact (le_abs_self t).trans this
  have hpow : T ^ (11 / 2 : ℝ) * T ^ x ≤ ‖(3 / 2 : ℂ) + t * I‖ ^ (σ - 1 / 2) := by
    rw [← Real.rpow_add hTpos, show (11 / 2 : ℝ) + x = σ - 1 / 2 by rw [hσ]; ring]
    exact Real.rpow_le_rpow hTpos.le (ht.trans hTn) (by rw [hσ]; linarith)
  have hexp : Real.exp (-2) ≤ Real.exp (-(π * |t|) / 2) * Real.exp ((π / 2 - 1 / T) * t) := by
    rw [← Real.exp_add, abs_of_pos htpos]
    apply Real.exp_le_exp.mpr
    have : t / T ≤ 2 := by rw [div_le_iff₀ hTpos]; linarith
    have e : -(π * t) / 2 + (π / 2 - 1 / T) * t = -(t / T) := by field_simp; ring
    rw [e]; linarith
  have hL0 := norm_nonneg (tauL ((σ : ℂ) + t * I))
  have hE : Real.exp (-12) = Real.exp (-10) * Real.exp (-2) := by rw [← Real.exp_add]; norm_num
  calc cH * (T ^ (11 / 2 : ℝ) * T ^ x) * ‖tauL ((σ : ℂ) + t * I)‖
      = (2 * π) ^ (-7 : ℝ) * ((Real.sqrt π / 3 * Real.exp (-10) *
          (T ^ (11 / 2 : ℝ) * T ^ x)) * Real.exp (-2)) * ‖tauL ((σ : ℂ) + t * I)‖ := by
        rw [cH, hE]; ring
    _ ≤ ‖(2 * π : ℂ) ^ (-((σ : ℂ) + t * I))‖ * ((Real.sqrt π / 3 * Real.exp (-10) *
          ‖(3 / 2 : ℂ) + t * I‖ ^ (σ - 1 / 2)) *
          (Real.exp (-(π * |t|) / 2) * Real.exp ((π / 2 - 1 / T) * t))) *
          ‖tauL ((σ : ℂ) + t * I)‖ := by gcongr
    _ = ‖(2 * π : ℂ) ^ (-((σ : ℂ) + t * I))‖ * (Real.sqrt π / 3 * Real.exp (-10) *
          ‖(3 / 2 : ℂ) + t * I‖ ^ (σ - 1 / 2) * Real.exp (-(π * |t|) / 2)) *
          Real.exp ((π / 2 - 1 / T) * t) * ‖tauL ((σ : ℂ) + t * I)‖ := by ring
    _ ≤ ‖(2 * π : ℂ) ^ (-((σ : ℂ) + t * I))‖ * ‖Complex.Gamma ((σ : ℂ) + t * I)‖ *
          Real.exp ((π / 2 - 1 / T) * t) * ‖tauL ((σ : ℂ) + t * I)‖ := by gcongr
    _ = _ := by ring

/-- **Uniform mean square near the critical line**: `∫_T^{2T} |L(Δ,6+x+it)|² ≤ C T / x`
for all `0 < x ≤ 1`, `T ≥ 1`, with `C` independent of `x`. -/
theorem mean_square_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 → ∀ T : ℝ, 1 ≤ T →
    ∫ t in Icc T (2 * T), ‖tauL (((6 + x : ℝ) : ℂ) + t * I)‖ ^ 2 ≤ C * T / x := by
  obtain ⟨M, hM0, hmean⟩ := mean_sq_Fs
  have hcH := cH_pos
  refine ⟨36 * π ^ 2 * M ^ 2 * (π / 2) ^ 14 / cH ^ 2, by positivity,
    fun x hx0 hx1 T hT => ?_⟩
  have hTpos : 0 < T := by linarith
  set β : ℝ := π / 2 - 1 / T with hβ
  have hinv : 1 / T ≤ 1 := by rw [div_le_one hTpos]; exact hT
  have hinvpos : 0 < 1 / T := by positivity
  have hβ0 : 0 ≤ β := by rw [hβ]; linarith [Real.pi_gt_three]
  have hβπ : β < π / 2 := by rw [hβ]; linarith
  have hm := hmean x hx0 hx1 β hβ0 hβπ T hTpos
  set c : ℝ := Real.cos β with hc
  have hcpos : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβπ⟩
  -- `c ≥ 2/(πT)`
  have hcge : 2 / (π * T) ≤ c := by
    rw [hc, hβ, Real.cos_pi_div_two_sub]
    have := Real.mul_le_sin hinvpos.le (by linarith [Real.pi_gt_three])
    calc 2 / (π * T) = 2 / π * (1 / T) := by field_simp
      _ ≤ _ := this
  have hcinv : c⁻¹ ≤ π * T / 2 := by
    rw [inv_le_comm₀ hcpos (by positivity)]
    calc (π * T / 2)⁻¹ = 2 / (π * T) := by field_simp
      _ ≤ c := hcge
  set Q : ℝ := π * T / 2 with hQ
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith [Real.pi_gt_three]
  -- `A ≤ 6πM Q^6 Q^x`
  have hc6 : (c ^ 6)⁻¹ ≤ Q ^ 6 := by
    rw [← inv_pow]; exact pow_le_pow_left₀ (by positivity) hcinv 6
  have hcx : c ^ (-x) ≤ Q ^ x := by
    rw [Real.rpow_neg hcpos.le, ← Real.inv_rpow hcpos.le]
    exact Real.rpow_le_rpow (by positivity) hcinv hx0.le
  have hQx : Q ^ x ≤ (π / 2) * T ^ x := by
    rw [hQ, show π * T / 2 = (π / 2) * T by ring, Real.mul_rpow (by positivity) hTpos.le]
    have h1 : (π / 2) ^ x ≤ π / 2 := by
      calc (π / 2) ^ x ≤ (π / 2) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hx1
        _ = π / 2 := Real.rpow_one _
    have := Real.rpow_pos_of_pos hTpos x
    gcongr
  set A : ℝ := 6 * π * M / c ^ 6 * c ^ (-x) with hA
  have hAle : A ≤ 6 * π * M * Q ^ 6 * ((π / 2) * T ^ x) := by
    rw [hA, div_eq_mul_inv]
    have := Real.rpow_pos_of_pos hcpos (-x)
    calc 6 * π * M * (c ^ 6)⁻¹ * c ^ (-x) ≤ 6 * π * M * Q ^ 6 * Q ^ x := by gcongr
      _ ≤ _ := by gcongr
  have hA0 : 0 ≤ A := by rw [hA]; have := Real.rpow_pos_of_pos hcpos (-x); positivity
  -- pointwise lower bound
  set P : ℝ := cH * (T ^ (11 / 2 : ℝ) * T ^ x) with hP
  have hPpos : 0 < P := by rw [hP]; have := Real.rpow_pos_of_pos hTpos x; positivity
  have hpt : ∀ t ∈ Icc T (2 * T), ‖tauL (((6 + x : ℝ) : ℂ) + t * I)‖ ^ 2 ≤
      ‖Fs (6 + x) β t‖ ^ 2 / P ^ 2 := by
    intro t ht
    have hl := Fs_lower hx0.le hx1 hT ht.1 ht.2
    rw [← hβ, ← hP] at hl
    rw [le_div_iff₀ (by positivity), ← mul_pow, mul_comm]
    exact pow_le_pow_left₀ (by positivity) hl 2
  have hLc : Continuous fun t : ℝ => ‖tauL (((6 + x : ℝ) : ℂ) + t * I)‖ ^ 2 :=
    ((tauLSeries_entire.continuous.comp (by fun_prop)).norm.pow 2)
  have hFc : Continuous fun t => ‖Fs (6 + x) β t‖ ^ 2 / P ^ 2 :=
    ((continuous_Fs _ _).norm.pow 2).div_const _
  have h1 : ∫ t in Icc T (2 * T), ‖tauL (((6 + x : ℝ) : ℂ) + t * I)‖ ^ 2 ≤
      (∫ t in Icc T (2 * T), ‖Fs (6 + x) β t‖ ^ 2) / P ^ 2 := by
    rw [← integral_div]
    exact setIntegral_mono_on hLc.integrableOn_Icc hFc.integrableOn_Icc measurableSet_Icc hpt
  refine h1.trans ?_
  rw [div_le_iff₀ (by positivity)]
  refine hm.trans ?_
  -- `A²/x ≤ C T/x · P²`
  have hTx := Real.rpow_pos_of_pos hTpos x
  have hT112 : (T ^ (11 / 2 : ℝ)) ^ 2 = T ^ 11 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]; norm_num
  have hP2 : P ^ 2 = cH ^ 2 * T ^ 11 * (T ^ x) ^ 2 := by
    rw [hP, mul_pow, mul_pow, hT112]; ring
  rw [hP2, div_le_iff₀ hx0]
  have hA2 : A ^ 2 ≤ (6 * π * M * Q ^ 6 * ((π / 2) * T ^ x)) ^ 2 :=
    pow_le_pow_left₀ hA0 hAle 2
  have hQ6 : Q ^ 6 = (π / 2) ^ 6 * T ^ 6 := by rw [hQ]; ring
  calc A ^ 2 ≤ (6 * π * M * Q ^ 6 * ((π / 2) * T ^ x)) ^ 2 := hA2
    _ = 36 * π ^ 2 * M ^ 2 * (π / 2) ^ 14 * T ^ 12 * (T ^ x) ^ 2 := by rw [hQ6]; ring
    _ = 36 * π ^ 2 * M ^ 2 * (π / 2) ^ 14 / cH ^ 2 * T / x *
          (cH ^ 2 * T ^ 11 * (T ^ x) ^ 2) * x := by field_simp

end RamanujanTau.HardyCountHafner
