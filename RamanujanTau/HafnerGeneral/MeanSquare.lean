/-
# Uniform mean square of `L(f, σ+it)` near the critical line, for a cusp form of weight `2p+2`

**Theorem** (`mean_square_uniform`). For `f ∈ S_{2p+2}(SL₂(ℤ))` there is `C` such that for all
`0 < x ≤ 1` and `T ≥ 1`

    ∫_T^{2T} |L(f, p+1+x+it)|² dt ≤ C · T / x.

The proof is `HardyCountHafner.MeanSquare` with `Δ` replaced by `f`:
1. `Λ(f,σ+it)e^{βt} = ∫ Φ_σ(−2πξ+iβ) e^{−2πiξt} dξ` (`Fourier.Fs_eq_fI`),
   `Φ_σ(w) = 2π e^{σw} f(i e^w)`;
2. `|f(z)| (Im z)^{p+1} ≤ M e^{−π Im z}` (`GeneralCuspMoments.exists_cusp_bound`) gives
   `|Φ_σ(u+iβ)| ≤ 2πM c^{−(p+1)} e^{xu} e^{−πce^u} ≤ 6πM c^{−(p+1)−x}/(1+(x(u+log c))²)`;
3. Schur (`HardyCountHafner.integral_tri_norm_fI_sq_le_gen`);
4. Stirling from below (`Stirling.stirling_le_norm_Gamma`, valid for every `σ ≥ 3/2`),
   `β = π/2 − 1/T`: the powers `T^{2p+2+2x}` and `T^{2p+1+2x}` cancel.
-/
import RamanujanTau.HafnerGeneral.Fourier
import RamanujanTau.GeneralCuspMoments.CuspRay
import RamanujanTau.HardyCountHafner.MeanSquare

set_option autoImplicit false

namespace RamanujanTau.HafnerGeneral

open Complex MeasureTheory Set Filter Topology ModularForm
open UpperHalfPlane hiding I
open RamanujanTau.HeckeConvexGeneral RamanujanTau.HardyZerosGeneral
  RamanujanTau.HardyCountLinear RamanujanTau.HardyCount
  RamanujanTau.GeneralCuspMoments
open scoped Real FourierTransform MatrixGroups

variable {p : ℕ}

lemma half_k' (p : ℕ) : (((2 * p + 2 : ℕ) : ℝ)) / 2 = (p : ℝ) + 1 := by push_cast; ring

lemma sig_lo (p : ℕ) {x : ℝ} (hx : 0 ≤ x) : (((2 * p + 2 : ℕ) : ℝ)) / 2 ≤ (p : ℝ) + 1 + x := by
  rw [half_k']; linarith

lemma sig_hi (p : ℕ) {x : ℝ} (hx : x ≤ 1) :
    (p : ℝ) + 1 + x ≤ (((2 * p + 2 : ℕ) : ℝ)) / 2 + 1 := by
  rw [half_k']; linarith

/-- `‖G_σ(u+iβ)‖ ≤ M c^{−(p+1)} e^{(σ−p−1)u} e^{−π c e^u}` with `c = cos β`. -/
lemma norm_Gs_le (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) {M : ℝ}
    (hM : ∀ z : ℂ, 0 < z.im → ‖Fc f z‖ * z.im ^ (p + 1) ≤ M * Real.exp (-(π * z.im)))
    (σ : ℝ) {u β : ℝ} (hβ : |β| < π / 2) :
    ‖Gs f σ ((u : ℂ) + β * I)‖ ≤
      M / Real.cos β ^ (p + 1) * (Real.exp ((σ - ((p : ℝ) + 1)) * u) *
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
  have h := hM _ hz
  rw [e] at h
  rw [Gs, norm_mul, Complex.norm_exp]
  have hre : ((σ : ℂ) * w).re = σ * u := by rw [hwdef]; simp
  rw [hre]
  set Dn := ‖Fc f (cexp w * I)‖ with hDn
  set v := Real.exp u * Real.cos β with hv
  have hE1 : Real.exp (σ * u) = Real.exp ((σ - ((p : ℝ) + 1)) * u) * Real.exp u ^ (p + 1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have hcos : 0 < Real.cos β ^ (p + 1) := by positivity
  have hX : 0 < Real.exp ((σ - ((p : ℝ) + 1)) * u) := Real.exp_pos _
  rw [hE1, div_mul_eq_mul_div, le_div_iff₀ hcos]
  calc Real.exp ((σ - ((p : ℝ) + 1)) * u) * Real.exp u ^ (p + 1) * Dn * Real.cos β ^ (p + 1)
      = Real.exp ((σ - ((p : ℝ) + 1)) * u) * (Dn * v ^ (p + 1)) := by rw [hv, mul_pow]; ring
    _ ≤ Real.exp ((σ - ((p : ℝ) + 1)) * u) * (M * Real.exp (-(π * v))) := by gcongr
    _ = _ := by rw [hv]; ring_nf

/-- **Mean square of `F(t) = Λ(f,σ+it)e^{βt}`**, `σ = p+1+x`, uniformly in `0 < x ≤ 1`. -/
theorem mean_sq_Fs (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 < x → x ≤ 1 → ∀ β : ℝ, 0 ≤ β → β < π / 2 →
    ∀ T : ℝ, 0 < T → ∫ t in Icc T (2 * T), ‖Fs f ((p : ℝ) + 1 + x) β t‖ ^ 2 ≤
      (6 * π * M / Real.cos β ^ (p + 1) * Real.cos β ^ (-x)) ^ 2 / x := by
  obtain ⟨M, hM0, hM⟩ := exists_cusp_bound f
  refine ⟨M, hM0, fun x hx0 hx1 β hβ0 hβ T hT => ?_⟩
  set σ : ℝ := (p : ℝ) + 1 + x with hσ
  have h1 := sig_lo p hx0.le
  have h2 := sig_hi p hx1
  rw [← hσ] at h1 h2
  set c : ℝ := Real.cos β with hcdef
  have hc0 : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ⟩
  have hβabs : |β| < π / 2 := by rw [abs_of_nonneg hβ0]; exact hβ
  set A : ℝ := 6 * π * M / c ^ (p + 1) * c ^ (-x) with hA
  have hA0 : 0 ≤ A := by rw [hA]; have := Real.rpow_pos_of_pos hc0 (-x); positivity
  set k : ℝ → ℝ := fun ξ => A * (1 + (x * (-2 * π * ξ + Real.log c)) ^ 2)⁻¹ with hk'
  have hki : Integrable k := (HardyCountHafner.integrable_lorentz hx0 (Real.log c)).const_mul A
  have hkK : ∀ ξ, k ξ ≤ A := by
    intro ξ
    have : (1 + (x * (-2 * π * ξ + Real.log c)) ^ 2)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (x * (-2 * π * ξ + Real.log c))])
    calc k ξ = A * (1 + (x * (-2 * π * ξ + Real.log c)) ^ 2)⁻¹ := rfl
      _ ≤ A * 1 := by gcongr
      _ = A := mul_one A
  have hkint : ∫ ξ, k ξ = A / (2 * x) := by
    rw [hk', integral_const_mul, HardyCountHafner.integral_lorentz hx0]; ring
  have hstrip : ∀ ξ : ℝ, (((-2 * π * ξ : ℝ) : ℂ) + β * I) ∈ strip := by
    intro ξ; show |(((-2 * π * ξ : ℝ) : ℂ) + β * I).im| < π / 2; simpa using hβabs
  have hgb : ∀ ξ, ‖gS f σ β ξ‖ ≤ k ξ := by
    intro ξ
    rw [gS, Phis_eq_strip f hk h1 h2 (hstrip ξ), norm_mul]
    have h2π : ‖(2 * π : ℂ)‖ = 2 * π := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h2π]
    have hG := norm_Gs_le f hM σ (u := -2 * π * ξ) hβabs
    have hkf := HardyCountHafner.kf_le (x := x) (c := c) hx0.le hx1 hc0 (-2 * π * ξ)
    have e : σ - ((p : ℝ) + 1) = x := by rw [hσ]; ring
    rw [e, ← hcdef] at hG
    have hMc : 0 ≤ M / c ^ (p + 1) := by positivity
    calc 2 * π * ‖Gs f σ (((-2 * π * ξ : ℝ) : ℂ) + β * I)‖
        ≤ 2 * π * (M / c ^ (p + 1) * (Real.exp (x * (-2 * π * ξ)) *
            Real.exp (-(π * c * Real.exp (-2 * π * ξ))))) := by gcongr
      _ ≤ 2 * π * (M / c ^ (p + 1) * (3 * c ^ (-x) *
            (1 + (x * (-2 * π * ξ + Real.log c)) ^ 2)⁻¹)) := by gcongr
      _ = k ξ := by rw [hk', hA]; ring
  have hgc : Continuous (gS f σ β) := by
    unfold gS
    exact (differentiableOn_Phis f hk h1 h2).continuousOn.comp_continuous (by fun_prop) hstrip
  have hgi : Integrable (gS f σ β) :=
    hki.mono' hgc.aestronglyMeasurable (Eventually.of_forall hgb)
  have hFeq : ∀ t, Fs f σ β t = fI (gS f σ β) t := Fs_eq_fI f hk h1 h2 hβ0 hβ hgi
  have hmain := HardyCountHafner.integral_tri_norm_fI_sq_le_gen hgc hki hgb hkK hT.le (3 * T / 2)
  rw [hkint] at hmain
  have hsq : ∀ t, ‖fI (gS f σ β) t‖ ^ 2 = ‖Fs f σ β t‖ ^ 2 := fun t => by rw [hFeq]
  simp only [hsq] at hmain
  set B : ℝ := ∫ ξ, ‖gS f σ β ξ‖ with hB
  have hBd : ∀ t, ‖Fs f σ β t‖ ≤ B := fun t => by rw [hFeq]; exact norm_fI_le t
  have hFc : Continuous fun t => ‖Fs f σ β t‖ ^ 2 :=
    ((continuous_Fs f (by omega) σ β).norm.pow 2)
  have hWI : Integrable fun t => tri T (t - 3 * T / 2) * ‖Fs f σ β t‖ ^ 2 := by
    have h1 : Integrable fun t => tri T (t - 3 * T / 2) := (integrable_tri T).comp_sub_right _
    have h2 := h1.bdd_mul (f := fun t => ‖Fs f σ β t‖ ^ 2) (c := B ^ 2)
      hFc.aestronglyMeasurable (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hBd t) 2)
    refine h2.congr (Eventually.of_forall fun t => ?_)
    simp only; ring
  have hpt : ∀ t ∈ Icc T (2 * T), ‖Fs f σ β t‖ ^ 2 ≤
      2 / T * (tri T (t - 3 * T / 2) * ‖Fs f σ β t‖ ^ 2) := by
    intro t ht
    have habs : |t - 3 * T / 2| ≤ T / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have htri : T / 2 ≤ tri T (t - 3 * T / 2) := by
      rw [tri_of_abs_le (by linarith)]; linarith
    have hsq0 := sq_nonneg ‖Fs f σ β t‖
    rw [← mul_assoc]
    have : 1 ≤ 2 / T * tri T (t - 3 * T / 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hT]; linarith
    nlinarith
  calc ∫ t in Icc T (2 * T), ‖Fs f σ β t‖ ^ 2
      ≤ ∫ t in Icc T (2 * T), 2 / T * (tri T (t - 3 * T / 2) * ‖Fs f σ β t‖ ^ 2) :=
        setIntegral_mono_on (hFc.integrableOn_Icc) (hWI.const_mul _).integrableOn
          measurableSet_Icc hpt
    _ ≤ ∫ t, 2 / T * (tri T (t - 3 * T / 2) * ‖Fs f σ β t‖ ^ 2) :=
        setIntegral_le_integral (hWI.const_mul _) (Eventually.of_forall fun t =>
          mul_nonneg (by positivity) (mul_nonneg (tri_nonneg _ _) (sq_nonneg _)))
    _ = 2 / T * ∫ t, tri T (t - 3 * T / 2) * ‖Fs f σ β t‖ ^ 2 := integral_const_mul _ _
    _ ≤ 2 / T * (A * (A / (2 * x)) * T) := by gcongr
    _ = A ^ 2 / x := by field_simp

/-- The Stirling constant for the lower bound. -/
noncomputable def cH (p : ℕ) : ℝ :=
  (2 * π) ^ (-((p : ℝ) + 2)) * (Real.sqrt π / 3) * Real.exp (-12)

lemma cH_pos (p : ℕ) : 0 < cH p := by unfold cH; positivity

/-- **Stirling from below**: `c_H T^{p+1/2} T^x |L(f,p+1+x+it)| ≤ |Λ(f,p+1+x+it)| e^{βt}` on
`[T,2T]`, `β = π/2 − 1/T`. -/
lemma Fs_lower (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hp : 1 ≤ p) {x T t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hT : 1 ≤ T) (ht : T ≤ t) (ht' : t ≤ 2 * T) :
    cH p * (T ^ ((p : ℝ) + 1 / 2) * T ^ x) * ‖fL f ((((p : ℝ) + 1 + x : ℝ) : ℂ) + t * I)‖ ≤
      ‖Fs f ((p : ℝ) + 1 + x) (π / 2 - 1 / T) t‖ := by
  set σ : ℝ := (p : ℝ) + 1 + x with hσ
  have hp0 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hTpos : 0 < T := by linarith
  have htpos : 0 < t := by linarith
  have hs : ∀ n : ℕ, ((σ : ℂ) + t * I : ℂ) ≠ -n :=
    ne_neg_nat_of_re_pos (by simp; linarith)
  rw [Fs, Zs, heckeLambda_eq_fL f hs, norm_mul, norm_mul, norm_mul, Complex.norm_exp]
  have hre : (((π / 2 - 1 / T : ℝ) : ℂ) * (t : ℂ)).re = (π / 2 - 1 / T) * t := by simp
  rw [hre]
  have h2π : (2 * π) ^ (-((p : ℝ) + 2)) ≤ ‖(2 * π : ℂ) ^ (-((σ : ℂ) + t * I))‖ := by
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
  have hpow : T ^ ((p : ℝ) + 1 / 2) * T ^ x ≤ ‖(3 / 2 : ℂ) + t * I‖ ^ (σ - 1 / 2) := by
    rw [← Real.rpow_add hTpos, show (p : ℝ) + 1 / 2 + x = σ - 1 / 2 by rw [hσ]; ring]
    exact Real.rpow_le_rpow hTpos.le (ht.trans hTn) (by rw [hσ]; linarith)
  have hexp : Real.exp (-2) ≤ Real.exp (-(π * |t|) / 2) * Real.exp ((π / 2 - 1 / T) * t) := by
    rw [← Real.exp_add, abs_of_pos htpos]
    apply Real.exp_le_exp.mpr
    have : t / T ≤ 2 := by rw [div_le_iff₀ hTpos]; linarith
    have e : -(π * t) / 2 + (π / 2 - 1 / T) * t = -(t / T) := by field_simp; ring
    rw [e]; linarith
  have hL0 := norm_nonneg (fL f ((σ : ℂ) + t * I))
  have hE : Real.exp (-12) = Real.exp (-10) * Real.exp (-2) := by rw [← Real.exp_add]; norm_num
  calc cH p * (T ^ ((p : ℝ) + 1 / 2) * T ^ x) * ‖fL f ((σ : ℂ) + t * I)‖
      = (2 * π) ^ (-((p : ℝ) + 2)) * ((Real.sqrt π / 3 * Real.exp (-10) *
          (T ^ ((p : ℝ) + 1 / 2) * T ^ x)) * Real.exp (-2)) * ‖fL f ((σ : ℂ) + t * I)‖ := by
        rw [cH, hE]; ring
    _ ≤ ‖(2 * π : ℂ) ^ (-((σ : ℂ) + t * I))‖ * ((Real.sqrt π / 3 * Real.exp (-10) *
          ‖(3 / 2 : ℂ) + t * I‖ ^ (σ - 1 / 2)) *
          (Real.exp (-(π * |t|) / 2) * Real.exp ((π / 2 - 1 / T) * t))) *
          ‖fL f ((σ : ℂ) + t * I)‖ := by gcongr
    _ = ‖(2 * π : ℂ) ^ (-((σ : ℂ) + t * I))‖ * (Real.sqrt π / 3 * Real.exp (-10) *
          ‖(3 / 2 : ℂ) + t * I‖ ^ (σ - 1 / 2) * Real.exp (-(π * |t|) / 2)) *
          Real.exp ((π / 2 - 1 / T) * t) * ‖fL f ((σ : ℂ) + t * I)‖ := by ring
    _ ≤ ‖(2 * π : ℂ) ^ (-((σ : ℂ) + t * I))‖ * ‖Complex.Gamma ((σ : ℂ) + t * I)‖ *
          Real.exp ((π / 2 - 1 / T) * t) * ‖fL f ((σ : ℂ) + t * I)‖ := by gcongr
    _ = _ := by ring

lemma rpow_half_sq {T : ℝ} (hT : 0 < T) (p : ℕ) :
    (T ^ ((p : ℝ) + 1 / 2)) ^ 2 = T ^ (2 * p + 1) := by
  rw [← Real.rpow_natCast (T ^ _) 2, ← Real.rpow_mul hT.le, ← Real.rpow_natCast]
  congr 1; push_cast; ring

/-- **Uniform mean square near the critical line**: `∫_T^{2T} |L(f,p+1+x+it)|² ≤ C T / x`
for all `0 < x ≤ 1`, `T ≥ 1`, with `C` independent of `x`. -/
theorem mean_square_uniform (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 → ∀ T : ℝ, 1 ≤ T →
      ∫ t in Icc T (2 * T), ‖fL f ((((p : ℝ) + 1 + x : ℝ) : ℂ) + t * I)‖ ^ 2 ≤ C * T / x := by
  obtain ⟨M, hM0, hmean⟩ := mean_sq_Fs f hk
  have hcH := cH_pos p
  refine ⟨36 * π ^ 2 * M ^ 2 * (π / 2) ^ (2 * p + 4) / cH p ^ 2, by positivity,
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
  have hc6 : (c ^ (p + 1))⁻¹ ≤ Q ^ (p + 1) := by
    rw [← inv_pow]; exact pow_le_pow_left₀ (by positivity) hcinv _
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
  set A : ℝ := 6 * π * M / c ^ (p + 1) * c ^ (-x) with hA
  have hAle : A ≤ 6 * π * M * Q ^ (p + 1) * ((π / 2) * T ^ x) := by
    rw [hA, div_eq_mul_inv]
    have := Real.rpow_pos_of_pos hcpos (-x)
    calc 6 * π * M * (c ^ (p + 1))⁻¹ * c ^ (-x) ≤ 6 * π * M * Q ^ (p + 1) * Q ^ x := by gcongr
      _ ≤ _ := by gcongr
  have hA0 : 0 ≤ A := by rw [hA]; have := Real.rpow_pos_of_pos hcpos (-x); positivity
  set P : ℝ := cH p * (T ^ ((p : ℝ) + 1 / 2) * T ^ x) with hP
  have hPpos : 0 < P := by rw [hP]; have := Real.rpow_pos_of_pos hTpos x; positivity
  have hpt : ∀ t ∈ Icc T (2 * T), ‖fL f ((((p : ℝ) + 1 + x : ℝ) : ℂ) + t * I)‖ ^ 2 ≤
      ‖Fs f ((p : ℝ) + 1 + x) β t‖ ^ 2 / P ^ 2 := by
    intro t ht
    have hl := Fs_lower f (by omega) hx0.le hx1 hT ht.1 ht.2
    rw [← hβ, ← hP] at hl
    rw [le_div_iff₀ (by positivity), ← mul_pow, mul_comm]
    exact pow_le_pow_left₀ (by positivity) hl 2
  have hLc : Continuous fun t : ℝ => ‖fL f ((((p : ℝ) + 1 + x : ℝ) : ℂ) + t * I)‖ ^ 2 :=
    (((fL_entire f (by omega)).continuous.comp (by fun_prop)).norm.pow 2)
  have hFc : Continuous fun t => ‖Fs f ((p : ℝ) + 1 + x) β t‖ ^ 2 / P ^ 2 :=
    ((continuous_Fs f (by omega) _ _).norm.pow 2).div_const _
  have h1 : ∫ t in Icc T (2 * T), ‖fL f ((((p : ℝ) + 1 + x : ℝ) : ℂ) + t * I)‖ ^ 2 ≤
      (∫ t in Icc T (2 * T), ‖Fs f ((p : ℝ) + 1 + x) β t‖ ^ 2) / P ^ 2 := by
    rw [← integral_div]
    exact setIntegral_mono_on hLc.integrableOn_Icc hFc.integrableOn_Icc measurableSet_Icc hpt
  refine h1.trans ?_
  rw [div_le_iff₀ (by positivity)]
  refine hm.trans ?_
  have hTx := Real.rpow_pos_of_pos hTpos x
  have hP2 : P ^ 2 = cH p ^ 2 * T ^ (2 * p + 1) * (T ^ x) ^ 2 := by
    rw [hP, mul_pow, mul_pow, rpow_half_sq hTpos]; ring
  rw [hP2, div_le_iff₀ hx0]
  have hA2 : A ^ 2 ≤ (6 * π * M * Q ^ (p + 1) * ((π / 2) * T ^ x)) ^ 2 :=
    pow_le_pow_left₀ hA0 hAle 2
  have hQ6 : Q ^ (p + 1) = (π / 2) ^ (p + 1) * T ^ (p + 1) := by
    rw [hQ, show π * T / 2 = (π / 2) * T by ring, mul_pow]
  have hcH2 : cH p ^ 2 ≠ 0 := by positivity
  calc A ^ 2 ≤ (6 * π * M * Q ^ (p + 1) * ((π / 2) * T ^ x)) ^ 2 := hA2
    _ = 36 * π ^ 2 * M ^ 2 * (π / 2) ^ (2 * p + 4) * (T ^ (2 * p + 1) * T) * (T ^ x) ^ 2 := by
        rw [hQ6]; ring
    _ = 36 * π ^ 2 * M ^ 2 * (π / 2) ^ (2 * p + 4) / cH p ^ 2 * T / x *
          (cH p ^ 2 * T ^ (2 * p + 1) * (T ^ x) ^ 2) * x := by
        field_simp

end RamanujanTau.HafnerGeneral
