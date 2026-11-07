/-
# Bruhat decomposition, part 2: the pair integrals `I(γ)` and their regrouping

* `Iγ γ = ∫ ft · conj(ft ∘ γ)`, `Ip γ = ∫⁻ ‖ft‖ ‖ft ∘ γ‖`; `tsum_Ip_le : Σ_γ Ip γ ≤ N₀ ∫⁻ ‖ft‖`.
* `hasSum_right_T` (sum over the right `Γ∞`-coset): `Σ_k I(g Tᵏ) = ∫ ff · conj(ft ∘ g)`.
* `Rg_eq` (`c ≠ 0`): `∫ ff · conj(ft ∘ γ) = e(−h(a+d)/c) · K(a/c)`,
  `K(t) = ∫ ff(q) 1_{[0,1)}(t + Re ι_c q₁) conj ff(ι_c q)`.
* `hasSum_K`: `Σ_m K(t + m) = J(c) = ∫ ff · conj(ff ∘ ι_c)`.
-/
import RamanujanTau.SCSProof.Bruhat1

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

/-- `I(γ) = ∫ ft · conj(ft ∘ γ)`. -/
noncomputable def Iγ (γ : SL(2, ℤ)) : ℂ := ∫ q, ft P q * conj (ft P (dsmul γ q))

/-- `I⁺(γ) = ∫⁻ ‖ft‖ ‖ft ∘ γ‖`. -/
noncomputable def Ip (γ : SL(2, ℤ)) : ℝ≥0∞ := ∫⁻ q, ‖ft P q‖ₑ * ‖ft P (dsmul γ q)‖ₑ

lemma measurable_ft_dsmul (γ : SL(2, ℤ)) : Measurable fun q => ft P (dsmul γ q) :=
  (measurable_ft P).comp (measurable_dsmul γ)

lemma Y_mul_le (P : Par) : P.Y * (1 + P.ε) ≤ 2 * P.Y := by
  have := P.hε1; have := P.hY; nlinarith

/-- Pointwise local finiteness on the support of `ft`. -/
lemma tsum_enorm_ft_le (q : ℍ × ℍ) :
    ‖ft P q‖ₑ * ∑' γ : SL(2, ℤ), ‖ft P (dsmul γ q)‖ₑ ≤ N0 P * ‖ft P q‖ₑ := by
  by_cases h : ft P q = 0
  · simp [h]
  obtain ⟨h1, h2⟩ := ft_ne_zero P h
  rw [mul_comm]
  gcongr
  exact count_le P q h1 h2.1.1 (h2.1.2.trans (Y_mul_le P))

theorem tsum_Ip_le : ∑' γ, Ip P γ ≤ N0 P * ∫⁻ q, ‖ft P q‖ₑ := by
  unfold Ip
  rw [← lintegral_tsum fun γ => ((measurable_ft P).enorm.mul
    (measurable_ft_dsmul P γ).enorm).aemeasurable]
  simp_rw [ENNReal.tsum_mul_left]
  rw [← lintegral_const_mul _ (measurable_ft P).enorm]
  exact lintegral_mono fun q => tsum_enorm_ft_le P q

lemma tsum_Ip_ne_top : ∑' γ, Ip P γ ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (lintegral_ft_ne_top P)) (tsum_Ip_le P)

lemma norm_integral_le_toReal (f : ℍ × ℍ → ℂ) : ‖∫ q, f q‖ ≤ (∫⁻ q, ‖f q‖ₑ).toReal := by
  refine (norm_integral_le_lintegral_norm f).trans ?_
  simp_rw [ofReal_norm_eq_enorm]; exact le_rfl

lemma norm_Iγ_le (γ : SL(2, ℤ)) : ‖Iγ P γ‖ ≤ (Ip P γ).toReal := by
  refine (norm_integral_le_toReal _).trans (le_of_eq ?_)
  unfold Ip; congr 1; refine lintegral_congr fun q => ?_
  rw [enorm_mul, RCLike.enorm_conj]

lemma summable_Iγ : Summable (Iγ P) :=
  Summable.of_norm_bounded (ENNReal.summable_toReal (tsum_Ip_ne_top P)) (norm_Iγ_le P)

/-! ### The right coset sum -/

lemma coe_strip_T (k : ℤ) (w : ℍ) :
    strip.indicator (1 : ℍ → ℂ) (ModularGroup.T ^ (-k) • w) =
      (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℂ) (w.re + ((-k : ℤ) : ℝ)) := by
  have hiff : (ModularGroup.T ^ (-k) • w ∈ strip) ↔ (w.re + ((-k : ℤ) : ℝ) ∈ Ico (0 : ℝ) 1) := by
    rw [strip_iff, re_T_zpow_smul, add_comm]
  by_cases hm : ModularGroup.T ^ (-k) • w ∈ strip
  · rw [indicator_of_mem hm, indicator_of_mem (hiff.1 hm)]; rfl
  · rw [indicator_of_notMem hm, indicator_of_notMem (fun h => hm (hiff.2 h))]

lemma ft_eq_ind (q : ℍ × ℍ) : ft P q = strip.indicator (1 : ℍ → ℂ) q.1 * ff P q := by
  unfold ft indicator; split_ifs <;> simp

lemma tsum_ft_T (q : ℍ × ℍ) :
    ∑' k : ℤ, ft P (dsmul (ModularGroup.T ^ (-k)) q) = ff P q := by
  have e : ∀ k : ℤ, ft P (dsmul (ModularGroup.T ^ (-k)) q) =
      (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℂ) (q.1.re + ((-k : ℤ) : ℝ)) * ff P q := by
    intro k
    rw [ft_eq_ind, dsmul_T_zpow, ff_tau_int, ← dsmul_T_zpow]
    simp only [dsmul]
    rw [coe_strip_T]
  simp_rw [e]
  rw [tsum_mul_right]
  have := (Equiv.neg ℤ).tsum_eq (fun k : ℤ => (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℂ)
    (q.1.re + ((-k : ℤ) : ℝ)))
  simp only [Equiv.neg_apply, neg_neg] at this
  rw [← this, tsum_strip_shift, one_mul]

lemma tsum_enorm_ft_T (q : ℍ × ℍ) :
    ∑' k : ℤ, ‖ft P (dsmul (ModularGroup.T ^ (-k)) q)‖ₑ = ‖ff P q‖ₑ := by
  have e : ∀ k : ℤ, ‖ft P (dsmul (ModularGroup.T ^ (-k)) q)‖ₑ =
      strip.indicator (1 : ℍ → ℝ≥0∞) (ModularGroup.T ^ (-k) • q.1) * ‖ff P q‖ₑ := by
    intro k
    rw [ft_eq_ind, dsmul_T_zpow, ff_tau_int, ← dsmul_T_zpow, enorm_mul]
    simp only [dsmul]
    congr 1
    unfold indicator; split_ifs <;> simp
  simp_rw [e]
  rw [ENNReal.tsum_mul_right, tsum_strip, one_mul]

lemma enorm_ff_le_one (q : ℍ × ℍ) : ‖ff P q‖ₑ ≤ 1 := by
  rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_one.2 (norm_ff_le P q)

lemma lintegral_ft_dsmul (g : SL(2, ℤ)) :
    ∫⁻ q, ‖ft P (dsmul g q)‖ₑ = ∫⁻ q, ‖ft P q‖ₑ :=
  (measurePreserving_dsmul g).lintegral_comp_emb (dsmulEquiv g).measurableEmbedding
    (fun q => ‖ft P q‖ₑ)

/-- **Right coset sum.** -/
theorem hasSum_right_T (g : SL(2, ℤ)) :
    HasSum (fun k : ℤ => Iγ P (g * ModularGroup.T ^ k))
      (∫ q, ff P q * conj (ft P (dsmul g q))) := by
  have hk : ∀ k : ℤ, Iγ P (g * ModularGroup.T ^ k) =
      ∫ q, ft P (dsmul (ModularGroup.T ^ (-k)) q) * conj (ft P (dsmul g q)) := by
    intro k
    unfold Iγ
    rw [← (measurePreserving_dsmul (ModularGroup.T ^ (-k))).integral_comp
      (dsmulEquiv _).measurableEmbedding]
    congr 1; funext q
    rw [dsmul_mul, ← dsmul_mul (ModularGroup.T ^ k), ← zpow_add, add_neg_cancel, zpow_zero,
      dsmul_one]
  simp_rw [hk]
  have hmeas : ∀ k : ℤ, AEStronglyMeasurable
      (fun q => ft P (dsmul (ModularGroup.T ^ (-k)) q) * conj (ft P (dsmul g q))) volume :=
    fun k => ((measurable_ft_dsmul P _).mul
      (Complex.continuous_conj.measurable.comp (measurable_ft_dsmul P g))).aestronglyMeasurable
  have hfin : ∑' k : ℤ, ∫⁻ q, ‖ft P (dsmul (ModularGroup.T ^ (-k)) q) *
      conj (ft P (dsmul g q))‖ₑ ≠ ∞ := by
    simp_rw [enorm_mul, RCLike.enorm_conj]
    rw [← lintegral_tsum fun k => ((measurable_ft_dsmul P _).enorm.mul
      (measurable_ft_dsmul P g).enorm).aemeasurable]
    simp_rw [ENNReal.tsum_mul_right, tsum_enorm_ft_T]
    refine ne_top_of_le_ne_top (lintegral_ft_ne_top P) ?_
    rw [← lintegral_ft_dsmul P g]
    refine lintegral_mono fun q => ?_
    calc ‖ff P q‖ₑ * ‖ft P (dsmul g q)‖ₑ ≤ 1 * ‖ft P (dsmul g q)‖ₑ := by
          gcongr; exact enorm_ff_le_one P q
      _ = _ := one_mul _
  have hsum : Summable fun k : ℤ =>
      ∫ q, ft P (dsmul (ModularGroup.T ^ (-k)) q) * conj (ft P (dsmul g q)) := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hfin) fun k => ?_
    exact norm_integral_le_toReal _
  convert hsum.hasSum using 1
  rw [← integral_tsum hmeas hfin]
  congr 1; funext q
  rw [tsum_mul_right, tsum_ft_T]

/-! ### The layer `c ≠ 0` -/

/-- `K(t) = ∫ ff(q) 1_{[0,1)}(t + Re ι_c q₁) conj ff(ι_c q)`. -/
noncomputable def Kint (c : ℝ) (hc : c ≠ 0) (t : ℝ) : ℂ :=
  ∫ q, ff P q * ((Ico (0 : ℝ) 1).indicator (1 : ℝ → ℂ) (t + (gcGL c hc • q.1).re) *
    conj (ff P (dGL (gcGL c hc) q)))

/-- `J(c) = ∫ ff · conj(ff ∘ ι_c)`. -/
noncomputable def Jc (c : ℝ) (hc : c ≠ 0) : ℂ :=
  ∫ q, ff P q * conj (ff P (dGL (gcGL c hc) q))

/-- `J⁺(c) = ∫⁻ ‖ff‖ ‖ff ∘ ι_c‖`. -/
noncomputable def Jp (c : ℝ) (hc : c ≠ 0) : ℝ≥0∞ :=
  ∫⁻ q, ‖ff P q‖ₑ * ‖ff P (dGL (gcGL c hc) q)‖ₑ

lemma measurable_ff_dGL (g : GL (Fin 2) ℝ) : Measurable fun q => ff P (dGL g q) :=
  (measurable_ff P).comp (measurePreserving_dGL g).measurable

lemma measurable_gc_re (c : ℝ) (hc : c ≠ 0) : Measurable fun q : ℍ × ℍ => (gcGL c hc • q.1).re :=
  measurable_re_H.comp ((measurable_const_smul _).comp measurable_fst)

/-- `ft(γq) = 1(a/c + Re ι τ z) e(ha/c) ff(ι τ q)`. -/
lemma ft_smul_decomp (γ : SL(2, ℤ)) (hc : ((γ 1 0 : ℤ) : ℝ) ≠ 0) (q : ℍ × ℍ) :
    ft P (dsmul γ q) = (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℂ)
        ((γ 0 0 : ℝ) / γ 1 0 + (gcGL (γ 1 0 : ℝ) hc • (dGL (tauGL ((γ 1 1 : ℝ) / γ 1 0)) q).1).re) *
      (cexp (2 * π * I * P.h * ((γ 0 0 : ℝ) / γ 1 0)) *
        ff P (dGL (gcGL (γ 1 0 : ℝ) hc) (dGL (tauGL ((γ 1 1 : ℝ) / γ 1 0)) q))) := by
  rw [ft_eq_ind, dsmul_eq_decomp γ hc, ff_tau]
  have hiff : (dGL (tauGL ((γ 0 0 : ℝ) / γ 1 0)) (dGL (gcGL (γ 1 0 : ℝ) hc)
      (dGL (tauGL ((γ 1 1 : ℝ) / γ 1 0)) q))).1 ∈ strip ↔ ((γ 0 0 : ℝ) / γ 1 0 +
      (gcGL (γ 1 0 : ℝ) hc • (dGL (tauGL ((γ 1 1 : ℝ) / γ 1 0)) q).1).re) ∈ Ico (0 : ℝ) 1 := by
    simp only [dGL, strip_iff, tau_smul_re]
  congr 1
  · by_cases hm : (dGL (tauGL ((γ 0 0 : ℝ) / γ 1 0)) (dGL (gcGL (γ 1 0 : ℝ) hc)
      (dGL (tauGL ((γ 1 1 : ℝ) / γ 1 0)) q))).1 ∈ strip
    · rw [indicator_of_mem hm, indicator_of_mem (hiff.1 hm)]; rfl
    · rw [indicator_of_notMem hm, indicator_of_notMem (fun h => hm (hiff.2 h))]
  · push_cast; rfl

lemma Rg_eq_aux (a c d : ℝ) (hc : c ≠ 0) (F : ℍ × ℍ → ℂ)
    (hF : ∀ q, F q = (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℂ)
        (a / c + (gcGL c hc • (dGL (tauGL (d / c)) q).1).re) *
      (cexp (2 * π * I * P.h * (a / c)) * ff P (dGL (gcGL c hc) (dGL (tauGL (d / c)) q)))) :
    ∫ q, ff P q * conj (F q) = cexp (-2 * π * I * P.h * ((a + d) / c)) * Kint P c hc (a / c) := by
  simp_rw [hF]
  rw [← integral_dGL (tauGL (-(d / c)))]
  have e1 : ∀ q : ℍ × ℍ, dGL (tauGL (d / c)) (dGL (tauGL (-(d / c))) q) = q := by
    intro q; rw [dGL_tau_add, add_neg_cancel, dGL_tau_zero]
  simp_rw [e1, ff_tau]
  unfold Kint
  rw [← integral_const_mul]
  congr 1; funext q
  simp only [map_mul]
  have hind : conj ((Ico (0 : ℝ) 1).indicator (1 : ℝ → ℂ) (a / c + (gcGL c hc • q.1).re)) =
      (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℂ) (a / c + (gcGL c hc • q.1).re) := by
    unfold indicator; split_ifs <;> simp
  rw [hind, ← Complex.exp_conj]
  have hc2 : conj (2 * ↑π * I * ↑P.h * ((a / c : ℝ) : ℂ)) =
      -(2 * ↑π * I * ↑P.h * ((a / c : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp
  have hexp : cexp (2 * ↑π * I * ↑P.h * ((-(d / c) : ℝ) : ℂ)) * cexp (-(2 * ↑π * I * ↑P.h *
      ((a / c : ℝ) : ℂ))) = cexp (-2 * π * I * P.h * ((a + d) / c)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [← hexp]
  push_cast at hc2 ⊢
  rw [hc2]
  ring

/-- **The `c ≠ 0` formula.** -/
theorem Rg_eq (γ : SL(2, ℤ)) (hc : ((γ 1 0 : ℤ) : ℝ) ≠ 0) :
    ∫ q, ff P q * conj (ft P (dsmul γ q)) =
      cexp (-2 * π * I * P.h * ((((γ 0 0 : ℤ) : ℝ) + ((γ 1 1 : ℤ) : ℝ)) / ((γ 1 0 : ℤ) : ℝ))) *
        Kint P ((γ 1 0 : ℤ) : ℝ) hc (((γ 0 0 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ)) :=
  Rg_eq_aux P _ _ _ hc _ (ft_smul_decomp P γ hc)

/-- **The left coset sum.** -/
theorem hasSum_K (c : ℝ) (hc : c ≠ 0) (hJ : Jp P c hc ≠ ∞) (t : ℝ) :
    HasSum (fun m : ℤ => Kint P c hc (t + m)) (Jc P c hc) := by
  have hmeas : ∀ m : ℤ, AEStronglyMeasurable (fun q => ff P q *
      ((Ico (0 : ℝ) 1).indicator (1 : ℝ → ℂ) ((t + m) + (gcGL c hc • q.1).re) *
        conj (ff P (dGL (gcGL c hc) q)))) volume := by
    intro m
    refine ((measurable_ff P).mul (Measurable.mul ?_
      (Complex.continuous_conj.measurable.comp (measurable_ff_dGL P _)))).aestronglyMeasurable
    exact (measurable_one.indicator measurableSet_Ico).comp
      (measurable_const.add (measurable_gc_re c hc))
  have hpt : ∀ (m : ℤ) (q : ℍ × ℍ), ‖ff P q * ((Ico (0 : ℝ) 1).indicator (1 : ℝ → ℂ)
      ((t + m) + (gcGL c hc • q.1).re) * conj (ff P (dGL (gcGL c hc) q)))‖ₑ =
      (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) ((t + (gcGL c hc • q.1).re) + m) *
        (‖ff P q‖ₑ * ‖ff P (dGL (gcGL c hc) q)‖ₑ) := by
    intro m q
    rw [enorm_mul, enorm_mul, RCLike.enorm_conj]
    have : (t + m) + (gcGL c hc • q.1).re = (t + (gcGL c hc • q.1).re) + m := by ring
    rw [this]
    unfold indicator; split_ifs <;> simp
  have hstripE : ∀ s : ℝ, ∑' m : ℤ, (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) (s + m) = 1 := by
    intro s
    have := tsum_strip_shift s
    have hmem : ∀ m : ℤ, s + m ∈ Ico (0 : ℝ) 1 ↔ m = -⌊s⌋ := by
      intro m
      simp only [mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩
        have : ⌊s⌋ = -m := by
          rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
        omega
      · rintro rfl
        push_cast
        constructor <;> linarith [Int.floor_le s, Int.lt_floor_add_one s]
    rw [tsum_eq_single (-⌊s⌋) (fun m hm => indicator_of_notMem (fun h => hm ((hmem m).1 h)) _)]
    rw [indicator_of_mem ((hmem _).2 rfl)]
    rfl
  have hfin : ∑' m : ℤ, ∫⁻ q, ‖ff P q * ((Ico (0 : ℝ) 1).indicator (1 : ℝ → ℂ)
      ((t + m) + (gcGL c hc • q.1).re) * conj (ff P (dGL (gcGL c hc) q)))‖ₑ ≠ ∞ := by
    simp_rw [hpt]
    have hF : ∀ m : ℤ, Measurable fun q : ℍ × ℍ => (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞)
        ((t + (gcGL c hc • q.1).re) + m) * (‖ff P q‖ₑ * ‖ff P (dGL (gcGL c hc) q)‖ₑ) := fun m =>
      ((measurable_one.indicator measurableSet_Ico).comp
        ((measurable_const.add (measurable_gc_re c hc)).add measurable_const)).mul
        ((measurable_ff P).enorm.mul (measurable_ff_dGL P _).enorm)
    rw [← lintegral_tsum fun m => (hF m).aemeasurable]
    simp_rw [ENNReal.tsum_mul_right, hstripE, one_mul]
    exact hJ
  have hsum := Summable.of_norm_bounded (ENNReal.summable_toReal hfin)
    (fun m => norm_integral_le_toReal _)
  unfold Kint
  convert hsum.hasSum using 1
  unfold Jc
  rw [← integral_tsum hmeas hfin]
  congr 1; funext q
  rw [tsum_mul_left, tsum_mul_right]
  have := tsum_strip_shift (t + (gcGL c hc • q.1).re)
  have e : ∀ m : ℤ, (t + m) + (gcGL c hc • q.1).re = (t + (gcGL c hc • q.1).re) + m :=
    fun m => by ring
  simp_rw [e, this, one_mul]

end RamanujanTau.SCSProof
