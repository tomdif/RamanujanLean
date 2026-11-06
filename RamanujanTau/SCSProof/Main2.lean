/-
# Lower bounds for `m_I`, `m_B` and the Lipschitz bound for `cf`
-/
import RamanujanTau.SCSProof.Main1

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.RankinSelberg
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

lemma mI_ge : P.ε / (4 * P.Y) ≤ mI P := by
  have hY := P.hY; have hε := P.hε; have hε1 := P.hε1
  unfold mI
  have hc : ∀ y ∈ Icc P.Y (P.Y * (1 + P.ε)), 1 / (P.Y * (1 + P.ε)) ^ 2 ≤ 1 / y ^ 2 := by
    intro y hy
    have : 0 < y := hY.trans_le hy.1
    gcongr; exact hy.2
  calc P.ε / (4 * P.Y) ≤ (P.Y * (1 + P.ε) - P.Y) * (1 / (P.Y * (1 + P.ε)) ^ 2) := by
        rw [div_le_iff₀ (by positivity)]
        field_simp
        have h4 : (1 + P.ε) ^ 2 ≤ 4 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h4 hε.le]
    _ = ∫ y in Icc P.Y (P.Y * (1 + P.ε)), 1 / (P.Y * (1 + P.ε)) ^ 2 := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by nlinarith), smul_eq_mul]
    _ ≤ _ := setIntegral_mono_on (integrableOn_const (by simp)) (integrableOn_inv_sq P)
        measurableSet_Icc hc

lemma mB_ge : P.ε ^ 2 ≤ mB P := by
  have hY := P.hY; have hε := P.hε; have hε1 := P.hε1
  unfold mB
  have hm : Measurable fun ζ : ℍ => {ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℝ≥0∞) (ζ : ℂ) :=
    (measurable_one.indicator (measurableSet_inB P)).comp UpperHalfPlane.measurable_coe
  have hfin : ∫⁻ ζ : ℍ, {ζ : ℂ | inB P ζ}.indicator 1 (ζ : ℂ) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_B_le P)
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin, lintegral_H _ hm]
  set box := Icc (P.θ - P.ε) (P.θ + P.ε) ×ˢ Icc (1 - P.ε) (1 + P.ε)
  have hbox : box ⊆ {p : ℝ × ℝ | 0 < p.2} := fun p hp => by
    have := hp.2.1; show 0 < p.2; linarith
  have hle : ∀ p ∈ {p : ℝ × ℝ | 0 < p.2}, box.indicator (fun _ => ENNReal.ofReal (4 / 9)) p ≤
      {ζ : ℂ | inB P ζ}.indicator 1 ((toH p : ℍ) : ℂ) * ENNReal.ofReal (1 / p.2 ^ 2) := by
    intro p hp
    by_cases hb : p ∈ box
    · rw [indicator_of_mem hb]
      have hB : ((toH p : ℍ) : ℂ) ∈ {ζ : ℂ | inB P ζ} := by
        show inB P ((toH p : ℍ) : ℂ)
        rw [coe_toH hp]
        refine ⟨?_, ?_⟩ <;> simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im] <;>
          rw [abs_le] <;> constructor <;> nlinarith [hb.1.1, hb.1.2, hb.2.1, hb.2.2]
      rw [indicator_of_mem hB, Pi.one_apply, one_mul]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : p.2 ≤ 3 / 2 := by linarith [hb.2.2]
      have h0 : 0 < p.2 := hp
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    · rw [indicator_of_notMem hb]; exact bot_le
  calc ENNReal.ofReal (P.ε ^ 2) ≤ ENNReal.ofReal (4 / 9) * volume box := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
          ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith
    _ = ∫⁻ p in {p : ℝ × ℝ | 0 < p.2}, box.indicator (fun _ => ENNReal.ofReal (4 / 9)) p := by
        rw [lintegral_indicator_const ((measurableSet_Icc.prod measurableSet_Icc)),
          Measure.restrict_apply (measurableSet_Icc.prod measurableSet_Icc),
          inter_eq_left.2 hbox]
    _ ≤ _ := setLIntegral_mono' (measurableSet_lt measurable_const measurable_snd) hle

end RamanujanTau.SCSProof
