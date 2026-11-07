/-
# Bruhat decomposition, part 3: support of `J(c)` and the Kloosterman phase

* `Jp_eq_zero` (`|c| ≥ 2/Y ⇒ J⁺(c) = 0`), `Jp_le` (`J⁺(c) ≤ 64 ε³/(|c| Y)`);
* `norm_R_le`: `‖∫ ff · conj(ft ∘ γ)‖ ≤ ∫⁻ ‖ft‖`;
* `phase_sum_eq`: `Σ_{0≤r<|c|, (r,c)=1} e(−h(r + gcdA(r,c))/c)` is `S(∓h,∓h;|c|)`, so its norm is
  `‖S(h,h;|c|)‖`.
-/
import RamanujanTau.SCSProof.Bruhat2

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.TauBound
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

lemma gc_smul_im (c : ℝ) (hc : c ≠ 0) (z : ℍ) :
    (gcGL c hc • z).im = z.im / (c ^ 2 * Complex.normSq (z : ℂ)) := by
  change ((gcGL c hc • z : ℍ) : ℂ).im = _
  rw [coe_gc_smul, Complex.div_im]
  have hz : (z : ℂ) ≠ 0 := fun h => by have := z.im_pos; rw [← UpperHalfPlane.coe_im, h] at this; simp at this
  simp only [Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im, neg_zero, zero_mul,
    zero_div, sub_zero, Complex.normSq_mul]
  have h2 : ((c : ℂ) ^ 2 * z).im = c ^ 2 * z.im := by
    simp [pow_two, Complex.mul_im]
  rw [h2]
  have : Complex.normSq ((c : ℂ) ^ 2) = c ^ 4 := by
    rw [pow_two, Complex.normSq_mul, Complex.normSq_ofReal]; ring
  rw [this]
  have hn : Complex.normSq (z : ℂ) ≠ 0 := (Complex.normSq_pos.2 hz).ne'
  field_simp
  ring

/-- Both factors of `J(c)` are nonzero only in a bounded `x`-range, and only for `|c| < 2/Y`. -/
lemma ff_gc_support (c : ℝ) (hc : c ≠ 0) (q : ℍ × ℍ) (h1 : ff P q ≠ 0)
    (h2 : ff P (dGL (gcGL c hc) q) ≠ 0) :
    |c| * P.Y < 2 ∧ |q.1.re| ≤ 2 / |c| ∧ inI P q.1.im ∧ inB P (rel q.1 q.2) := by
  have hs1 : q ∈ suppF P := by
    by_contra h; exact h1 (by unfold ff; rw [if_neg h])
  have hs2 : dGL (gcGL c hc) q ∈ suppF P := by
    by_contra h; exact h2 (by unfold ff; rw [if_neg h])
  have hY := P.hY; have hε1 := P.hε1
  obtain ⟨⟨hy1, hy2⟩, hB⟩ := hs1
  obtain ⟨⟨hg1, -⟩, -⟩ := hs2
  simp only [dGL] at hg1
  rw [gc_smul_im] at hg1
  set z := q.1
  have hzi := z.im_pos
  have hn : 0 < Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_apply]; nlinarith [sq_nonneg (z : ℂ).re, show (z : ℂ).im = z.im from rfl]
  have hc2 : 0 < c ^ 2 := by positivity
  rw [le_div_iff₀ (by positivity)] at hg1
  have hnorm : c ^ 2 * Complex.normSq (z : ℂ) ≤ 3 / 2 := by
    have : P.Y * (c ^ 2 * Complex.normSq (z : ℂ)) ≤ P.Y * (3 / 2) := by nlinarith
    exact le_of_mul_le_mul_left this hY
  have hnsq : Complex.normSq (z : ℂ) = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.normSq_apply]; change z.re * z.re + z.im * z.im = _; ring
  rw [hnsq] at hnorm
  have habs : |c| ^ 2 = c ^ 2 := sq_abs c
  have hcpos : 0 < |c| := abs_pos.2 hc
  refine ⟨?_, ?_, ⟨hy1, hy2⟩, hB⟩
  · have : c ^ 2 * P.Y ^ 2 ≤ 3 / 2 := by nlinarith [sq_nonneg z.re]
    nlinarith
  · rw [le_div_iff₀ hcpos, ← abs_mul]
    have : (c * z.re) ^ 2 ≤ 2 ^ 2 := by nlinarith [sq_nonneg z.im]
    have h3 := abs_le_of_sq_le_sq' this (by norm_num : (0:ℝ) ≤ 2)
    rw [abs_le, mul_comm z.re c]; exact h3

lemma enorm_ff_mul_le (c : ℝ) (hc : c ≠ 0) (q : ℍ × ℍ) :
    ‖ff P q‖ₑ * ‖ff P (dGL (gcGL c hc) q)‖ₑ ≤
      ({z : ℍ | |c| * P.Y < 2 ∧ |z.re| ≤ 2 / |c| ∧ inI P z.im}.indicator 1 q.1) *
        {ζ : ℂ | inB P ζ}.indicator 1 (rel q.1 q.2) := by
  by_cases h1 : ff P q = 0
  · simp [h1]
  by_cases h2 : ff P (dGL (gcGL c hc) q) = 0
  · simp [h2]
  obtain ⟨a1, a2, a3, a4⟩ := ff_gc_support P c hc q h1 h2
  rw [indicator_of_mem (show q.1 ∈ {z : ℍ | |c| * P.Y < 2 ∧ |z.re| ≤ 2 / |c| ∧ inI P z.im}
    from ⟨a1, a2, a3⟩), indicator_of_mem (show rel q.1 q.2 ∈ {ζ : ℂ | inB P ζ} from a4)]
  simp only [Pi.one_apply, mul_one]
  calc ‖ff P q‖ₑ * ‖ff P (dGL (gcGL c hc) q)‖ₑ ≤ 1 * 1 :=
        mul_le_mul' (enorm_ff_le_one P q) (enorm_ff_le_one P _)
    _ = 1 := one_mul 1

lemma measurableSet_Ac (c : ℝ) :
    MeasurableSet {z : ℍ | |c| * P.Y < 2 ∧ |z.re| ≤ 2 / |c| ∧ inI P z.im} := by
  simp only [Set.setOf_and]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · by_cases h : |c| * P.Y < 2
    · simp [h]
    · simp [h]
  · exact measurableSet_le measurable_re_H.abs measurable_const
  · exact measurableSet_inI_set P

/-- `J⁺(c) ≤ 64 ε³ / (|c| Y)`, and `J⁺(c) = 0` once `|c| Y ≥ 2`. -/
theorem Jp_le (c : ℝ) (hc : c ≠ 0) :
    Jp P c hc ≤ (if |c| * P.Y < 2 then ENNReal.ofReal (64 * P.ε ^ 3 / (|c| * P.Y)) else 0) := by
  have hY := P.hY; have hε := P.hε
  have hcpos : 0 < |c| := abs_pos.2 hc
  calc Jp P c hc ≤ ∫⁻ q : ℍ × ℍ,
        ({z : ℍ | |c| * P.Y < 2 ∧ |z.re| ≤ 2 / |c| ∧ inI P z.im}.indicator 1 q.1) *
          {ζ : ℂ | inB P ζ}.indicator 1 (rel q.1 q.2) :=
        lintegral_mono fun q => enorm_ff_mul_le P c hc q
    _ = (∫⁻ z, {z : ℍ | |c| * P.Y < 2 ∧ |z.re| ≤ 2 / |c| ∧ inI P z.im}.indicator 1 z) *
          ∫⁻ ζ : ℍ, {ζ : ℂ | inB P ζ}.indicator 1 (ζ : ℂ) :=
        lintegral_rel_prod _ (measurable_one.indicator (measurableSet_Ac P c)) _
          (measurableSet_inB P)
    _ ≤ _ := by
        split_ifs with hcY
        · have hA : ∫⁻ z, {z : ℍ | |c| * P.Y < 2 ∧ |z.re| ≤ 2 / |c| ∧ inI P z.im}.indicator 1 z ≤
              ENNReal.ofReal (4 * P.ε / (|c| * P.Y)) := by
            refine (lintegral_box_le _ (measurable_one.indicator (measurableSet_Ac P c))
              (a := -(2 / |c|)) (b := 2 / |c|) (c := P.Y) (d := P.Y * (1 + P.ε)) hY
              (by have : 0 < 2 / |c| := by positivity
                  linarith) (by nlinarith)
              (fun ζ => by unfold indicator; split_ifs <;> simp) (fun ζ hζ => ?_)).trans ?_
            · have hm : ζ ∈ {z : ℍ | |c| * P.Y < 2 ∧ |z.re| ≤ 2 / |c| ∧ inI P z.im} := by
                by_contra h; exact hζ (indicator_of_notMem h _)
              obtain ⟨-, h2, h3, h4⟩ := hm
              rw [abs_le] at h2
              exact ⟨h2.1, h2.2, h3, h4⟩
            · refine le_of_eq (congrArg ENNReal.ofReal ?_)
              field_simp; ring
          calc _ ≤ ENNReal.ofReal (4 * P.ε / (|c| * P.Y)) * ENNReal.ofReal (16 * P.ε ^ 2) :=
                mul_le_mul' hA (lintegral_B_le P)
            _ = ENNReal.ofReal (64 * P.ε ^ 3 / (|c| * P.Y)) := by
                rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp; ring
        · have h0 : ∫⁻ z, {z : ℍ | |c| * P.Y < 2 ∧ |z.re| ≤ 2 / |c| ∧ inI P z.im}.indicator
              (1 : ℍ → ℝ≥0∞) z = 0 := by
            refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun z => ?_)
            exact indicator_of_notMem (fun h => hcY h.1) _
          rw [h0, zero_mul]

lemma Jp_ne_top (c : ℝ) (hc : c ≠ 0) : Jp P c hc ≠ ∞ :=
  ne_top_of_le_ne_top (by split_ifs <;> simp) (Jp_le P c hc)

/-- Generic bound `‖∫ ff · conj(ft ∘ γ)‖ ≤ ∫⁻ ‖ft‖`. -/
theorem norm_R_le (γ : SL(2, ℤ)) :
    ‖∫ q, ff P q * conj (ft P (dsmul γ q))‖ ≤ (∫⁻ q, ‖ft P q‖ₑ).toReal := by
  refine (norm_integral_le_toReal _).trans (ENNReal.toReal_mono (lintegral_ft_ne_top P) ?_)
  rw [← lintegral_ft_dsmul P γ]
  refine lintegral_mono fun q => ?_
  rw [enorm_mul, RCLike.enorm_conj]
  calc ‖ff P q‖ₑ * ‖ft P (dsmul γ q)‖ₑ ≤ 1 * ‖ft P (dsmul γ q)‖ₑ := by
        gcongr; exact enorm_ff_le_one P q
    _ = _ := one_mul _

lemma norm_Kint_le (c : ℝ) (hc : c ≠ 0) (t : ℝ) : ‖Kint P c hc t‖ ≤ (Jp P c hc).toReal := by
  refine (norm_integral_le_toReal _).trans ?_
  have hJ := Jp_ne_top P c hc
  refine ENNReal.toReal_mono hJ (lintegral_mono fun q => ?_)
  rw [enorm_mul, enorm_mul, RCLike.enorm_conj]
  calc ‖ff P q‖ₑ * (‖(Ico (0 : ℝ) 1).indicator (1 : ℝ → ℂ) (t + (gcGL c hc • q.1).re)‖ₑ *
        ‖ff P (dGL (gcGL c hc) q)‖ₑ) ≤ ‖ff P q‖ₑ * (1 * ‖ff P (dGL (gcGL c hc) q)‖ₑ) := by
        gcongr
        unfold indicator; split_ifs <;> simp
    _ = _ := by rw [one_mul]

end RamanujanTau.SCSProof
