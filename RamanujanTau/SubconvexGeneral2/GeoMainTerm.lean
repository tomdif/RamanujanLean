/-
# Weight-`k` main-term comparison and Lipschitz bound for `cfF`
(copy of `SCSProof.Main1.main_term_le` and `SCSProof.Main4.cf_sub_le`)
-/
import RamanujanTau.SubconvexGeneral2.GeoGbounds

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral2

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.RankinSelberg RamanujanTau.SCSProof RamanujanTau.SubconvexGeneral
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (P : Par)

lemma integrable_FζF {m : ℕ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖PsiF f z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ m) :
    Integrable fun ζ : ℍ => {ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ) * ∫ y, KyF f P ζ y := by
  have hmp := measurePreserving_skew
  have hgi := integrable_gF f P hM0 hM
  have hint : Integrable (fun p : ℍ × ℍ => ({ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (p.2 : ℂ)) *
      AzF f P p.2 p.1) := by
    have := (hmp.integrable_comp hgi.aestronglyMeasurable).2 hgi
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    exact gF_skew f P p
  rw [Measure.volume_eq_prod] at hint
  have := hint.integral_prod_right
  refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
  simp only
  rw [integral_const_mul, integral_AzF f P ζ hM0 hM]

lemma integrable_KyF {m : ℕ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖PsiF f z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ m) (ζ : ℍ) :
    Integrable (KyF f P ζ) := by
  have h := integrable_HfF f P hM0 hM ζ
  rw [Measure.volume_eq_prod] at h
  exact h.integral_prod_right.congr (Filter.Eventually.of_forall fun y => integral_HfF_x f P ζ y)

/-- **Main-term comparison**, weight `k`. -/
theorem main_term_leF {m : ℕ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖PsiF f z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ m)
    (c0 : ℂ) (E : ℝ) (hE : ∀ y ∈ Icc P.Y (P.Y * (1 + P.ε)), ∀ ζ : ℍ, inB P (ζ : ℂ) →
      ‖cfF f P y ζ - c0‖ ≤ E) :
    ‖c0‖ * (mI P * mB P) ≤ ‖∫ p, PsiF f p.1 p.2 * conj (ft P p)‖ + E * (mI P * mB P) := by
  have hY := P.hY
  rw [QF_eq f P hM0 hM]
  set F := fun ζ : ℍ => {ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ) * ∫ y, KyF f P ζ y
  set F0 := fun ζ : ℍ => {ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ) * (c0 * (mI P : ℂ))
  have hF := integrable_FζF f P hM0 hM
  have hF0 : Integrable F0 := (integrable_inB_C P).mul_const _
  have hc0W : ∫ ζ, F0 ζ = c0 * ((mI P * mB P : ℝ) : ℂ) := by
    simp only [F0]
    rw [integral_mul_const, integral_inB_C]; push_cast; ring
  -- inner bound
  have hinner : ∀ ζ : ℍ, inB P (ζ : ℂ) →
      ‖(∫ y, KyF f P ζ y) - c0 * (mI P : ℂ)‖ ≤ E * mI P := by
    intro ζ hζ
    have hKi := integrable_KyF f P hM0 hM ζ
    have hc : Integrable fun y : ℝ => (Icc P.Y (P.Y * (1 + P.ε))).indicator
        (fun y => ((1 / y ^ 2 : ℝ) : ℂ) * c0) y := by
      refine (integrable_indicator_iff measurableSet_Icc).2 ?_
      exact ((integrableOn_inv_sq P).ofReal).mul_const _
    have hcint : ∫ y, (Icc P.Y (P.Y * (1 + P.ε))).indicator
        (fun y => ((1 / y ^ 2 : ℝ) : ℂ) * c0) y = c0 * (mI P : ℂ) := by
      rw [integral_indicator measurableSet_Icc, integral_mul_const, integral_complex_ofReal]
      unfold mI; ring
    rw [← hcint, ← integral_sub hKi hc]
    have hbd : ∀ y, ‖KyF f P ζ y - (Icc P.Y (P.Y * (1 + P.ε))).indicator
        (fun y => ((1 / y ^ 2 : ℝ) : ℂ) * c0) y‖ ≤
        (Icc P.Y (P.Y * (1 + P.ε))).indicator (fun y => 1 / y ^ 2 * E) y := by
      intro y
      unfold KyF
      by_cases hy : y ∈ Icc P.Y (P.Y * (1 + P.ε))
      · rw [indicator_of_mem hy, indicator_of_mem hy, indicator_of_mem hy, ← mul_sub, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg (by have := hY.trans_le hy.1; positivity)]
        gcongr
        exact hE y hy ζ hζ
      · rw [indicator_of_notMem hy, indicator_of_notMem hy, indicator_of_notMem hy]; simp
    calc ‖∫ y, (KyF f P ζ y - (Icc P.Y (P.Y * (1 + P.ε))).indicator
          (fun y => ((1 / y ^ 2 : ℝ) : ℂ) * c0) y)‖
        ≤ ∫ y, (Icc P.Y (P.Y * (1 + P.ε))).indicator (fun y => 1 / y ^ 2 * E) y :=
          norm_integral_le_of_norm_le ((integrable_indicator_iff measurableSet_Icc).2
            ((integrableOn_inv_sq P).mul_const _)) (Filter.Eventually.of_forall hbd)
      _ = E * mI P := by
          rw [integral_indicator measurableSet_Icc, integral_mul_const]; unfold mI; ring
  -- outer bound
  have hdiff : ‖(∫ ζ, F ζ) - c0 * ((mI P * mB P : ℝ) : ℂ)‖ ≤ E * (mI P * mB P) := by
    rw [← hc0W]
    have hs : ∫ ζ, (F ζ - F0 ζ) = (∫ ζ, F ζ) - ∫ ζ, F0 ζ := integral_sub hF hF0
    refine (le_of_eq (congrArg norm hs.symm)).trans ?_
    have hbd : ∀ ζ : ℍ, ‖F ζ - F0 ζ‖ ≤ {ζ : ℍ | inB P (ζ : ℂ)}.indicator (fun _ => E * mI P) ζ := by
      intro ζ
      simp only [F, F0]
      by_cases hζ : inB P (ζ : ℂ)
      · rw [indicator_of_mem (show (ζ : ℂ) ∈ {ζ : ℂ | inB P ζ} from hζ),
          indicator_of_mem (show ζ ∈ {ζ : ℍ | inB P (ζ : ℂ)} from hζ), Pi.one_apply, one_mul,
          one_mul]
        exact hinner ζ hζ
      · rw [indicator_of_notMem (show (ζ : ℂ) ∉ {ζ : ℂ | inB P ζ} from hζ),
          indicator_of_notMem (show ζ ∉ {ζ : ℍ | inB P (ζ : ℂ)} from hζ)]; simp
    have hm : MeasurableSet {ζ : ℍ | inB P (ζ : ℂ)} :=
      (measurableSet_inB P).preimage UpperHalfPlane.measurable_coe
    have hint : Integrable ({ζ : ℍ | inB P (ζ : ℂ)}.indicator (fun _ => E * mI P)) := by
      refine (integrable_indicator_iff hm).2 (integrableOn_const ?_)
      rw [← lintegral_indicator_one hm]
      refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans (le_of_eq ?_) (lintegral_B_le P))
      congr 1
    refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hbd)).trans (le_of_eq ?_)
    rw [integral_indicator hm, setIntegral_const]
    have : (volume.real {ζ : ℍ | inB P (ζ : ℂ)}) = mB P := by
      unfold mB Measure.real
      rw [← lintegral_indicator_one hm]
      congr 1
    rw [this, smul_eq_mul]; ring
  have := norm_sub_norm_le (c0 * ((mI P * mB P : ℝ) : ℂ)) (∫ ζ, F ζ)
  rw [norm_sub_rev] at hdiff
  have hW0 : 0 ≤ mI P * mB P := by
    unfold mI mB
    exact mul_nonneg (setIntegral_nonneg measurableSet_Icc fun y hy => by
      have := hY.trans_le hy.1; positivity) ENNReal.toReal_nonneg
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hW0] at this
  linarith

lemma natpow_pred_mul (j : ℕ) (x : ℝ) : (j : ℝ) * x ^ (j - 1) * x = j * x ^ j := by
  rcases j with _ | j
  · simp
  · rw [Nat.add_sub_cancel, mul_assoc, ← pow_succ]

/-- **Lipschitz bound for `cfF` on the box.** -/
theorem cfF_sub_le (hhσ : P.h * (4 * π * P.Y) ≤ 1)
    (hS1 : Summable (fun n : ℕ => n * aabsF f P.h n * Real.exp (-n * (2 * π * P.Y))))
    (hT1 : Summable (fun n : ℕ => aabsF f P.h n * Real.exp (-n * (2 * π * P.Y))))
    (hT0 : Summable (fun n : ℕ => aabsF f P.h n * Real.exp (-n * (4 * π * P.Y)))) :
    ∀ y ∈ Icc P.Y (P.Y * (1 + P.ε)), ∀ ζ : ℍ, inB P (ζ : ℂ) →
      ‖cfF f P y ζ - cfF f P P.Y (zeta0 P)‖ ≤
        (2 * P.Y * Aθ P) ^ k * (2 * π * P.Y * P.ε * (Aθ P + 2)) *
            ∑' n : ℕ, n * aabsF f P.h n * Real.exp (-n * (2 * π * P.Y)) +
          ((k : ℝ) + 1) * (2 * P.Y * Aθ P) ^ k * P.ε *
            ∑' n : ℕ, aabsF f P.h n * Real.exp (-n * (4 * π * P.Y)) := by
  intro y hy ζ hζ
  have hY := P.hY; have hε := P.hε; have hε1 := P.hε1
  have hA := Aθ_ge P
  have hy0 : 0 < y := hY.trans_le hy.1
  have hy2 : y ≤ 2 * P.Y := hy.2.trans (Y_mul_le P)
  have hyY : |y - P.Y| ≤ P.Y * P.ε := by
    rw [abs_of_nonneg (by linarith [hy.1])]; nlinarith [hy.2]
  obtain ⟨hb1, hb2, hb3⟩ := inB_bounds P hζ
  set S1 := ∑' n : ℕ, n * aabsF f P.h n * Real.exp (-n * (2 * π * P.Y))
  set T0 := ∑' n : ℕ, aabsF f P.h n * Real.exp (-n * (4 * π * P.Y))
  have hS1n : 0 ≤ S1 := tsum_nonneg fun n =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (aabsF_nonneg f _ _)) (Real.exp_pos _).le
  have hT0n : 0 ≤ T0 := tsum_nonneg fun n => mul_nonneg (aabsF_nonneg f _ _) (Real.exp_pos _).le
  set u : ℂ := (y : ℂ) * (I - conj (ζ : ℂ))
  set u0 : ℂ := (P.Y : ℂ) * (I - conj ((zeta0 P : ℍ) : ℂ))
  set Wv : ℂ := 2 * π * y * (1 + I * conj (ζ : ℂ))
  set W0 : ℂ := 2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ))
  set e : ℝ := Real.exp (-2 * π * P.h * y)
  set e0 : ℝ := Real.exp (-2 * π * P.h * P.Y)
  have hcf : cfF f P y ζ = u ^ k * (e : ℂ) * GhF f P.h Wv := rfl
  have hc0 : cfF f P P.Y (zeta0 P) = u0 ^ k * (e0 : ℂ) * GhF f P.h W0 := rfl
  have hu : ‖u‖ ≤ 2 * P.Y * Aθ P := by
    simp only [u]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hy0.le]
    calc y * ‖I - conj (ζ : ℂ)‖ ≤ (2 * P.Y) * Aθ P := by
          gcongr; exact norm_I_sub_conj P hζ
      _ = _ := by ring
  have hu0 : ‖u0‖ ≤ 2 * P.Y * Aθ P := by
    simp only [u0]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hY.le]
    calc P.Y * ‖I - conj ((zeta0 P : ℍ) : ℂ)‖ ≤ (2 * P.Y) * Aθ P := by
          gcongr
          · linarith
          · exact norm_I_sub_conj P (inB_zeta0 P)
      _ = _ := by ring
  have huu : ‖u - u0‖ ≤ P.Y * P.ε * (Aθ P + 2) := by
    have e1 : u - u0 = ((y - P.Y : ℝ) : ℂ) * (I - conj (ζ : ℂ)) +
        (P.Y : ℂ) * conj ((zeta0 P : ℍ) - (ζ : ℂ)) := by
      simp only [u, u0, map_sub]; push_cast; ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_conj,
      Real.norm_eq_abs, Real.norm_of_nonneg hY.le]
    have h1 := norm_I_sub_conj P hζ
    have h2 : ‖((zeta0 P : ℍ) : ℂ) - (ζ : ℂ)‖ ≤ 2 * P.ε := by
      rw [norm_sub_rev]; exact norm_sub_zeta0 P hζ
    calc |y - P.Y| * ‖I - conj (ζ : ℂ)‖ + P.Y * ‖((zeta0 P : ℍ) : ℂ) - (ζ : ℂ)‖
        ≤ (P.Y * P.ε) * Aθ P + P.Y * (2 * P.ε) := by gcongr
      _ = _ := by ring
  have hWW : ‖Wv - W0‖ ≤ 2 * π * P.Y * P.ε * (Aθ P + 2) := by
    have e1 : Wv - W0 = 2 * π * ((((y - P.Y : ℝ) : ℂ) * (1 + I * conj (ζ : ℂ))) +
        (P.Y : ℂ) * (I * conj ((ζ : ℂ) - (zeta0 P : ℂ)))) := by
      simp only [Wv, W0, map_sub]; push_cast; ring
    rw [e1, norm_mul]
    have h2π : ‖(2 * π : ℂ)‖ = 2 * π := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [h2π]
    have : ‖((y - P.Y : ℝ) : ℂ) * (1 + I * conj (ζ : ℂ)) + (P.Y : ℂ) * (I * conj ((ζ : ℂ) -
        (zeta0 P : ℂ)))‖ ≤ P.Y * P.ε * (Aθ P + 2) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I,
        Complex.norm_conj, Real.norm_eq_abs, Real.norm_of_nonneg hY.le, one_mul]
      have h1 := norm_one_add_I_conj P hζ
      have h2 := norm_sub_zeta0 P hζ
      calc |y - P.Y| * ‖1 + I * conj (ζ : ℂ)‖ + P.Y * ‖(ζ : ℂ) - (zeta0 P : ℂ)‖
          ≤ (P.Y * P.ε) * Aθ P + P.Y * (2 * P.ε) := by gcongr
        _ = _ := by ring
    calc 2 * π * ‖_‖ ≤ 2 * π * (P.Y * P.ε * (Aθ P + 2)) := by gcongr
      _ = _ := by ring
  have hReW : 2 * π * P.Y ≤ Wv.re := by
    simp only [Wv]; rw [re_W]
    have : 2 * π * P.Y * 1 ≤ 2 * π * y * (1 + (ζ : ℂ).im) := by
      gcongr
      · linarith [hy.1]
      · linarith
    linarith
  have hReW0 : W0.re = 4 * π * P.Y := by
    simp only [W0]; rw [re_W, coe_zeta0]; simp; ring
  have hG := norm_GhF_sub_le f P.h hReW (by rw [hReW0]; nlinarith [Real.pi_pos]) hS1 hT1
  have hG0 : ‖GhF f P.h W0‖ ≤ T0 := by
    have := norm_GhF_le f P.h W0 (by rw [hReW0]; exact hT0)
    rwa [hReW0] at this
  have he1 : e ≤ 1 := Real.exp_le_one_iff.2 (by
    have hh : (0 : ℝ) ≤ P.h := Nat.cast_nonneg _
    have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * π) hh) hy0.le
    linarith)
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hee : |e - e0| ≤ P.ε / 2 := by
    have hh : (0 : ℝ) ≤ P.h := Nat.cast_nonneg _
    have := real_exp_sub_le (a := 2 * π * P.h * y) (b := 2 * π * P.h * P.Y) (by positivity)
      (by positivity)
    simp only [e, e0]
    rw [show -2 * π * P.h * y = -(2 * π * P.h * y) by ring,
      show -2 * π * P.h * P.Y = -(2 * π * P.h * P.Y) by ring]
    refine this.trans ?_
    rw [show 2 * π * P.h * y - 2 * π * P.h * P.Y = 2 * π * P.h * (y - P.Y) by ring, abs_mul,
      abs_of_nonneg (by positivity)]
    calc 2 * π * P.h * |y - P.Y| ≤ 2 * π * P.h * (P.Y * P.ε) := by gcongr
      _ = (P.h * (4 * π * P.Y)) * (P.ε / 2) := by ring
      _ ≤ 1 * (P.ε / 2) := by gcongr
      _ = _ := one_mul _
  -- the decomposition
  rw [hcf, hc0]
  have hsplit : u ^ k * (e : ℂ) * GhF f P.h Wv - u0 ^ k * (e0 : ℂ) * GhF f P.h W0 =
      u ^ k * (e : ℂ) * (GhF f P.h Wv - GhF f P.h W0) +
        ((u ^ k - u0 ^ k) * (e : ℂ) + u0 ^ k * ((e - e0 : ℝ) : ℂ)) * GhF f P.h W0 := by
    push_cast; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hm : 0 ≤ 2 * P.Y * Aθ P := by positivity
  have hpow := powk_sub_le k u u0 hu hu0
  have t1 : ‖u ^ k * (e : ℂ) * (GhF f P.h Wv - GhF f P.h W0)‖ ≤
      (2 * P.Y * Aθ P) ^ k * (2 * π * P.Y * P.ε * (Aθ P + 2)) * S1 := by
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg he0]
    calc ‖u‖ ^ k * e * ‖GhF f P.h Wv - GhF f P.h W0‖ ≤ (2 * P.Y * Aθ P) ^ k * 1 *
          (‖Wv - W0‖ * S1) := by gcongr
      _ ≤ (2 * P.Y * Aθ P) ^ k * 1 * ((2 * π * P.Y * P.ε * (Aθ P + 2)) * S1) := by gcongr
      _ = _ := by ring
  have t2 : ‖((u ^ k - u0 ^ k) * (e : ℂ) + u0 ^ k * ((e - e0 : ℝ) : ℂ)) * GhF f P.h W0‖ ≤
      ((k : ℝ) + 1) * (2 * P.Y * Aθ P) ^ k * P.ε * T0 := by
    rw [norm_mul]
    have hin : ‖(u ^ k - u0 ^ k) * (e : ℂ) + u0 ^ k * ((e - e0 : ℝ) : ℂ)‖ ≤
        ((k : ℝ) + 1) * (2 * P.Y * Aθ P) ^ k * P.ε := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg he0, Real.norm_eq_abs]
      have hk : (k : ℝ) * (2 * P.Y * Aθ P) ^ (k - 1) * ‖u - u0‖ ≤
          (k : ℝ) * (2 * P.Y * Aθ P) ^ k * P.ε := by
        calc (k : ℝ) * (2 * P.Y * Aθ P) ^ (k - 1) * ‖u - u0‖
            ≤ (k : ℝ) * (2 * P.Y * Aθ P) ^ (k - 1) * (P.Y * P.ε * (Aθ P + 2)) := by gcongr
          _ ≤ (k : ℝ) * (2 * P.Y * Aθ P) ^ (k - 1) * ((2 * P.Y * Aθ P) * P.ε) := by
              have : P.Y * P.ε * (Aθ P + 2) ≤ (2 * P.Y * Aθ P) * P.ε := by
                nlinarith [mul_pos hY hε]
              exact mul_le_mul_of_nonneg_left this (by positivity)
          _ = (k : ℝ) * (2 * P.Y * Aθ P) ^ (k - 1) * (2 * P.Y * Aθ P) * P.ε := by ring
          _ = _ := by rw [natpow_pred_mul]
      calc ‖u ^ k - u0 ^ k‖ * e + ‖u0‖ ^ k * |e - e0|
          ≤ ((k : ℝ) * (2 * P.Y * Aθ P) ^ (k - 1) * ‖u - u0‖) * 1 +
              (2 * P.Y * Aθ P) ^ k * (P.ε / 2) := by
            gcongr
        _ ≤ (k : ℝ) * (2 * P.Y * Aθ P) ^ k * P.ε + (2 * P.Y * Aθ P) ^ k * P.ε := by
            have : 0 ≤ (2 * P.Y * Aθ P) ^ k * P.ε := by positivity
            nlinarith
        _ = ((k : ℝ) + 1) * (2 * P.Y * Aθ P) ^ k * P.ε := by ring
    calc _ ≤ ((k : ℝ) + 1) * (2 * P.Y * Aθ P) ^ k * P.ε * T0 := by gcongr
      _ = _ := rfl
  linarith

end RamanujanTau.SubconvexGeneral2
