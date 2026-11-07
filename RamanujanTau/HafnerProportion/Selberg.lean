/-
# Hafner's positive proportion for `L(Δ,s)`, conditional on Selberg's mean values

`SelbergHyp` (named hypothesis, mentions no zeros): for every `K ≥ 1` and every large `T` there is
a mollifier `M = Σ_{n≤y} b(n) n^{11/2−s}` with `b(1) = 1`, `|b(n)| ≤ β n^η`, `y^{2+2η} ≤ T^{1/4}`
(so `y ≤ T^{1/8}` at most) such that, with `h = K / log T`,

* (MV2) the mollified second moment  `∫_T^{3T} |L(Δ,6+iu) M(6+iu)²|² du ≤ B T`;
* (SK)  Selberg's key lemma          `∫_T^{2T} I(t)² dt ≤ (D/√K) T h²`,
        `I(t) = ∫_t^{t+h} Z(u)|M(6+iu)|² du`;

with `β, η, B, D` independent of `K` and `T`.  (H1) is proved here unconditionally
(`FirstMoment.mollified_first_moment` + `Reduce.double_lower`), (H2) follows from (MV2)
(`Reduce.sq_integral_le`, `Reduce.double_upper`), and `Abstract.selberg_zeros` counts.
-/
import RamanujanTau.HafnerProportion.FirstMoment

set_option autoImplicit false

namespace RamanujanTau.HafnerProportion

open Complex MeasureTheory Set Filter
open RamanujanTau.HeckeL
open scoped Real

/-- **Named hypothesis**: the mollified second moment (MV2) and Selberg's key lemma (SK). -/
def SelbergHyp : Prop :=
  ∃ β η B D : ℝ, 0 ≤ β ∧ 0 ≤ η ∧ η ≤ 1 ∧ 0 < B ∧ 0 ≤ D ∧
    ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∃ (b : ℕ → ℂ) (y : ℕ), 1 ≤ y ∧ b 1 = 1 ∧ (∀ n : ℕ, ‖b n‖ ≤ β * (n : ℝ) ^ η) ∧
        (y : ℝ) ^ (2 + 2 * η) ≤ T ^ (1 / 4 : ℝ) ∧
        (∫ u in T..(3 * T), ‖tauL (6 + u * I) * Mc b y (6 + u * I) ^ 2‖ ^ 2) ≤ B * T ∧
        (∫ t in Icc T (2 * T), selI ZH (wM b y) (K / Real.log T) t ^ 2) ≤
          D / Real.sqrt K * T * (K / Real.log T) ^ 2

/-- **(H1), unconditional**: `∫_T^{2T} J ≥ T h / 4` for `0 < h ≤ T/8`. -/
theorem selberg_H1 {β η : ℝ} (hβ : 0 ≤ β) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ (b : ℕ → ℂ) (y : ℕ), 1 ≤ y → b 1 = 1 →
      (∀ n : ℕ, ‖b n‖ ≤ β * (n : ℝ) ^ η) → (y : ℝ) ^ (2 + 2 * η) ≤ T ^ (1 / 4 : ℝ) →
      ∀ h : ℝ, 0 < h → h ≤ T / 8 →
        1 / 4 * T * h ≤ ∫ t in Icc T (2 * T), selJ ZH (wM b y) h t := by
  obtain ⟨T₀, hT₀1, hFM⟩ := mollified_first_moment hβ hη0 hη1
  refine ⟨T₀, hT₀1, fun T hT b y hy hb1 hb hyT h hh hhT => ?_⟩
  have hT1 : 1 ≤ T := le_trans hT₀1 hT
  have hG : Continuous fun u => |ZH u| * wM b y u := continuous_ZH.abs.mul (continuous_wM b y)
  have hG0 : ∀ u, 0 ≤ |ZH u| * wM b y u := fun u => mul_nonneg (abs_nonneg _) (wM_nonneg b y u)
  have hlow := double_lower (T := T) hG hG0 hh.le (by linarith)
  have hfm := hFM T hT b y hy hb1 hb hyT (T + h) (2 * T) (by linarith) (by linarith)
    (by linarith)
  have hJ : (∫ t in Icc T (2 * T), selJ ZH (wM b y) h t) =
      ∫ t in Icc T (2 * T), (∫ u in t..t + h, |ZH u| * wM b y u) := rfl
  rw [hJ]
  refine le_trans ?_ hlow
  have : T / 4 ≤ ∫ u in (T + h)..(2 * T), |ZH u| * wM b y u := by linarith
  nlinarith

/-- **(H2) from (MV2)**: `∫_T^{2T} J² ≤ B T h²` for `0 < h ≤ T`. -/
theorem selberg_H2 {b : ℕ → ℂ} {y : ℕ} {T h B : ℝ} (hT : 0 < T) (hh : 0 < h) (hhT : h ≤ T)
    (hMV : (∫ u in T..(3 * T), ‖tauL (6 + u * I) * Mc b y (6 + u * I) ^ 2‖ ^ 2) ≤ B * T) :
    ∫ t in Icc T (2 * T), selJ ZH (wM b y) h t ^ 2 ≤ B * T * h ^ 2 := by
  set G : ℝ → ℝ := fun u => |ZH u| * wM b y u with hGdef
  have hG : Continuous G := continuous_ZH.abs.mul (continuous_wM b y)
  have hG0 : ∀ u, 0 ≤ G u := fun u => mul_nonneg (abs_nonneg _) (wM_nonneg b y u)
  have hG2 : Continuous fun u => G u ^ 2 := hG.pow 2
  have hG20 : ∀ u, 0 ≤ G u ^ 2 := fun u => sq_nonneg _
  have hMV' : (∫ u in T..(3 * T), G u ^ 2) ≤ B * T := by
    refine le_of_eq_of_le ?_ hMV
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hGdef, norm_LM2_line]
  have hJc : Continuous (selJ ZH (wM b y) h) := continuous_selJ continuous_ZH (continuous_wM b y) h
  have hRc : Continuous fun t => h * ∫ u in t..t + h, G u ^ 2 :=
    continuous_const.mul (continuous_shortInt hG2 h)
  have hstep1 : ∫ t in Icc T (2 * T), selJ ZH (wM b y) h t ^ 2 ≤
      ∫ t in Icc T (2 * T), h * ∫ u in t..t + h, G u ^ 2 :=
    setIntegral_mono (hJc.pow 2).integrableOn_Icc hRc.integrableOn_Icc
      fun t => sq_integral_le hG hG0 hh
  rw [integral_const_mul] at hstep1
  have hstep2 := double_upper hG2 hG20 hh.le hT.le
  have hstep3 : (∫ u in T..(2 * T + h), G u ^ 2) ≤ ∫ u in T..(3 * T), G u ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Eventually.of_forall hG20) (hG2.intervalIntegrable _ _)
  calc _ ≤ h * ∫ t in Icc T (2 * T), ∫ u in t..t + h, G u ^ 2 := hstep1
    _ ≤ h * (h * ∫ u in T..(2 * T + h), G u ^ 2) := mul_le_mul_of_nonneg_left hstep2 hh.le
    _ ≤ h * (h * (B * T)) := by
        gcongr
        exact hstep3.trans hMV'
    _ = B * T * h ^ 2 := by ring

/-- **Hafner's theorem (positive proportion), conditional on `SelbergHyp`**:
`N₀(T) ≫ T log T`, counting distinct critical ordinates in `[T, 3T]`. -/
theorem tauL_critical_zeros_T_log_T_of_selberg (H : SelbergHyp) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, T ≤ γ ∧ γ ≤ 3 * T ∧ tauL (6 + γ * I) = 0) ∧ c * T * Real.log T ≤ S.card := by
  obtain ⟨β, η, B, D, hβ, hη0, hη1, hB, hD, hK⟩ := H
  set K : ℝ := (256 * D + 1) ^ 2 with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; nlinarith
  have hsqrt : Real.sqrt K = 256 * D + 1 := by
    rw [hKdef]; exact Real.sqrt_sq (by linarith)
  have hDK : D / Real.sqrt K ≤ (1 / 4) ^ 2 / 16 := by
    rw [hsqrt, div_le_iff₀ (by linarith)]; nlinarith
  obtain ⟨T₀, hT₀⟩ := hK K hK1
  obtain ⟨T₁, hT₁1, hH1⟩ := selberg_H1 hβ hη0 hη1
  refine ⟨5 / (256 * B * K), max (max T₀ T₁) (Real.exp (8 * K)), by positivity,
    fun T hT => ?_⟩
  have hTT₀ : T₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTT₁ : T₁ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTe : Real.exp (8 * K) ≤ T := le_trans (le_max_right _ _) hT
  have hT1 : 1 ≤ T := le_trans hT₁1 hTT₁
  have hT0 : 0 < T := by linarith
  have hlog : 8 * K ≤ Real.log T := by
    rw [← Real.log_exp (8 * K)]; exact Real.log_le_log (Real.exp_pos _) hTe
  have hlog0 : 0 < Real.log T := by linarith
  set h : ℝ := K / Real.log T with hhdef
  have hh : 0 < h := by positivity
  have hh8 : h ≤ 1 / 8 := by
    rw [hhdef, div_le_iff₀ hlog0]; linarith
  have hhT : h ≤ T / 8 := by linarith
  obtain ⟨b, y, hy, hb1, hb, hyT, hMV, hSK⟩ := hT₀ T hTT₀
  have H1 := hH1 T hTT₁ b y hy hb1 hb hyT h hh hhT
  have H2 := selberg_H2 hT0 hh (by linarith) hMV
  have H3 : ∫ t in Icc T (2 * T), selI ZH (wM b y) h t ^ 2 ≤ (1 / 4) ^ 2 / 16 * T * h ^ 2 := by
    refine hSK.trans ?_
    have : 0 ≤ T * h ^ 2 := by positivity
    nlinarith
  obtain ⟨F, hF, hcard⟩ := selberg_zeros continuous_ZH (continuous_wM b y) (wM_nonneg b y)
    hT0 hh (by norm_num : (0 : ℝ) < 1 / 4) hB H1 H2 H3
  refine ⟨F, fun γ hγ => ?_, ?_⟩
  · obtain ⟨hγI, hz⟩ := hF γ hγ
    exact ⟨hγI.1, by linarith [hγI.2], tauL_zero_of_ZH_zero hz⟩
  · refine le_trans (le_of_eq ?_) hcard
    rw [hhdef]
    field_simp
    ring

end RamanujanTau.HafnerProportion
