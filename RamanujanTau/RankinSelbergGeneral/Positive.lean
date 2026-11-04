/-
# Positivity of `‖f‖²` and the two-sided bound for every nonzero level-one cusp form

* `Horo.petNormSq_pos_of`: for any `HoroFn`, if `G > 0` at one interior point of `𝓕` with
  `Im > 1`, then `∫_𝓕 G dμ > 0` (open set of positive Lebesgue measure).
* `exists_ne_zero_near`: a nonzero cusp form does not vanish identically near `2i` (identity
  theorem on the connected upper half-plane).
* `petNormSqF_pos`: `‖f‖² > 0` for `f ≠ 0`; hence the Rankin–Selberg constant is positive.
* `rankinSelberg_two_sided`: with `n₀` the index of the first nonzero coefficient,
  `c₁ N ≤ ∑_{n≤N} |a(n)|²/n^{k−1} ≤ c₂ N` for every `N ≥ n₀`, and the sum is `0` for `N < n₀`.
* `rankinSelberg_isTheta`: `∑_{n≤N} |a(n)|²/n^{k−1} = Θ(N)`.
-/
import RamanujanTau.RankinSelbergGeneral.Cusp

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.RankinSelbergGeneral.Horo

open Finset Real Filter Topology MeasureTheory Set
open RamanujanTau.EisensteinReal.Horo
open HoroFn
open UpperHalfPlane hiding I

variable [HoroFn]

/-- `∫_𝓕 G dμ > 0` as soon as `G > 0` at one point `p₀` with `Im p₀ > 1`, `|Re p₀| < 1/2`. -/
theorem petNormSq_pos_of {p₀ : ℝ × ℝ} (h1 : 1 < p₀.2) (h2 : |p₀.1| < 1 / 2)
    (h3 : 0 < G (gpt p₀.1 p₀.2)) : 0 < petNormSq := by
  obtain ⟨M, -, hM⟩ := exists_G_le
  have hnn : 0 ≤ᵐ[volume.restrict Freg] gR := by
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Freg]
    exact Eventually.of_forall fun p _ => div_nonneg (G_nonneg _) (by positivity)
  rw [petNormSq_eq, setIntegral_pos_iff_support_of_nonneg_ae hnn (integrableOn_gR hM)]
  set W : Set (ℝ × ℝ) := ({p | 1 < p.2} ∩ {p | |p.1| < 1 / 2}) ∩ {p | 0 < G (gpt p.1 p.2)}
  have hWo : IsOpen W :=
    ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_fst.abs continuous_const)).inter
      (isOpen_lt continuous_const (continuous_G.comp continuous_gpt))
  have hWne : W.Nonempty := ⟨p₀, ⟨h1, h2⟩, h3⟩
  have hsub : W ⊆ Function.support gR ∩ Freg := by
    rintro p ⟨⟨hp1, hp2⟩, hp3⟩
    have hp1' : (1 : ℝ) < p.2 := hp1
    refine ⟨?_, ?_⟩
    · simp only [Function.mem_support, gR]
      exact (div_pos hp3 (by positivity)).ne'
    · exact ⟨by linarith, le_of_lt hp2, by nlinarith [sq_nonneg p.1]⟩
  exact (hWo.measure_pos volume hWne).trans_le (measure_mono hsub)

end RamanujanTau.RankinSelbergGeneral.Horo

namespace RamanujanTau.RankinSelbergGeneral

open Finset Real Filter Topology MeasureTheory Asymptotics
open Complex ModularForm
open RamanujanTau.RankinSelberg hiding G G_smul continuous_G G_pos
open UpperHalfPlane hiding I
open scoped MatrixGroups

variable {k : ℕ}

/-- A nonzero level-one cusp form does not vanish on the whole disc `|z − 2i| < 1/4`. -/
lemma exists_ne_zero_near (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    ∃ z : ℍ, dist (z : ℂ) (2 * Complex.I) < 1 / 4 ∧ f z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hf
  set F : ℂ → ℂ := f ∘ UpperHalfPlane.ofComplex with hF
  have han : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)).analyticOnNhd
      isOpen_upperHalfPlaneSet
  have h0 : (2 * Complex.I) ∈ {z : ℂ | 0 < z.im} := by simp
  have hev : F =ᶠ[𝓝 (2 * Complex.I)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (2 * Complex.I) (by norm_num : (0 : ℝ) < 1 / 4)]
      with w hw
    have hw' : dist w (2 * Complex.I) < 1 / 4 := hw
    have him : 0 < w.im := by
      have h := Complex.abs_im_le_norm (w - 2 * Complex.I)
      rw [← dist_eq_norm] at h
      simp only [Complex.sub_im, Complex.mul_im] at h
      norm_num at h
      have := (abs_lt.1 (lt_of_le_of_lt h hw')).1
      linarith
    simp only [hF, Function.comp, Pi.zero_apply]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
    exact hcon ⟨w, him⟩ hw'
  have hEq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (Convex.isPreconnected (convex_halfSpace_im_gt 0)) h0 hev
  ext z
  have := hEq z.im_pos
  simp only [hF, Function.comp, Pi.zero_apply, UpperHalfPlane.ofComplex_apply] at this
  simpa using this

/-- **`‖f‖² > 0` for every nonzero level-one cusp form.** -/
theorem petNormSqF_pos (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) : 0 < petNormSqF f := by
  letI := horoFn f
  obtain ⟨z, hz, hfz⟩ := exists_ne_zero_near f hf
  have hre : |z.re| < 1 / 2 := by
    have h := Complex.abs_re_le_norm ((z : ℂ) - 2 * Complex.I)
    rw [← dist_eq_norm] at h
    simp only [Complex.sub_re, Complex.mul_re] at h
    norm_num at h
    exact lt_of_le_of_lt h (by linarith)
  have him : 1 < z.im := by
    have h := Complex.abs_im_le_norm ((z : ℂ) - 2 * Complex.I)
    rw [← dist_eq_norm] at h
    simp only [Complex.sub_im, Complex.mul_im] at h
    norm_num at h
    have := (abs_lt.1 (lt_of_le_of_lt h hz)).1
    linarith
  have hG : 0 < Gf f (Horo.gpt z.re z.im) := by
    rw [Horo.gpt_eq (by linarith)]
    unfold Gf
    have := z.im_pos
    have : 0 < ‖f z‖ := norm_pos_iff.2 hfz
    positivity
  exact Horo.petNormSq_pos_of (p₀ := (z.re, z.im)) him hre hG

/-- The partial sum `S(N) = ∑_{n ≤ N} |a(n)|²/n^{k−1}`. -/
noncomputable def S (f : CuspForm 𝒮ℒ (k : ℤ)) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1)

/-- The Rankin–Selberg constant `c_f = (3/π)(4π)^k ‖f‖²/(k−1)!`. -/
noncomputable def rsConst (f : CuspForm 𝒮ℒ (k : ℤ)) : ℝ :=
  3 / π * (4 * π) ^ k * petNormSqF f / (Nat.factorial (k - 1) : ℝ)

lemma rsConst_pos (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) : 0 < rsConst f := by
  have := petNormSqF_pos f hf
  unfold rsConst; positivity

lemma tendsto_S (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => S f N / N) atTop (𝓝 (rsConst f)) :=
  rankinSelberg_asymptotic f hk

lemma term_nonneg (f : CuspForm 𝒮ℒ (k : ℤ)) (n : ℕ) : 0 ≤ coeffSq f n / (n : ℝ) ^ (k - 1) :=
  div_nonneg (sq_nonneg _) (by positivity)

/-- A nonzero cusp form of weight `k ≥ 1` has a nonzero coefficient. -/
lemma exists_coeff_ne_zero (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hk : 1 ≤ k) :
    ∃ n, 1 ≤ n ∧ coeffSq f n ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : ∀ N, S f N = 0 := fun N => Finset.sum_eq_zero fun n hn => by
    rw [h n (Finset.mem_Icc.1 hn).1, zero_div]
  have := tendsto_S f hk
  simp only [h0, zero_div] at this
  exact (rsConst_pos f hf).ne' (tendsto_nhds_unique this tendsto_const_nhds)

/-- **Two-sided bound for every nonzero level-one cusp form.** With `n₀` the first index with
`a(n₀) ≠ 0`: `S(N) = 0` for `N < n₀`, and `c₁N ≤ S(N) ≤ c₂N` for every `N ≥ n₀`. -/
theorem rankinSelberg_two_sided (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hk : 1 ≤ k) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ coeffSq f n₀ ≠ 0 ∧ (∀ N < n₀, S f N = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ N ≥ n₀, c₁ * N ≤ S f N ∧ S f N ≤ c₂ * N := by
  classical
  have hex := exists_coeff_ne_zero f hf hk
  set n₀ := Nat.find hex with hn₀
  obtain ⟨hn₀1, hn₀ne⟩ := Nat.find_spec hex
  have hmin : ∀ n, 1 ≤ n → n < n₀ → coeffSq f n = 0 := fun n h1 h2 => by
    by_contra h; exact Nat.find_min hex h2 ⟨h1, h⟩
  have hzero : ∀ N < n₀, S f N = 0 := fun N hN => Finset.sum_eq_zero fun n hn => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    rw [hmin n h1 (by omega), zero_div]
  refine ⟨n₀, hn₀1, hn₀ne, hzero, ?_⟩
  have hT := tendsto_S f hk
  have hc := rsConst_pos f hf
  -- upper bound: the convergent sequence `S N / N` is bounded
  obtain ⟨B, hB⟩ := hT.bddAbove_range
  -- lower bound eventually
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hT.eventually (lt_mem_nhds (half_lt_self hc)))
  set N₀ := max N₁ 1
  set b := coeffSq f n₀ / (n₀ : ℝ) ^ (k - 1)
  have hb : 0 < b := div_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hn₀ne)) (by positivity)
  have hN₀ : (0 : ℝ) < N₀ := by positivity
  refine ⟨min (rsConst f / 2) (b / N₀), max B 1, lt_min (by positivity) (by positivity),
    by positivity, fun N hN => ⟨?_, ?_⟩⟩
  · have hN1 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    by_cases hNN : N₁ ≤ N
    · have h := hN₁ N hNN
      rw [lt_div_iff₀ hN1] at h
      calc min (rsConst f / 2) (b / N₀) * N ≤ rsConst f / 2 * N :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hN1.le
        _ ≤ S f N := h.le
    · have hSb : b ≤ S f N :=
        Finset.single_le_sum (f := fun n => coeffSq f n / (n : ℝ) ^ (k - 1))
          (fun n _ => term_nonneg f n) (Finset.mem_Icc.2 ⟨hn₀1, hN⟩)
      have hNlt : (N : ℝ) ≤ N₀ := by
        have : N ≤ N₀ := le_trans (by omega) (le_max_left _ _)
        exact_mod_cast this
      calc min (rsConst f / 2) (b / N₀) * N ≤ b / N₀ * N :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hN1.le
        _ ≤ b / N₀ * N₀ := mul_le_mul_of_nonneg_left hNlt (by positivity)
        _ = b := by field_simp
        _ ≤ S f N := hSb
  · have hN1 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have h := hB ⟨N, rfl⟩
    simp only at h
    rw [div_le_iff₀ hN1] at h
    calc S f N ≤ B * N := h
      _ ≤ max B 1 * N := mul_le_mul_of_nonneg_right (le_max_left _ _) hN1.le

/-- **`∑_{n≤N} |a(n)|²/n^{k−1} = Θ(N)`** for every nonzero level-one cusp form. -/
theorem rankinSelberg_isTheta (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hk : 1 ≤ k) :
    (fun N : ℕ => S f N) =Θ[atTop] (fun N : ℕ => (N : ℝ)) := by
  obtain ⟨n₀, -, -, -, c₁, c₂, hc₁, hc₂, hb⟩ := rankinSelberg_two_sided f hf hk
  have hS : ∀ N, 0 ≤ S f N := fun N => Finset.sum_nonneg fun n _ => term_nonneg f n
  refine ⟨IsBigO.of_bound c₂ ?_, IsBigO.of_bound c₁⁻¹ ?_⟩
  · filter_upwards [eventually_ge_atTop n₀] with N hN
    rw [Real.norm_of_nonneg (hS N), Real.norm_of_nonneg (Nat.cast_nonneg N)]
    exact (hb N hN).2
  · filter_upwards [eventually_ge_atTop n₀] with N hN
    rw [Real.norm_of_nonneg (hS N), Real.norm_of_nonneg (Nat.cast_nonneg N)]
    have := (hb N hN).1
    rw [inv_mul_eq_div, le_div_iff₀ hc₁]
    linarith

/-- The Rankin–Selberg asymptotic in terms of `S` and the positive constant `c_f`. -/
theorem rankinSelberg_asymptotic_pos (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hk : 1 ≤ k) :
    0 < rsConst f ∧ Tendsto (fun N : ℕ => S f N / N) atTop (𝓝 (rsConst f)) :=
  ⟨rsConst_pos f hf, tendsto_S f hk⟩

end RamanujanTau.RankinSelbergGeneral

#print axioms RamanujanTau.RankinSelbergGeneral.Horo.petNormSq_pos_of
#print axioms RamanujanTau.RankinSelbergGeneral.petNormSqF_pos
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_two_sided
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_isTheta
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_asymptotic_pos
