/-
# Backlund's bound: `arg L(Δ, x+iT)` on `6 ≤ x ≤ σ₁` is `O(log T)`

`σ₁ ≥ 7` is a line with `Re L(Δ, σ₁+iy) ≥ 1/2` (`HardyCount.re_tauL_right_ge`).

The auxiliary entire function `g(z) = (L(z+iT) + L(z−iT))/2` equals `Re L(x+iT)` for real `x`
(`L(s̄) = \overline{L(s)}`).  Jensen's inequality for `g` on the discs `|z − σ₁| ≤ σ₁ − 6 < σ₁ − 5`
bounds the number of zeros of `Re L(x+iT)` on `[6, σ₁]` by `O(log T)`, and `ArgCount` turns this
into `|Im ∫₆^{σ₁} L'/L(x+iT) dx| ≤ π(#zeros + 1) = O(log T)` (`backlund`).
-/
import RamanujanTau.ZeroCountRvM.ArgCount
import RamanujanTau.ZeroCount.Jensen
import RamanujanTau.HardyCount.Contour

set_option autoImplicit false

namespace RamanujanTau.ZeroCountRvM

open Complex Set Filter Topology Metric MeromorphicOn intervalIntegral MeasureTheory
open RamanujanTau.HeckeL RamanujanTau.HeckeConvex RamanujanTau.HeckeZeros RamanujanTau.ZeroCount
open scoped ComplexConjugate Real

/-- Polynomial growth on `Re s ≥ 5`. -/
lemma tauL_growth : ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 5 ≤ s.re → ‖tauL s‖ ≤ B * (1 + ‖s‖) ^ 2 := by
  obtain ⟨A, hA0, hA⟩ := tauL_poly_bound
  obtain ⟨D, hD0, hD⟩ := tauL_bounded_of_gt (σ := 7) (by norm_num)
  refine ⟨A + D, by positivity, fun s hs => ?_⟩
  have h1 : 1 ≤ (1 + ‖s‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg s])
  rcases le_or_gt s.re 9 with h9 | h9
  · have := hA s hs h9
    nlinarith
  · have := hD s (by linarith)
    nlinarith

lemma hasDerivAt_tauL_horiz (T x : ℝ) :
    HasDerivAt (fun x : ℝ => tauL (x + T * I)) (deriv tauL (x + T * I)) x := by
  have h : HasDerivAt (fun w : ℂ => tauL (w + T * I)) (deriv tauL ((x : ℂ) + T * I)) (x : ℂ) :=
    (tauLSeries_entire _).hasDerivAt.comp_add_const _ _
  exact h.comp_ofReal

lemma continuous_deriv_tauL : Continuous (deriv tauL) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact (tauLSeries_entire.analyticAt z).deriv.continuousAt

/-- **Backlund.** -/
theorem backlund : ∃ σ₁ : ℝ, 7 ≤ σ₁ ∧ (∀ y : ℝ, 1 / 2 ≤ (tauL (σ₁ + y * I)).re) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, (∀ x ∈ Icc (6 : ℝ) σ₁, tauL (x + T * I) ≠ 0) →
      |(∫ x in (6 : ℝ)..σ₁, deriv tauL (x + T * I) / tauL (x + T * I)).im| ≤
        C * Real.log (|T| + 2) := by
  obtain ⟨σ₁, hσ₁, hre⟩ := HardyCount.re_tauL_right_ge
  obtain ⟨B, hB0, hB⟩ := tauL_growth
  set r : ℝ := σ₁ - 6 with hr
  set R : ℝ := σ₁ - 5 with hR
  have hr0 : 0 < r := by linarith
  have hrR : r < R := by linarith
  have hlam : 0 < Real.log (R / r) := Real.log_pos (by rw [one_lt_div hr0]; linarith)
  set lam := Real.log (R / r)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K₀ : ℝ := Real.log 2 + Real.log (B + 1) + 2 * Real.log (1 + 2 * σ₁) with hK₀
  have hK₀0 : 0 ≤ K₀ := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ B + 1 by linarith)
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + 2 * σ₁ by linarith)
    rw [hK₀]; linarith
  refine ⟨σ₁, hσ₁, hre, π * (K₀ / (lam * Real.log 2) + 2 / lam + 1 / Real.log 2), by positivity,
    fun T hT => ?_⟩
  set L : ℝ := Real.log (|T| + 2) with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg T])
  -- the auxiliary function
  set g : ℂ → ℂ := fun z => (tauL (z + T * I) + tauL (z - T * I)) / 2 with hg
  have hgd : Differentiable ℂ g := by
    rw [hg]
    exact ((tauLSeries_entire.comp (differentiable_id.add_const _)).add
      (tauLSeries_entire.comp (differentiable_id.sub_const _))).div_const _
  have hgreal : ∀ x : ℝ, g x = ((tauL (x + T * I)).re : ℂ) := by
    intro x
    have hc : tauL ((x : ℂ) - T * I) = conj (tauL (x + T * I)) := by
      rw [← tauL_conj]; congr 1; simp [map_add, conj_ofReal]; ring
    rw [hg]; simp only []
    rw [hc, Complex.add_conj]; push_cast; ring
  set c : ℂ := (σ₁ : ℂ)
  have hgc : 1 / 2 ≤ ‖g c‖ := by
    rw [hgreal σ₁, Complex.norm_real, Real.norm_eq_abs]
    exact (hre T).trans (le_abs_self _)
  have hgc0 : g c ≠ 0 := by intro h; rw [h, norm_zero] at hgc; norm_num at hgc
  -- bound on the big circle
  set M : ℝ := (B + 1) * (1 + 2 * σ₁ + |T|) ^ 2 with hM
  have hM1 : 1 ≤ M := by
    have h1 : 1 ≤ (1 + 2 * σ₁ + |T|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg T])
    nlinarith
  have hbound : ∀ z ∈ sphere c |R|, ‖g z‖ ≤ M := by
    intro z hz
    rw [mem_sphere, dist_eq_norm, abs_of_pos (by linarith : (0 : ℝ) < R)] at hz
    have hre5 : 5 ≤ z.re := by
      have := Complex.abs_re_le_norm (z - c)
      rw [hz, sub_re] at this
      have hcre : c.re = σ₁ := by simp [c]
      rw [hcre] at this
      linarith [(abs_le.mp this).1]
    have hzn : ‖z‖ ≤ 2 * σ₁ := by
      have : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        calc ‖z‖ = ‖(z - c) + c‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      have hcn : ‖c‖ = σ₁ := by simp [c, abs_of_pos (by linarith : (0 : ℝ) < σ₁)]
      linarith
    have hTI : ‖(T : ℂ) * I‖ = |T| := by simp
    have h1 : ‖tauL (z + T * I)‖ ≤ B * (1 + 2 * σ₁ + |T|) ^ 2 := by
      refine (hB _ (by simpa using hre5)).trans ?_
      have hn : ‖z + T * I‖ ≤ 2 * σ₁ + |T| := by
        calc ‖z + T * I‖ ≤ ‖z‖ + ‖(T : ℂ) * I‖ := norm_add_le _ _
          _ ≤ 2 * σ₁ + |T| := by linarith
      have h' : 1 + ‖z + T * I‖ ≤ 1 + 2 * σ₁ + |T| := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h' 2) hB0
    have h2 : ‖tauL (z - T * I)‖ ≤ B * (1 + 2 * σ₁ + |T|) ^ 2 := by
      refine (hB _ (by simpa using hre5)).trans ?_
      have hn : ‖z - T * I‖ ≤ 2 * σ₁ + |T| := by
        calc ‖z - T * I‖ ≤ ‖z‖ + ‖(T : ℂ) * I‖ := norm_sub_le _ _
          _ ≤ 2 * σ₁ + |T| := by linarith
      have h' : 1 + ‖z - T * I‖ ≤ 1 + 2 * σ₁ + |T| := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h' 2) hB0
    rw [hg]; simp only []
    rw [norm_div]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    have := norm_add_le (tauL (z + T * I)) (tauL (z - T * I))
    have hsq : 0 ≤ (1 + 2 * σ₁ + |T|) ^ 2 := sq_nonneg _
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have hJ := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := R) (M := M)
    (by rw [abs_of_pos hr0]; exact hr0) (by rw [abs_of_pos hr0, abs_of_pos (by linarith)]; exact hrR)
    hM1 (fun z _ => hgd.analyticAt z) hgc0 hbound
  -- divisor facts
  set U := closedBall c |r|
  set D := divisor g U
  have hfin := D.finiteSupport (isCompact_closedBall _ _)
  have hord : ∀ u, analyticOrderAt g u ≠ ⊤ := by
    intro u h
    rw [AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero u (fun z => hgd.analyticAt z)] at h
    exact hgc0 (by rw [h]; rfl)
  have hDpos : ∀ u ∈ U, g u = 0 → 1 ≤ D u := by
    intro u hu hgu
    rw [AnalyticOnNhd.divisor_apply (fun z _ => hgd.analyticAt z) hu]
    have h0 : analyticOrderAt g u ≠ 0 := analyticOrderAt_ne_zero.2 ⟨hgd.analyticAt u, hgu⟩
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hord u)
    rw [← hm]
    have : m ≠ 0 := by rintro rfl; exact h0 (by rw [← hm]; rfl)
    simp only [ENat.map_coe, WithTop.untop₀_coe]
    omega
  have hDnn : ∀ u, 0 ≤ D u := fun u => AnalyticOnNhd.divisor_nonneg (f := g) (U := U) (fun z _ => hgd.analyticAt z) u
  -- the zero set of `Re L(x+iT)` on `[6, σ₁]`
  set Z : Set ℝ := {x | x ∈ Icc (6 : ℝ) σ₁ ∧ (tauL (x + T * I)).re = 0}
  have hZU : ∀ x ∈ Z, (x : ℂ) ∈ U ∧ g x = 0 := by
    intro x hx
    refine ⟨?_, by rw [hgreal, hx.2]; simp⟩
    rw [mem_closedBall, dist_eq_norm, abs_of_pos hr0]
    have : (x : ℂ) - c = ((x - σ₁ : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hx.1.1, hx.1.2]
  have hZfin : Z.Finite := by
    apply (hfin.preimage (Complex.ofReal_injective.injOn)).subset
    intro x hx
    have := hZU x hx
    show D x ≠ 0
    have := hDpos _ this.1 this.2
    omega
  classical
  set S := hZfin.toFinset
  have hcard : (S.card : ℝ) ≤ ((∑ᶠ u, D u : ℤ) : ℝ) := by
    have himg : (S.image (fun x : ℝ => (x : ℂ))).card = S.card :=
      Finset.card_image_of_injective _ Complex.ofReal_injective
    have hle : ((S.image (fun x : ℝ => (x : ℂ))).card : ℤ) ≤ ∑ᶠ u, D u := by
      rw [finsum_eq_sum_of_support_subset (s := S.image (fun x : ℝ => (x : ℂ)) ∪ hfin.toFinset) D
        (by intro x hx; simp [hx])]
      calc ((S.image (fun x : ℝ => (x : ℂ))).card : ℤ)
          = ∑ u ∈ S.image (fun x : ℝ => (x : ℂ)), (1 : ℤ) := by simp
        _ ≤ ∑ u ∈ S.image (fun x : ℝ => (x : ℂ)), D u := by
          apply Finset.sum_le_sum
          intro u hu
          rw [Finset.mem_image] at hu
          obtain ⟨x, hx, rfl⟩ := hu
          rw [Set.Finite.mem_toFinset] at hx
          exact hDpos _ (hZU x hx).1 (hZU x hx).2
        _ ≤ ∑ u ∈ S.image (fun x : ℝ => (x : ℂ)) ∪ hfin.toFinset, D u :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun u _ _ => hDnn u)
    rw [himg] at hle
    exact_mod_cast hle
  -- the argument bound
  have harg := abs_im_integral_logDeriv_le (f := fun x : ℝ => tauL (x + T * I))
    (f' := fun x : ℝ => deriv tauL (x + T * I)) S.card 6 σ₁ (by linarith)
    (fun x _ => hasDerivAt_tauL_horiz T x)
    ((continuous_deriv_tauL.comp (by fun_prop)).continuousOn)
    hT S le_rfl (fun x hx h0 => by
      rw [Set.Finite.mem_toFinset]; exact ⟨Ioo_subset_Icc_self hx, h0⟩)
  refine harg.trans ?_
  -- arithmetic
  have hJ' : ((∑ᶠ u, D u : ℤ) : ℝ) ≤ (K₀ + 2 * L) / lam := by
    refine hJ.trans ?_
    apply div_le_div_of_nonneg_right _ hlam.le
    have hgcpos : 0 < ‖g c‖ := by linarith
    have hMpos : 0 < M := by linarith
    have h1 : Real.log (M / ‖g c‖) ≤ Real.log (2 * M) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ hgcpos]; nlinarith
    have h2 : Real.log (2 * M) = Real.log 2 + Real.log (B + 1) +
        2 * Real.log (1 + 2 * σ₁ + |T|) := by
      rw [Real.log_mul (by norm_num) hMpos.ne', hM, Real.log_mul (by linarith)
        (by positivity), Real.log_pow]; push_cast; ring
    have h3 : Real.log (1 + 2 * σ₁ + |T|) ≤ Real.log (1 + 2 * σ₁) + L := by
      rw [hL, ← Real.log_mul (by linarith) (by linarith [abs_nonneg T])]
      apply Real.log_le_log (by linarith [abs_nonneg T])
      nlinarith [abs_nonneg T]
    rw [hK₀]; linarith
  have hfac : 1 ≤ L / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
  have hfinal : (S.card : ℝ) + 1 ≤ (K₀ / (lam * Real.log 2) + 2 / lam + 1 / Real.log 2) * L := by
    have e1 : (K₀ + 2 * L) / lam = K₀ / lam + 2 / lam * L := by ring
    have e2 : K₀ / lam ≤ K₀ / (lam * Real.log 2) * L := by
      rw [div_mul_eq_div_div, div_mul_eq_mul_div, le_div_iff₀ hl2]
      have : K₀ / lam * Real.log 2 ≤ K₀ / lam * L := by
        apply mul_le_mul_of_nonneg_left hL2 (by positivity)
      linarith
    have e3 : (1 : ℝ) ≤ 1 / Real.log 2 * L := by rw [one_div_mul_eq_div]; exact hfac
    nlinarith
  calc π * ((S.card : ℝ) + 1) ≤ π * ((K₀ / (lam * Real.log 2) + 2 / lam + 1 / Real.log 2) * L) := by
        gcongr
    _ = _ := by ring

end RamanujanTau.ZeroCountRvM
