/-
# Backlund's bound for an arbitrary entire function (no conjugation symmetry)

For an entire `G` with `Re G(σ₁+iy) ≥ 1/2` and polynomial growth on `a − 1/2 ≤ Re s ≤ 2σ₁ − a + 1/2`:

  `|Im ∫_a^{σ₁} G'/G(x+iT) dx| ≤ C log(|T|+2)`     (`backlund_gen`, every real `T`)

The Δ version (`ZeroCountRvM.backlund`) used `L(s̄) = \overline{L(s)}` to make
`g(z) = (L(z+iT) + L(z−iT))/2` real on the real axis.  For a general cusp form the coefficients
need not be real; here `G*(z) = \overline{G(\bar z)}` (entire, same growth) and
`g(z) = (G(z+iT) + G*(z−iT))/2` satisfies `g(x) = Re G(x+iT)` for real `x`.

Also `abs_re_integral_logDeriv_vert`: `|Re ∫_{y₀}^{y₁} G'/G(σ₁+iy) dy| ≤ π`.
-/
import RamanujanTau.ZeroCountRvM.ArgCount
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false

namespace RamanujanTau.GeneralZeros

open Complex Set Filter Topology Metric MeromorphicOn intervalIntegral MeasureTheory
open RamanujanTau.ZeroCountRvM
open scoped ComplexConjugate Real

lemma differentiable_conj_conj {G : ℂ → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (fun z => conj (G (conj z))) := by
  intro z
  have := (hG (conj z)).conj_conj
  simp only [Complex.conj_conj] at this
  exact this

lemma hasDerivAt_horiz {G : ℂ → ℂ} (hG : Differentiable ℂ G) (T x : ℝ) :
    HasDerivAt (fun x : ℝ => G (x + T * I)) (deriv G (x + T * I)) x := by
  have h : HasDerivAt (fun w : ℂ => G (w + T * I)) (deriv G ((x : ℂ) + T * I)) (x : ℂ) :=
    (hG _).hasDerivAt.comp_add_const _ _
  exact h.comp_ofReal

lemma continuous_deriv_of_entire {G : ℂ → ℂ} (hG : Differentiable ℂ G) :
    Continuous (deriv G) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact (hG.analyticAt z).deriv.continuousAt

/-- **Backlund, general form.** -/
theorem backlund_gen {G : ℂ → ℂ} (hG : Differentiable ℂ G) {a σ₁ B : ℝ} (ha : 1 / 2 ≤ a)
    (haσ : a < σ₁) (hB0 : 0 ≤ B)
    (hB : ∀ s : ℂ, a - 1 / 2 ≤ s.re → s.re ≤ 2 * σ₁ - a + 1 / 2 → ‖G s‖ ≤ B * (1 + ‖s‖) ^ 2)
    (hre : ∀ y : ℝ, 1 / 2 ≤ (G (σ₁ + y * I)).re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, (∀ x ∈ Icc a σ₁, G (x + T * I) ≠ 0) →
      |(∫ x in a..σ₁, deriv G (x + T * I) / G (x + T * I)).im| ≤ C * Real.log (|T| + 2) := by
  set r : ℝ := σ₁ - a with hr
  set R : ℝ := σ₁ - a + 1 / 2 with hR
  have hσ₁0 : 0 < σ₁ := by linarith
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
  have hGs := differentiable_conj_conj hG
  refine ⟨π * (K₀ / (lam * Real.log 2) + 2 / lam + 1 / Real.log 2), by positivity,
    fun T hT => ?_⟩
  set L : ℝ := Real.log (|T| + 2) with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg T])
  -- the auxiliary function
  set g : ℂ → ℂ := fun z => (G (z + T * I) + conj (G (conj (z - T * I)))) / 2 with hg
  have hgd : Differentiable ℂ g := by
    rw [hg]
    exact ((hG.comp (differentiable_id.add_const _)).add
      (hGs.comp (differentiable_id.sub_const _))).div_const _
  have hgreal : ∀ x : ℝ, g x = ((G (x + T * I)).re : ℂ) := by
    intro x
    have hc : conj ((x : ℂ) - T * I) = (x : ℂ) + T * I := by
      simp [map_sub, conj_ofReal]
    rw [hg]; simp only []
    rw [hc, Complex.add_conj]; push_cast; ring
  set c : ℂ := (σ₁ : ℂ)
  have hgc : 1 / 2 ≤ ‖g c‖ := by
    rw [hgreal σ₁, Complex.norm_real, Real.norm_eq_abs]
    have := hre T
    exact this.trans (le_abs_self _)
  have hgc0 : g c ≠ 0 := by intro h; rw [h, norm_zero] at hgc; norm_num at hgc
  -- bound on the big circle
  set M : ℝ := (B + 1) * (1 + 2 * σ₁ + |T|) ^ 2 with hM
  have hM1 : 1 ≤ M := by
    have h1 : 1 ≤ (1 + 2 * σ₁ + |T|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg T])
    nlinarith
  have hbound : ∀ z ∈ sphere c |R|, ‖g z‖ ≤ M := by
    intro z hz
    rw [mem_sphere, dist_eq_norm, abs_of_pos (by linarith : (0 : ℝ) < R)] at hz
    have hcre : c.re = σ₁ := by simp [c]
    have hreb : |z.re - σ₁| ≤ R := by
      have := Complex.abs_re_le_norm (z - c)
      rw [hz, sub_re, hcre] at this
      exact this
    have hre1 : a - 1 / 2 ≤ z.re := by linarith [(abs_le.mp hreb).1]
    have hre2 : z.re ≤ 2 * σ₁ - a + 1 / 2 := by linarith [(abs_le.mp hreb).2]
    have hzn : ‖z‖ ≤ 2 * σ₁ := by
      have : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        calc ‖z‖ = ‖(z - c) + c‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      have hcn : ‖c‖ = σ₁ := by simp [c, abs_of_pos hσ₁0]
      linarith
    have hTI : ‖(T : ℂ) * I‖ = |T| := by simp
    have h1 : ‖G (z + T * I)‖ ≤ B * (1 + 2 * σ₁ + |T|) ^ 2 := by
      refine (hB _ (by simpa using hre1) (by simpa using hre2)).trans ?_
      have hn : ‖z + T * I‖ ≤ 2 * σ₁ + |T| := by
        calc ‖z + T * I‖ ≤ ‖z‖ + ‖(T : ℂ) * I‖ := norm_add_le _ _
          _ ≤ 2 * σ₁ + |T| := by linarith
      have h' : 1 + ‖z + T * I‖ ≤ 1 + 2 * σ₁ + |T| := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h' 2) hB0
    have h2 : ‖conj (G (conj (z - T * I)))‖ ≤ B * (1 + 2 * σ₁ + |T|) ^ 2 := by
      rw [Complex.norm_conj]
      refine (hB _ (by simpa using hre1) (by simpa using hre2)).trans ?_
      have hn : ‖conj (z - T * I)‖ ≤ 2 * σ₁ + |T| := by
        rw [Complex.norm_conj]
        calc ‖z - T * I‖ ≤ ‖z‖ + ‖(T : ℂ) * I‖ := norm_sub_le _ _
          _ ≤ 2 * σ₁ + |T| := by linarith
      have h' : 1 + ‖conj (z - T * I)‖ ≤ 1 + 2 * σ₁ + |T| := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h' 2) hB0
    rw [hg]; simp only []
    rw [norm_div]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    have := norm_add_le (G (z + T * I)) (conj (G (conj (z - T * I))))
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
  have hDnn : ∀ u, 0 ≤ D u := fun u =>
    AnalyticOnNhd.divisor_nonneg (f := g) (U := U) (fun z _ => hgd.analyticAt z) u
  -- the zero set of `Re G(x+iT)` on `[a, σ₁]`
  set Z : Set ℝ := {x | x ∈ Icc a σ₁ ∧ (G (x + T * I)).re = 0}
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
  have harg := abs_im_integral_logDeriv_le (f := fun x : ℝ => G (x + T * I))
    (f' := fun x : ℝ => deriv G (x + T * I)) S.card a σ₁ haσ.le
    (fun x _ => hasDerivAt_horiz hG T x)
    (((continuous_deriv_of_entire hG).comp (by fun_prop)).continuousOn)
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

/-- The vertical contribution: `|Re ∫_{y₀}^{y₁} G'/G(σ₁+iy) dy| ≤ π` when `Re G ≥ 1/2` on the
line. -/
lemma abs_re_integral_logDeriv_vert {G : ℂ → ℂ} (hG : Differentiable ℂ G) {σ₁ y₀ y₁ : ℝ}
    (hy : y₀ ≤ y₁) (hre : ∀ y : ℝ, 1 / 2 ≤ (G (σ₁ + y * I)).re) :
    |(∫ y in y₀..y₁, deriv G (σ₁ + y * I) / G (σ₁ + y * I)).re| ≤ π := by
  have hne : ∀ y : ℝ, G (σ₁ + y * I) ≠ 0 := by
    intro y h; have := hre y; rw [h] at this; simp at this; linarith
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => G (σ₁ + y * I)) (deriv G (σ₁ + y * I) * I) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (σ₁ : ℂ) + (y : ℂ) * I) I y := by
      simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (σ₁ : ℂ)
    exact (hG _).hasDerivAt.comp y h1
  have h := abs_im_integral_logDeriv_le (f := fun y : ℝ => G (σ₁ + y * I))
    (f' := fun y : ℝ => deriv G (σ₁ + y * I) * I) 0 y₀ y₁ hy (fun y _ => hd y)
    (((continuous_deriv_of_entire hG).comp (by fun_prop)).mul continuous_const).continuousOn
    (fun y _ => hne y) ∅ le_rfl (fun y _ h0 => by
      have := hre y; rw [h0] at this; norm_num at this)
  simp only [Finset.card_empty, Nat.cast_zero, zero_add, mul_one] at h
  have heq : ∫ y in y₀..y₁, deriv G (σ₁ + y * I) * I / G (σ₁ + y * I) =
      I * ∫ y in y₀..y₁, deriv G (σ₁ + y * I) / G (σ₁ + y * I) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr; intro y _
    simp only []; ring
  rw [heq, I_mul_im] at h
  exact h

end RamanujanTau.GeneralZeros
