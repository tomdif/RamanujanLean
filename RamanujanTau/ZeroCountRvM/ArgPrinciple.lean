/-
# The argument principle on a rectangle

For an entire `F ≢ 0` with no zeros on the boundary of `[x₀,x₁] × [y₀,y₁]`,
`∮ F'/F = 2πi · Σ_{ρ inside} ord_ρ F` (`arg_principle_rect`).

Proof: Mathlib's `MeromorphicOn.extract_zeros_poles` on a closed disc `U ⊇` rectangle gives
`F = (∏_u (z − u)^{ord_u F}) · g` near each boundary point, with `g` analytic and zero-free on
`U`.  So on the boundary `F'/F = Σ_u ord_u/(z − u) + g'/g`; Cauchy kills `g'/g`, and
`RectInv` evaluates `∮ 1/(z − u)` (`2πi` inside, `0` outside).
-/
import RamanujanTau.ZeroCountRvM.RectInv
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Calculus.LogDeriv

set_option autoImplicit false

namespace RamanujanTau.ZeroCountRvM

open Complex Set intervalIntegral MeasureTheory Filter Topology Metric MeromorphicOn
open scoped Real Interval

/-- The boundary of the rectangle `[x₀,x₁] × [y₀,y₁]`. -/
def rectBd (x₀ x₁ y₀ y₁ : ℝ) : Set ℂ :=
  {z | (z.re ∈ [[x₀, x₁]] ∧ (z.im = y₀ ∨ z.im = y₁)) ∨ (z.im ∈ [[y₀, y₁]] ∧ (z.re = x₀ ∨ z.re = x₁))}

section bd
variable {x₀ x₁ y₀ y₁ : ℝ}

lemma bd_bot {x : ℝ} (hx : x ∈ [[x₀, x₁]]) : (x : ℂ) + y₀ * I ∈ rectBd x₀ x₁ y₀ y₁ := by
  left; simp [hx]
lemma bd_top {x : ℝ} (hx : x ∈ [[x₀, x₁]]) : (x : ℂ) + y₁ * I ∈ rectBd x₀ x₁ y₀ y₁ := by
  left; simp [hx]
lemma bd_left {y : ℝ} (hy : y ∈ [[y₀, y₁]]) : (x₀ : ℂ) + y * I ∈ rectBd x₀ x₁ y₀ y₁ := by
  right; simp [hy]
lemma bd_right {y : ℝ} (hy : y ∈ [[y₀, y₁]]) : (x₁ : ℂ) + y * I ∈ rectBd x₀ x₁ y₀ y₁ := by
  right; simp [hy]

lemma rectInt_congr {f g : ℂ → ℂ} (h : EqOn f g (rectBd x₀ x₁ y₀ y₁)) :
    rectInt f x₀ x₁ y₀ y₁ = rectInt g x₀ x₁ y₀ y₁ := by
  unfold rectInt
  rw [integral_congr (fun x hx => h (bd_bot hx)), integral_congr (fun x hx => h (bd_top hx)),
    integral_congr (fun y hy => h (bd_right hy)), integral_congr (fun y hy => h (bd_left hy))]

lemma seg_bot {f : ℂ → ℂ} (hf : ContinuousOn f (rectBd x₀ x₁ y₀ y₁)) :
    IntervalIntegrable (fun x : ℝ => f (x + y₀ * I)) volume x₀ x₁ :=
  (hf.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + y₀ * I).continuousOn
    (fun x hx => bd_bot hx)).intervalIntegrable
lemma seg_top {f : ℂ → ℂ} (hf : ContinuousOn f (rectBd x₀ x₁ y₀ y₁)) :
    IntervalIntegrable (fun x : ℝ => f (x + y₁ * I)) volume x₀ x₁ :=
  (hf.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + y₁ * I).continuousOn
    (fun x hx => bd_top hx)).intervalIntegrable
lemma seg_left {f : ℂ → ℂ} (hf : ContinuousOn f (rectBd x₀ x₁ y₀ y₁)) :
    IntervalIntegrable (fun y : ℝ => f (x₀ + y * I)) volume y₀ y₁ :=
  (hf.comp (by fun_prop : Continuous fun y : ℝ => (x₀ : ℂ) + y * I).continuousOn
    (fun y hy => bd_left hy)).intervalIntegrable
lemma seg_right {f : ℂ → ℂ} (hf : ContinuousOn f (rectBd x₀ x₁ y₀ y₁)) :
    IntervalIntegrable (fun y : ℝ => f (x₁ + y * I)) volume y₀ y₁ :=
  (hf.comp (by fun_prop : Continuous fun y : ℝ => (x₁ : ℂ) + y * I).continuousOn
    (fun y hy => bd_right hy)).intervalIntegrable

lemma rectInt_add {f g : ℂ → ℂ} (hf : ContinuousOn f (rectBd x₀ x₁ y₀ y₁))
    (hg : ContinuousOn g (rectBd x₀ x₁ y₀ y₁)) :
    rectInt (fun z => f z + g z) x₀ x₁ y₀ y₁ = rectInt f x₀ x₁ y₀ y₁ + rectInt g x₀ x₁ y₀ y₁ := by
  unfold rectInt
  rw [integral_add (seg_bot hf) (seg_bot hg), integral_add (seg_top hf) (seg_top hg),
    integral_add (seg_right hf) (seg_right hg), integral_add (seg_left hf) (seg_left hg)]
  simp only [smul_eq_mul]; ring

lemma rectInt_const_mul (c : ℂ) (f : ℂ → ℂ) :
    rectInt (fun z => c * f z) x₀ x₁ y₀ y₁ = c * rectInt f x₀ x₁ y₀ y₁ := by
  unfold rectInt
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]; ring

lemma rectInt_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (rectBd x₀ x₁ y₀ y₁)) :
    rectInt (fun z => ∑ i ∈ s, f i z) x₀ x₁ y₀ y₁ = ∑ i ∈ s, rectInt (f i) x₀ x₁ y₀ y₁ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rectInt]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [rectInt_add (hf a (Finset.mem_insert_self a s))
      (continuousOn_finsetSum _ fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    rw [ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

end bd

lemma abs_le_of_mem_uIcc {a b x : ℝ} (h : x ∈ [[a, b]]) : |x| ≤ |a| + |b| := by
  rcases mem_uIcc.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  · rw [abs_le]; constructor <;>
      linarith [le_abs_self a, le_abs_self b, neg_abs_le a, neg_abs_le b]

/-- **Argument principle on a rectangle** for an entire function. -/
theorem arg_principle_rect {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : ∃ z, F z ≠ 0)
    {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁)
    (hB : ∀ z ∈ rectBd x₀ x₁ y₀ y₁, F z ≠ 0) :
    ∃ S : Finset ℂ,
      (∀ u, u ∈ S ↔ (F u = 0 ∧ x₀ < u.re ∧ u.re < x₁ ∧ y₀ < u.im ∧ u.im < y₁)) ∧
      rectInt (logDeriv F) x₀ x₁ y₀ y₁ = 2 * π * I * ∑ u ∈ S, (analyticOrderNatAt F u : ℂ) := by
  classical
  set R : ℝ := |x₀| + |x₁| + |y₀| + |y₁| + 1 with hR
  set U : Set ℂ := closedBall (0 : ℂ) R with hU
  have hrect : [[x₀, x₁]] ×ℂ [[y₀, y₁]] ⊆ ball (0 : ℂ) R := by
    intro z hz
    rw [mem_reProdIm] at hz
    rw [mem_ball, dist_zero_right]
    have h1 := abs_le_of_mem_uIcc hz.1
    have h2 := abs_le_of_mem_uIcc hz.2
    have := Complex.norm_le_abs_re_add_abs_im z
    linarith
  have hBrect : rectBd x₀ x₁ y₀ y₁ ⊆ [[x₀, x₁]] ×ℂ [[y₀, y₁]] := by
    intro z hz
    rw [mem_reProdIm]
    rcases hz with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
    · exact ⟨h1, h2 ▸ left_mem_uIcc⟩
    · exact ⟨h1, h2 ▸ right_mem_uIcc⟩
    · exact ⟨h2 ▸ left_mem_uIcc, h1⟩
    · exact ⟨h2 ▸ right_mem_uIcc, h1⟩
  have hballU : ball (0 : ℂ) R ⊆ U := ball_subset_closedBall
  have hAn : AnalyticOnNhd ℂ F U := fun z _ => hF.analyticAt z
  obtain ⟨z₁, hz₁⟩ := hF0
  have hord : ∀ u, analyticOrderAt F u ≠ ⊤ := by
    intro u h
    rw [AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero u (fun z => hF.analyticAt z)] at h
    exact hz₁ (by rw [h]; rfl)
  have h₂ : ∀ u : U, meromorphicOrderAt F u ≠ ⊤ := by
    intro u
    rw [(hF.analyticAt u).meromorphicOrderAt_eq]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hord u)
    rw [← hn]; simp
  set D := divisor F U with hDdef
  have h₃ : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := hAn.meromorphicOn.extract_zeros_poles h₂ h₃
  set n : ℂ → ℕ := fun u => analyticOrderNatAt F u with hn
  have hD : ∀ u ∈ U, D u = (n u : ℤ) := by
    intro u hu
    rw [hDdef, AnalyticOnNhd.divisor_apply hAn hu]
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hord u)
    simp only [hn, analyticOrderNatAt]
    rw [← hm, ENat.toNat_coe]
    rfl
  set Sall : Finset ℂ := h₃.toFinset with hSall
  have hmemSall : ∀ u, u ∈ Sall ↔ (u ∈ U ∧ F u = 0) := by
    intro u
    rw [hSall, Set.Finite.mem_toFinset, Function.mem_support]
    constructor
    · intro h
      have huU : u ∈ U := D.supportWithinDomain (by simpa using h)
      refine ⟨huU, ?_⟩
      rw [hD u huU] at h
      have h0 : analyticOrderAt F u ≠ 0 := by
        intro h0; apply h; simp [hn, analyticOrderNatAt, h0]
      exact (analyticOrderAt_ne_zero.mp h0).2
    · rintro ⟨huU, hFu⟩
      rw [hD u huU]
      have h0 : analyticOrderAt F u ≠ 0 := analyticOrderAt_ne_zero.2 ⟨hF.analyticAt u, hFu⟩
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hord u)
      have hm0 : m ≠ 0 := by rintro rfl; exact h0 (by rw [← hm]; rfl)
      simp only [hn, analyticOrderNatAt, ← hm, ENat.toNat_coe]
      exact_mod_cast hm0
  set P : ℂ → ℂ := fun w => ∏ u ∈ Sall, (w - u) ^ (n u) with hP
  -- the factorisation near each boundary point
  have hloc : ∀ z ∈ ball (0 : ℂ) R, F z ≠ 0 → F =ᶠ[𝓝 z] fun w => P w * g w := by
    intro z hz hFz
    have hzU : z ∈ U := hballU hz
    have hprod : (∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) = ∏ u ∈ Sall, (· - u) ^ D u := by
      apply finprod_eq_prod_of_mulSupport_subset
      intro u hu
      rw [Function.mem_mulSupport] at hu
      simp only [Finset.mem_coe, hSall, Set.Finite.mem_toFinset, Function.mem_support]
      intro h0; apply hu; rw [h0]; funext w; simp
    have hrhs : ∀ w, ((∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) • g) w = P w * g w := by
      intro w
      rw [hprod, Pi.smul_apply', Finset.prod_apply, smul_eq_mul, hP]
      congr 1
      apply Finset.prod_congr rfl
      intro u hu
      rw [hD u ((hmemSall u).1 hu).1, zpow_natCast, Pi.pow_apply]
    have hNE : F =ᶠ[𝓝[≠] z] fun w => P w * g w := by
      have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hfg) z hzU
      have hUn : U ∈ 𝓝[≠] z :=
        mem_nhdsWithin_of_mem_nhds (mem_of_superset (isOpen_ball.mem_nhds hz) hballU)
      filter_upwards [h1, hUn] with w hw hwU
      rcases hw with hw | hw
      · rw [Set.mem_setOf_eq] at hw; rw [hw, hrhs]
      · exact absurd hwU hw
    have hgc : ContinuousAt g z := (hg_an z hzU).continuousAt
    have hPc : ContinuousAt P z := by rw [hP]; fun_prop
    exact (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (hF.continuous.continuousAt)
      (hPc.mul hgc)).mp hNE
  -- logarithmic derivative at boundary points
  have hzu : ∀ z, F z ≠ 0 → ∀ u ∈ Sall, z - u ≠ 0 := by
    intro z hFz u hu h
    rw [sub_eq_zero] at h
    exact hFz (h ▸ ((hmemSall u).1 hu).2)
  have hlog : ∀ z ∈ ball (0 : ℂ) R, F z ≠ 0 →
      logDeriv F z = (∑ u ∈ Sall, (n u : ℂ) * (1 / (z - u))) + logDeriv g z := by
    intro z hz hFz
    have hzU : z ∈ U := hballU hz
    have he := hloc z hz hFz
    have hgz : g z ≠ 0 := hg_ne ⟨z, hzU⟩
    have hPz : P z ≠ 0 := by
      rw [hP, Finset.prod_ne_zero_iff]
      intro u hu; exact pow_ne_zero _ (hzu z hFz u hu)
    have h1 : logDeriv F z = logDeriv (fun w => P w * g w) z := by
      rw [logDeriv_apply, logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
    rw [h1, logDeriv_mul z hPz hgz (by rw [hP]; fun_prop) (hg_an z hzU).differentiableAt]
    congr 1
    rw [hP, logDeriv_prod]
    · apply Finset.sum_congr rfl
      intro u hu
      rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply]
      simp [div_eq_mul_inv]
    · intro u hu; exact pow_ne_zero _ (hzu z hFz u hu)
    · intro u _; fun_prop
  -- boundary ⊆ ball
  have hBball : rectBd x₀ x₁ y₀ y₁ ⊆ ball (0 : ℂ) R := hBrect.trans hrect
  have hcongr : rectInt (logDeriv F) x₀ x₁ y₀ y₁ =
      rectInt (fun z => (∑ u ∈ Sall, (n u : ℂ) * (1 / (z - u))) + logDeriv g z) x₀ x₁ y₀ y₁ :=
    rectInt_congr fun z hz => hlog z (hBball hz) (hB z hz)
  have hcont_inv : ∀ u ∈ Sall, ContinuousOn (fun z => (n u : ℂ) * (1 / (z - u)))
      (rectBd x₀ x₁ y₀ y₁) := by
    intro u hu
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro z hz; exact hzu z (hB z hz) u hu
  have hdg : ∀ z ∈ ball (0 : ℂ) R, DifferentiableAt ℂ (logDeriv g) z := by
    intro z hz
    have hzU := hballU hz
    show DifferentiableAt ℂ (fun w => deriv g w / g w) z
    exact ((hg_an z hzU).deriv.differentiableAt).div (hg_an z hzU).differentiableAt
      (hg_ne ⟨z, hzU⟩)
  have hg0 : rectInt (logDeriv g) x₀ x₁ y₀ y₁ = 0 :=
    rectInt_eq_zero fun z hz => (hdg z (hrect hz)).differentiableWithinAt
  rw [hcongr, rectInt_add (continuousOn_finsetSum _ hcont_inv)
    (fun z hz => (hdg z (hBball hz)).continuousAt.continuousWithinAt), hg0, add_zero,
    rectInt_sum _ _ hcont_inv]
  simp_rw [rectInt_const_mul]
  -- evaluate each `∮ 1/(z−u)`
  set S := Sall.filter (fun u => x₀ < u.re ∧ u.re < x₁ ∧ y₀ < u.im ∧ u.im < y₁) with hS
  have hval : ∀ u ∈ Sall, rectInt (fun z => 1 / (z - u)) x₀ x₁ y₀ y₁ =
      if (x₀ < u.re ∧ u.re < x₁ ∧ y₀ < u.im ∧ u.im < y₁) then 2 * π * I else 0 := by
    intro u hu
    split_ifs with hin
    · exact rectInt_inv_of_mem hin.1 hin.2.1 hin.2.2.1 hin.2.2.2
    · apply rectInt_inv_of_not_mem
      intro hmem
      have hFu := ((hmemSall u).1 hu).2
      apply hB u _ hFu
      rw [mem_reProdIm, uIcc_of_le hx.le, uIcc_of_le hy.le] at hmem
      obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hmem
      simp only [not_and_or, not_lt] at hin
      rcases hin with h | h | h | h
      · right; exact ⟨by rw [uIcc_of_le hy.le]; exact ⟨b1, b2⟩, Or.inl (le_antisymm h a1)⟩
      · right; exact ⟨by rw [uIcc_of_le hy.le]; exact ⟨b1, b2⟩, Or.inr (le_antisymm a2 h)⟩
      · left; exact ⟨by rw [uIcc_of_le hx.le]; exact ⟨a1, a2⟩, Or.inl (le_antisymm h b1)⟩
      · left; exact ⟨by rw [uIcc_of_le hx.le]; exact ⟨a1, a2⟩, Or.inr (le_antisymm b2 h)⟩
  refine ⟨S, ?_, ?_⟩
  · intro u
    rw [hS, Finset.mem_filter, hmemSall]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      refine ⟨⟨hballU (hrect ?_), h⟩, h'⟩
      rw [mem_reProdIm, uIcc_of_le hx.le, uIcc_of_le hy.le]
      exact ⟨⟨h'.1.le, h'.2.1.le⟩, ⟨h'.2.2.1.le, h'.2.2.2.le⟩⟩
  · rw [Finset.sum_congr rfl (fun u hu => by rw [hval u hu]), hS, Finset.sum_filter,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> ring

end RamanujanTau.ZeroCountRvM
