/-
# The auxiliary function `Ψ(z) = KK(z)³ HH(z+iγ)⁴ HH(z+2iγ) = (z−1)³F(z)`

For `|γ| ≥ 1`:

* `Ψ` is holomorphic on `Ω = {Re z > 3/5, |Im z| < 1/2}` (`differentiableOn_PsiS`);
* `Ψ(σ) = (σ−1)³ F(σ)` for real `σ > 1` (`PsiS_real`);
* `Ψ(u) ≠ 0` for `Re u > 1` (`PsiS_ne_zero`);
* `HH(β+iγ) = 0` gives a zero of order `≥ 4` at `β` (`four_le_order_PsiS`);
* `‖Ψ(z)‖ ≤ B (9+|γ|)^{10}` on `|z − (1+δ)| ≤ 1/4` (`norm_PsiS_le`; really `(9+|γ|)^5`).
-/
import RamanujanTau.Sym2ZeroFree.Basic

set_option autoImplicit false

namespace RamanujanTau.Sym2ZeroFree

open Complex Metric Set Filter Topology
open RamanujanTau.EdgeNonvanishing RamanujanTau.TauPNTUncond RamanujanTau.ZeroFreeRegion

/-- The factor carrying the zero: `HH(z+iγ)⁴`. -/
noncomputable def Bpart (γ : ℝ) (z : ℂ) : ℂ :=
  HH (z + (γ : ℂ) * I) * HH (z + (γ : ℂ) * I) * (HH (z + (γ : ℂ) * I) * HH (z + (γ : ℂ) * I))

/-- The rest: `KK(z)³ HH(z+2iγ)`. -/
noncomputable def RestS (γ : ℝ) (z : ℂ) : ℂ := KK z ^ 3 * HH (z + ((2 * γ : ℝ) : ℂ) * I)

/-- `Ψ = (z−1)³F(z)`. -/
noncomputable def PsiS (γ : ℝ) (z : ℂ) : ℂ := Bpart γ z * RestS γ z

lemma shift_ne {z : ℂ} (hz : |z.im| < 1 / 2) {u : ℝ} (hu : 1 ≤ |u|) :
    z + (u : ℂ) * I ≠ 0 ∧ z + (u : ℂ) * I ≠ 1 := by
  have him : (z + (u : ℂ) * I).im = z.im + u := by simp
  have hne : z.im + u ≠ 0 := by
    intro h
    have : u = -z.im := by linarith
    rw [this, abs_neg] at hu; linarith
  refine ⟨fun h => hne ?_, fun h => hne ?_⟩
  · rw [← him, h]; simp
  · rw [← him, h]; simp

lemma two_abs {γ : ℝ} (hγ : 1 ≤ |γ|) : 1 ≤ |2 * γ| := by
  rw [abs_mul]; norm_num; linarith

lemma differentiableAt_HH_shift {z : ℂ} (hz : |z.im| < 1 / 2) {u : ℝ} (hu : 1 ≤ |u|) :
    DifferentiableAt ℂ (fun z => HH (z + (u : ℂ) * I)) z := by
  obtain ⟨h0, h1⟩ := shift_ne hz hu
  exact (differentiableAt_HH h0 h1).comp (f := fun w : ℂ => w + (u : ℂ) * I) z (by fun_prop)

lemma differentiableAt_Bpart {γ : ℝ} (hγ : 1 ≤ |γ|) {z : ℂ} (hz : |z.im| < 1 / 2) :
    DifferentiableAt ℂ (Bpart γ) z := by
  have h := differentiableAt_HH_shift hz hγ
  unfold Bpart
  exact (h.mul h).mul (h.mul h)

lemma differentiableAt_RestS {γ : ℝ} (hγ : 1 ≤ |γ|) {z : ℂ} (hz : z ∈ Om) :
    DifferentiableAt ℂ (RestS γ) z := by
  obtain ⟨h1, h2⟩ := hz
  simp only [mem_setOf_eq] at h1 h2
  have hz0 : z ≠ 0 := by intro h; rw [h] at h1; simp at h1; linarith
  have hK := differentiableAt_KK hz0
  have hH := differentiableAt_HH_shift h2 (two_abs hγ)
  unfold RestS
  exact (hK.pow 3).mul hH

lemma differentiableOn_PsiS {γ : ℝ} (hγ : 1 ≤ |γ|) : DifferentiableOn ℂ (PsiS γ) Om :=
  fun z hz => ((differentiableAt_Bpart hγ hz.2).mul
    (differentiableAt_RestS hγ hz)).differentiableWithinAt

lemma analyticOnNhd_PsiS {γ : ℝ} (hγ : 1 ≤ |γ|) : AnalyticOnNhd ℂ (PsiS γ) Om :=
  (differentiableOn_PsiS hγ).analyticOnNhd isOpen_Om

/-- `Ψ(σ) = (σ−1)³ F(σ)` for real `σ > 1`. -/
theorem PsiS_real (γ : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    PsiS γ (σ : ℂ) = ((σ : ℂ) - 1) ^ 3 * FS σ γ := by
  have h0 : (σ : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1 : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [PsiS, Bpart, RestS, KK_eq h0 h1, FS]
  ring

/-- `Ψ` has no zeros on `Re u > 1`. -/
theorem PsiS_ne_zero (γ : ℝ) {u : ℂ} (hu : 1 < u.re) : PsiS γ u ≠ 0 := by
  have hK : KK u ≠ 0 := KK_ne_zero hu.le
  have hH : ∀ e : ℝ, HH (u + (e : ℂ) * I) ≠ 0 := fun e =>
    HH_ne_zero_of_gt (by simp; linarith)
  rw [PsiS, Bpart, RestS]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hH γ) (hH γ)) (mul_ne_zero (hH γ) (hH γ)))
    (mul_ne_zero (pow_ne_zero _ hK) (hH _))

/-- A zero `HH(β+iγ) = 0` gives a zero of order `≥ 4` of `Ψ` at `β`. -/
theorem four_le_order_PsiS {γ : ℝ} (hγ : 1 ≤ |γ|) {β : ℝ} (hβ : (β : ℂ) ∈ Om)
    (h0 : HH ((β : ℂ) + (γ : ℂ) * I) = 0) : (4 : ℕ∞) ≤ analyticOrderAt (PsiS γ) (β : ℂ) := by
  set b : ℂ := (β : ℂ)
  have hbim : |b.im| < 1 / 2 := hβ.2
  have hB : AnalyticAt ℂ (fun z => HH (z + (γ : ℂ) * I)) b := by
    exact DifferentiableOn.analyticAt (s := {z : ℂ | |z.im| < 1 / 2})
      (fun z hz => (differentiableAt_HH_shift hz hγ).differentiableWithinAt)
      ((isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).mem_nhds hbim)
  have hR : AnalyticAt ℂ (RestS γ) b :=
    DifferentiableOn.analyticAt (s := Om)
      (fun z hz => (differentiableAt_RestS hγ hz).differentiableWithinAt) (isOpen_Om.mem_nhds hβ)
  have o1 : 1 ≤ analyticOrderAt (fun z => HH (z + (γ : ℂ) * I)) b :=
    ENat.one_le_iff_ne_zero.mpr (analyticOrderAt_ne_zero.mpr ⟨hB, h0⟩)
  have hfun : PsiS γ = ((fun z => HH (z + (γ : ℂ) * I)) * (fun z => HH (z + (γ : ℂ) * I)) *
      ((fun z => HH (z + (γ : ℂ) * I)) * (fun z => HH (z + (γ : ℂ) * I)))) * RestS γ := by
    funext z; simp [PsiS, Bpart]
  rw [hfun, analyticOrderAt_mul ((hB.mul hB).mul (hB.mul hB)) hR,
    analyticOrderAt_mul (hB.mul hB) (hB.mul hB), analyticOrderAt_mul hB hB]
  have : (4 : ℕ∞) = 1 + 1 + (1 + 1) + 0 := by norm_num
  rw [this]
  gcongr
  exact bot_le

/-- **Polynomial growth of `Ψ`** on the disc. -/
theorem norm_PsiS_le : ∃ B : ℝ, 1 ≤ B ∧ ∀ γ : ℝ, 1 ≤ |γ| → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 8 →
    ∀ z ∈ closedBall ((1 + δ : ℝ) : ℂ) (1 / 4), ‖PsiS γ z‖ ≤ B * (9 + |γ|) ^ 10 := by
  obtain ⟨C, hC0, hC⟩ := norm_HH_le
  have hK0Om : closedBall (1 : ℂ) (3 / 8) ⊆ {z : ℂ | z ≠ 0} := by
    intro z hz
    rw [mem_closedBall, dist_eq] at hz
    have h1 := Complex.abs_re_le_norm (z - 1)
    simp only [sub_re, one_re] at h1
    have := (abs_le.mp (h1.trans hz)).1
    intro h; rw [h] at this; simp at this; linarith
  have hcont : ContinuousOn KK (closedBall (1 : ℂ) (3 / 8)) := fun z hz =>
    (differentiableAt_KK (hK0Om hz)).continuousAt.continuousWithinAt
  obtain ⟨C0, hC0'⟩ := (isCompact_closedBall (1 : ℂ) (3 / 8)).exists_bound_of_continuousOn hcont
  set C1 := max C0 0
  have hC1 : 0 ≤ C1 := le_max_right _ _
  set B := max 1 (C1 ^ 3 * C ^ 5 * 2) with hB
  refine ⟨B, le_max_left _ _, fun γ hγ δ hδ0 hδ z hz => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := ball_facts hδ0 hδ hz
  have hzK : z ∈ closedBall (1 : ℂ) (3 / 8) := by
    rw [mem_closedBall, dist_eq]
    rw [mem_closedBall, dist_eq] at hz
    have : ‖z - 1‖ ≤ ‖z - ((1 + δ : ℝ) : ℂ)‖ + ‖((1 + δ : ℝ) : ℂ) - 1‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have e : ((1 + δ : ℝ) : ℂ) - 1 = ((δ : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0] at this
    linarith
  have hKb : ‖KK z‖ ≤ C1 := (hC0' z hzK).trans (le_max_left _ _)
  set T := |γ|
  have hT : 1 ≤ T := hγ
  have hsh : ∀ u : ℝ, 1 ≤ |u| → ‖HH (z + (u : ℂ) * I)‖ ≤ C * (2 + |u|) := by
    intro u hu
    have hre : (z + (u : ℂ) * I).re = z.re := by simp
    have him : (z + (u : ℂ) * I).im = z.im + u := by simp
    have hi : 1 / 2 ≤ |(z + (u : ℂ) * I).im| := by
      rw [him]
      have := abs_sub_abs_le_abs_sub u (-z.im)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this
      linarith
    have hn : ‖z + (u : ℂ) * I‖ ≤ 2 + |u| := by
      have := norm_add_le z ((u : ℂ) * I)
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    calc ‖HH (z + (u : ℂ) * I)‖ ≤ C * ‖z + (u : ℂ) * I‖ := hC _ (by rw [hre]; exact h1) hi
      _ ≤ C * (2 + |u|) := by gcongr
  have hA := hsh γ hγ
  have hA' : ‖HH (z + (γ : ℂ) * I)‖ ≤ C * (9 + T) := hA.trans (by gcongr; linarith)
  have hD := hsh (2 * γ) (two_abs hγ)
  have hD' : ‖HH (z + ((2 * γ : ℝ) : ℂ) * I)‖ ≤ C * (2 * (9 + T)) := by
    refine hD.trans ?_
    rw [abs_mul]; norm_num
    gcongr
    linarith
  have hP : ‖PsiS γ z‖ = ‖HH (z + (γ : ℂ) * I)‖ ^ 4 * ‖KK z‖ ^ 3 *
      ‖HH (z + ((2 * γ : ℝ) : ℂ) * I)‖ := by
    simp only [PsiS, Bpart, RestS, norm_mul, norm_pow]; ring
  have h9 : 1 ≤ 9 + T := by linarith
  calc ‖PsiS γ z‖ ≤ (C * (9 + T)) ^ 4 * C1 ^ 3 * (C * (2 * (9 + T))) := by
        rw [hP]; gcongr
    _ = (C1 ^ 3 * C ^ 5 * 2) * (9 + T) ^ 5 := by ring
    _ ≤ B * (9 + T) ^ 10 := by
        gcongr
        · exact le_max_right _ _
        all_goals first | exact h9 | norm_num

end RamanujanTau.Sym2ZeroFree
