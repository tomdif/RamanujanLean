/-
# M3 step 4 (cont.): the two residues of the Mellin integral

With `p = iv/2` (`v ≠ 0`), shifting `Re z = 2 → −1/6` past the poles `z = 0` and `z = p` of
`Φ(z) e^{z²}/(z(2z − iv))`, `Φ(z) = Γ(a+z)Γ(b+z)α^{−z}`:

    ∫₁^∞ x^{iv−1} W̃_{u,u'}(αx²) dx
      = (G(p) α^{−p} e^{−v²/4} − 1)/(iv) + R,   G(p) = Γ(a+p)Γ(b+p)/(Γ(a)Γ(b))   (`mellin_Wsh`)

and `|R| ≤ K (α/(T(u)T(u')))^{1/6}` uniformly (`norm_Rsh_le`).  Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.Mellin
import RamanujanTau.SelbergKey2.WBound

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex MeasureTheory Set Filter Topology RamanujanTau.HeckeAFE RamanujanTau.SelbergKey
  RamanujanTau.SelbergKey2
open scoped Real

/-- `Φ(z) = Γ(a+z)Γ(b+z)α^{−z}`. -/
noncomputable def PhiM (a b : ℂ) (α : ℝ) (z : ℂ) : ℂ := Gamma (a + z) * Gamma (b + z) * (α : ℂ) ^ (-z)

/-- The Mellin integrand `Φ(z) e^{z²}/z/(2z − iv)`. -/
noncomputable def fM (a b : ℂ) (α v : ℝ) (z : ℂ) : ℂ :=
  Gamma (a + z) * Gamma (b + z) * (α : ℂ) ^ (-z) * cexp (z ^ 2) / z / (2 * z - v * I)

section
variable {a b : ℂ} (ha : 1 / 6 < a.re) (hb : 1 / 6 < b.re) {α : ℝ} (hα : 0 < α)
include ha hb hα

lemma differentiableOn_PhiM : DifferentiableOn ℂ (PhiM a b α) (strip (-1 / 6) 2) := by
  have hα0 : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  exact ((differentiableOn_Gamma_add (by linarith)).mul (differentiableOn_Gamma_add (by linarith))).mul
    (differentiable_neg.const_cpow (Or.inl hα0)).differentiableOn

lemma bdd_PhiM : ∃ M, ∀ u ∈ strip (-1 / 6) 2, ‖PhiM a b α u‖ ≤ M := by
  obtain ⟨M₁, hM₁⟩ := gamma_bdd_strip (s := a) (by norm_num : (-1 / 6 : ℝ) ≤ 2) (by linarith)
  obtain ⟨M₂, hM₂⟩ := gamma_bdd_strip (s := b) (by norm_num : (-1 / 6 : ℝ) ≤ 2) (by linarith)
  refine ⟨M₁ * M₂ * (α ^ (-(2:ℝ)) + α ^ (1 / 6 : ℝ)), fun z hz => ?_⟩
  unfold PhiM
  rw [norm_mul, norm_mul, norm_ofReal_cpow hα]
  have h1 := hM₁ z hz
  have h2 := hM₂ z hz
  have h3 := rpow_le_add_of_mem hα (a := -2) (b := 1 / 6) (x := (-z).re)
    (by simp; linarith [hz.2]) (by simp; linarith [hz.1])
  have hM0 : 0 ≤ M₁ := le_trans (norm_nonneg _) h1
  exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hM0) h3 (by positivity)
    (mul_nonneg hM0 (le_trans (norm_nonneg _) h2))

lemma integrable_PhiM_line (q : ℂ) (hq : q.re = 0) {c : ℝ} (hc : c ≠ 0) (h1 : -1 / 6 ≤ c) (h2 : c ≤ 2) :
    Integrable (fun y : ℝ => PhiM a b α ((c : ℂ) + y * I) * cexp (((c : ℂ) + y * I) ^ 2) /
      ((c : ℂ) + y * I - q)) := by
  obtain ⟨M, hM⟩ := bdd_PhiM ha hb hα
  have hne : ∀ y : ℝ, (c : ℂ) + y * I - q ≠ 0 := by
    intro y h; have := congrArg Complex.re h; simp [hq] at this; exact hc this
  have hcont : Continuous (fun y : ℝ => PhiM a b α ((c : ℂ) + y * I) * cexp (((c : ℂ) + y * I) ^ 2) /
      ((c : ℂ) + y * I - q)) := by
    refine Continuous.div (Continuous.mul ?_ (by fun_prop)) (by fun_prop) hne
    exact (differentiableOn_PhiM ha hb hα).continuousOn.comp_continuous (continuous_line c)
      (fun y => mem_strip_line h1 h2 y)
  have hc0 : 0 < |c| := abs_pos.2 hc
  refine Integrable.mono' ((integrable_exp_neg_mul_sq one_pos).const_mul
    (|M| * Real.exp (c ^ 2) / |c|)) hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [norm_div, norm_mul, norm_cexp_sq]
  have hge : |c| ≤ ‖(c : ℂ) + y * I - q‖ := by
    have := Complex.abs_re_le_norm ((c : ℂ) + y * I - q); simpa [hq] using this
  rw [div_le_iff₀ (lt_of_lt_of_le hc0 hge)]
  have hP := (hM _ (mem_strip_line h1 h2 y)).trans (le_abs_self M)
  have e : Real.exp (c ^ 2 - y ^ 2) = Real.exp (c ^ 2) * Real.exp (-1 * y ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  calc ‖PhiM a b α (↑c + ↑y * I)‖ * (Real.exp (c ^ 2) * Real.exp (-1 * y ^ 2))
      ≤ |M| * (Real.exp (c ^ 2) * Real.exp (-1 * y ^ 2)) := by gcongr
    _ = |M| * Real.exp (c ^ 2) / |c| * Real.exp (-1 * y ^ 2) * |c| := by field_simp
    _ ≤ _ := by gcongr

/-- Partial fractions on a line `Re z = c ≠ 0`. -/
lemma vline_fM_split {v : ℝ} (hv : v ≠ 0) {c : ℝ} (hc : c ≠ 0) (h1 : -1 / 6 ≤ c) (h2 : c ≤ 2) :
    vline (fM a b α v) c = ((v : ℂ) * I)⁻¹ *
      (vline (fun u => PhiM a b α u * cexp (u ^ 2) / (u - ((v / 2 : ℝ) : ℂ) * I)) c -
        vline (fun u => PhiM a b α u * cexp (u ^ 2) / u) c) := by
  have i1 := integrable_PhiM_line ha hb hα (((v / 2 : ℝ) : ℂ) * I) (by simp) hc h1 h2
  have i0 := integrable_PhiM_line ha hb hα 0 (by simp) hc h1 h2
  simp only [sub_zero] at i0
  unfold vline
  rw [← integral_sub i1 i0, ← integral_const_mul]
  congr 1; ext y
  set z : ℂ := (c : ℂ) + y * I
  have hz : z ≠ 0 := line_ne_zero hc y
  have hzp : z - ((v / 2 : ℝ) : ℂ) * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [z] at this; exact hc this
  have h2z : 2 * z - v * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [z] at this; exact hc this
  have hvI : (v : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hv) I_ne_zero
  have hp : ((v / 2 : ℝ) : ℂ) * I = (v : ℂ) / 2 * I := by push_cast; ring
  rw [hp] at hzp ⊢
  have key : ∀ w : ℂ, w / z / (2 * z - v * I) = ((v : ℂ) * I)⁻¹ * (w / (z - (v : ℂ) / 2 * I) - w / z) := by
    intro w
    rw [div_sub_div _ _ hzp hz, inv_mul_eq_div, div_div, div_div,
      div_eq_div_iff (mul_ne_zero hz h2z) (mul_ne_zero (mul_ne_zero hzp hz) hvI)]
    ring
  unfold fM PhiM
  rw [key]

/-- **The two residues.** -/
theorem vline_fM_residues {v : ℝ} (hv : v ≠ 0) :
    vline (fM a b α v) 2 - vline (fM a b α v) (-1 / 6) =
      2 * π * (PhiM a b α (((v / 2 : ℝ) : ℂ) * I) * Real.exp (-(v / 2) ^ 2) - PhiM a b α 0) /
        ((v : ℂ) * I) := by
  have hd := differentiableOn_PhiM ha hb hα
  have hB := bdd_PhiM ha hb hα
  rw [vline_fM_split ha hb hα hv (by norm_num) (by norm_num) le_rfl,
    vline_fM_split ha hb hα hv (by norm_num) le_rfl (by norm_num)]
  have r1 := vline_residue_at (v / 2) (by norm_num : (-1 / 6 : ℝ) < 0) (by norm_num : (0:ℝ) < 2) hd hB
  have r0 := vline_residue (by norm_num : (-1 / 6 : ℝ) < 0) (by norm_num : (0:ℝ) < 2) hd hB
  rw [← mul_sub, show ∀ A B C D : ℂ, A - B - (C - D) = (A - C) - (B - D) from fun _ _ _ _ => by ring,
    r1, r0]
  field_simp

end

/-- The remainder `R = (2π)⁻¹ ∫_{(−1/6)} … / (Γ(a)Γ(b))`. -/
noncomputable def Rsh (u u' v α : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * vline (fM (6 + u * I) (6 - u' * I) α v) (-1 / 6) /
    (Gamma (6 + u * I) * Gamma (6 - u' * I))

/-- `G(p) = Γ(a+p)Γ(b+p)/(Γ(a)Γ(b))`, `a = 6+iu`, `b = 6−iu'`. -/
noncomputable def Gsh (u u' : ℝ) (p : ℂ) : ℂ :=
  Gamma (6 + u * I + p) * Gamma (6 - u' * I + p) / (Gamma (6 + u * I) * Gamma (6 - u' * I))

/-- **Mellin evaluation of the lag weight** (exact, `v ≠ 0`). -/
theorem mellin_Wsh (u u' : ℝ) {v : ℝ} (hv : v ≠ 0) {α : ℝ} (hα : 0 < α) :
    ∫ x in Ioi (1:ℝ), (x : ℂ) ^ ((v : ℂ) * I - 1) * Wsh u u' (α * x ^ 2) =
      (Gsh u u' (((v / 2 : ℝ) : ℂ) * I) * (α : ℂ) ^ (-(((v / 2 : ℝ) : ℂ) * I)) *
          Real.exp (-(v / 2) ^ 2) - 1) / ((v : ℂ) * I) + Rsh u u' v α := by
  have ha : (1 / 6 : ℝ) < (6 + u * I : ℂ).re := by simp; norm_num
  have hb : (1 / 6 : ℝ) < (6 - u' * I : ℂ).re := by simp; norm_num
  have hΓ : Gamma (6 + u * I) * Gamma (6 - u' * I) ≠ 0 :=
    mul_ne_zero (HafnerProportion.Gamma_line_ne_zero u) (Gamma_six_sub_ne u')
  have hvI : (v : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hv) I_ne_zero
  unfold Wsh
  have e1 : (fun x : ℝ => (x : ℂ) ^ ((v : ℂ) * I - 1) * (W2sh (6 + u * I) (6 - u' * I) (α * x ^ 2) 2 /
      (Gamma (6 + u * I) * Gamma (6 - u' * I)))) = fun x : ℝ =>
      (x : ℂ) ^ ((v : ℂ) * I - 1) * W2sh (6 + u * I) (6 - u' * I) (α * x ^ 2) 2 /
        (Gamma (6 + u * I) * Gamma (6 - u' * I)) := by
    funext x; ring
  rw [e1, integral_div, mellin_line2 (by linarith) (by linarith) hα v]
  have hres := vline_fM_residues ha hb hα hv
  have e2 : vline (fun z => Gamma (6 + u * I + z) * Gamma (6 - u' * I + z) * (α : ℂ) ^ (-z) *
      cexp (z ^ 2) / z / (2 * z - v * I)) 2 = vline (fM (6 + u * I) (6 - u' * I) α v) 2 := rfl
  rw [e2, show vline (fM (6 + u * I) (6 - u' * I) α v) 2 =
      vline (fM (6 + u * I) (6 - u' * I) α v) (-1 / 6) +
        2 * π * (PhiM (6 + u * I) (6 - u' * I) α (((v / 2 : ℝ) : ℂ) * I) * Real.exp (-(v / 2) ^ 2) -
          PhiM (6 + u * I) (6 - u' * I) α 0) / ((v : ℂ) * I) by rw [← hres]; ring]
  unfold Rsh Gsh PhiM
  simp only [add_zero, neg_zero, cpow_zero, mul_one]
  set g := Gamma (6 + u * I) * Gamma (6 - u' * I) with hg
  have h2π : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  field_simp
  ring

end RamanujanTau.SelbergKeyDiag2
