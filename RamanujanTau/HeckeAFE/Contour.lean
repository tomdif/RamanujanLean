/-
# Vertical line integrals with Gaussian decay

Generic contour machinery for the smoothed approximate functional equation.

* `vline f c = ∫_ℝ f(c + iy) dy` (so `(1/2πi)∫_{(c)} f(u) du = vline f c / (2π)`);
* `vline_shift`: if `f` is holomorphic on the closed strip `a ≤ Re u ≤ b` and
  `‖f(x+iy)‖ ≤ C e^{−y²/2}` there, then `vline f a = vline f b` (Cauchy on rectangles, height → ∞);
* `vline_gauss_div`: `∫_ℝ e^{u²}/u dy = π` on `Re u = b > 0` (so `(1/2πi)∫_{(b)} e^{u²} du/u = 1/2`),
  and `= −π` on `Re u < 0`;
* `vline_residue`: for `F` holomorphic and bounded on `a ≤ Re u ≤ b`, `a < 0 < b`,
  `vline (F e^{u²}/u) b − vline (F e^{u²}/u) a = 2π F(0)` (the residue at `u = 0`).
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.HeckeAFE

open Complex MeasureTheory Set Filter Topology
open scoped Real

/-- The vertical line integral `∫_ℝ f(c+iy) dy`. -/
noncomputable def vline (f : ℂ → ℂ) (c : ℝ) : ℂ := ∫ y : ℝ, f (c + y * I)

/-- The closed vertical strip `a ≤ Re u ≤ b`. -/
def strip (a b : ℝ) : Set ℂ := {u : ℂ | a ≤ u.re ∧ u.re ≤ b}

/-- Uniform Gaussian decay on the strip `a ≤ Re u ≤ b`. -/
def GaussDecay (f : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x y : ℝ, a ≤ x → x ≤ b → ‖f (x + y * I)‖ ≤ C * Real.exp (-(1 / 2) * y ^ 2)

@[simp] lemma re_line (c y : ℝ) : ((c : ℂ) + y * I).re = c := by simp
@[simp] lemma im_line (c y : ℝ) : ((c : ℂ) + y * I).im = y := by simp

lemma mem_strip_line {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (y : ℝ) :
    (c : ℂ) + y * I ∈ strip a b := by simp [strip, hac, hcb]

lemma isClosed_strip (a b : ℝ) : IsClosed (strip a b) :=
  (isClosed_le continuous_const continuous_re).inter (isClosed_le continuous_re continuous_const)

lemma strip_mem_nhds {a b : ℝ} {z : ℂ} (ha : a < z.re) (hb : z.re < b) : strip a b ∈ 𝓝 z := by
  have ho : IsOpen (Complex.re ⁻¹' Ioo a b) := continuous_re.isOpen_preimage _ isOpen_Ioo
  refine Filter.mem_of_superset (ho.mem_nhds ⟨ha, hb⟩) ?_
  intro u hu; exact ⟨hu.1.le, hu.2.le⟩

lemma norm_cexp_sq (x y : ℝ) : ‖cexp (((x : ℂ) + y * I) ^ 2)‖ = Real.exp (x ^ 2 - y ^ 2) := by
  rw [Complex.norm_exp]; congr 1; simp [sq]

lemma continuous_line (c : ℝ) : Continuous (fun y : ℝ => (c : ℂ) + y * I) := by fun_prop

lemma integrable_line {f : ℂ → ℂ} {a b c : ℝ} (hf : ContinuousOn f (strip a b))
    (hd : GaussDecay f a b) (hac : a ≤ c) (hcb : c ≤ b) :
    Integrable (fun y : ℝ => f (c + y * I)) := by
  obtain ⟨C, hC⟩ := hd
  have hcont : Continuous (fun y : ℝ => f (c + y * I)) :=
    hf.comp_continuous (continuous_line c) fun y => mem_strip_line hac hcb y
  refine Integrable.mono' ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul C)
    hcont.aestronglyMeasurable ?_
  exact Eventually.of_forall fun y => hC c y hac hcb

lemma tendsto_exp_neg_half_sq :
    Tendsto (fun R : ℝ => Real.exp (-(1 / 2) * R ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun R : ℝ => (1 / 2) * R ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).const_mul_atTop (by norm_num)
  have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h)
  refine h2.congr fun R => ?_
  simp [neg_mul]

/-- **Shifting a vertical line integral** across a strip of holomorphy with Gaussian decay. -/
theorem vline_shift {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b) (hf : DifferentiableOn ℂ f (strip a b))
    (hd : GaussDecay f a b) : vline f a = vline f b := by
  have hd' := hd
  obtain ⟨C, hC⟩ := hd
  have hrect : ∀ R : ℝ,
      (∫ x : ℝ in a..b, f (x + (-R : ℝ) * I)) - (∫ x : ℝ in a..b, f (x + (R : ℝ) * I)) +
        I • (∫ y : ℝ in (-R)..R, f (b + y * I)) - I • (∫ y : ℝ in (-R)..R, f (a + y * I)) = 0 := by
    intro R
    have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) + (-R : ℝ) * I) ((b : ℂ) + (R : ℝ) * I) ?_
    · simpa only [re_line, im_line] using H
    · refine hf.mono fun u hu => ?_
      rw [mem_reProdIm] at hu
      simp only [re_line, im_line] at hu
      rw [Set.uIcc_of_le hab] at hu
      exact ⟨hu.1.1, hu.1.2⟩
  -- horizontal sides vanish
  have hhor : ∀ s : ℝ → ℝ, (∀ R, |s R| = |R|) →
      Tendsto (fun R : ℝ => ∫ x : ℝ in a..b, f (x + (s R : ℝ) * I)) atTop (𝓝 0) := by
    intro s hs
    have hb : ∀ R : ℝ, ‖∫ x : ℝ in a..b, f (x + (s R : ℝ) * I)‖ ≤
        C * Real.exp (-(1 / 2) * R ^ 2) * |b - a| := by
      intro R
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
      rw [Set.uIoc_of_le hab] at hx
      have := hC x (s R) hx.1.le hx.2
      have e : (s R) ^ 2 = R ^ 2 := by rw [← sq_abs, hs R, sq_abs]
      rwa [e] at this
    refine squeeze_zero_norm hb ?_
    have := (tendsto_exp_neg_half_sq.const_mul C).mul_const |b - a|
    simpa using this
  have h1 := hhor (fun R => -R) (fun R => abs_neg R)
  have h2 := hhor (fun R => R) (fun R => rfl)
  have hvb : Tendsto (fun R : ℝ => ∫ y : ℝ in (-R)..R, f (b + y * I)) atTop (𝓝 (vline f b)) :=
    intervalIntegral_tendsto_integral (integrable_line hf.continuousOn hd' hab le_rfl)
      tendsto_neg_atTop_atBot tendsto_id
  have hva : Tendsto (fun R : ℝ => ∫ y : ℝ in (-R)..R, f (a + y * I)) atTop (𝓝 (vline f a)) :=
    intervalIntegral_tendsto_integral (integrable_line hf.continuousOn hd' le_rfl hab)
      tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((h1.sub h2).add (hvb.const_smul I)).sub (hva.const_smul I)
  have hlim' : Tendsto (fun R : ℝ =>
      (∫ x : ℝ in a..b, f (x + (-R : ℝ) * I)) - (∫ x : ℝ in a..b, f (x + (R : ℝ) * I)) +
        I • (∫ y : ℝ in (-R)..R, f (b + y * I)) - I • (∫ y : ℝ in (-R)..R, f (a + y * I)))
      atTop (𝓝 0) := by
    simp_rw [hrect]; exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hlim hlim'
  simp only [sub_zero, zero_add, smul_eq_mul] at heq
  have : I * (vline f b - vline f a) = 0 := by rw [mul_sub]; exact heq
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h I_ne_zero
  · exact (sub_eq_zero.mp h).symm

/-! ## The Gaussian kernel `e^{u²}/u` -/

lemma line_ne_zero {c : ℝ} (hc : c ≠ 0) (y : ℝ) : (c : ℂ) + y * I ≠ 0 := by
  intro h; exact hc (by simpa using congrArg Complex.re h)

lemma norm_line_ge {c : ℝ} (y : ℝ) : |c| ≤ ‖(c : ℂ) + y * I‖ := by
  have := Complex.abs_re_le_norm ((c : ℂ) + y * I)
  simpa using this

/-- inner Gaussian integral: `∫_ℝ e^{u² − ux} dy = √π e^{−x²/4}` on `u = b + iy`. -/
lemma inner_gauss (b x : ℝ) :
    ∫ y : ℝ, cexp (((b : ℂ) + y * I) ^ 2 - ((b : ℂ) + y * I) * x) =
      (π : ℂ) ^ (1 / 2 : ℂ) * cexp (-(x : ℂ) ^ 2 / 4) := by
  have e : ∀ y : ℝ, ((b : ℂ) + y * I) ^ 2 - ((b : ℂ) + y * I) * x =
      (-1 : ℂ) * (y : ℂ) ^ 2 + (I * (2 * b - x)) * y + (b ^ 2 - b * x) := by
    intro y; linear_combination (y : ℂ) ^ 2 * I_sq
  simp_rw [e]
  rw [integral_cexp_quadratic (by simp) _ _]
  congr 1
  · simp
  · congr 1; linear_combination ((2 * (b : ℂ) - x) ^ 2 / 4) * I_sq

lemma integrable_gauss_prod (b : ℝ) (hb : 0 < b) :
    Integrable (Function.uncurry fun (y x : ℝ) =>
      cexp (((b : ℂ) + y * I) ^ 2 - ((b : ℂ) + y * I) * x))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have h1 : Integrable (fun y : ℝ => Real.exp (b ^ 2) * Real.exp (-1 * y ^ 2)) :=
    (integrable_exp_neg_mul_sq one_pos).const_mul _
  have h2 : Integrable (fun x : ℝ => Real.exp (-b * x)) (volume.restrict (Ioi 0)) :=
    exp_neg_integrableOn_Ioi 0 hb
  have hp := h1.mul_prod h2
  refine hp.mono' ?_ (Eventually.of_forall fun z => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    exact Complex.continuous_exp.comp (by fun_prop)
  · show ‖cexp (((b : ℂ) + z.1 * I) ^ 2 - ((b : ℂ) + z.1 * I) * z.2)‖ ≤
      Real.exp (b ^ 2) * Real.exp (-1 * z.1 ^ 2) * Real.exp (-b * z.2)
    rw [Complex.norm_exp]
    have : (((b : ℂ) + z.1 * I) ^ 2 - ((b : ℂ) + z.1 * I) * z.2).re = b ^ 2 - z.1 ^ 2 - b * z.2 := by
      simp [sq]
    rw [this, ← Real.exp_add, ← Real.exp_add]
    apply le_of_eq; congr 1; ring

/-- **`∫_ℝ e^{u²}/u dy = π`** on the line `Re u = b > 0`. -/
theorem vline_gauss_div {b : ℝ} (hb : 0 < b) : vline (fun u => cexp (u ^ 2) / u) b = π := by
  unfold vline
  have hinv : ∀ y : ℝ, cexp (((b : ℂ) + y * I) ^ 2) / ((b : ℂ) + y * I) =
      ∫ x : ℝ in Ioi 0, cexp (((b : ℂ) + y * I) ^ 2 - ((b : ℂ) + y * I) * x) := by
    intro y
    have hre : (-((b : ℂ) + y * I)).re < 0 := by simp [hb]
    have hI := integral_exp_mul_complex_Ioi hre 0
    simp only [ofReal_zero, mul_zero, Complex.exp_zero] at hI
    have : ∀ x : ℝ, cexp (((b : ℂ) + y * I) ^ 2 - ((b : ℂ) + y * I) * x) =
        cexp (((b : ℂ) + y * I) ^ 2) * cexp (-((b : ℂ) + y * I) * x) := by
      intro x; rw [← Complex.exp_add]; ring_nf
    simp_rw [this]
    rw [integral_const_mul, hI, div_eq_mul_inv]
    congr 1
    rw [neg_div, div_neg, neg_neg, one_div]
  simp_rw [hinv]
  rw [integral_integral_swap (integrable_gauss_prod b hb)]
  simp_rw [inner_gauss]
  rw [integral_const_mul]
  have hg := integral_gaussian_complex_Ioi (b := (1 / 4 : ℂ)) (by norm_num)
  have e : ∀ x : ℝ, cexp (-(x : ℂ) ^ 2 / 4) = cexp (-(1 / 4 : ℂ) * (x : ℂ) ^ 2) := by
    intro x; congr 1; ring
  simp_rw [e]
  rw [hg]
  have e1 : (π : ℂ) / (1 / 4) = ((4 * π : ℝ) : ℂ) := by push_cast; ring
  rw [e1]
  have hs1 : (π : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt π : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]; norm_num
  have hs2 : ((4 * π : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (4 * π) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]; norm_num
  rw [hs1, hs2]
  have h4 : Real.sqrt (4 * π) = 2 * Real.sqrt π := by
    rw [Real.sqrt_mul (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [h4]
  have hpi : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
  have : ((Real.sqrt π : ℝ) : ℂ) * (((2 * Real.sqrt π : ℝ) : ℂ) / 2) = ((Real.sqrt π * Real.sqrt π : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, hpi]

/-- Reflection `y ↦ −y`: if `g(−u) = −h(u)` then `vline g (−c) = −vline h c`. -/
lemma vline_neg_eq {g h : ℂ → ℂ} (hgh : ∀ u, g (-u) = -h u) (c : ℝ) :
    vline g (-c) = -vline h c := by
  unfold vline
  rw [← integral_neg]
  rw [← integral_neg_eq_self (fun y : ℝ => g ((-c : ℝ) + y * I))]
  congr 1; ext y
  rw [← hgh]; congr 1; push_cast; ring

/-- `vline g (−c) = −vline g' c` reflection for an odd integrand. -/
lemma vline_neg_of_odd {g : ℂ → ℂ} (hg : ∀ u, g (-u) = -g u) (c : ℝ) :
    vline g (-c) = -vline g c := by
  unfold vline
  rw [← integral_neg]
  rw [← integral_neg_eq_self (fun y : ℝ => g ((-c : ℝ) + y * I))]
  congr 1; ext y
  rw [← hg]; congr 1; push_cast; ring

theorem vline_gauss_div_neg {a : ℝ} (ha : a < 0) : vline (fun u => cexp (u ^ 2) / u) a = -π := by
  have h := vline_neg_of_odd (g := fun u => cexp (u ^ 2) / u)
    (fun u => by simp [div_neg]) (-a)
  rw [neg_neg] at h
  rw [h, vline_gauss_div (by linarith)]

lemma integrable_gauss_div {c : ℝ} (hc : c ≠ 0) :
    Integrable (fun y : ℝ => cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)) := by
  have hcont : Continuous (fun y : ℝ => cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)) :=
    Continuous.div (by fun_prop) (continuous_line c) (line_ne_zero hc)
  refine Integrable.mono'
    ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)).const_mul (Real.exp (c ^ 2) / |c|))
    hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [norm_div, norm_cexp_sq]
  have hpos : 0 < |c| := abs_pos.2 hc
  rw [div_le_iff₀ (lt_of_lt_of_le hpos (norm_line_ge y))]
  have e : Real.exp (c ^ 2 - y ^ 2) = Real.exp (c ^ 2) * Real.exp (-1 * y ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  calc Real.exp (c ^ 2) * Real.exp (-1 * y ^ 2)
      = Real.exp (c ^ 2) / |c| * Real.exp (-1 * y ^ 2) * |c| := by field_simp
    _ ≤ _ := by gcongr; exact norm_line_ge y

/-! ## The residue at `u = 0` -/

lemma dslope_bdd {F : ℂ → ℂ} {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hF : DifferentiableOn ℂ F (strip a b)) {M : ℝ} (hM : ∀ u ∈ strip a b, ‖F u‖ ≤ M) :
    ∃ M' : ℝ, ∀ u ∈ strip a b, ‖dslope F 0 u‖ ≤ M' := by
  have hD : DifferentiableOn ℂ (dslope F 0) (strip a b) :=
    (Complex.differentiableOn_dslope (strip_mem_nhds (by simpa using ha) (by simpa using hb))).2 hF
  have hKc : IsCompact (strip a b ∩ Metric.closedBall 0 1) :=
    (isCompact_closedBall 0 1).inter_left (isClosed_strip a b)
  obtain ⟨K, hK⟩ := hKc.exists_bound_of_continuousOn (hD.continuousOn.mono inter_subset_left)
  have h0 : (0:ℂ) ∈ strip a b := by simp [strip, ha.le, hb.le]
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 h0)
  refine ⟨max K (2 * M), fun u hu => ?_⟩
  by_cases h1 : ‖u‖ ≤ 1
  · exact (hK u ⟨hu, by simpa using h1⟩).trans (le_max_left _ _)
  · push Not at h1
    have hu0 : u ≠ 0 := by rintro rfl; simp at h1; linarith
    rw [dslope_of_ne _ hu0, slope_def_field, sub_zero, norm_div]
    rw [div_le_iff₀ (by linarith)]
    have hmx : 0 ≤ max K (2 * M) := le_trans (by linarith) (le_max_right _ _)
    calc ‖F u - F 0‖ ≤ ‖F u‖ + ‖F 0‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hM u hu, hM 0 h0]
      _ ≤ max K (2 * M) := le_max_right _ _
      _ ≤ max K (2 * M) * ‖u‖ := le_mul_of_one_le_right hmx h1.le

/-- **Residue at `u = 0`.** For `F` holomorphic and bounded on `a ≤ Re u ≤ b` with `a < 0 < b`,
`∫_{(b)} − ∫_{(a)}` of `F(u) e^{u²}/u` (in `dy`) is `2π F(0)`. -/
theorem vline_residue {F : ℂ → ℂ} {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hF : DifferentiableOn ℂ F (strip a b)) (hM : ∃ M, ∀ u ∈ strip a b, ‖F u‖ ≤ M) :
    vline (fun u => F u * cexp (u ^ 2) / u) b - vline (fun u => F u * cexp (u ^ 2) / u) a =
      2 * π * F 0 := by
  obtain ⟨M, hM⟩ := hM
  obtain ⟨M', hM'⟩ := dslope_bdd ha hb hF hM
  set H : ℂ → ℂ := fun u => dslope F 0 u * cexp (u ^ 2) with hHdef
  have hD : DifferentiableOn ℂ (dslope F 0) (strip a b) :=
    (Complex.differentiableOn_dslope (strip_mem_nhds (by simpa using ha) (by simpa using hb))).2 hF
  have hHd : DifferentiableOn ℂ H (strip a b) :=
    hD.mul (Complex.differentiable_exp.comp (differentiable_pow 2)).differentiableOn
  have hHg : GaussDecay H a b := by
    refine ⟨M' * Real.exp (a ^ 2 + b ^ 2), fun x y hax hxb => ?_⟩
    simp only [hHdef]
    rw [norm_mul, norm_cexp_sq]
    have h1 := hM' _ (mem_strip_line hax hxb y)
    have hx2 : x ^ 2 ≤ a ^ 2 + b ^ 2 := by
      rcases le_total 0 x with h | h <;> nlinarith
    have h2 : Real.exp (x ^ 2 - y ^ 2) ≤ Real.exp (a ^ 2 + b ^ 2) * Real.exp (-(1 / 2) * y ^ 2) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith [sq_nonneg y]
    calc _ ≤ M' * (Real.exp (a ^ 2 + b ^ 2) * Real.exp (-(1 / 2) * y ^ 2)) :=
          mul_le_mul h1 h2 (by positivity) (le_trans (norm_nonneg _) h1)
      _ = _ := by ring
  have hshift := vline_shift (by linarith) hHd hHg
  have hsplit : ∀ c : ℝ, c ≠ 0 → a ≤ c → c ≤ b →
      vline (fun u => F u * cexp (u ^ 2) / u) c =
        vline H c + F 0 * vline (fun u => cexp (u ^ 2) / u) c := by
    intro c hc hac hcb
    unfold vline
    rw [← integral_const_mul, ← integral_add (integrable_line hHd.continuousOn hHg hac hcb)
      ((integrable_gauss_div hc).const_mul _)]
    congr 1; ext y
    have hu := line_ne_zero hc y
    simp only [hHdef]
    rw [dslope_of_ne _ hu, slope_def_field, sub_zero]
    field_simp
    ring
  rw [hsplit b hb.ne' (by linarith) le_rfl, hsplit a ha.ne le_rfl (by linarith), hshift, vline_gauss_div hb,
    vline_gauss_div_neg ha]
  ring

end RamanujanTau.HeckeAFE
