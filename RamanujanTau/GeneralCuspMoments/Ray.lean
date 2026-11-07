/-
# The ray integral of `|D|²` for an abstract `1`-periodic holomorphic `D` on `ℍ`

This is `CriticalMeanSquareAsymp.{Block, RayAsymp}` (the case `D = Δ`, `p = 5`) with the weight
made a parameter: `D : ℂ → ℂ` is holomorphic on `ℍ`, `1`-periodic, and
`|D(z)| (Im z)^{p+1} ≤ M e^{−π Im z}`; `h(y) = y^{2p+2} ∫₀¹ |D(x+iy)|² dx → c₀` as `y → 0⁺`.
For a cusp form `f` of weight `k = 2p+2`, `D = f` and `c₀ = (3/π)‖f‖²`.

Along a ray `τ = σw + iκw` (`σ = ±1`, `w > 0`) with `R(u) = G(s e^u) (s e^u)/s^{2p+2}`,
`G(w) = w^{2p+1}|D(σw+iκw)|²`:

    κ^{2p+2} ∫_0^∞ R / log(1/κ) → c₀        as κ = cot β → 0⁺ (`ray_tendsto`).
-/
import RamanujanTau.CriticalMeanSquareAsymp.Harmonic

set_option autoImplicit false

namespace RamanujanTau.GeneralCuspMoments

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.CriticalMeanSquareAsymp
open scoped Real Interval

/-- The point `x + iy`. -/
noncomputable def pz (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * I

@[simp] lemma pz_im (x y : ℝ) : (pz x y).im = y := by simp [pz]
@[simp] lemma pz_re (x y : ℝ) : (pz x y).re = x := by simp [pz]

/-- Horizontal mean `H(y) = ∫₀¹ |D(x+iy)|² dx`. -/
noncomputable def HhD (D : ℂ → ℂ) (y : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, ‖D (pz x y)‖ ^ 2

/-- Hypotheses on `D`. -/
structure RayHyp (p : ℕ) (D : ℂ → ℂ) (c₀ : ℝ) : Prop where
  diff : DifferentiableOn ℂ D {z : ℂ | 0 < z.im}
  per : ∀ z, D (z + 1) = D z
  bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 0 < z.im →
    ‖D z‖ * z.im ^ (p + 1) ≤ M * Real.exp (-(π * z.im))
  horo : Tendsto (fun y => y ^ (2 * p + 2) * HhD D y) (𝓝[>] 0) (𝓝 c₀)

variable {p : ℕ} {D : ℂ → ℂ} {c₀ : ℝ}

lemma RayHyp.continuousOn (h : RayHyp p D c₀) : ContinuousOn D {z : ℂ | 0 < z.im} :=
  h.diff.continuousOn

lemma RayHyp.bounds (h : RayHyp p D c₀) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 0 < z.im →
    ‖D z‖ ≤ M / z.im ^ (p + 1) ∧ ‖D z‖ * z.im ^ (p + 1) ≤ M * Real.exp (-(π * z.im)) := by
  obtain ⟨M, hM0, hM⟩ := h.bound
  refine ⟨M, hM0, fun z hz => ⟨?_, hM z hz⟩⟩
  have hy : 0 < z.im ^ (p + 1) := by positivity
  have he : Real.exp (-(π * z.im)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := mul_pos Real.pi_pos hz; linarith)
  rw [le_div_iff₀ hy]
  calc ‖D z‖ * z.im ^ (p + 1) ≤ M * Real.exp (-(π * z.im)) := hM z hz
    _ ≤ M * 1 := by gcongr
    _ = M := mul_one M

/-- **Vertical Lipschitz bound** (Cauchy estimate). -/
lemma RayHyp.lip (h : RayHyp p D c₀) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x y₁ y₂ y₀ : ℝ, 0 < y₀ → y₀ ≤ y₁ →
    y₀ ≤ y₂ → ‖D (pz x y₁) - D (pz x y₂)‖ ≤ A * |y₁ - y₂| / y₀ ^ (p + 2) := by
  obtain ⟨M, hM0, hMb'⟩ := h.bounds
  have hMb : ∀ z : ℂ, 0 < z.im → ‖D z‖ ≤ M / z.im ^ (p + 1) := fun z hz => (hMb' z hz).1
  refine ⟨2 ^ (p + 2) * M, by positivity, fun x y₁ y₂ y₀ hy₀ h1 h2 => ?_⟩
  set R : ℝ := y₀ / 2 with hR
  have hR0 : 0 < R := by positivity
  have hder : ∀ z : ℂ, y₀ ≤ z.im → ‖deriv D z‖ ≤ 2 ^ (p + 2) * M / y₀ ^ (p + 2) := by
    intro z hz
    have hsub : closure (Metric.ball z R) ⊆ {w : ℂ | 0 < w.im} := by
      rw [closure_ball z hR0.ne']
      intro w hw
      have hd : |w.im - z.im| ≤ R := by
        have := Complex.abs_im_le_norm (w - z)
        rw [Complex.sub_im] at this
        exact this.trans (by simpa [dist_eq_norm] using hw)
      show 0 < w.im
      have := neg_abs_le (w.im - z.im)
      rw [hR] at hd; linarith
    have hd : DiffContOnCl ℂ D (Metric.ball z R) := (h.diff.mono hsub).diffContOnCl
    have hsph : ∀ w ∈ Metric.sphere z R, ‖D w‖ ≤ M / R ^ (p + 1) := by
      intro w hw
      have hd' : |w.im - z.im| ≤ R := by
        have := Complex.abs_im_le_norm (w - z)
        rw [Complex.sub_im] at this
        exact this.trans (mem_sphere_iff_norm.mp hw).le
      have hwim : R ≤ w.im := by
        have := neg_abs_le (w.im - z.im)
        rw [hR] at hd' ⊢; linarith
      have hw0 : 0 < w.im := by linarith
      refine (hMb w hw0).trans ?_
      gcongr
    have := norm_deriv_le_of_forall_mem_sphere_norm_le hR0 hd hsph
    refine this.trans (le_of_eq ?_)
    rw [hR, div_div, ← pow_succ, div_pow]
    field_simp
  set φ : ℝ → ℂ := fun y => D (pz x y) with hφ
  have hφd : ∀ y ∈ Ici y₀, HasDerivWithinAt φ (deriv D (pz x y) * I) (Ici y₀) y := by
    intro y hy
    have hy' : 0 < (pz x y).im := by simp; exact lt_of_lt_of_le hy₀ hy
    have hDa : DifferentiableAt ℂ D (pz x y) :=
      h.diff.differentiableAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hy')
    have hg : HasDerivAt (fun y : ℝ => pz x y) I y := by
      have := ((hasDerivAt_id (y : ℂ)).comp_ofReal (z := y)).mul_const I
      simp only [id, one_mul] at this
      exact this.const_add (x : ℂ)
    exact (hDa.hasDerivAt.comp y hg).hasDerivWithinAt
  have hbd : ∀ y ∈ Ici y₀, ‖deriv D (pz x y) * I‖ ≤ 2 ^ (p + 2) * M / y₀ ^ (p + 2) := by
    intro y hy
    rw [norm_mul, Complex.norm_I, mul_one]
    exact hder _ (by simpa using hy)
  have := (convex_Ici y₀).norm_image_sub_le_of_norm_hasDerivWithin_le hφd hbd
    (show y₂ ∈ Ici y₀ from h2) (show y₁ ∈ Ici y₀ from h1)
  simp only [hφ, Real.norm_eq_abs] at this
  calc ‖D (pz x y₁) - D (pz x y₂)‖ ≤ 2 ^ (p + 2) * M / y₀ ^ (p + 2) * |y₁ - y₂| := this
    _ = 2 ^ (p + 2) * M * |y₁ - y₂| / y₀ ^ (p + 2) := by ring

/-! ### Blocks -/

/-- The signed ray integrand `w^{2p+1} |D(σw + iκw)|²`. -/
noncomputable def Gsig (p : ℕ) (D : ℂ → ℂ) (σ κ w : ℝ) : ℝ :=
  w ^ (2 * p + 1) * ‖D (pz (σ * w) (κ * w))‖ ^ 2

lemma Gsig_nonneg (σ κ : ℝ) {w : ℝ} (hw : 0 ≤ w) : 0 ≤ Gsig p D σ κ w := by
  unfold Gsig; positivity

lemma continuousOn_Gsig (h : RayHyp p D c₀) (σ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ContinuousOn (Gsig p D σ κ) (Ioi 0) := by
  have hc : Continuous fun w : ℝ => pz (σ * w) (κ * w) := by unfold pz; fun_prop
  have h1 : ContinuousOn (fun w : ℝ => D (pz (σ * w) (κ * w))) (Ioi 0) :=
    h.continuousOn.comp hc.continuousOn (fun w hw => by
      show 0 < (pz (σ * w) (κ * w)).im
      rw [pz_im]; exact mul_pos hκ hw)
  exact (continuousOn_pow _).mul (h1.norm.pow 2)

lemma continuous_D_horiz (h : RayHyp p D c₀) (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    Continuous fun w : ℝ => D (pz (σ * w) y) :=
  h.continuousOn.comp_continuous (by unfold pz; fun_prop) (fun w => by
    show 0 < (pz (σ * w) y).im
    rw [pz_im]; exact hy)

lemma integral_period_sig (h : RayHyp p D c₀) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (y a : ℝ) :
    ∫ w in a..a + 1, ‖D (pz (σ * w) y)‖ ^ 2 = HhD D y := by
  have hper : Function.Periodic (fun x : ℝ => ‖D (pz x y)‖ ^ 2) 1 := by
    intro x
    simp only
    rw [show pz (x + 1) y = pz x y + 1 by simp [pz]; ring, h.per]
  rcases hσ with rfl | rfl
  · simp only [one_mul]
    have := hper.intervalIntegral_add_eq a 0
    rw [this, zero_add]
    rfl
  · simp only [neg_one_mul]
    have h2 := intervalIntegral.integral_comp_neg (a := a) (b := a + 1)
      (fun x : ℝ => ‖D (pz x y)‖ ^ 2)
    simp only at h2
    rw [h2]
    have := hper.intervalIntegral_add_eq (-(a + 1)) 0
    rw [show -a = -(a + 1) + 1 by ring, this, zero_add]
    rfl

lemma pow_succ_diff_le' {x : ℝ} (hx : 1 ≤ x) (N : ℕ) :
    (x + 1) ^ (N + 1) - x ^ (N + 1) ≤ (2 ^ (N + 1) - 1) * x ^ N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    have hxN : 0 ≤ x ^ N := by positivity
    have e : (x + 1) ^ (N + 1 + 1) - x ^ (N + 1 + 1) =
        (x + 1) * ((x + 1) ^ (N + 1) - x ^ (N + 1)) + x ^ (N + 1) := by ring
    rw [e]
    have h2N : (1 : ℝ) ≤ 2 ^ (N + 1) := one_le_pow₀ (by norm_num)
    have h1 : (x + 1) * ((x + 1) ^ (N + 1) - x ^ (N + 1)) ≤
        (2 * x) * ((2 ^ (N + 1) - 1) * x ^ N) := by
      have h0 : 0 ≤ (x + 1) ^ (N + 1) - x ^ (N + 1) := by
        have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ x) (by linarith : x ≤ x + 1) (N + 1)
        linarith
      exact mul_le_mul (by linarith) ih h0 (by nlinarith)
    calc (x + 1) * ((x + 1) ^ (N + 1) - x ^ (N + 1)) + x ^ (N + 1)
        ≤ (2 * x) * ((2 ^ (N + 1) - 1) * x ^ N) + x ^ (N + 1) := by linarith
      _ = (2 ^ (N + 1 + 1) - 1) * x ^ (N + 1) := by ring

lemma pow_succ_diff_le {x : ℝ} (hx : 1 ≤ x) (N : ℕ) :
    (x + 1) ^ (N + 1) - x ^ (N + 1) ≤ 2 ^ (N + 1) * x ^ N := by
  have := pow_succ_diff_le' hx N
  have : 0 ≤ x ^ N := by positivity
  nlinarith

/-- **Sharp block comparison.** -/
lemma block_sharp (h : RayHyp p D c₀) {M A : ℝ} (hM0 : 0 ≤ M) (hA0 : 0 ≤ A)
    (hM : ∀ z : ℂ, 0 < z.im → ‖D z‖ ≤ M / z.im ^ (p + 1))
    (hA : ∀ x y₁ y₂ y₀ : ℝ, 0 < y₀ → y₀ ≤ y₁ → y₀ ≤ y₂ →
      ‖D (pz x y₁) - D (pz x y₂)‖ ≤ A * |y₁ - y₂| / y₀ ^ (p + 2))
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {κ N : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) :
    |(∫ w in N..N + 1, Gsig p D σ κ w) - N ^ (2 * p + 1) * HhD D (κ * N)| ≤
      (2 ^ (2 * p + 1) * M ^ 2 + 2 * A * M) / (κ ^ (2 * p + 2) * N ^ 2) := by
  have hN0 : 0 < N := by linarith
  set y₀ : ℝ := κ * N with hy₀
  have hy₀0 : 0 < y₀ := mul_pos hκ hN0
  set f : ℝ → ℝ := fun w => ‖D (pz (σ * w) y₀)‖ ^ 2 with hf
  have hfc : Continuous f := (continuous_D_horiz h σ hy₀0).norm.pow 2
  set B : ℝ := (2 ^ (2 * p + 1) * M ^ 2 + 2 * A * M) / (κ ^ (2 * p + 2) * N ^ 2) with hB
  have hpt : ∀ w ∈ Ι N (N + 1), ‖Gsig p D σ κ w - N ^ (2 * p + 1) * f w‖ ≤ B := by
    intro w hw
    rw [uIoc_of_le (by linarith)] at hw
    obtain ⟨hw1, hw2⟩ := hw
    have hw1' : N ≤ w := hw1.le
    have hw0 : 0 < w := by linarith
    set a := D (pz (σ * w) (κ * w))
    set b := D (pz (σ * w) y₀)
    have hy₀w : y₀ ≤ κ * w := by rw [hy₀]; gcongr
    have ha : ‖a‖ ≤ M / y₀ ^ (p + 1) := by
      refine (hM _ (by rw [pz_im]; positivity)).trans ?_
      rw [pz_im]; gcongr
    have hb : ‖b‖ ≤ M / y₀ ^ (p + 1) := by
      refine (hM _ (by rw [pz_im]; positivity)).trans ?_
      rw [pz_im]
    have hab : ‖a - b‖ ≤ A * κ / y₀ ^ (p + 2) := by
      have h := hA (σ * w) (κ * w) y₀ y₀ hy₀0 hy₀w le_rfl
      have habs : |κ * w - y₀| ≤ κ := by
        rw [hy₀, ← mul_sub, abs_of_nonneg (by nlinarith)]
        nlinarith
      refine h.trans ?_
      rw [div_le_div_iff_of_pos_right (by positivity)]
      exact mul_le_mul_of_nonneg_left habs hA0
    have hsq : |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ A * κ / y₀ ^ (p + 2) * (2 * (M / y₀ ^ (p + 1))) := by
      have e : ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) := by ring
      rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖a‖ + ‖b‖)]
      have h1 : |‖a‖ - ‖b‖| ≤ ‖a - b‖ := abs_norm_sub_norm_le a b
      have h2 : ‖a‖ + ‖b‖ ≤ 2 * (M / y₀ ^ (p + 1)) := by linarith
      exact mul_le_mul (h1.trans hab) h2 (by positivity) (by positivity)
    have hw11 : N ^ (2 * p + 1) ≤ w ^ (2 * p + 1) := pow_le_pow_left₀ hN0.le hw1' _
    have hw11' : w ^ (2 * p + 1) - N ^ (2 * p + 1) ≤ 2 ^ (2 * p + 1) * N ^ (2 * p) := by
      have := pow_le_pow_left₀ hw0.le hw2 (2 * p + 1)
      have := pow_succ_diff_le hN (2 * p)
      linarith
    have ha2 : ‖a‖ ^ 2 ≤ (M / y₀ ^ (p + 1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
    have e : Gsig p D σ κ w - N ^ (2 * p + 1) * f w = (w ^ (2 * p + 1) - N ^ (2 * p + 1)) * ‖a‖ ^ 2 +
        N ^ (2 * p + 1) * (‖a‖ ^ 2 - ‖b‖ ^ 2) := by
      simp only [Gsig, hf, a, b]; ring
    rw [Real.norm_eq_abs, e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ N ^ (2 * p + 1))]
    have t1 : (w ^ (2 * p + 1) - N ^ (2 * p + 1)) * ‖a‖ ^ 2 ≤
        2 ^ (2 * p + 1) * N ^ (2 * p) * (M / y₀ ^ (p + 1)) ^ 2 :=
      mul_le_mul hw11' ha2 (by positivity) (by positivity)
    have t2 : N ^ (2 * p + 1) * |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤
        N ^ (2 * p + 1) * (A * κ / y₀ ^ (p + 2) * (2 * (M / y₀ ^ (p + 1)))) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have e2 : 2 ^ (2 * p + 1) * N ^ (2 * p) * (M / y₀ ^ (p + 1)) ^ 2 +
        N ^ (2 * p + 1) * (A * κ / y₀ ^ (p + 2) * (2 * (M / y₀ ^ (p + 1)))) = B := by
      rw [hB, hy₀]; field_simp; ring
    linarith
  have hint2 : IntervalIntegrable (Gsig p D σ κ) volume N (N + 1) := by
    refine ContinuousOn.intervalIntegrable ((continuousOn_Gsig h σ hκ).mono ?_)
    rw [uIcc_of_le (by linarith)]
    intro w hw; exact lt_of_lt_of_le hN0 hw.1
  have hint1 : IntervalIntegrable (fun w => N ^ (2 * p + 1) * f w) volume N (N + 1) :=
    (hfc.const_mul _).intervalIntegrable _ _
  have hval : ∫ w in N..N + 1, N ^ (2 * p + 1) * f w = N ^ (2 * p + 1) * HhD D y₀ := by
    rw [intervalIntegral.integral_const_mul, hf, integral_period_sig h hσ]
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [intervalIntegral.integral_sub hint2 hint1, hval, Real.norm_eq_abs] at hbd
  rw [show N + 1 - N = 1 by ring, abs_one, mul_one] at hbd
  exact hbd

lemma sum_inv_sq_le' (n : ℕ) :
    ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 2 - 2 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have key : 1 / ((n : ℝ) + 1) ^ 2 ≤ 2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 1 + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    push_cast
    linarith

/-- The horocycle mean `h(y) = y^{2p+2} H(y)`. -/
noncomputable def hD (p : ℕ) (D : ℂ → ℂ) (y : ℝ) : ℝ := y ^ (2 * p + 2) * HhD D y

/-- **Summed blocks** `N = 1, …, n`. -/
lemma sum_sharp (h : RayHyp p D c₀) {M A : ℝ} (hM0 : 0 ≤ M) (hA0 : 0 ≤ A)
    (hM : ∀ z : ℂ, 0 < z.im → ‖D z‖ ≤ M / z.im ^ (p + 1))
    (hA : ∀ x y₁ y₂ y₀ : ℝ, 0 < y₀ → y₀ ≤ y₁ → y₀ ≤ y₂ →
      ‖D (pz x y₁) - D (pz x y₂)‖ ≤ A * |y₁ - y₂| / y₀ ^ (p + 2))
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    |κ ^ (2 * p + 2) * (∫ w in (1 : ℝ)..(n : ℝ) + 1, Gsig p D σ κ w) -
      ∑ j ∈ Finset.range n, hD p D (κ * ((j : ℝ) + 1)) / ((j : ℝ) + 1)| ≤
      2 * (2 ^ (2 * p + 1) * M ^ 2 + 2 * A * M) := by
  set B := 2 ^ (2 * p + 1) * M ^ 2 + 2 * A * M with hB
  have hB0 : 0 ≤ B := by positivity
  have hκ12 : 0 < κ ^ (2 * p + 2) := by positivity
  have hii : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → IntervalIntegrable (Gsig p D σ κ) volume a b := by
    intro a b ha hb
    refine ContinuousOn.intervalIntegrable ((continuousOn_Gsig h σ hκ).mono ?_)
    intro w hw
    have : (1 : ℝ) ≤ min a b := le_min ha hb
    show 0 < w
    linarith [hw.1]
  suffices H : ∀ n : ℕ, |κ ^ (2 * p + 2) * (∫ w in (1 : ℝ)..(n : ℝ) + 1, Gsig p D σ κ w) -
      ∑ j ∈ Finset.range n, hD p D (κ * ((j : ℝ) + 1)) / ((j : ℝ) + 1)| ≤
      B * ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 by
    refine (H n).trans ?_
    have h1 := sum_inv_sq_le' n
    have h2 : 0 ≤ 2 / ((n : ℝ) + 1) := by positivity
    nlinarith
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hsplit : ∫ w in (1 : ℝ)..((n + 1 : ℕ) : ℝ) + 1, Gsig p D σ κ w =
        (∫ w in (1 : ℝ)..(n : ℝ) + 1, Gsig p D σ κ w) +
          ∫ w in (n : ℝ) + 1..(n : ℝ) + 1 + 1, Gsig p D σ κ w := by
      push_cast
      exact (intervalIntegral.integral_add_adjacent_intervals (hii _ _ le_rfl hn1)
        (hii _ _ hn1 (by linarith))).symm
    have hblk := block_sharp h hM0 hA0 hM hA hσ hκ hn1
    rw [hsplit, Finset.sum_range_succ, Finset.sum_range_succ]
    have hA' : hD p D (κ * ((n : ℝ) + 1)) / ((n : ℝ) + 1) =
        κ ^ (2 * p + 2) * (((n : ℝ) + 1) ^ (2 * p + 1) * HhD D (κ * ((n : ℝ) + 1))) := by
      unfold hD
      have hn0 : (n : ℝ) + 1 ≠ 0 := by positivity
      rw [mul_pow, show 2 * p + 2 = (2 * p + 1) + 1 by ring, pow_succ ((n : ℝ) + 1) (2 * p + 1)]
      field_simp
    rw [hA']
    have hblk' : |κ ^ (2 * p + 2) * (∫ w in (n : ℝ) + 1..(n : ℝ) + 1 + 1, Gsig p D σ κ w) -
        κ ^ (2 * p + 2) * (((n : ℝ) + 1) ^ (2 * p + 1) * HhD D (κ * ((n : ℝ) + 1)))| ≤
          B * (1 / ((n : ℝ) + 1) ^ 2) := by
      rw [← mul_sub, abs_mul, abs_of_pos hκ12]
      calc κ ^ (2 * p + 2) * |_| ≤ κ ^ (2 * p + 2) * (B / (κ ^ (2 * p + 2) * ((n : ℝ) + 1) ^ 2)) :=
            mul_le_mul_of_nonneg_left hblk hκ12.le
        _ = B * (1 / ((n : ℝ) + 1) ^ 2) := by field_simp
    set I1 := ∫ w in (1 : ℝ)..(n : ℝ) + 1, Gsig p D σ κ w
    set I2 := ∫ w in (n : ℝ) + 1..(n : ℝ) + 1 + 1, Gsig p D σ κ w
    set S1 := ∑ j ∈ Finset.range n, hD p D (κ * ((j : ℝ) + 1)) / ((j : ℝ) + 1)
    set T2 := κ ^ (2 * p + 2) * (((n : ℝ) + 1) ^ (2 * p + 1) * HhD D (κ * ((n : ℝ) + 1)))
    have e : κ ^ (2 * p + 2) * (I1 + I2) - (S1 + T2) =
        (κ ^ (2 * p + 2) * I1 - S1) + (κ ^ (2 * p + 2) * I2 - T2) := by ring
    rw [e, mul_add]
    exact (abs_add_le _ _).trans (add_le_add ih hblk')

/-! ### One ray -/

/-- Change of variables `w = s e^u` for a general ray integrand. -/
lemma integral_change {R g : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (hg : ContinuousOn g (Ioi 0))
    (hR : ∀ u, R u = g (s * Real.exp u) / s ^ (2 * p + 2) * (s * Real.exp u)) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∫ u in Real.log (a / s)..Real.log (b / s), R u = (∫ w in a..b, g w) / s ^ (2 * p + 2) := by
  have hcv := intervalIntegral.integral_comp_mul_deriv'
    (a := Real.log (a / s)) (b := Real.log (b / s))
    (f := fun u => s * Real.exp u) (f' := fun u => s * Real.exp u)
    (g := fun w => g w / s ^ (2 * p + 2))
    (fun u _ => (Real.hasDerivAt_exp u).const_mul s)
    (continuous_const.mul Real.continuous_exp).continuousOn
    ((hg.div_const _).mono (by
      rintro _ ⟨u, _, rfl⟩; show 0 < s * Real.exp u; positivity))
  simp only [Function.comp_apply] at hcv
  rw [Real.exp_log (div_pos ha hs), Real.exp_log (div_pos hb hs),
    mul_div_cancel₀ _ hs.ne', mul_div_cancel₀ _ hs.ne'] at hcv
  rw [← intervalIntegral.integral_div, ← hcv]
  exact intervalIntegral.integral_congr (fun u _ => hR u)

/-- Cusp tail. -/
lemma tail_bound {σ s κ M U : ℝ} {R : ℝ → ℝ} (hs : 0 < s) (hκ : 0 < κ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖D z‖ * z.im ^ (p + 1) ≤ M * Real.exp (-(π * z.im)))
    (hR : ∀ u, R u = Gsig p D σ κ (s * Real.exp u) / s ^ (2 * p + 2) * (s * Real.exp u))
    (hRi : IntegrableOn R (Ioi U)) (hU : 1 ≤ κ * (s * Real.exp U)) :
    κ ^ (2 * p + 2) * ∫ u in Ioi U, R u ≤ M ^ 2 / s ^ (2 * p + 2) := by
  have hpt : ∀ u ∈ Ioi U, κ ^ (2 * p + 2) * R u ≤
      M ^ 2 / s ^ (2 * p + 2) * Real.exp U * Real.exp (-u) := by
    intro u hu
    have hu' : U < u := hu
    set w := s * Real.exp u with hw
    have hw0 : 0 < w := by positivity
    have him : 0 < (pz (σ * w) (κ * w)).im := by rw [pz_im]; positivity
    have hb := hM _ him
    rw [pz_im] at hb
    have hκw : u - U ≤ κ * w := by
      have h1 : κ * w = κ * (s * Real.exp U) * Real.exp (u - U) := by
        rw [hw, Real.exp_sub]; field_simp
      have h2 : u - U + 1 ≤ Real.exp (u - U) := Real.add_one_le_exp _
      have h3 : 1 * Real.exp (u - U) ≤ κ * (s * Real.exp U) * Real.exp (u - U) :=
        mul_le_mul_of_nonneg_right hU (Real.exp_pos _).le
      linarith
    have hexp : Real.exp (-(π * (κ * w))) ^ 2 ≤ Real.exp U * Real.exp (-u) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : 1 ≤ π := by linarith [Real.pi_gt_three]
      have hκw0 : 0 ≤ κ * w := by positivity
      push_cast; nlinarith
    have hsq : (‖D (pz (σ * w) (κ * w))‖ * (κ * w) ^ (p + 1)) ^ 2 ≤
        M ^ 2 * (Real.exp U * Real.exp (-u)) := by
      have h0 : 0 ≤ ‖D (pz (σ * w) (κ * w))‖ * (κ * w) ^ (p + 1) := by positivity
      calc (‖D (pz (σ * w) (κ * w))‖ * (κ * w) ^ (p + 1)) ^ 2 ≤
            (M * Real.exp (-(π * (κ * w)))) ^ 2 := pow_le_pow_left₀ h0 hb 2
        _ = M ^ 2 * Real.exp (-(π * (κ * w))) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
    rw [hR u, ← hw]
    unfold Gsig
    have e : κ ^ (2 * p + 2) * (w ^ (2 * p + 1) * ‖D (pz (σ * w) (κ * w))‖ ^ 2 / s ^ (2 * p + 2) * w) =
        (‖D (pz (σ * w) (κ * w))‖ * (κ * w) ^ (p + 1)) ^ 2 / s ^ (2 * p + 2) := by ring
    rw [e, show M ^ 2 / s ^ (2 * p + 2) * Real.exp U * Real.exp (-u) =
      M ^ 2 * (Real.exp U * Real.exp (-u)) / s ^ (2 * p + 2) by ring]
    gcongr
  have hint2 : IntegrableOn (fun u => M ^ 2 / s ^ (2 * p + 2) * Real.exp U * Real.exp (-u)) (Ioi U) :=
    (integrableOn_exp_neg_Ioi U).const_mul _
  rw [← integral_const_mul]
  refine (setIntegral_mono_on (hRi.const_mul _) hint2 measurableSet_Ioi hpt).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_neg_Ioi, mul_assoc, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, mul_one]

/-- **One ray, decomposed.** -/
lemma ray_decomp (h : RayHyp p D c₀) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {M A : ℝ} (hM0 : 0 ≤ M)
    (hA0 : 0 ≤ A)
    (hMb : ∀ z : ℂ, 0 < z.im → ‖D z‖ ≤ M / z.im ^ (p + 1) ∧
      ‖D z‖ * z.im ^ (p + 1) ≤ M * Real.exp (-(π * z.im)))
    (hA : ∀ x y₁ y₂ y₀ : ℝ, 0 < y₀ → y₀ ≤ y₁ → y₀ ≤ y₂ →
      ‖D (pz x y₁) - D (pz x y₂)‖ ≤ A * |y₁ - y₂| / y₀ ^ (p + 2))
    {s κ : ℝ} (hs : 1 / 2 ≤ s) (hs1 : s < 1) (hκ : 0 < κ) (hκ1 : κ < 1) {R : ℝ → ℝ}
    (hR : ∀ u, R u = Gsig p D σ κ (s * Real.exp u) / s ^ (2 * p + 2) * (s * Real.exp u))
    (hRi : Integrable R) :
    |s ^ (2 * p + 2) * (κ ^ (2 * p + 2) * ∫ u in Ioi 0, R u) -
      ∑ j ∈ Finset.range ⌊1 / κ⌋₊, hD p D (κ * ((j : ℝ) + 1)) / ((j : ℝ) + 1)| ≤
      2 * M ^ 2 + 2 * (2 ^ (2 * p + 1) * M ^ 2 + 2 * A * M) := by
  have hs0 : 0 < s := by linarith
  set n := ⌊1 / κ⌋₊ with hn
  set N₂ : ℝ := (n : ℝ) + 1 with hN₂
  have hN₂1 : 1 ≤ N₂ := by rw [hN₂]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hκN : 1 ≤ κ * N₂ := by
    have := Nat.lt_floor_add_one (1 / κ)
    rw [← hn, div_lt_iff₀ hκ] at this
    rw [hN₂]; linarith
  set U := Real.log (N₂ / s) with hU
  have hU0 : 0 ≤ U := Real.log_nonneg (by rw [le_div_iff₀ hs0]; linarith)
  have hsU : s * Real.exp U = N₂ := by rw [hU, Real.exp_log (by positivity)]; field_simp
  have hR0 : ∀ u, 0 ≤ R u := fun u => by
    rw [hR u]
    have := Gsig_nonneg (p := p) (D := D) σ κ (show 0 ≤ s * Real.exp u by positivity)
    positivity
  have hsplit : ∫ u in Ioi 0, R u = (∫ u in (0 : ℝ)..U, R u) + ∫ u in Ioi U, R u := by
    rw [← Ioc_union_Ioi_eq_Ioi hU0, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      hRi.integrableOn hRi.integrableOn, intervalIntegral.integral_of_le hU0]
  have hcv : ∫ u in (0 : ℝ)..U, R u = (∫ w in s..N₂, Gsig p D σ κ w) / s ^ (2 * p + 2) := by
    have := integral_change (p := p) hs0 (continuousOn_Gsig h σ hκ) hR hs0 (by positivity : 0 < N₂)
    rw [div_self hs0.ne', Real.log_one] at this
    exact this
  have hii : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable (Gsig p D σ κ) volume a b := by
    intro a b ha hb
    refine ContinuousOn.intervalIntegrable ((continuousOn_Gsig h σ hκ).mono ?_)
    intro w hw
    show 0 < w
    have : 0 < min a b := lt_min ha hb
    linarith [hw.1]
  have hsplit2 : ∫ w in s..N₂, Gsig p D σ κ w =
      (∫ w in s..1, Gsig p D σ κ w) + ∫ w in (1 : ℝ)..N₂, Gsig p D σ κ w :=
    (intervalIntegral.integral_add_adjacent_intervals (hii _ _ hs0 one_pos)
      (hii _ _ one_pos (by linarith))).symm
  have hκ12 : 0 < κ ^ (2 * p + 2) := by positivity
  have hP1 : 0 ≤ κ ^ (2 * p + 2) * ∫ w in s..1, Gsig p D σ κ w ∧
      κ ^ (2 * p + 2) * ∫ w in s..1, Gsig p D σ κ w ≤ M ^ 2 := by
    constructor
    · exact mul_nonneg hκ12.le (intervalIntegral.integral_nonneg hs1.le fun w hw =>
        Gsig_nonneg σ κ (by linarith [hw.1]))
    · have hpt : ∀ w ∈ Ι s 1, ‖κ ^ (2 * p + 2) * Gsig p D σ κ w‖ ≤ 2 * M ^ 2 := by
        intro w hw
        rw [uIoc_of_le hs1.le] at hw
        obtain ⟨hw1, hw2⟩ := hw
        have hw0 : 0 < w := by linarith
        have him : 0 < (pz (σ * w) (κ * w)).im := by rw [pz_im]; positivity
        have hb := (hMb _ him).1
        rw [pz_im] at hb
        have hb2 : ‖D (pz (σ * w) (κ * w))‖ ^ 2 ≤ (M / (κ * w) ^ (p + 1)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hκ12.le (Gsig_nonneg σ κ hw0.le))]
        unfold Gsig
        have e : κ ^ (2 * p + 2) * (w ^ (2 * p + 1) * (M / (κ * w) ^ (p + 1)) ^ 2) = M ^ 2 / w := by
          field_simp; ring
        have h1 : κ ^ (2 * p + 2) * (w ^ (2 * p + 1) * ‖D (pz (σ * w) (κ * w))‖ ^ 2) ≤ M ^ 2 / w := by
          rw [← e]; gcongr
        have h2 : M ^ 2 / w ≤ 2 * M ^ 2 := by
          rw [div_le_iff₀ hw0]; nlinarith [sq_nonneg M]
        linarith
      have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs] at this
      have h3 := (le_abs_self _).trans this
      have h4 : 2 * M ^ 2 * |1 - s| ≤ M ^ 2 := by
        rw [abs_of_pos (by linarith)]; nlinarith [sq_nonneg M]
      linarith
  have hP3 : 0 ≤ κ ^ (2 * p + 2) * ∫ u in Ioi U, R u ∧
      κ ^ (2 * p + 2) * ∫ u in Ioi U, R u ≤ M ^ 2 / s ^ (2 * p + 2) := by
    refine ⟨mul_nonneg hκ12.le (setIntegral_nonneg measurableSet_Ioi fun u _ => hR0 u), ?_⟩
    exact tail_bound hs0 hκ (fun z hz => (hMb z hz).2) hR hRi.integrableOn (by rw [hsU]; exact hκN)
  have hP2 := sum_sharp h hM0 hA0 (fun z hz => (hMb z hz).1) hA hσ hκ n
  rw [← hN₂] at hP2
  have hs12 : 0 < s ^ (2 * p + 2) := by positivity
  have eq : s ^ (2 * p + 2) * (κ ^ (2 * p + 2) * ∫ u in Ioi 0, R u) =
      κ ^ (2 * p + 2) * (∫ w in s..1, Gsig p D σ κ w) +
        κ ^ (2 * p + 2) * (∫ w in (1 : ℝ)..N₂, Gsig p D σ κ w) +
        s ^ (2 * p + 2) * (κ ^ (2 * p + 2) * ∫ u in Ioi U, R u) := by
    rw [hsplit, hcv, hsplit2]; field_simp
  rw [eq]
  have hP3' : s ^ (2 * p + 2) * (κ ^ (2 * p + 2) * ∫ u in Ioi U, R u) ≤ M ^ 2 := by
    have := mul_le_mul_of_nonneg_left hP3.2 hs12.le
    rwa [mul_div_cancel₀ _ hs12.ne'] at this
  have hP3'' : 0 ≤ s ^ (2 * p + 2) * (κ ^ (2 * p + 2) * ∫ u in Ioi U, R u) := mul_nonneg hs12.le hP3.1
  rw [abs_le] at hP2 ⊢
  constructor <;> linarith [hP1.1, hP1.2]

/-- `cot β → 0⁺` as `β → π/2⁻`. -/
lemma tendsto_cot' : Tendsto (fun β => Real.cos β / Real.sin β) (𝓝[<] (π / 2)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : ContinuousAt (fun β => Real.cos β / Real.sin β) (π / 2) :=
      Real.continuous_cos.continuousAt.div Real.continuous_sin.continuousAt (by simp)
    have := h.tendsto
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT (show 0 < π / 2 by positivity)] with β hβ
    exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [hβ.1, Real.pi_pos], hβ.2⟩)
      (Real.sin_pos_of_pos_of_lt_pi hβ.1 (by linarith [hβ.2, Real.pi_pos]))

lemma tendsto_sin_pow' (N : ℕ) : Tendsto (fun β => Real.sin β ^ N) (𝓝[<] (π / 2)) (𝓝 1) := by
  have := (Real.continuous_sin.pow N).continuousAt (x := π / 2) |>.tendsto
  simp only [Real.sin_pi_div_two, one_pow] at this
  exact this.mono_left nhdsWithin_le_nhds

lemma alg_identity' {a L S t : ℝ} (ht : t ≠ 0) (hL : L ≠ 0) :
    a / L = (S / L + (t * a - S) / L) / t := by
  field_simp; ring

/-- **`κ^{2p+2} ∫_0^∞ R / log(1/κ) → c₀` along one ray.** -/
lemma ray_tendsto (h : RayHyp p D c₀) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {R : ℝ → ℝ → ℝ}
    (hR : ∀ β, 0 < Real.sin β → ∀ u, R β u =
      Gsig p D σ (Real.cos β / Real.sin β) (Real.sin β * Real.exp u) / Real.sin β ^ (2 * p + 2) *
        (Real.sin β * Real.exp u))
    (hRi : ∀ β, 0 < β → β < π / 2 → Integrable (R β)) :
    Tendsto (fun β => (Real.cos β / Real.sin β) ^ (2 * p + 2) * (∫ u in Ioi 0, R β u) /
      Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2)) (𝓝 c₀) := by
  obtain ⟨M, hM0, hMb⟩ := h.bounds
  obtain ⟨A, hA0, hA⟩ := h.lip
  set C₁ := 2 * M ^ 2 + 2 * (2 ^ (2 * p + 1) * M ^ 2 + 2 * A * M) with hC₁
  set Sm : ℝ → ℝ := fun κ => ∑ j ∈ Finset.range ⌊1 / κ⌋₊,
    hD p D (κ * ((j : ℝ) + 1)) / ((j : ℝ) + 1) with hSm
  have hh0 : ∀ y, 0 < y → 0 ≤ hD p D y := fun y hy => by
    unfold hD HhD
    exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg zero_le_one
      fun x _ => sq_nonneg _)
  have hhH : ∀ y, 0 < y → hD p D y ≤ M ^ 2 := by
    intro y hy
    unfold hD HhD
    rw [← intervalIntegral.integral_const_mul]
    have hc : Continuous fun x : ℝ => y ^ (2 * p + 2) * ‖D (pz x y)‖ ^ 2 := by
      have := (continuous_D_horiz h 1 hy).norm.pow 2
      simp only [one_mul] at this
      exact continuous_const.mul this
    have hm := intervalIntegral.integral_mono_on (f := fun x => y ^ (2 * p + 2) * ‖D (pz x y)‖ ^ 2)
      (g := fun _ => M ^ 2) zero_le_one (hc.intervalIntegrable _ _)
      (intervalIntegrable_const (μ := MeasureTheory.volume)) (fun x _ => ?_)
    · simpa using hm
    · have him : 0 < (pz x y).im := by rw [pz_im]; exact hy
      have hb := (hMb _ him).1
      rw [pz_im] at hb
      have h0 : 0 ≤ ‖D (pz x y)‖ := norm_nonneg _
      have hb' : ‖D (pz x y)‖ * y ^ (p + 1) ≤ M := by
        rw [le_div_iff₀ (by positivity)] at hb; exact hb
      have e : y ^ (2 * p + 2) * ‖D (pz x y)‖ ^ 2 = (‖D (pz x y)‖ * y ^ (p + 1)) ^ 2 := by ring
      show y ^ (2 * p + 2) * ‖D (pz x y)‖ ^ 2 ≤ M ^ 2
      rw [e]
      exact pow_le_pow_left₀ (by positivity) hb' 2
  have hH := harm_tendsto hh0 hhH h.horo
  have hHβ := hH.comp tendsto_cot'
  have hLβ : Tendsto (fun β => Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2)) atTop := by
    have h1 : Tendsto (fun κ : ℝ => Real.log (1 / κ)) (𝓝[>] 0) atTop := by
      have := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
      refine this.congr fun κ => ?_
      simp [one_div]
    exact h1.comp tendsto_cot'
  have hev : ∀ᶠ β in 𝓝[<] (π / 2), π / 3 < β ∧ β < π / 2 :=
    Ioo_mem_nhdsLT (show π / 3 < π / 2 by linarith [Real.pi_pos])
  have hE : Tendsto (fun β => (Real.sin β ^ (2 * p + 2) * ((Real.cos β / Real.sin β) ^ (2 * p + 2) *
      ∫ u in Ioi 0, R β u) - Sm (Real.cos β / Real.sin β)) /
      Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2)) (𝓝 0) := by
    have hC : Tendsto (fun β => C₁ / Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2))
        (𝓝 0) := tendsto_const_nhds.div_atTop hLβ
    refine squeeze_zero_norm' ?_ hC
    filter_upwards [hev, hLβ.eventually_gt_atTop 0] with β hβ hL
    obtain ⟨hβ1, hβ2⟩ := hβ
    have hs : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ2⟩
    have hs2 : 1 / 2 ≤ Real.sin β := by
      have h1 : Real.sin (π / 6) ≤ Real.sin β := Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos]) hβ2.le (by linarith [Real.pi_pos])
      rwa [Real.sin_pi_div_six] at h1
    have hs1 : Real.sin β < 1 := by
      have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl hβ2
      rwa [Real.sin_pi_div_two] at this
    have hκ1 : Real.cos β / Real.sin β < 1 := by
      rw [div_lt_one hs]
      have h1 : Real.cos β < Real.cos (π / 4) := Real.cos_lt_cos_of_nonneg_of_le_pi
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      have h2 : Real.sin (π / 4) < Real.sin β := Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by linarith [Real.pi_pos]) hβ2.le (by linarith [Real.pi_pos])
      rw [Real.cos_pi_div_four] at h1; rw [Real.sin_pi_div_four] at h2
      linarith
    have hd := ray_decomp h hσ hM0 hA0 hMb hA hs2 hs1 (div_pos hc hs) hκ1 (hR β hs)
      (hRi β (by linarith [Real.pi_pos]) hβ2)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right hd hL.le
  have hlim := (hHβ.add hE).div (tendsto_sin_pow' (2 * p + 2)) one_ne_zero
  rw [add_zero, div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev, hLβ.eventually_gt_atTop 0] with β hβ hL
  have hs : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, hβ.1])
    (by linarith [Real.pi_pos, hβ.2])
  have key := alg_identity' (a := (Real.cos β / Real.sin β) ^ (2 * p + 2) * ∫ u in Ioi 0, R β u)
    (L := Real.log (1 / (Real.cos β / Real.sin β))) (S := Sm (Real.cos β / Real.sin β))
    (pow_ne_zero (2 * p + 2) hs.ne') hL.ne'
  exact key.symm

end RamanujanTau.GeneralCuspMoments
