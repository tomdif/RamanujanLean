/-
# Item (c), part 2: the `P̃` weight and the `t`-integral of the smoothed sum

`Wint X H F = ∫_{16}^X F + (1/H)∫_X^{X+H} (X+H−t) F(t) dt` is the `P̃` weight at frequency `0`
(`Ptil_zero`). For `f` with a log asymptotic, `Σ_m f(m) Wint(V(2 lg m − Λ₀ − 2ℓ(t))) = Wint Φ` with
`Φ(t) = Σ_m f(m) V(2 lg m − Λ₀ − 2ℓ(t))` (`hasSum_Wint`, dominated convergence), and `Φ` is continuous
(`continuousOn_Phi`, Weierstrass).
-/
import RamanujanTau.HafnerBridge2.Smooth

set_option autoImplicit false

namespace RamanujanTau.HafnerBridge2

open MeasureTheory Set Filter Topology Complex
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.GoodSecondTerm2
open scoped Interval

/-- The `P̃` weight. -/
noncomputable def Wint (X H : ℝ) (F : ℝ → ℝ) : ℝ :=
  (∫ t in (16 : ℝ)..X, F t) + (1 / H) * ∫ t in X..X + H, (X + H - t) * F t

lemma Ptil_zero (Λ X H : ℝ) : Ptil Λ 0 X H = ((Wint X H (WV Λ) : ℝ) : ℂ) := by
  unfold Ptil Wint
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  push_cast; ring

section
variable {X H : ℝ} (hX : 16 ≤ X) (hH : 0 < H)
include hX hH

lemma ii_left {F : ℝ → ℝ} (hF : ContinuousOn F (Icc 16 (X + H))) : IntervalIntegrable F volume 16 X :=
  (hF.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc hX

lemma ii_right {F : ℝ → ℝ} (hF : ContinuousOn F (Icc 16 (X + H))) :
    IntervalIntegrable (fun t => (X + H - t) * F t) volume X (X + H) :=
  (((continuousOn_const.sub continuousOn_id).mul hF).mono (Icc_subset_Icc hX le_rfl)).intervalIntegrable_of_Icc
    (by linarith)

lemma Wint_add {F G : ℝ → ℝ} (hF : ContinuousOn F (Icc 16 (X + H))) (hG : ContinuousOn G (Icc 16 (X + H))) :
    Wint X H (fun t => F t + G t) = Wint X H F + Wint X H G := by
  unfold Wint
  rw [intervalIntegral.integral_add (ii_left hX hH hF) (ii_left hX hH hG)]
  have : (fun t => (X + H - t) * (F t + G t)) = fun t => (X + H - t) * F t + (X + H - t) * G t := by
    funext t; ring
  rw [this, intervalIntegral.integral_add (ii_right hX hH hF) (ii_right hX hH hG)]
  ring

lemma Wint_sub {F G : ℝ → ℝ} (hF : ContinuousOn F (Icc 16 (X + H))) (hG : ContinuousOn G (Icc 16 (X + H))) :
    Wint X H (fun t => F t - G t) = Wint X H F - Wint X H G := by
  unfold Wint
  rw [intervalIntegral.integral_sub (ii_left hX hH hF) (ii_left hX hH hG)]
  have : (fun t => (X + H - t) * (F t - G t)) = fun t => (X + H - t) * F t - (X + H - t) * G t := by
    funext t; ring
  rw [this, intervalIntegral.integral_sub (ii_right hX hH hF) (ii_right hX hH hG)]
  ring

omit hX hH in
lemma Wint_smul (a : ℝ) (F : ℝ → ℝ) : Wint X H (fun t => a * F t) = a * Wint X H F := by
  unfold Wint
  rw [intervalIntegral.integral_const_mul]
  have : (fun t => (X + H - t) * (a * F t)) = fun t => a * ((X + H - t) * F t) := by funext t; ring
  rw [this, intervalIntegral.integral_const_mul]; ring

lemma abs_Wint_le {F G : ℝ → ℝ} (hF : ContinuousOn F (Icc 16 (X + H))) (hG : ContinuousOn G (Icc 16 (X + H)))
    (hFG : ∀ t ∈ Icc 16 (X + H), |F t| ≤ G t) : |Wint X H F| ≤ ∫ t in (16 : ℝ)..X + H, G t := by
  have hXH : X ≤ X + H := by linarith
  have h1 : |∫ t in (16 : ℝ)..X, F t| ≤ ∫ t in (16 : ℝ)..X, G t := by
    refine (intervalIntegral.abs_integral_le_integral_abs hX).trans ?_
    refine intervalIntegral.integral_mono_on hX (ii_left hX hH hF).abs (ii_left hX hH hG) (fun t ht => ?_)
    exact hFG t ⟨ht.1, ht.2.trans hXH⟩
  have h2 : |(1 / H) * ∫ t in X..X + H, (X + H - t) * F t| ≤ ∫ t in X..X + H, G t := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / H)]
    have hGi : IntervalIntegrable G volume X (X + H) :=
      (hG.mono (Icc_subset_Icc hX le_rfl)).intervalIntegrable_of_Icc hXH
    have hb : |∫ t in X..X + H, (X + H - t) * F t| ≤ ∫ t in X..X + H, H * G t := by
      refine (intervalIntegral.abs_integral_le_integral_abs hXH).trans ?_
      refine intervalIntegral.integral_mono_on hXH (ii_right hX hH hF).abs (hGi.const_mul H) (fun t ht => ?_)
      rw [abs_mul, abs_of_nonneg (by linarith [ht.2])]
      have hG0 : |F t| ≤ G t := hFG t ⟨hX.trans ht.1, ht.2⟩
      have := abs_nonneg (F t)
      have : X + H - t ≤ H := by linarith [ht.1]
      nlinarith
    rw [intervalIntegral.integral_const_mul] at hb
    calc 1 / H * |∫ t in X..X + H, (X + H - t) * F t| ≤ 1 / H * (H * ∫ t in X..X + H, G t) := by gcongr
      _ = _ := by field_simp
  have hsplit : (∫ t in (16 : ℝ)..X, G t) + ∫ t in X..X + H, G t = ∫ t in (16 : ℝ)..X + H, G t :=
    intervalIntegral.integral_add_adjacent_intervals (ii_left hX hH hG)
      ((hG.mono (Icc_subset_Icc hX le_rfl)).intervalIntegrable_of_Icc hXH)
  unfold Wint
  rw [← hsplit]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

lemma Wint_nonneg {F : ℝ → ℝ} (hF : ContinuousOn F (Icc 16 (X + H))) (hF0 : ∀ t ∈ Icc 16 (X + H), 0 ≤ F t) :
    0 ≤ Wint X H F := by
  have hXH : X ≤ X + H := by linarith
  unfold Wint
  refine add_nonneg (intervalIntegral.integral_nonneg hX fun t ht => hF0 t ⟨ht.1, ht.2.trans hXH⟩)
    (mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hXH fun t ht => ?_))
  exact mul_nonneg (by linarith [ht.2]) (hF0 t ⟨hX.trans ht.1, ht.2⟩)

lemma Wint_le {F : ℝ → ℝ} (hF : ContinuousOn F (Icc 16 (X + H))) (hF0 : ∀ t ∈ Icc 16 (X + H), 0 ≤ F t) :
    Wint X H F ≤ ∫ t in (16 : ℝ)..X + H, F t := by
  have := abs_Wint_le hX hH hF hF (fun t ht => by rw [abs_of_nonneg (hF0 t ht)])
  exact (le_abs_self _).trans this

end

/-! ### Interchanging `Σ_m` and the `t`-integral -/

section
variable {f : ℕ → ℝ} {c K E : ℝ} (hE : 0 ≤ E) (hS : LogAsym f c K E) (Λ₀ : ℝ)

/-- `Φ(t) = Σ_m f(m) V(2 lg m − Λ₀ − 2ℓ(t))`. -/
noncomputable def Phi (f : ℕ → ℝ) (Λ₀ t : ℝ) : ℝ := ∑' m : ℕ, f m * V (2 * lg m - (Λ₀ + 2 * ellT t))

lemma continuous_V' : Continuous V := continuous_V

lemma continuousOn_term (m : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t => f m * V (2 * lg m - (Λ₀ + 2 * ellT t))) (Icc a b) :=
  continuousOn_const.mul (continuous_V.comp_continuousOn
    (continuousOn_const.sub (continuousOn_const.add (continuousOn_const.mul (continuousOn_ellT ha)))))

lemma V_le_at_b {m : ℕ} {a b t : ℝ} (ha : 0 < a) (ht : t ∈ Icc a b) :
    V (2 * lg m - (Λ₀ + 2 * ellT t)) ≤ V (2 * lg m - (Λ₀ + 2 * ellT b)) := by
  apply antitone_V
  have := ellT_mono (ha.trans_le ht.1) ht.2
  linarith

include hE hS

lemma continuousOn_Phi {a b : ℝ} (ha : 0 < a) : ContinuousOn (Phi f Λ₀) (Icc a b) := by
  refine continuousOn_tsum (fun m => continuousOn_term Λ₀ m ha) (summable_absf_V hE hS (Λ₀ + 2 * ellT b))
    (fun m t ht => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (V_nonneg _)]
  exact mul_le_mul_of_nonneg_left (V_le_at_b Λ₀ ha ht) (abs_nonneg _)

lemma hasSum_interval {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc a b))
    {M : ℝ} (hM : ∀ t ∈ Icc a b, |φ t| ≤ M) :
    HasSum (fun m : ℕ => f m * ∫ t in a..b, φ t * V (2 * lg m - (Λ₀ + 2 * ellT t)))
      (∫ t in a..b, φ t * Phi f Λ₀ t) := by
  have hF : ∀ m : ℕ, ∫ t in a..b, f m * (φ t * V (2 * lg m - (Λ₀ + 2 * ellT t))) =
      f m * ∫ t in a..b, φ t * V (2 * lg m - (Λ₀ + 2 * ellT t)) := fun m => intervalIntegral.integral_const_mul _ _
  simp_rw [← hF]
  have hIoc : Ι a b ⊆ Icc a b := by rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun m _ => |f m| * M * V (2 * lg m - (Λ₀ + 2 * ellT b))) (fun m => ?_) (fun m => ?_) ?_ ?_ ?_
  · have hc : ContinuousOn (fun t => f m * (φ t * V (2 * lg m - (Λ₀ + 2 * ellT t)))) (Icc a b) := by
      have := (continuousOn_term (f := fun _ => 1) Λ₀ m ha (b := b))
      have h2 : ContinuousOn (fun t => V (2 * lg m - (Λ₀ + 2 * ellT t))) (Icc a b) := by simpa using this
      exact continuousOn_const.mul (hφ.mul h2)
    exact (hc.mono hIoc).aestronglyMeasurable measurableSet_uIoc
  · refine Eventually.of_forall fun t ht => ?_
    have htI := hIoc ht
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (V_nonneg _)]
    have h1 := hM t htI
    have h2 := V_le_at_b (m := m) Λ₀ ha htI
    have := abs_nonneg (f m)
    have := abs_nonneg (φ t)
    have := V_nonneg (2 * lg m - (Λ₀ + 2 * ellT t))
    calc |f m| * (|φ t| * V (2 * lg m - (Λ₀ + 2 * ellT t))) ≤ |f m| * (M * V (2 * lg m - (Λ₀ + 2 * ellT b))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (V_nonneg _) ((abs_nonneg _).trans h1))
            (abs_nonneg _)
      _ = _ := by ring
  · refine Eventually.of_forall fun t _ => ?_
    exact ((summable_absf_V hE hS (Λ₀ + 2 * ellT b)).mul_left M).congr fun m => by ring
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t _ => ?_
    have := ((summable_f_V hE hS (Λ₀ + 2 * ellT t)).hasSum).mul_left (φ t)
    refine this.congr_fun (fun m => ?_)
    ring

/-- `Σ_m f(m) Wint(V(2 lg m − Λ₀ − 2ℓ)) = Wint Φ`. -/
lemma hasSum_Wint {X H : ℝ} (hX : 16 ≤ X) (hH : 0 < H) :
    HasSum (fun m : ℕ => f m * Wint X H (fun t => V (2 * lg m - (Λ₀ + 2 * ellT t)))) (Wint X H (Phi f Λ₀)) := by
  have hXH : X ≤ X + H := by linarith
  have h1 := hasSum_interval hE hS Λ₀ (a := 16) (b := X) (by norm_num) hX (φ := fun _ => 1)
    continuousOn_const (M := 1) (fun t _ => by norm_num)
  have h2 := hasSum_interval hE hS Λ₀ (a := X) (b := X + H) (by linarith) hXH (φ := fun t => X + H - t)
    (continuousOn_const.sub continuousOn_id) (M := H) (fun t ht => by
      rw [abs_of_nonneg (by linarith [ht.2])]; linarith [ht.1])
  have h := h1.add (h2.mul_left (1 / H))
  unfold Wint
  simp only [one_mul] at h
  refine h.congr_fun (fun m => ?_)
  simp only
  ring

end

end RamanujanTau.HafnerBridge2
