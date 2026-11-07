/-
# Riemann's kernel `Φ` as an explicit series, and `γ(n) = 32 · n!/(2n)! · ∫_0^∞ u^{2n} Φ(u) du`

With `K = (k+1)²` put `mono a j k u = K^j e^{au} exp(−πK e^{2u})` and

* `Φ(u) = Σ_k (2π²K² e^{9u/2} − 3πK e^{5u/2}) e^{−πK e^{2u}}`  (`PhiR`, Riemann's `Φ`),
* `Φ'(u) = Σ_k` (termwise derivative)  (`PhiD`),
* `h(u) = Σ_k e^{u/2} e^{−πK e^{2u}} = e^{u/2} θ₀(e^{2u})`, with `8Φ = 4h'' − h` termwise.

All series are dominated on `u ≥ 0` by `L · K³e^{−π(K−1)} · e^{−u}` (`mono_le`), which gives integrability,
termwise integration and termwise integration by parts.  The substitution `t = e^{2u}` turns `FXi`
(`∫_1^∞ (log t)^m t^{−3/4} θ₀`) into `2^{m+1} ∫_0^∞ u^m h`, and two integrations by parts give

  **`gammaMathlib_eq_mom`** : `γ(n) = 32 · n!/(2n)! · ∫_0^∞ u^{2n} Φ(u) du`  for `n ≥ 1`,

and **`kernelMom_PhiR`** : `KernelMom PhiR PhiD` (positivity, integrability, `∫u^{m+1}Φ' = −(m+1)∫u^mΦ`).
-/
import RamanujanTau.GORZXiEff.Turan2
import RamanujanTau.GORZXi.XiTaylor
import RamanujanTau.GORZXi.XiStein

set_option autoImplicit false

namespace GORZXiEff

open Real Set MeasureTheory Filter Topology GORZXi

/-! ## monomials and the basic bound -/

noncomputable def Kk (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ 2

lemma Kk_ge_one (k : ℕ) : 1 ≤ Kk k := by
  unfold Kk; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

noncomputable def mono (a : ℝ) (j k : ℕ) (u : ℝ) : ℝ :=
  Kk k ^ j * rexp (a * u) * rexp (-π * Kk k * rexp (2 * u))

lemma mono_nonneg (a : ℝ) (j k : ℕ) (u : ℝ) : 0 ≤ mono a j k u := by
  unfold mono; have := Kk_ge_one k; positivity

lemma continuous_mono (a : ℝ) (j k : ℕ) : Continuous (mono a j k) := by
  unfold mono; fun_prop

lemma hasDerivAt_mono (a : ℝ) (j k : ℕ) (u : ℝ) :
    HasDerivAt (mono a j k) (a * mono a j k u - 2 * π * mono (a + 2) (j + 1) k u) u := by
  have h1 : HasDerivAt (fun u => rexp (a * u)) (rexp (a * u) * a) u :=
    ((hasDerivAt_id u).const_mul a).exp.congr_deriv (by simp)
  have h2 : HasDerivAt (fun u => rexp (-π * Kk k * rexp (2 * u)))
      (rexp (-π * Kk k * rexp (2 * u)) * (-π * Kk k * (rexp (2 * u) * 2))) u := by
    have : HasDerivAt (fun u => rexp (2 * u)) (rexp (2 * u) * 2) u :=
      ((hasDerivAt_id u).const_mul 2).exp.congr_deriv (by simp)
    exact (this.const_mul (-π * Kk k)).exp
  have := (h1.const_mul (Kk k ^ j)).mul h2
  convert this using 1
  simp only [mono]
  rw [show (a + 2) * u = a * u + 2 * u by ring, exp_add, pow_succ]
  ring

noncomputable def cK (k : ℕ) : ℝ := Kk k ^ 3 * rexp (-π * (Kk k - 1))

lemma cK_nonneg (k : ℕ) : 0 ≤ cK k := by unfold cK; have := Kk_ge_one k; positivity

lemma mono_le {a : ℝ} {j : ℕ} (k : ℕ) {u : ℝ} (hu : 0 ≤ u) (ha : a ≤ 8) (hj : j ≤ 3) :
    mono a j k u ≤ cK k * rexp (-u) := by
  have hK := Kk_ge_one k
  have hY := quadratic_le_exp_of_nonneg (x := 2 * u) (by linarith)
  have hpi := pi_gt_three
  have h9 : 9 * u ≤ π * rexp (2 * u) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hpi.le) (exp_pos (2 * u)).le, sq_nonneg (u - 1 / 4)]
  have hY1 : 1 ≤ rexp (2 * u) := by nlinarith
  have hexp : rexp (a * u) * rexp (-π * Kk k * rexp (2 * u)) ≤ rexp (-π * (Kk k - 1)) * rexp (-u) := by
    rw [← exp_add, ← exp_add]
    apply exp_le_exp.2
    nlinarith [mul_nonneg (sub_nonneg.2 hK) (sub_nonneg.2 hY1), pi_pos]
  have hKj : Kk k ^ j ≤ Kk k ^ 3 := pow_le_pow_right₀ hK hj
  unfold mono cK
  calc Kk k ^ j * rexp (a * u) * rexp (-π * Kk k * rexp (2 * u))
      = Kk k ^ j * (rexp (a * u) * rexp (-π * Kk k * rexp (2 * u))) := by ring
    _ ≤ Kk k ^ 3 * (rexp (-π * (Kk k - 1)) * rexp (-u)) :=
        mul_le_mul hKj hexp (by positivity) (by positivity)
    _ = _ := by ring

lemma summable_cK : Summable cK := by
  have hs : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ 6 * rexp (-π * ((k + 1 : ℕ) : ℝ)) :=
    (summable_nat_add_iff 1).2 (summable_pow_mul_exp_neg_nat_mul 6 pi_pos)
  refine Summable.of_nonneg_of_le cK_nonneg (fun k => ?_) (hs.mul_left (rexp π))
  unfold cK Kk
  push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [← pow_mul]
  have : rexp (-π * (((k : ℝ) + 1) ^ 2 - 1)) ≤ rexp π * rexp (-π * ((k : ℝ) + 1)) := by
    rw [← exp_add]; apply exp_le_exp.2
    have h1 : ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 pi_pos.le]
  calc ((k : ℝ) + 1) ^ (2 * 3) * rexp (-π * (((k : ℝ) + 1) ^ 2 - 1))
      ≤ ((k : ℝ) + 1) ^ (2 * 3) * (rexp π * rexp (-π * ((k : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

lemma integrableOn_pow_exp (m : ℕ) : IntegrableOn (fun u : ℝ => u ^ m * rexp (-u)) (Ioi 0) := by
  have := GammaIntegral_convergent (s := (m : ℝ) + 1) (by positivity)
  refine this.congr_fun (fun u hu => ?_) measurableSet_Ioi
  simp only [add_sub_cancel_right, rpow_natCast]; ring

/-! ## dominated families -/

section Family

variable {F : ℕ → ℝ → ℝ} {L : ℝ}

/-- a family dominated by `L · cK k · e^{−u}` on `u ≥ 0`. -/
structure Dom (F : ℕ → ℝ → ℝ) (L : ℝ) : Prop where
  cont : ∀ k, Continuous (F k)
  bound : ∀ k u, 0 ≤ u → |F k u| ≤ L * cK k * rexp (-u)

lemma Dom.L_nonneg (h : Dom F L) : 0 ≤ L := by
  have h1 := h.bound 0 0 le_rfl
  have : 0 < cK 0 * rexp (-0) := by
    unfold cK; have := Kk_ge_one 0; positivity
  nlinarith [abs_nonneg (F 0 0)]

lemma Dom.int (h : Dom F L) (k m : ℕ) : IntegrableOn (fun u => u ^ m * F k u) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_pow_exp m).const_mul (L * cK k))
    (((continuous_pow m).mul (h.cont k)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : (0 : ℝ) < u := hu
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu'.le m)]
  calc u ^ m * |F k u| ≤ u ^ m * (L * cK k * rexp (-u)) :=
        mul_le_mul_of_nonneg_left (h.bound k u hu'.le) (pow_nonneg hu'.le m)
    _ = _ := by ring

lemma Dom.summable (h : Dom F L) {u : ℝ} (hu : 0 ≤ u) : Summable fun k => F k u :=
  Summable.of_norm_bounded ((summable_cK.mul_left L).mul_right (rexp (-u)))
    (fun k => by rw [Real.norm_eq_abs]; exact h.bound k u hu)

lemma Dom.abs_tsum_le (h : Dom F L) {u : ℝ} (hu : 0 ≤ u) :
    |∑' k, F k u| ≤ L * (∑' k, cK k) * rexp (-u) := by
  have hs := ((summable_cK.mul_left L).mul_right (rexp (-u)))
  have := tsum_of_norm_bounded hs.hasSum (fun k => by rw [Real.norm_eq_abs]; exact h.bound k u hu)
  rw [Real.norm_eq_abs] at this
  rw [tsum_mul_right, tsum_mul_left] at this
  exact this

lemma Dom.continuousOn (h : Dom F L) : ContinuousOn (fun u => ∑' k, F k u) (Ici 0) :=
  continuousOn_tsum (fun k => (h.cont k).continuousOn) (summable_cK.mul_left L) (fun k u hu => by
    rw [Real.norm_eq_abs]
    refine (h.bound k u hu).trans ?_
    have : rexp (-u) ≤ 1 := exp_le_one_iff.2 (by simp at hu; linarith)
    have := mul_nonneg h.L_nonneg (cK_nonneg k)
    nlinarith)

lemma Dom.int_tsum (h : Dom F L) (m : ℕ) :
    IntegrableOn (fun u => u ^ m * ∑' k, F k u) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_pow_exp m).const_mul (L * ∑' k, cK k))
    ((((continuous_pow m).continuousOn).mul (h.continuousOn.mono Ioi_subset_Ici_self)).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : (0 : ℝ) < u := hu
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu'.le m)]
  calc u ^ m * |∑' k, F k u| ≤ u ^ m * (L * (∑' k, cK k) * rexp (-u)) :=
        mul_le_mul_of_nonneg_left (h.abs_tsum_le hu'.le) (pow_nonneg hu'.le m)
    _ = _ := by ring

lemma Dom.summable_int (h : Dom F L) (m : ℕ) :
    Summable fun k => ∫ u in Ioi (0 : ℝ), ‖u ^ m * F k u‖ := by
  set G := ∫ u in Ioi (0 : ℝ), u ^ m * rexp (-u)
  refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
    ((summable_cK.mul_left L).mul_right G)
  rw [show L * cK k * G = ∫ u in Ioi (0 : ℝ), L * cK k * (u ^ m * rexp (-u)) by
    rw [integral_const_mul]]
  refine setIntegral_mono_on (h.int k m).norm ((integrableOn_pow_exp m).const_mul _) measurableSet_Ioi
    fun u hu => ?_
  have hu' : (0 : ℝ) < u := hu
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu'.le m)]
  calc u ^ m * |F k u| ≤ u ^ m * (L * cK k * rexp (-u)) :=
        mul_le_mul_of_nonneg_left (h.bound k u hu'.le) (pow_nonneg hu'.le m)
    _ = _ := by ring

lemma Dom.integral_tsum (h : Dom F L) (m : ℕ) :
    ∫ u in Ioi (0 : ℝ), u ^ m * ∑' k, F k u = ∑' k, ∫ u in Ioi (0 : ℝ), u ^ m * F k u := by
  rw [integral_tsum_of_summable_integral_norm (fun k => h.int k m) (h.summable_int m)]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  exact (tsum_mul_left).symm

lemma Dom.summable_integral (h : Dom F L) (m : ℕ) :
    Summable fun k => ∫ u in Ioi (0 : ℝ), u ^ m * F k u :=
  Summable.of_norm_bounded (h.summable_int m) (fun k => norm_integral_le_integral_norm _)

lemma Dom.decay (h : Dom F L) (k m : ℕ) : Tendsto (fun u => u ^ m * F k u) atTop (𝓝 0) := by
  have ht := (tendsto_pow_mul_exp_neg_atTop_nhds_zero m).const_mul (L * cK k)
  rw [mul_zero] at ht
  refine squeeze_zero_norm' ?_ ht
  filter_upwards [eventually_ge_atTop 0] with u hu
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu m)]
  calc u ^ m * |F k u| ≤ u ^ m * (L * cK k * rexp (-u)) :=
        mul_le_mul_of_nonneg_left (h.bound k u hu) (pow_nonneg hu m)
    _ = _ := by ring

end Family

lemma abs_lin3 {c₁ c₂ c₃ x₁ x₂ x₃ B : ℝ} (h₁ : 0 ≤ x₁) (h₁' : x₁ ≤ B) (h₂ : 0 ≤ x₂) (h₂' : x₂ ≤ B)
    (h₃ : 0 ≤ x₃) (h₃' : x₃ ≤ B) :
    |c₁ * x₁ + c₂ * x₂ + c₃ * x₃| ≤ (|c₁| + |c₂| + |c₃|) * B := by
  have e : ∀ c x : ℝ, 0 ≤ x → x ≤ B → |c * x| ≤ |c| * B := fun c x hx hxB => by
    rw [abs_mul, abs_of_nonneg hx]; exact mul_le_mul_of_nonneg_left hxB (abs_nonneg c)
  calc |c₁ * x₁ + c₂ * x₂ + c₃ * x₃| ≤ |c₁ * x₁| + |c₂ * x₂| + |c₃ * x₃| :=
        by linarith [abs_add_le (c₁ * x₁ + c₂ * x₂) (c₃ * x₃), abs_add_le (c₁ * x₁) (c₂ * x₂)]
    _ ≤ |c₁| * B + |c₂| * B + |c₃| * B := by
        gcongr
        · exact e _ _ h₁ h₁'
        · exact e _ _ h₂ h₂'
        · exact e _ _ h₃ h₃'
    _ = _ := by ring

/-- a 3-term combination of monomials (exponents `≤ 8`, `K`-degree `≤ 3`) is dominated. -/
lemma dom_lin3 (c₁ c₂ c₃ a₁ a₂ a₃ : ℝ) (j₁ j₂ j₃ : ℕ) (ha₁ : a₁ ≤ 8) (ha₂ : a₂ ≤ 8) (ha₃ : a₃ ≤ 8)
    (hj₁ : j₁ ≤ 3) (hj₂ : j₂ ≤ 3) (hj₃ : j₃ ≤ 3) :
    Dom (fun k u => c₁ * mono a₁ j₁ k u + c₂ * mono a₂ j₂ k u + c₃ * mono a₃ j₃ k u)
      (|c₁| + |c₂| + |c₃|) := by
  refine ⟨fun k => by
    have := continuous_mono a₁ j₁ k; have := continuous_mono a₂ j₂ k
    have := continuous_mono a₃ j₃ k; fun_prop, fun k u hu => ?_⟩
  rw [mul_assoc]
  exact abs_lin3 (mono_nonneg _ _ _ _) (mono_le k hu ha₁ hj₁) (mono_nonneg _ _ _ _)
    (mono_le k hu ha₂ hj₂) (mono_nonneg _ _ _ _) (mono_le k hu ha₃ hj₃)

/-! ## the kernel `Φ`, its derivative, and `h` -/

noncomputable def phik (k : ℕ) (u : ℝ) : ℝ :=
  2 * π ^ 2 * mono (9 / 2) 2 k u + (-3 * π) * mono (5 / 2) 1 k u + 0 * mono 0 0 k u

noncomputable def phik' (k : ℕ) (u : ℝ) : ℝ :=
  15 * π ^ 2 * mono (9 / 2) 2 k u + (-4 * π ^ 3) * mono (13 / 2) 3 k u +
    (-(15 / 2) * π) * mono (5 / 2) 1 k u

noncomputable def hk (k : ℕ) (u : ℝ) : ℝ := 1 * mono (1 / 2) 0 k u + 0 * mono 0 0 k u + 0 * mono 0 0 k u

noncomputable def hk' (k : ℕ) (u : ℝ) : ℝ :=
  (1 / 2) * mono (1 / 2) 0 k u + (-2 * π) * mono (5 / 2) 1 k u + 0 * mono 0 0 k u

noncomputable def hk'' (k : ℕ) (u : ℝ) : ℝ :=
  (1 / 4) * mono (1 / 2) 0 k u + (-6 * π) * mono (5 / 2) 1 k u + 4 * π ^ 2 * mono (9 / 2) 2 k u

/-- **Riemann's kernel** `Φ(u) = Σ_{k≥1} (2π²k⁴e^{9u/2} − 3πk²e^{5u/2}) e^{−πk²e^{2u}}`. -/
noncomputable def PhiR (u : ℝ) : ℝ := ∑' k, phik k u

/-- the termwise derivative `Φ'` of `PhiR`. -/
noncomputable def PhiD (u : ℝ) : ℝ := ∑' k, phik' k u

lemma dom_phik : Dom phik (|2 * π ^ 2| + |-3 * π| + |0|) := dom_lin3 _ _ _ _ _ _ 2 1 0 (by norm_num) (by norm_num) (by norm_num)
  (by norm_num) (by norm_num) (by norm_num)
lemma dom_phik' : Dom phik' (|15 * π ^ 2| + |-4 * π ^ 3| + |-(15 / 2) * π|) := dom_lin3 _ _ _ _ _ _ 2 3 1 (by norm_num) (by norm_num) (by norm_num)
  (by norm_num) (by norm_num) (by norm_num)
lemma dom_hk : Dom hk (|1| + |0| + |0|) := dom_lin3 _ _ _ _ _ _ 0 0 0 (by norm_num) (by norm_num) (by norm_num)
  (by norm_num) (by norm_num) (by norm_num)
lemma dom_hk' : Dom hk' (|1 / 2| + |-2 * π| + |0|) := dom_lin3 _ _ _ _ _ _ 0 1 0 (by norm_num) (by norm_num) (by norm_num)
  (by norm_num) (by norm_num) (by norm_num)
lemma dom_hk'' : Dom hk'' (|1 / 4| + |-6 * π| + |4 * π ^ 2|) := dom_lin3 _ _ _ _ _ _ 0 1 2 (by norm_num) (by norm_num) (by norm_num)
  (by norm_num) (by norm_num) (by norm_num)

lemma hasDerivAt_phik (k : ℕ) (u : ℝ) : HasDerivAt (phik k) (phik' k u) u := by
  have := (((hasDerivAt_mono (9 / 2) 2 k u).const_mul (2 * π ^ 2)).add
    ((hasDerivAt_mono (5 / 2) 1 k u).const_mul (-3 * π))).add ((hasDerivAt_mono 0 0 k u).const_mul 0)
  convert this using 1
  simp only [phik']; norm_num; ring

lemma hasDerivAt_hk (k : ℕ) (u : ℝ) : HasDerivAt (hk k) (hk' k u) u := by
  have := (((hasDerivAt_mono (1 / 2) 0 k u).const_mul 1).add
    ((hasDerivAt_mono 0 0 k u).const_mul 0)).add ((hasDerivAt_mono 0 0 k u).const_mul 0)
  convert this using 1
  simp only [hk']; norm_num; ring

lemma hasDerivAt_hk' (k : ℕ) (u : ℝ) : HasDerivAt (hk' k) (hk'' k u) u := by
  have := (((hasDerivAt_mono (1 / 2) 0 k u).const_mul (1 / 2)).add
    ((hasDerivAt_mono (5 / 2) 1 k u).const_mul (-2 * π))).add ((hasDerivAt_mono 0 0 k u).const_mul 0)
  convert this using 1
  simp only [hk'']; norm_num; ring

lemma phik_eq (k : ℕ) (u : ℝ) : phik k u = (1 / 2) * hk'' k u - (1 / 8) * hk k u := by
  simp only [phik, hk, hk'']; ring

lemma mono_92 (k : ℕ) (u : ℝ) : mono (9 / 2) 2 k u = Kk k * rexp (2 * u) * mono (5 / 2) 1 k u := by
  simp only [mono]; rw [show 9 / 2 * u = 5 / 2 * u + 2 * u by ring, exp_add]; ring

lemma phik_nonneg (k : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ phik k u := by
  have h1 : 1 ≤ rexp (2 * u) := one_le_exp (by linarith)
  have hK := Kk_ge_one k
  have hm := mono_nonneg (5 / 2) 1 k u
  have : 3 ≤ 2 * π * (Kk k * rexp (2 * u)) := by nlinarith [pi_gt_three, one_le_mul_of_one_le_of_one_le hK h1]
  simp only [phik, mono_92]
  nlinarith [mul_nonneg (mul_nonneg pi_pos.le hm) (sub_nonneg.2 this)]

lemma phik_pos (k : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 < phik k u := by
  have h1 : 1 ≤ rexp (2 * u) := one_le_exp (by linarith)
  have hK := Kk_ge_one k
  have hm : 0 < mono (5 / 2) 1 k u := by unfold mono; positivity
  have : 3 < 2 * π * (Kk k * rexp (2 * u)) := by nlinarith [pi_gt_three, one_le_mul_of_one_le_of_one_le hK h1]
  simp only [phik, mono_92]
  nlinarith [mul_pos (mul_pos pi_pos hm) (sub_pos.2 this)]

lemma PhiR_pos {u : ℝ} (hu : 0 ≤ u) : 0 < PhiR u :=
  (dom_phik.summable hu).tsum_pos (fun k => phik_nonneg k hu) 0 (phik_pos 0 hu)

/-- termwise IBP summed: `∫_0^∞ u^{m+1}Φ' = −(m+1)∫_0^∞ u^mΦ`. -/
lemma ibp_PhiR (m : ℕ) : ∫ u in Ioi (0 : ℝ), u ^ (m + 1) * PhiD u = -((m + 1 : ℝ) * mom PhiR m) := by
  unfold PhiD mom PhiR
  rw [dom_phik'.integral_tsum, dom_phik.integral_tsum, ← tsum_mul_left, ← tsum_neg]
  congr 1; funext k
  exact ibp_of (hasDerivAt_phik k) m (dom_phik.int k m) (dom_phik'.int k (m + 1)) (dom_phik.decay k (m + 1))

/-- **`Φ` satisfies the moment hypotheses of the Chebyshev–Turán argument.** -/
theorem kernelMom_PhiR : KernelMom PhiR PhiD :=
  ⟨fun _ hu => PhiR_pos hu.le, dom_phik.int_tsum, dom_phik'.int_tsum, ibp_PhiR⟩

/-! ## the link with `FXi` -/

/-- `Σ_k h_k(u) = e^{u/2} θ₀(e^{2u})`. -/
lemma tsum_hk (u : ℝ) : ∑' k, hk k u = rexp (u / 2) * theta0 (rexp (2 * u)) := by
  have hs := (theta0_hasSum (exp_pos (2 * u))).mul_left (rexp (u / 2))
  rw [← hs.tsum_eq]
  congr 1; funext k
  simp only [hk, mono, Kk]; norm_num; ring

/-- substitution `t = e^{2u}`: `∫_0^∞ u^m e^{u/2} θ₀(e^{2u}) du = 2^{−(m+1)} F(m)`. -/
lemma FXi_eq_H (m : ℕ) : FXi m = 2 ^ (m + 1) * ∫ u in Ioi (0 : ℝ), u ^ m * ∑' k, hk k u := by
  set g : ℝ → ℝ := fun t => Real.log t ^ m * t ^ (-(3 / 4 : ℝ)) * theta0 t
  have himg : (fun u : ℝ => rexp (2 * u)) '' Ici 0 ⊆ Ici 1 := by
    rintro _ ⟨u, hu, rfl⟩; exact one_le_exp (by simp at hu; linarith)
  have himg' : (fun u : ℝ => rexp (2 * u)) '' Ioi 0 ⊆ Ioi 1 := by
    rintro _ ⟨u, hu, rfl⟩; exact Real.one_lt_exp_iff.2 (by simp at hu; linarith)
  have hpt : ∀ u : ℝ, (g ∘ fun u => rexp (2 * u)) u * (2 * rexp (2 * u)) =
      2 ^ (m + 1) * (u ^ m * ∑' k, hk k u) := by
    intro u
    simp only [g, Function.comp, Real.log_exp, tsum_hk]
    rw [← Real.exp_mul]
    have : rexp (2 * u * -(3 / 4 : ℝ)) * rexp (2 * u) = rexp (u / 2) := by
      rw [← exp_add]; ring_nf
    rw [mul_pow, pow_succ]
    linear_combination (2 ^ m * u ^ m * 2 * theta0 (rexp (2 * u))) * this
  have hgI : IntegrableOn g (Ioi 1) := by
    have := integrable_rhoT m 0 0
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [rhoT, g]
  have key := integral_comp_mul_deriv_Ioi (a := 0) (f := fun u => rexp (2 * u))
    (f' := fun u => 2 * rexp (2 * u)) (g := g) (by fun_prop)
    (tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop two_pos))
    (fun u _ => by
      have : HasDerivAt (fun u => rexp (2 * u)) (rexp (2 * u) * 2) u :=
        ((hasDerivAt_id u).const_mul 2).exp.congr_deriv (by simp)
      exact (this.congr_deriv (by ring)).hasDerivWithinAt)
    (by
      refine ContinuousOn.mono ?_ himg'
      refine ((ContinuousOn.pow (continuousOn_log.mono fun t ht => ?_) m).mul
        (ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl ?_)).mul
          (continuousOn_theta0.mono fun t ht => ?_)
      · simp at ht ⊢; linarith
      · simp at ht ⊢; linarith
      · simp at ht ⊢; linarith)
    (((integrableOn_Ici_iff_integrableOn_Ioi (f := g) (b := 1)).2 hgI).mono_set himg)
    (by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact IntegrableOn.congr_fun ((dom_hk.int_tsum m).const_mul (2 ^ (m + 1)))
        (fun u _ => (hpt u).symm) measurableSet_Ioi)
  simp only [mul_zero, exp_zero] at key
  rw [FXi, ← key, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun u _ => hpt u

/-- `∫ u^{2n+2} Φ = ½(2n+2)(2n+1)∫u^{2n}h − ⅛∫u^{2n+2}h` (two integrations by parts). -/
lemma mom_PhiR_succ (n : ℕ) :
    mom PhiR (2 * n + 2) = (1 / 2) * ((2 * n + 2) * (2 * n + 1)) *
        (∫ u in Ioi (0 : ℝ), u ^ (2 * n) * ∑' k, hk k u) -
      (1 / 8) * ∫ u in Ioi (0 : ℝ), u ^ (2 * n + 2) * ∑' k, hk k u := by
  unfold mom PhiR
  rw [dom_phik.integral_tsum, dom_hk.integral_tsum, dom_hk.integral_tsum, ← tsum_mul_left,
    ← tsum_mul_left, ← Summable.tsum_sub ((dom_hk.summable_integral _).mul_left _)
      ((dom_hk.summable_integral _).mul_left _)]
  congr 1; funext k
  have e2 : ∫ u in Ioi (0 : ℝ), u ^ (2 * n + 1 + 1) * hk'' k u =
      -((2 * n + 2 : ℝ) * ∫ u in Ioi (0 : ℝ), u ^ (2 * n + 1) * hk' k u) := by
    have := ibp_of (hasDerivAt_hk' k) (2 * n + 1) (dom_hk'.int k _) (dom_hk''.int k _)
      (dom_hk'.decay k _)
    unfold mom at this
    refine this.trans ?_; push_cast; ring
  have e1 : ∫ u in Ioi (0 : ℝ), u ^ (2 * n + 1) * hk' k u =
      -((2 * n + 1 : ℝ) * ∫ u in Ioi (0 : ℝ), u ^ (2 * n) * hk k u) := by
    have := ibp_of (hasDerivAt_hk k) (2 * n) (dom_hk.int k _) (dom_hk'.int k _) (dom_hk.decay k _)
    unfold mom at this
    refine this.trans ?_; push_cast; ring
  have hsplit : ∫ u in Ioi (0 : ℝ), u ^ (2 * n + 2) * phik k u =
      (1 / 2) * (∫ u in Ioi (0 : ℝ), u ^ (2 * n + 1 + 1) * hk'' k u) -
        (1 / 8) * ∫ u in Ioi (0 : ℝ), u ^ (2 * n + 2) * hk k u := by
    have := integral_sub ((dom_hk''.int k (2 * n + 1 + 1)).const_mul (1 / 2))
      ((dom_hk.int k (2 * n + 2)).const_mul (1 / 8))
    rw [integral_const_mul, integral_const_mul] at this
    refine Eq.trans ?_ this
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [phik_eq]; ring
  rw [hsplit, e2, e1]
  ring

/-- **`γ(n) = 32 · n!/(2n)! · ∫_0^∞ u^{2n} Φ(u) du`** for `n ≥ 1` (Mathlib's `γ`). -/
theorem gammaMathlib_eq_mom (n : ℕ) (hn : 1 ≤ n) :
    gammaMathlib n = 32 * fq n * mom PhiR (2 * n) := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hF0 : FXi (2 * n) = 2 * 4 ^ n * ∫ u in Ioi (0 : ℝ), u ^ (2 * n) * ∑' k, hk k u := by
    rw [FXi_eq_H, pow_succ, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]; ring
  have hF2 : FXi (2 * n + 2) = 8 * 4 ^ n * ∫ u in Ioi (0 : ℝ), u ^ (2 * n + 2) * ∑' k, hk k u := by
    rw [FXi_eq_H, pow_succ, pow_succ, pow_succ, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]; ring
  rw [gammaMathlib_eq _ hn, show 2 * (n + 1) = 2 * n + 2 by ring, mom_PhiR_succ]
  simp only [gammaXi, aXi, BXi, show 2 * (n + 1) = 2 * n + 2 by ring, show 2 * n + 2 - 2 = 2 * n by omega, hF0, hF2, fq]
  rw [Nat.cast_choose_two]
  push_cast
  rw [pow_succ]
  field_simp
  ring

end GORZXiEff
