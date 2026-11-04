/-
# The unfolding identity `RSUnfoldG` and the power saving for an abstract `RSFn`

Generalizes `RankinError/RSUnfoldProof.lean` and `rsData_of_unfold` (`RSFE.lean`):

* `RSUnfold_realG`: for real `σ > 2`, `mellin(Φ − ‖G‖)(σ) = γₘ(σ) ζ(2σ) ∑ aₙ n^{−σ}`,
  `aₙ = cₙ/n^m`;
* `rsUnfoldG`: the same for complex `Re s > 2` (identity theorem);
* `rsDataG : RSDataM m aF ‖G‖`;
* **`power_saving_RSFn`** (`m ≥ 2`): `|∑_{n≤N} aₙ − ‖G‖ c_m N| ≤ C N^{1−1/84}`.
-/
import RamanujanTau.RankinErrorGeneral.UnfoldG

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.RankinErrorGeneral

open Real Filter Topology MeasureTheory Set
open RamanujanTau.RankinSelberg hiding G G_smul continuous_G G_pos
open RamanujanTau.RankinError
open RamanujanTau.RankinSelbergGeneral RamanujanTau.RankinSelbergGeneral.Horo
open HoroFn RSFn
open scoped ENNReal

variable [RSFn]

/-- **The unfolding identity** for an `RSFn`. -/
def RSUnfoldG : Prop :=
  ∀ s : ℂ, 2 < s.re → mellin (fun t => (PhiG t : ℂ) - (petNormSq : ℂ)) s =
    gamM m s * riemannZeta (2 * s) * LSeries (fun n => (aF n : ℂ)) s

lemma mellinConv_PhiG {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (fun t => (PhiG t : ℂ) - (petNormSq : ℂ)) s := by
  have h := (rsFEG.hasMellin (s := s) (by simp [rsFEG]; linarith)).1
  exact h

lemma mellin_integrand_ofRealG {σ t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ ((σ : ℂ) - 1) • ((PhiG t : ℂ) - (petNormSq : ℂ)) =
      ((t ^ (σ - 1) * (PhiG t - petNormSq) : ℝ) : ℂ) := by
  rw [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_cpow ht.le, Complex.ofReal_sub]
  push_cast; rfl

lemma integrableOn_mellin_PhiG_real {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun t => t ^ (σ - 1) * (PhiG t - petNormSq)) (Ioi 0) := by
  have h := mellinConv_PhiG (s := (σ : ℂ)) (by simpa using hσ)
  have h2 : IntegrableOn (fun t : ℝ => ((t ^ (σ - 1) * (PhiG t - petNormSq) : ℝ) : ℂ)) (Ioi 0) :=
    h.congr_fun (fun t (ht : 0 < t) => mellin_integrand_ofRealG ht) measurableSet_Ioi
  simpa using h2.re

lemma mellin_PhiG_ofReal (σ : ℝ) :
    mellin (fun t => (PhiG t : ℂ) - (petNormSq : ℂ)) σ =
      ((∫ t in Ioi 0, t ^ (σ - 1) * (PhiG t - petNormSq) : ℝ) : ℂ) := by
  unfold mellin
  exact (setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) =>
    mellin_integrand_ofRealG ht).trans integral_complex_ofReal

lemma integral_mellin_PhiG_real {σ : ℝ} (hσ : 1 < σ) :
    ∫ t in Ioi 0, t ^ (σ - 1) * (PhiG t - petNormSq) =
      2 * (Real.Gamma σ * π ^ (-σ)) * (∑' g : ℕ, ((g : ℝ) + 1) ^ (-(2 * σ))) *
        ∑' n : ℕ, cf n * Real.Gamma (σ + m) / (4 * π * n) ^ (σ + m) := by
  have hσ0 : 0 < σ := by linarith
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ t ^ (σ - 1) * (PhiG t - petNormSq) := fun t (ht : 0 < t) =>
    mul_nonneg (Real.rpow_nonneg ht.le _) (PhiG_sub_nonneg ht)
  have hI0 : 0 ≤ ∫ t in Ioi 0, t ^ (σ - 1) * (PhiG t - petNormSq) :=
    setIntegral_nonneg measurableSet_Ioi hnn
  have hL : ENNReal.ofReal (∫ t in Ioi 0, t ^ (σ - 1) * (PhiG t - petNormSq)) =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (σ - 1)) * ENNReal.ofReal (PhiG t - petNormSq) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_mellin_PhiG_real hσ)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hnn))]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  rw [lintegral_mellin_PhiG hσ0] at hL
  have h := congrArg ENNReal.toReal hL
  rw [ENNReal.toReal_ofReal hI0] at h
  rw [h, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by have := Real.Gamma_pos_of_pos hσ0; positivity), Zfun,
    ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top),
    ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  congr 1
  · congr 1
    exact tsum_congr fun g => ENNReal.toReal_ofReal (by positivity)
  · refine tsum_congr fun n => ENNReal.toReal_ofReal ?_
    have := Real.Gamma_pos_of_pos (show 0 < σ + m by positivity)
    have := cf_nonneg n
    have : 0 ≤ (4 * π * n) ^ (σ + m) := Real.rpow_nonneg (by positivity) _
    positivity

lemma gamM_ofReal (m : ℕ) (σ : ℝ) :
    gamM m σ = ((2 * π ^ (-σ) * Real.Gamma σ * Real.Gamma (σ + m) * (4 * π) ^ (-σ - m) : ℝ) : ℂ) := by
  have h1 : (π : ℂ) ^ (-(σ : ℂ)) = ((π ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow Real.pi_pos.le]; push_cast; rfl
  have h2 : ((4 * π : ℝ) : ℂ) ^ (-(σ : ℂ) - m) = (((4 * π) ^ (-σ - m) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl
  have h4 : Complex.Gamma ((σ : ℂ) + m) = ((Real.Gamma (σ + m) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  unfold gamM
  rw [h1, h2, h4, Complex.Gamma_ofReal]
  push_cast; ring

lemma LSeries_aF_ofReal (σ : ℝ) :
    LSeries (fun n => (aF n : ℂ)) σ = ((∑' n : ℕ, aF n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
  unfold LSeries
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def]
  split_ifs with h
  · subst h; simp [aF_zero]
  · rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast; rfl

lemma tsum_cf_Gamma_eq {σ : ℝ} (hσ : 0 < σ) :
    ∑' n : ℕ, cf n * Real.Gamma (σ + m) / (4 * π * n) ^ (σ + m) =
      Real.Gamma (σ + m) * (4 * π) ^ (-σ - m) * ∑' n : ℕ, aF n / (n : ℝ) ^ σ := by
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (0 : ℝ) ^ (σ + m) = 0 := Real.zero_rpow (by positivity)
    simp [aF, cf_zero, this]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h4 : (0 : ℝ) < 4 * π := by positivity
    rw [Real.mul_rpow h4.le hn0.le, show -σ - m = -(σ + m) by ring, Real.rpow_neg h4.le,
      Real.rpow_add hn0, Real.rpow_natCast]
    unfold aF
    have : 0 < (4 * π) ^ (σ + (m : ℝ)) := Real.rpow_pos_of_pos h4 _
    have : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hn0 _
    field_simp

/-- **`RSUnfoldG` at real points `σ > 2`.** -/
theorem RSUnfold_realG {σ : ℝ} (hσ : 2 < σ) :
    mellin (fun t => (PhiG t : ℂ) - (petNormSq : ℂ)) σ =
      gamM m σ * riemannZeta (2 * σ) * LSeries (fun n => (aF n : ℂ)) σ := by
  rw [mellin_PhiG_ofReal, integral_mellin_PhiG_real (by linarith), gamM_ofReal,
    zeta_ofReal (by linarith), LSeries_aF_ofReal, tsum_cf_Gamma_eq (by linarith)]
  push_cast; ring

/-! ### Extension to complex `s` by the identity theorem -/

/-- `mellin(Φ − ‖Δ‖²) = Λ₀(s) − κ/s − κ/(1−s)` for `Re s > 1`. -/
lemma mellin_PhiG_eq_Λ {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t => (PhiG t : ℂ) - (petNormSq : ℂ)) s =
      rsFEG.Λ₀ s - 1 / s * (petNormSq : ℂ) - 1 / (1 - s) * (petNormSq : ℂ) := by
  have hm := (rsFEG.hasMellin (s := s) (by simp [rsFEG]; linarith)).2
  have hm' : mellin (fun t => (PhiG t : ℂ) - (petNormSq : ℂ)) s = rsFEG.Λ s := hm
  rw [hm', WeakFEPair.Λ]
  change rsFEG.Λ₀ s - (1 / s) • (petNormSq : ℂ) - ((1:ℂ) / (((1:ℝ):ℂ) - s)) • (petNormSq : ℂ) = _
  simp only [smul_eq_mul, Complex.ofReal_one]

lemma abscissa_aF_le : LSeries.abscissaOfAbsConv (fun n => (aF n : ℂ)) ≤ ((2 : ℝ) : EReal) := by
  obtain ⟨K, hK0, hK⟩ := exists_aF_le
  have h := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (f := fun n => (aF n : ℂ))
    (x := 1) ⟨K, fun n _ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (aF_nonneg n), Real.rpow_one]
      exact hK n⟩
  have e : ((1 : ℝ) : EReal) + 1 = ((2 : ℝ) : EReal) := by
    rw [← EReal.coe_one, ← EReal.coe_add]; norm_num
  rwa [e] at h

/-- **The Rankin–Selberg unfolding identity, proved.** -/
theorem rsUnfoldG : RSUnfoldG := by
  intro s hs
  set U : Set ℂ := {s : ℂ | 2 < s.re} with hU
  set f : ℂ → ℂ := fun s => rsFEG.Λ₀ s - 1 / s * (petNormSq : ℂ) - 1 / (1 - s) * (petNormSq : ℂ)
    with hf
  set g : ℂ → ℂ := fun s => gamM m s * riemannZeta (2 * s) * LSeries (fun n => (aF n : ℂ)) s
    with hg
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hfd : DifferentiableOn ℂ f U := by
    intro z hz
    have hz' : 2 < z.re := hz
    have h0 : z ≠ 0 := by intro h; rw [h] at hz'; simp at hz'; linarith
    have h1 : 1 - z ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((rsFEG.differentiable_Λ₀ z).sub ((differentiableAt_const _).div differentiableAt_id h0
      |>.mul_const _)).sub (((differentiableAt_const _).div
        ((differentiableAt_const _).sub differentiableAt_id) h1).mul_const _)
  have hgd : DifferentiableOn ℂ g U := by
    have hL : DifferentiableOn ℂ (LSeries fun n => (aF n : ℂ)) U :=
      (LSeries_differentiableOn _).mono fun z (hz : 2 < z.re) =>
        lt_of_le_of_lt abscissa_aF_le (EReal.coe_lt_coe_iff.2 hz)
    refine DifferentiableOn.mul (fun z hz => ?_) hL
    have hz' : 2 < z.re := hz
    refine DifferentiableAt.differentiableWithinAt ?_
    have hG1 : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z fun m hm => by
      have := congrArg Complex.re hm; simp at this; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    have hG2 : DifferentiableAt ℂ (fun w => Complex.Gamma (w + m)) z := by
      refine (Complex.differentiableAt_Gamma (z + m) fun j hj => ?_).comp z
        (differentiableAt_id.add_const _)
      have := congrArg Complex.re hj; simp at this
      linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j), (Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    have hζ : DifferentiableAt ℂ (fun w => riemannZeta (2 * w)) z := by
      refine (differentiableAt_riemannZeta ?_).comp z (differentiableAt_id.const_mul 2)
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hp1 : DifferentiableAt ℂ (fun w : ℂ => (π : ℂ) ^ (-w)) z :=
      differentiableAt_id.neg.const_cpow (Or.inl pi_ne_zero')
    have hp2 : DifferentiableAt ℂ (fun w : ℂ => ((4 * π : ℝ) : ℂ) ^ (-w - m)) z :=
      (differentiableAt_id.neg.sub_const _).const_cpow (Or.inl fourpi_ne_zero)
    unfold gamM
    exact (((((differentiableAt_const _).mul hp1).mul hG1).mul hG2).mul hp2).mul hζ
  have h3 : (3 : ℂ) ∈ U := by simp [hU]; norm_num
  have hfreq : ∃ᶠ z in 𝓝[≠] (3 : ℂ), f z = g z := by
    have ht : Tendsto (fun n : ℕ => (3 : ℂ) + 1 / ((n : ℂ) + 1)) atTop (𝓝[≠] (3 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (3 : ℂ)
      · simp only [mem_compl_iff, mem_singleton_iff, add_eq_left, one_div, inv_eq_zero]
        exact_mod_cast Nat.succ_ne_zero n
    refine ht.frequently (Frequently.of_forall fun n => ?_)
    have e : (3 : ℂ) + 1 / ((n : ℂ) + 1) = ((3 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; rfl
    have hσ : 2 < 3 + 1 / ((n : ℝ) + 1) := by
      linarith [show (0:ℝ) < 1 / ((n : ℝ) + 1) by positivity]
    rw [e]
    simp only [hf, hg]
    rw [← mellin_PhiG_eq_Λ (by rw [Complex.ofReal_re]; linarith), RSUnfold_realG hσ]
  have heq := (hfd.analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
    (hgd.analyticOnNhd hUo) (convex_halfSpace_re_gt 2).isPreconnected h3 hfreq
  rw [mellin_PhiG_eq_Λ (by linarith)]
  exact heq hs


/-- The weight-`(m+1)` Rankin–Selberg data for an `RSFn`, unconditionally. -/
noncomputable def rsDataG : RSDataM m aF petNormSq where
  Λ₀ := rsFEG.Λ₀
  diff := rsFEG.differentiable_Λ₀
  L₀ := (rsFEG_Λ₀_bdd (-3 / 2) (5 / 2)).choose
  bdd := (rsFEG_Λ₀_bdd (-3 / 2) (5 / 2)).choose_spec
  fe := fun s => by
    have := rsFEG.functional_equation₀ s
    rw [rsFEG_symm_Λ₀] at this
    simpa [rsFEG] using this
  unfold := fun s hs => by
    rw [← rsUnfoldG s hs]
    have hm := (rsFEG.hasMellin (s := s) (by simp [rsFEG]; linarith)).2
    have hm' : mellin (fun t => (PhiG t : ℂ) - (petNormSq : ℂ)) s = rsFEG.Λ s := hm
    rw [hm', WeakFEPair.Λ]
    change rsFEG.Λ₀ s - (1 / s) • (petNormSq : ℂ) - ((1:ℂ) / (((1:ℝ):ℂ) - s)) • (petNormSq : ℂ) = _
    simp only [smul_eq_mul, Complex.ofReal_one]
    have hs0 : s ≠ 0 := by intro h0; rw [h0] at hs; simp at hs; linarith
    have hs1 : (1:ℂ) - s ≠ 0 := by
      intro h1; have := congrArg Complex.re h1; simp at this; linarith
    have hs1' : s - 1 ≠ 0 := by
      intro h1; have := congrArg Complex.re h1; simp at this; linarith
    field_simp
    ring

lemma petNormSq_nonneg : 0 ≤ petNormSq := by
  rw [petNormSq_eq]
  exact setIntegral_nonneg measurableSet_Freg fun p hp =>
    div_nonneg (G_nonneg _) (by have := Freg_im hp; positivity)

/-- **Power saving `1/84` for an abstract `RSFn` of weight `m + 1 ≥ 3`.** -/
theorem power_saving_RSFn (hm : 2 ≤ m) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, aF n - petNormSq * rsConstM m * N| ≤ C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) :=
  power_saving_84_of_RSDataM hm aF aF_nonneg aF_zero petNormSq_nonneg rsDataG summable_aF

end RamanujanTau.RankinErrorGeneral

#print axioms RamanujanTau.RankinErrorGeneral.rsUnfoldG
#print axioms RamanujanTau.RankinErrorGeneral.power_saving_RSFn
