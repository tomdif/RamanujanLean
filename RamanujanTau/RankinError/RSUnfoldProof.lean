/-
# The Rankin–Selberg unfolding identity `RSUnfold`, and the unconditional power saving (F6)

* `RSUnfold_real`: for real `σ > 2`, `mellin(Φ − ‖Δ‖²)(σ) = γ(σ) ζ(2σ) ∑ τ(n)² n^{−σ−11}`, the real
  form of `lintegral_mellin_Phi`.
* `rsUnfold : RSUnfold`: both sides are holomorphic on `Re s > 2` (`mellin(Φ − ‖Δ‖²) = rsFE.Λ`
  there), and they agree on `(2, ∞)`; the identity theorem
  (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) extends the equality.
* **`rankinSelberg_power_saving_unconditional`**:
  `|∑_{n≤N} τ(n)²/n¹¹ − (3/π)(4π)¹²‖Δ‖²/11! · N| ≤ C N^{1 − 2^{−22}}`.
-/
import RamanujanTau.RankinError.RSMellin

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Real Filter Topology MeasureTheory Set
open RamanujanTau.RankinSelberg RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open scoped ENNReal

lemma mellinConv_Phi {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (fun t => (Phi t : ℂ) - (petNormSq : ℂ)) s := by
  have h := (rsFE.hasMellin (s := s) (by simp [rsFE]; linarith)).1
  exact h

lemma mellin_integrand_ofReal {σ t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ ((σ : ℂ) - 1) • ((Phi t : ℂ) - (petNormSq : ℂ)) =
      ((t ^ (σ - 1) * (Phi t - petNormSq) : ℝ) : ℂ) := by
  rw [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_cpow ht.le, Complex.ofReal_sub]
  push_cast; rfl

lemma integrableOn_mellin_Phi_real {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun t => t ^ (σ - 1) * (Phi t - petNormSq)) (Ioi 0) := by
  have h := mellinConv_Phi (s := (σ : ℂ)) (by simpa using hσ)
  have h2 : IntegrableOn (fun t : ℝ => ((t ^ (σ - 1) * (Phi t - petNormSq) : ℝ) : ℂ)) (Ioi 0) :=
    h.congr_fun (fun t (ht : 0 < t) => mellin_integrand_ofReal ht) measurableSet_Ioi
  simpa using h2.re

lemma mellin_Phi_ofReal (σ : ℝ) :
    mellin (fun t => (Phi t : ℂ) - (petNormSq : ℂ)) σ =
      ((∫ t in Ioi 0, t ^ (σ - 1) * (Phi t - petNormSq) : ℝ) : ℂ) := by
  unfold mellin
  exact (setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) =>
    mellin_integrand_ofReal ht).trans integral_complex_ofReal

lemma integral_mellin_Phi_real {σ : ℝ} (hσ : 1 < σ) :
    ∫ t in Ioi 0, t ^ (σ - 1) * (Phi t - petNormSq) =
      2 * (Real.Gamma σ * π ^ (-σ)) * (∑' g : ℕ, ((g : ℝ) + 1) ^ (-(2 * σ))) *
        ∑' n : ℕ, ((tau n : ℝ)) ^ 2 * Real.Gamma (σ + 11) / (4 * π * n) ^ (σ + 11) := by
  have hσ0 : 0 < σ := by linarith
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ t ^ (σ - 1) * (Phi t - petNormSq) := fun t (ht : 0 < t) =>
    mul_nonneg (Real.rpow_nonneg ht.le _) (Phi_sub_nonneg ht)
  have hI0 : 0 ≤ ∫ t in Ioi 0, t ^ (σ - 1) * (Phi t - petNormSq) :=
    setIntegral_nonneg measurableSet_Ioi hnn
  have hL : ENNReal.ofReal (∫ t in Ioi 0, t ^ (σ - 1) * (Phi t - petNormSq)) =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (σ - 1)) * ENNReal.ofReal (Phi t - petNormSq) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_mellin_Phi_real hσ)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hnn))]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  rw [lintegral_mellin_Phi hσ0] at hL
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
    have := Real.Gamma_pos_of_pos (show 0 < σ + 11 by linarith)
    have : 0 ≤ (4 * π * n) ^ (σ + 11) := Real.rpow_nonneg (by positivity) _
    positivity

lemma gam_ofReal (σ : ℝ) :
    gam σ = ((2 * π ^ (-σ) * Real.Gamma σ * Real.Gamma (σ + 11) * (4 * π) ^ (-σ - 11) : ℝ) : ℂ) := by
  have h1 : (π : ℂ) ^ (-(σ : ℂ)) = ((π ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow Real.pi_pos.le]; push_cast; rfl
  have h2 : ((4 * π : ℝ) : ℂ) ^ (-(σ : ℂ) - 11) = (((4 * π) ^ (-σ - 11) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl
  have h4 : Complex.Gamma ((σ : ℂ) + 11) = ((Real.Gamma (σ + 11) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  unfold gam
  rw [h1, h2, h4, Complex.Gamma_ofReal]
  push_cast; ring

lemma zeta_ofReal {σ : ℝ} (hσ : 1 / 2 < σ) :
    riemannZeta (2 * (σ : ℂ)) = ((∑' g : ℕ, ((g : ℝ) + 1) ^ (-(2 * σ)) : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; linarith), Complex.ofReal_tsum]
  refine tsum_congr fun g => ?_
  rw [Real.rpow_neg (by positivity), Complex.ofReal_inv, Complex.ofReal_cpow (by positivity),
    one_div]
  push_cast; rfl

lemma LSeries_aTau_ofReal (σ : ℝ) :
    LSeries (fun n => (aTau n : ℂ)) σ = ((∑' n : ℕ, aTau n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
  unfold LSeries
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def]
  split_ifs with h
  · subst h; simp [aTau_zero]
  · rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast; rfl

lemma tsum_tau_Gamma_eq {σ : ℝ} (hσ : 0 < σ) :
    ∑' n : ℕ, ((tau n : ℝ)) ^ 2 * Real.Gamma (σ + 11) / (4 * π * n) ^ (σ + 11) =
      Real.Gamma (σ + 11) * (4 * π) ^ (-σ - 11) * ∑' n : ℕ, aTau n / (n : ℝ) ^ σ := by
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (0 : ℝ) ^ (σ + 11) = 0 := Real.zero_rpow (by linarith)
    simp [aTau, this]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h4 : (0 : ℝ) < 4 * π := by positivity
    rw [Real.mul_rpow h4.le hn0.le, show -σ - 11 = -(σ + 11) by ring, Real.rpow_neg h4.le,
      Real.rpow_add hn0, show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    unfold aTau
    have : 0 < (4 * π) ^ (σ + ((11 : ℕ) : ℝ)) := Real.rpow_pos_of_pos h4 _
    have : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hn0 _
    field_simp

/-- **`RSUnfold` at real points `σ > 2`.** -/
theorem RSUnfold_real {σ : ℝ} (hσ : 2 < σ) :
    mellin (fun t => (Phi t : ℂ) - (petNormSq : ℂ)) σ =
      gam σ * riemannZeta (2 * σ) * LSeries (fun n => (aTau n : ℂ)) σ := by
  rw [mellin_Phi_ofReal, integral_mellin_Phi_real (by linarith), gam_ofReal,
    zeta_ofReal (by linarith), LSeries_aTau_ofReal, tsum_tau_Gamma_eq (by linarith)]
  push_cast; ring

/-! ### Extension to complex `s` by the identity theorem -/

/-- `mellin(Φ − ‖Δ‖²) = Λ₀(s) − κ/s − κ/(1−s)` for `Re s > 1`. -/
lemma mellin_Phi_eq_Λ {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t => (Phi t : ℂ) - (petNormSq : ℂ)) s =
      rsFE.Λ₀ s - 1 / s * (petNormSq : ℂ) - 1 / (1 - s) * (petNormSq : ℂ) := by
  have hm := (rsFE.hasMellin (s := s) (by simp [rsFE]; linarith)).2
  have hm' : mellin (fun t => (Phi t : ℂ) - (petNormSq : ℂ)) s = rsFE.Λ s := hm
  rw [hm', WeakFEPair.Λ]
  change rsFE.Λ₀ s - (1 / s) • (petNormSq : ℂ) - ((1:ℂ) / (((1:ℝ):ℂ) - s)) • (petNormSq : ℂ) = _
  simp only [smul_eq_mul, Complex.ofReal_one]

lemma abscissa_aTau_le : LSeries.abscissaOfAbsConv (fun n => (aTau n : ℂ)) ≤ ((2 : ℝ) : EReal) := by
  obtain ⟨K, hK0, hK⟩ := exists_aTau_le
  have h := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (f := fun n => (aTau n : ℂ))
    (x := 1) ⟨K, fun n _ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (aTau_nonneg n), Real.rpow_one]
      exact hK n⟩
  have e : ((1 : ℝ) : EReal) + 1 = ((2 : ℝ) : EReal) := by
    rw [← EReal.coe_one, ← EReal.coe_add]; norm_num
  rwa [e] at h

/-- **The Rankin–Selberg unfolding identity, proved.** -/
theorem rsUnfold : RSUnfold := by
  intro s hs
  set U : Set ℂ := {s : ℂ | 2 < s.re} with hU
  set f : ℂ → ℂ := fun s => rsFE.Λ₀ s - 1 / s * (petNormSq : ℂ) - 1 / (1 - s) * (petNormSq : ℂ)
    with hf
  set g : ℂ → ℂ := fun s => gam s * riemannZeta (2 * s) * LSeries (fun n => (aTau n : ℂ)) s
    with hg
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hfd : DifferentiableOn ℂ f U := by
    intro z hz
    have hz' : 2 < z.re := hz
    have h0 : z ≠ 0 := by intro h; rw [h] at hz'; simp at hz'; linarith
    have h1 : 1 - z ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((rsFE.differentiable_Λ₀ z).sub ((differentiableAt_const _).div differentiableAt_id h0
      |>.mul_const _)).sub (((differentiableAt_const _).div
        ((differentiableAt_const _).sub differentiableAt_id) h1).mul_const _)
  have hgd : DifferentiableOn ℂ g U := by
    have hL : DifferentiableOn ℂ (LSeries fun n => (aTau n : ℂ)) U :=
      (LSeries_differentiableOn _).mono fun z (hz : 2 < z.re) =>
        lt_of_le_of_lt abscissa_aTau_le (EReal.coe_lt_coe_iff.2 hz)
    refine DifferentiableOn.mul (fun z hz => ?_) hL
    have hz' : 2 < z.re := hz
    refine DifferentiableAt.differentiableWithinAt ?_
    have hG1 : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z fun m hm => by
      have := congrArg Complex.re hm; simp at this; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    have hG2 : DifferentiableAt ℂ (fun w => Complex.Gamma (w + 11)) z := by
      refine (Complex.differentiableAt_Gamma (z + 11) fun m hm => ?_).comp z
        (differentiableAt_id.add_const 11)
      have := congrArg Complex.re hm; simp at this; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    have hζ : DifferentiableAt ℂ (fun w => riemannZeta (2 * w)) z := by
      refine (differentiableAt_riemannZeta ?_).comp z (differentiableAt_id.const_mul 2)
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hp1 : DifferentiableAt ℂ (fun w : ℂ => (π : ℂ) ^ (-w)) z :=
      differentiableAt_id.neg.const_cpow (Or.inl pi_ne_zero')
    have hp2 : DifferentiableAt ℂ (fun w : ℂ => ((4 * π : ℝ) : ℂ) ^ (-w - 11)) z :=
      (differentiableAt_id.neg.sub_const 11).const_cpow (Or.inl fourpi_ne_zero)
    unfold gam
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
    rw [← mellin_Phi_eq_Λ (by rw [Complex.ofReal_re]; linarith), RSUnfold_real hσ]
  have heq := (hfd.analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
    (hgd.analyticOnNhd hUo) (convex_halfSpace_re_gt 2).isPreconnected h3 hfreq
  rw [mellin_Phi_eq_Λ (by linarith)]
  exact heq hs

/-- **Rankin–Selberg with a power-saving error term, unconditionally.** -/
theorem rankinSelberg_power_saving_unconditional :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - 1 / 2 ^ 22 : ℝ) :=
  rankinSelberg_power_saving_of_unfold rsUnfold

end RamanujanTau.RankinError

#print axioms RamanujanTau.RankinError.RSUnfold_real
#print axioms RamanujanTau.RankinError.rsUnfold
#print axioms RamanujanTau.RankinError.rankinSelberg_power_saving_unconditional
