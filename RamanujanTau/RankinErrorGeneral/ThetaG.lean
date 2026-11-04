/-
# The theta integral `Φ(t) = ∫_𝓕 G Θ_t dμ` for an `RSFn`, and its weak functional-equation pair

Generalizes `RankinError/ThetaInt.lean` and `RankinError/RSFE.lean` from `G = |Δ|²y¹²` to any
`RSFn`: only `G ≥ 0`, invariance and `exp_decay` are used.

* `PhiG_inv`: `Φ(1/t) = tΦ(t)`; `PhiG_sub_le`: `0 ≤ Φ(t) − ‖G‖ ≤ C_R(t−1)^{−R}` (`t > 1`);
* `rsFEG : WeakFEPair ℂ` (`f = g = Φ`, `k = 1`, `ε = 1`, `f₀ = g₀ = ∫_𝓕 G dμ`);
* `rsFEG_Λ₀_bdd`: `Λ₀` is bounded on vertical strips.
-/
import RamanujanTau.RankinErrorGeneral.RSFn

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.RankinErrorGeneral

open Real Filter Topology MeasureTheory Set Asymptotics
open RamanujanTau.RankinSelberg hiding G G_smul continuous_G G_pos
open RamanujanTau.RankinError
open RamanujanTau.RankinSelbergGeneral RamanujanTau.RankinSelbergGeneral.Horo
open HoroFn
open UpperHalfPlane hiding I

variable [RSFn]

/-- The weights `gR · y^j` are integrable on `𝓕`. -/
lemma integrableOn_gR_mul_powG (j : ℕ) : IntegrableOn (fun p : ℝ × ℝ => gR p * p.2 ^ j) Freg := by
  obtain ⟨K, c, hK0, hc, hK⟩ := RSFn.exp_decay
  set S : Set (ℝ × ℝ) := Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioi 0
  have hFS : Freg ⊆ S := by
    intro p hp
    exact ⟨abs_le.1 hp.2.1, hp.1⟩
  have hint : IntegrableOn (fun p : ℝ × ℝ => (1 : ℝ) * (4 * K * (p.2 ^ (j : ℝ) * rexp (-c * p.2 ^ (1:ℝ))))) S := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact Integrable.mul_prod (μ := volume.restrict (Icc (-(1 / 2 : ℝ)) (1 / 2)))
      (ν := volume.restrict (Ioi (0:ℝ))) (f := fun _ : ℝ => (1:ℝ))
      (g := fun y : ℝ => 4 * K * (y ^ (j : ℝ) * rexp (-c * y ^ (1:ℝ))))
      (integrableOn_const (by simp))
      ((integrableOn_rpow_mul_exp_neg_mul_rpow (by have := (Nat.cast_nonneg j : (0:ℝ) ≤ j); linarith) le_rfl hc).const_mul _)
  refine (hint.mono_set hFS).mono' ?_ ?_
  · exact (measurable_gR.mul (measurable_snd.pow_const j)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Freg]
    refine Eventually.of_forall fun p hp => ?_
    have hy := Freg_im hp
    have hy0 : 0 < p.2 := by linarith
    have hG := hK (gpt p.1 p.2) (by rw [gpt_im]; exact le_max_of_le_left hy)
    rw [gpt_im, max_eq_left (by linarith)] at hG
    have hg : 0 ≤ gR p := div_nonneg (G_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg (by positivity)), Real.rpow_natCast,
      Real.rpow_one, one_mul]
    unfold gR
    have h4 : 1 / p.2 ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    calc G (gpt p.1 p.2) / p.2 ^ 2 * p.2 ^ j = G (gpt p.1 p.2) * (1 / p.2 ^ 2) * p.2 ^ j := by ring
      _ ≤ (K * rexp (-c * p.2)) * 4 * p.2 ^ j := by gcongr
      _ = 4 * K * (p.2 ^ j * rexp (-c * p.2)) := by ring

lemma integrableOn_gR_thetaG {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun p : ℝ × ℝ => gR p * theta p.1 p.2 t) Freg := by
  refine ((integrableOn_gR_mul_powG 1).const_mul (max 1 (1 / t) * (2 * vt0 ^ 2))).mono' ?_ ?_
  · exact (measurable_gR.mul (measurable_theta t)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Freg]
    refine Eventually.of_forall fun p hp => ?_
    have hy0 : 0 < p.2 := by linarith [Freg_im hp]
    have hg : 0 ≤ gR p := div_nonneg (G_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg (theta_nonneg _ _ _)), pow_one]
    have := theta_le_on_Freg hp ht
    calc gR p * theta p.1 p.2 t ≤ gR p * (max 1 (1 / t) * (2 * vt0 ^ 2) * p.2) :=
          mul_le_mul_of_nonneg_left this hg
      _ = _ := by ring

/-- `Φ(t) = ∫_𝓕 G Θ_t dμ`. -/
noncomputable def PhiG (t : ℝ) : ℝ := ∫ p in Freg, gR p * theta p.1 p.2 t

lemma PhiG_inv {t : ℝ} (ht : 0 < t) : PhiG (1 / t) = t * PhiG t := by
  unfold PhiG
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Freg fun p hp => ?_
  have hy0 : 0 < p.2 := by linarith [Freg_im hp]
  rw [theta_inv p.1 hy0 ht]; ring

lemma PhiG_antitoneOn : AntitoneOn PhiG (Ioi 0) := by
  intro s hs t ht hst
  unfold PhiG
  refine setIntegral_mono_on (integrableOn_gR_thetaG ht) (integrableOn_gR_thetaG hs)
    measurableSet_Freg fun p hp => ?_
  have hy0 : 0 < p.2 := by linarith [Freg_im hp]
  exact mul_le_mul_of_nonneg_left (theta_antitone p.1 hy0 hs hst)
    (div_nonneg (G_nonneg _) (by positivity))

/-- `0 ≤ Φ(t) − ‖Δ‖² ≤ C (t − 1)^{−R}` for `t > 1`. -/
lemma PhiG_sub_le (R : ℕ) : ∃ C : ℝ, ∀ t : ℝ, 1 < t →
    0 ≤ PhiG t - petNormSq ∧ PhiG t - petNormSq ≤ C * (t - 1) ^ (-(R : ℝ)) := by
  set I₀ : ℝ := ∫ p in Freg, gR p * p.2 ^ (R + 1) with hI₀
  refine ⟨(Nat.factorial R : ℝ) * (2 / π) ^ R * (2 * vt0 ^ 2) * I₀, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hdiff : PhiG t - petNormSq = ∫ p in Freg, gR p * (theta p.1 p.2 t - 1) := by
    unfold PhiG
    rw [petNormSq_eq, ← integral_sub (integrableOn_gR_thetaG ht0)
      (by simpa using integrableOn_gR_mul_powG 0)]
    congr 1; funext p; ring
  rw [hdiff]
  have hpt : ∀ p ∈ Freg, 0 ≤ gR p * (theta p.1 p.2 t - 1) := by
    intro p hp
    have hy0 : 0 < p.2 := by linarith [Freg_im hp]
    refine mul_nonneg (div_nonneg (G_nonneg _) (by positivity)) ?_
    -- `Θ ≥ 1` (the `(0,0)` term)
    have h := (summable_theta p.1 hy0 ht0).le_tsum (0, 0) (fun q _ => (Real.exp_pos _).le)
    have hq : Qf p.1 p.2 (0, 0) = 0 := by simp [Qf]
    rw [hq, mul_zero, Real.exp_zero] at h
    have h' : 1 ≤ theta p.1 p.2 t := h
    linarith
  constructor
  · exact setIntegral_nonneg measurableSet_Freg hpt
  · -- pointwise: `Θ_t − 1 ≤ e^{−π(t−1)/(2y)}·2yϑ₀² ≤ R! (2y/(π(t−1)))^R · 2yϑ₀²`
    have hbound : ∀ p ∈ Freg, gR p * (theta p.1 p.2 t - 1) ≤
        ((Nat.factorial R : ℝ) * (2 / π) ^ R * (2 * vt0 ^ 2) * (t - 1) ^ (-(R : ℝ))) *
          (gR p * p.2 ^ (R + 1)) := by
      intro p hp
      have hy := Freg_im hp
      have hy0 : 0 < p.2 := by linarith
      have hg : 0 ≤ gR p := div_nonneg (G_nonneg _) (by positivity)
      have h1 := theta_sub_one_le hy0 hp.2.1 hp.2.2 ht.le
      have h2 : theta p.1 p.2 1 ≤ 2 * p.2 * vt0 ^ 2 := theta_one_le hy hp.2.1 hp.2.2
      set u : ℝ := π * (t - 1) / (2 * p.2) with hu
      have hu0 : 0 < u := by rw [hu]; have := Real.pi_pos; apply div_pos <;> nlinarith
      have he : rexp (-π * (t - 1) / (2 * p.2)) ≤ (Nat.factorial R : ℝ) / u ^ R := by
        have := Real.pow_div_factorial_le_exp (x := u) hu0.le R
        rw [show -π * (t - 1) / (2 * p.2) = -u by rw [hu]; ring, Real.exp_neg,
          le_div_iff₀ (by positivity)]
        rw [div_le_iff₀ (by positivity)] at this
        calc (rexp u)⁻¹ * u ^ R ≤ (rexp u)⁻¹ * (rexp u * (Nat.factorial R : ℝ)) := by gcongr
          _ = (Nat.factorial R : ℝ) := by field_simp
      have hfac : (Nat.factorial R : ℝ) / u ^ R =
          (Nat.factorial R : ℝ) * (2 / π) ^ R * (t - 1) ^ (-(R : ℝ)) * p.2 ^ R := by
        rw [hu, Real.rpow_neg (by linarith), Real.rpow_natCast, div_pow, div_pow, mul_pow, mul_pow]
        have : t - 1 ≠ 0 := by linarith
        have hπ : π ≠ 0 := Real.pi_ne_zero
        first | (field_simp; ring) | field_simp
      calc gR p * (theta p.1 p.2 t - 1) ≤ gR p * (rexp (-π * (t - 1) / (2 * p.2)) * theta p.1 p.2 1) :=
            mul_le_mul_of_nonneg_left h1 hg
        _ ≤ gR p * (((Nat.factorial R : ℝ) / u ^ R) * (2 * p.2 * vt0 ^ 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul he h2 (theta_nonneg _ _ _) (by positivity)) hg
        _ = _ := by rw [hfac]; ring
    calc ∫ p in Freg, gR p * (theta p.1 p.2 t - 1)
        ≤ ∫ p in Freg, ((Nat.factorial R : ℝ) * (2 / π) ^ R * (2 * vt0 ^ 2) * (t - 1) ^ (-(R : ℝ))) *
          (gR p * p.2 ^ (R + 1)) :=
          setIntegral_mono_on ((integrableOn_gR_thetaG ht0).sub
            (by simpa using integrableOn_gR_mul_powG 0) |>.congr_fun (fun p _ => by simp only [Pi.sub_apply]; ring)
            measurableSet_Freg) ((integrableOn_gR_mul_powG (R + 1)).const_mul _)
            measurableSet_Freg hbound
      _ = _ := by rw [integral_const_mul]; ring

lemma locallyIntegrableOn_PhiG : LocallyIntegrableOn (fun t => (PhiG t : ℂ)) (Ioi 0) := by
  refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun K hK hKc => ?_
  exact ((PhiG_antitoneOn.mono hK).integrableOn_isCompact hKc).ofReal

lemma PhiG_top (r : ℝ) : (fun t => (PhiG t : ℂ) - (petNormSq : ℂ)) =O[atTop] (· ^ r) := by
  obtain ⟨R, hR⟩ := exists_nat_ge (-r)
  obtain ⟨C, hC⟩ := PhiG_sub_le R
  refine IsBigO.of_bound (|C| * 2 ^ (R : ℝ)) ?_
  filter_upwards [eventually_ge_atTop (2:ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  obtain ⟨h0, h1⟩ := hC t (by linarith)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
  have hR0 : -(R : ℝ) ≤ 0 := by simp
  have e1 : (t - 1) ^ (-(R : ℝ)) ≤ (t / 2) ^ (-(R : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) hR0
  have e2 : (t / 2) ^ (-(R : ℝ)) = 2 ^ (R : ℝ) * t ^ (-(R : ℝ)) := by
    rw [Real.div_rpow ht0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
  have e3 : t ^ (-(R : ℝ)) ≤ t ^ r := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc PhiG t - petNormSq ≤ C * (t - 1) ^ (-(R : ℝ)) := h1
    _ ≤ |C| * (t - 1) ^ (-(R : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |C| * (2 ^ (R : ℝ) * t ^ (-(R : ℝ))) := by rw [← e2]; gcongr
    _ ≤ |C| * (2 ^ (R : ℝ) * t ^ r) := by gcongr
    _ = |C| * 2 ^ (R : ℝ) * t ^ r := by ring

/-- The weak functional-equation pair `(Φ, Φ)`, weight `1`, root number `1`, constant `‖Δ‖²`. -/
noncomputable def rsFEG : WeakFEPair ℂ where
  f := fun t => (PhiG t : ℂ)
  g := fun t => (PhiG t : ℂ)
  k := 1
  ε := 1
  f₀ := (petNormSq : ℂ)
  g₀ := (petNormSq : ℂ)
  hf_int := locallyIntegrableOn_PhiG
  hg_int := locallyIntegrableOn_PhiG
  hk := one_pos
  hε := one_ne_zero
  h_feq := fun x hx => by
    simp only [Real.rpow_one, one_mul]
    rw [PhiG_inv hx]; push_cast; ring
  hf_top := PhiG_top
  hg_top := PhiG_top

lemma rsFEG_symm_Λ₀ : rsFEG.symm.Λ₀ = rsFEG.Λ₀ := by
  funext s
  simp only [WeakFEPair.Λ₀, WeakFEPair.f_modif, WeakFEPair.symm, rsFEG, inv_one]

/-- `Λ₀` is bounded on every vertical strip. -/
lemma rsFEG_Λ₀_bdd (a b : ℝ) : ∃ L : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖rsFEG.Λ₀ s‖ ≤ L := by
  set f := rsFEG.f_modif
  have hconv : ∀ s : ℂ, MellinConvergent f s := fun s => (rsFEG.toStrongFEPair.hasMellin s).1
  set L := (∫ t in Ioi (0:ℝ), ‖(t : ℂ) ^ ((a : ℂ) - 1) • f t‖) +
    ∫ t in Ioi (0:ℝ), ‖(t : ℂ) ^ ((b : ℂ) - 1) • f t‖ with hL
  refine ⟨L, fun s h1 h2 => ?_⟩
  have hΛ : rsFEG.Λ₀ s = mellin f s := rfl
  rw [hΛ, mellin]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hia := (hconv a).norm
  have hib := (hconv b).norm
  rw [hL, ← integral_add hia hib]
  refine setIntegral_mono_on (hconv s).norm (hia.add hib) measurableSet_Ioi fun t ht => ?_
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (rpow_le_add ht h1 h2) (norm_nonneg _)

end RamanujanTau.RankinErrorGeneral
