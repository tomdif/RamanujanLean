/-
# The Mellin transform of `Φ − ‖Δ‖²` at real points (F4)

For real `σ > 0`, in `[0, ∞]` (`lintegral_mellin_Phi`):

    ∫₀^∞ t^{σ−1} (Φ(t) − ‖Δ‖²) dt
      = 2 Γ(σ) π^{−σ} · ∑_{g≥1} g^{−2σ} · ∑ₙ τ(n)² Γ(σ+11) (4πn)^{−σ−11}.

Proof: the unfolding identity `unfold_theta`, Tonelli in `(t, v)`, Euler's integral
`∫₀^∞ t^{σ−1} e^{−πtg²/v} dt = Γ(σ)(v/(πg²))^σ` termwise, and the strip identity
`lintegral_mellin_horocycle` (E3a).
-/
import RamanujanTau.RankinError.UnfoldTheta

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Real Filter Topology MeasureTheory Set
open RamanujanTau.RankinSelberg RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open scoped ENNReal

lemma one_le_theta (x : ℝ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t) : 1 ≤ theta x y t := by
  have h := (summable_theta x hy ht).le_tsum (0, 0) (fun q _ => (Real.exp_pos _).le)
  have hq : Qf x y (0, 0) = 0 := by simp [Qf]
  rw [hq, mul_zero, Real.exp_zero] at h
  exact h

lemma integrableOn_gR_theta_sub {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun p : ℝ × ℝ => gR p * (theta p.1 p.2 t - 1)) Freg :=
  ((integrableOn_gR_theta ht).sub (by simpa using integrableOn_gR_mul_pow 0)).congr_fun
    (fun p _ => by simp only [Pi.sub_apply]; ring) measurableSet_Freg

lemma Phi_sub_eq {t : ℝ} (ht : 0 < t) :
    Phi t - petNormSq = ∫ p in Freg, gR p * (theta p.1 p.2 t - 1) := by
  unfold Phi
  rw [petNormSq_eq, ← integral_sub (integrableOn_gR_theta ht)
    (by simpa using integrableOn_gR_mul_pow 0)]
  congr 1; funext p; ring

lemma gR_theta_sub_nonneg {t : ℝ} (ht : 0 < t) {p : ℝ × ℝ} (hp : p ∈ Freg) :
    0 ≤ gR p * (theta p.1 p.2 t - 1) := by
  have hy0 : 0 < p.2 := by linarith [Freg_im hp]
  exact mul_nonneg (div_nonneg (G_pos _).le (by positivity))
    (sub_nonneg.2 (one_le_theta _ hy0 ht))

lemma Phi_sub_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ Phi t - petNormSq := by
  rw [Phi_sub_eq ht]
  exact setIntegral_nonneg measurableSet_Freg fun p hp => gR_theta_sub_nonneg ht hp

lemma ofReal_Phi_sub {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (Phi t - petNormSq) =
      ∫⁻ p in Freg, ENNReal.ofReal (gR p * (theta p.1 p.2 t - 1)) := by
  rw [Phi_sub_eq ht, ofReal_integral_eq_lintegral_ofReal (integrableOn_gR_theta_sub ht)
    ((ae_restrict_iff' measurableSet_Freg).2 (Eventually.of_forall fun p hp =>
      gR_theta_sub_nonneg ht hp))]

/-- The horocycle mean as a series of measurable terms. -/
noncomputable def Jfun (v : ℝ) : ℝ≥0∞ := ∑' n : ℕ, ENNReal.ofReal (mterm 2 n v)

lemma measurable_Jfun : Measurable Jfun :=
  Measurable.ennreal_tsum fun n => ENNReal.measurable_ofReal.comp (by unfold mterm; fun_prop)

lemma ofReal_Ihor {v : ℝ} (hv : 0 < v) : ENNReal.ofReal (Ihor v) = Jfun v := by
  have h := hasSum_mterm 2 hv
  rw [sub_self, Real.rpow_zero, mul_one] at h
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => mterm_nonneg 2 n hv) h.summable]
  rfl

/-- `ζ(2σ)` in `[0, ∞]`. -/
noncomputable def Zfun (σ : ℝ) : ℝ≥0∞ := ∑' g : ℕ, ENNReal.ofReal (((g : ℝ) + 1) ^ (-(2 * σ)))

/-- Euler's integral, termwise: `∫₀^∞ t^{σ−1} h_t(v) dt = Γ(σ) π^{−σ} v^σ ζ(2σ)`. -/
lemma lintegral_hfun {σ : ℝ} (hσ : 0 < σ) {v : ℝ} (hv : 0 < v) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (σ - 1)) * hfun t v =
      ENNReal.ofReal (Real.Gamma σ * π ^ (-σ) * v ^ σ) * Zfun σ := by
  unfold hfun Zfun
  simp_rw [← ENNReal.tsum_mul_left]
  have hmg : ∀ g : ℕ, Measurable fun t : ℝ => ENNReal.ofReal (t ^ (σ - 1)) *
      ENNReal.ofReal (rexp (-π * t * ((g : ℝ) + 1) ^ 2 / v)) := fun g =>
    (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  rw [lintegral_tsum fun g => (hmg g).aemeasurable]
  refine tsum_congr fun g => ?_
  set r : ℝ := π * ((g : ℝ) + 1) ^ 2 / v with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hint : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * rexp (-(r * t))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := σ - 1) (p := 1) (by linarith) le_rfl hr0
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
  have e1 : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (t ^ (σ - 1)) *
      ENNReal.ofReal (rexp (-π * t * ((g : ℝ) + 1) ^ 2 / v)) =
      ENNReal.ofReal (t ^ (σ - 1) * rexp (-(r * t))) := by
    intro t ht
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt ht) _)]
    congr 2
    rw [hr]; field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi e1, ← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le)),
    Real.integral_rpow_mul_exp_neg_mul_Ioi hσ hr0, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hg : (0 : ℝ) < (g : ℝ) + 1 := by positivity
  rw [hr, one_div_div, Real.div_rpow hv.le (by positivity), Real.mul_rpow Real.pi_pos.le
    (by positivity), Real.rpow_neg (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hg.le,
    Real.rpow_neg hg.le]
  push_cast
  field_simp

/-- **The Mellin transform of `Φ − ‖Δ‖²` at real `σ > 0`**, in `[0, ∞]`. -/
theorem lintegral_mellin_Phi {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (σ - 1)) * ENNReal.ofReal (Phi t - petNormSq) =
      2 * ENNReal.ofReal (Real.Gamma σ * π ^ (-σ)) * Zfun σ *
        ∑' n : ℕ, ENNReal.ofReal (((tau n : ℝ)) ^ 2 * Real.Gamma (σ + 11) /
          (4 * π * n) ^ (σ + 11)) := by
  set ρ : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal (1 / v ^ 2) with hρ
  have hρm : Measurable ρ :=
    ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_id.pow_const 2))
  -- step 1: unfold for each `t`
  have s1 : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (t ^ (σ - 1)) * ENNReal.ofReal (Phi t - petNormSq) =
      2 * ∫⁻ v in Ioi 0, ENNReal.ofReal (t ^ (σ - 1)) * (Jfun v * hfun t v * ρ v) := by
    intro t ht
    rw [ofReal_Phi_sub ht, unfold_theta ht, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [setLIntegral_congr_fun measurableSet_Ioi (fun v (hv : 0 < v) => by rw [ofReal_Ihor hv])]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi s1, lintegral_const_mul' _ _ (by simp)]
  -- step 2: Tonelli
  have hjoint : Measurable (Function.uncurry fun (t v : ℝ) =>
      ENNReal.ofReal (t ^ (σ - 1)) * (Jfun v * hfun t v * ρ v)) := by
    refine (ENNReal.measurable_ofReal.comp ?_).mul
      (((measurable_Jfun.comp measurable_snd).mul measurable_hfun_uncurry).mul
        (hρm.comp measurable_snd))
    exact measurable_fst.pow_const _
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  -- step 3: Euler's integral in `t`
  have s3 : ∀ v ∈ Ioi (0 : ℝ), ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (σ - 1)) * (Jfun v * hfun t v * ρ v) =
      Jfun v * ENNReal.ofReal (v ^ (σ - 2)) * (ENNReal.ofReal (Real.Gamma σ * π ^ (-σ)) * Zfun σ) := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    have e : ∀ t, ENNReal.ofReal (t ^ (σ - 1)) * (Jfun v * hfun t v * ρ v) =
        ENNReal.ofReal (t ^ (σ - 1)) * hfun t v * (Jfun v * ρ v) := fun t => by ring
    simp_rw [e]
    have hm : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (σ - 1)) * hfun t v :=
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
        (measurable_hfun_uncurry.comp (measurable_id.prodMk measurable_const))
    rw [lintegral_mul_const _ hm, lintegral_hfun hσ hv0]
    have e2 : ENNReal.ofReal (Real.Gamma σ * π ^ (-σ) * v ^ σ) * ρ v =
        ENNReal.ofReal (Real.Gamma σ * π ^ (-σ)) * ENNReal.ofReal (v ^ (σ - 2)) := by
      rw [hρ, ← ENNReal.ofReal_mul (by have := Real.Gamma_pos_of_pos hσ; positivity),
        ← ENNReal.ofReal_mul (by have := Real.Gamma_pos_of_pos hσ; positivity)]
      congr 1
      rw [Real.rpow_sub hv0, Real.rpow_two]
      ring
    calc ENNReal.ofReal (Real.Gamma σ * π ^ (-σ) * v ^ σ) * Zfun σ * (Jfun v * ρ v)
        = Jfun v * (ENNReal.ofReal (Real.Gamma σ * π ^ (-σ) * v ^ σ) * ρ v) * Zfun σ := by ring
      _ = _ := by rw [e2]; ring
  have hm4 : Measurable fun v : ℝ => Jfun v * ENNReal.ofReal (v ^ (σ - 2)) :=
    measurable_Jfun.mul (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
  rw [setLIntegral_congr_fun measurableSet_Ioi s3, lintegral_mul_const _ hm4]
  -- step 4: the strip side (E3a)
  have s4 : ∫⁻ v in Ioi 0, Jfun v * ENNReal.ofReal (v ^ (σ - 2)) =
      ∫⁻ v in Ioi 0, ENNReal.ofReal (Ihor v * v ^ (σ - 2)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
    rw [← ofReal_Ihor hv, ← ENNReal.ofReal_mul]
    unfold Ihor; rw [dif_pos hv]
    exact intervalIntegral.integral_nonneg zero_le_one fun x _ => (G_pos _).le
  rw [s4, lintegral_mellin_horocycle (by linarith)]
  ring

end RamanujanTau.RankinError

#print axioms RamanujanTau.RankinError.lintegral_mellin_Phi
