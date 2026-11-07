/-
# The theta integral `Φ(t) = ∫_𝓕 G(z) Θ_z(t) dμ` and its weak functional-equation pair

* `Phi_inv`: `Φ(1/t) = t Φ(t)`;
* `Phi_sub_le`: `0 ≤ Φ(t) − ‖Δ‖² ≤ C_R (t−1)^{−R}` for `t > 1`, every `R ∈ ℕ`;
* `rsFE : WeakFEPair ℂ` with `f = g = Φ`, `k = 1`, `ε = 1`, `f₀ = g₀ = ‖Δ‖²`.
-/
import RamanujanTau.RankinError.ThetaBound

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Real Filter Topology MeasureTheory Set Asymptotics
open RamanujanTau.RankinSelberg RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open UpperHalfPlane hiding I

lemma theta_eq_toReal (x y t : ℝ) :
    theta x y t = (∑' p : ℤ × ℤ, ENNReal.ofReal (rexp (-π * t * Qf x y p))).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  unfold theta
  congr 1; funext p
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]

lemma measurable_theta (t : ℝ) : Measurable fun p : ℝ × ℝ => theta p.1 p.2 t := by
  simp_rw [theta_eq_toReal]
  refine Measurable.ennreal_toReal (Measurable.ennreal_tsum fun q => ?_)
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
  unfold Qf
  fun_prop

/-- The weights `gR · y^j` are integrable on `𝓕`. -/
lemma integrableOn_gR_mul_pow (j : ℕ) : IntegrableOn (fun p : ℝ × ℝ => gR p * p.2 ^ j) Freg := by
  obtain ⟨K, c, hK0, hc, hK⟩ := exists_G_exp_le
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
    have hg : 0 ≤ gR p := div_nonneg (G_pos _).le (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg (by positivity)), Real.rpow_natCast,
      Real.rpow_one, one_mul]
    unfold gR
    have h4 : 1 / p.2 ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    calc G (gpt p.1 p.2) / p.2 ^ 2 * p.2 ^ j = G (gpt p.1 p.2) * (1 / p.2 ^ 2) * p.2 ^ j := by ring
      _ ≤ (K * rexp (-c * p.2)) * 4 * p.2 ^ j := by gcongr
      _ = 4 * K * (p.2 ^ j * rexp (-c * p.2)) := by ring

/-- `ϑ₀ = ∑ e^{−πk²}`. -/
noncomputable def vt0 : ℝ := ∑' k : ℤ, rexp (-π * (k : ℝ) ^ 2)

lemma theta_le_on_Freg {p : ℝ × ℝ} (hp : p ∈ Freg) {t : ℝ} (ht : 0 < t) :
    theta p.1 p.2 t ≤ max 1 (1 / t) * (2 * vt0 ^ 2) * p.2 := by
  have hy := Freg_im hp
  have hy0 : 0 < p.2 := by linarith
  have h1 : theta p.1 p.2 1 ≤ 2 * p.2 * vt0 ^ 2 := theta_one_le hy hp.2.1 hp.2.2
  rcases le_or_gt t 1 with h | h
  · refine (theta_le_of_le_one p.1 hy0 ht h).trans ?_
    rw [max_eq_right (by rw [le_div_iff₀ ht]; linarith)]
    rw [div_le_iff₀ ht]
    calc theta p.1 p.2 1 ≤ 2 * p.2 * vt0 ^ 2 := h1
      _ = 1 / t * (2 * vt0 ^ 2) * p.2 * t := by field_simp
  · refine (theta_antitone p.1 hy0 one_pos h.le).trans ?_
    rw [max_eq_left (by rw [div_le_iff₀ ht]; linarith)]
    linarith

lemma integrableOn_gR_theta {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun p : ℝ × ℝ => gR p * theta p.1 p.2 t) Freg := by
  refine ((integrableOn_gR_mul_pow 1).const_mul (max 1 (1 / t) * (2 * vt0 ^ 2))).mono' ?_ ?_
  · exact (measurable_gR.mul (measurable_theta t)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Freg]
    refine Eventually.of_forall fun p hp => ?_
    have hy0 : 0 < p.2 := by linarith [Freg_im hp]
    have hg : 0 ≤ gR p := div_nonneg (G_pos _).le (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg (theta_nonneg _ _ _)), pow_one]
    have := theta_le_on_Freg hp ht
    calc gR p * theta p.1 p.2 t ≤ gR p * (max 1 (1 / t) * (2 * vt0 ^ 2) * p.2) :=
          mul_le_mul_of_nonneg_left this hg
      _ = _ := by ring

/-- `Φ(t) = ∫_𝓕 G Θ_t dμ`. -/
noncomputable def Phi (t : ℝ) : ℝ := ∫ p in Freg, gR p * theta p.1 p.2 t

lemma Phi_inv {t : ℝ} (ht : 0 < t) : Phi (1 / t) = t * Phi t := by
  unfold Phi
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Freg fun p hp => ?_
  have hy0 : 0 < p.2 := by linarith [Freg_im hp]
  rw [theta_inv p.1 hy0 ht]; ring

lemma Phi_antitoneOn : AntitoneOn Phi (Ioi 0) := by
  intro s hs t ht hst
  unfold Phi
  refine setIntegral_mono_on (integrableOn_gR_theta ht) (integrableOn_gR_theta hs)
    measurableSet_Freg fun p hp => ?_
  have hy0 : 0 < p.2 := by linarith [Freg_im hp]
  exact mul_le_mul_of_nonneg_left (theta_antitone p.1 hy0 hs hst)
    (div_nonneg (G_pos _).le (by positivity))

/-- `0 ≤ Φ(t) − ‖Δ‖² ≤ C (t − 1)^{−R}` for `t > 1`. -/
lemma Phi_sub_le (R : ℕ) : ∃ C : ℝ, ∀ t : ℝ, 1 < t →
    0 ≤ Phi t - petNormSq ∧ Phi t - petNormSq ≤ C * (t - 1) ^ (-(R : ℝ)) := by
  set I₀ : ℝ := ∫ p in Freg, gR p * p.2 ^ (R + 1) with hI₀
  refine ⟨(Nat.factorial R : ℝ) * (2 / π) ^ R * (2 * vt0 ^ 2) * I₀, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hdiff : Phi t - petNormSq = ∫ p in Freg, gR p * (theta p.1 p.2 t - 1) := by
    unfold Phi
    rw [petNormSq_eq, ← integral_sub (integrableOn_gR_theta ht0)
      (by simpa using integrableOn_gR_mul_pow 0)]
    congr 1; funext p; ring
  rw [hdiff]
  have hpt : ∀ p ∈ Freg, 0 ≤ gR p * (theta p.1 p.2 t - 1) := by
    intro p hp
    have hy0 : 0 < p.2 := by linarith [Freg_im hp]
    refine mul_nonneg (div_nonneg (G_pos _).le (by positivity)) ?_
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
      have hg : 0 ≤ gR p := div_nonneg (G_pos _).le (by positivity)
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
          setIntegral_mono_on ((integrableOn_gR_theta ht0).sub
            (by simpa using integrableOn_gR_mul_pow 0) |>.congr_fun (fun p _ => by simp only [Pi.sub_apply]; ring)
            measurableSet_Freg) ((integrableOn_gR_mul_pow (R + 1)).const_mul _)
            measurableSet_Freg hbound
      _ = _ := by rw [integral_const_mul]; ring

end RamanujanTau.RankinError
