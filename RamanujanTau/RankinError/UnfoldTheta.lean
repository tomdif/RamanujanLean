/-
# The unfolding identity for the theta integral (F5)

For every `t > 0`, as an identity in `[0, ∞]` (`unfold_theta`):

    ∫_𝓕 G(z) (Θ_z(t) − 1) dx dy / y² = 2 ∫₀^∞ I(v) h_t(v) dv / v²,
    I(v) = ∫₀¹ G(x+iv) dx,   h_t(v) = ∑_{g ≥ 1} e^{−π t g²/v}.

Proof: `Θ_z(t) − 1 = ∑_γ 1_{strip}(γz) h_t(Im γz)` (`theta_coset`), `G` is invariant, so the
integrand is `1_U(z) ∑_γ Ψ(γz)` with `Ψ = 1_{strip} G h_t(Im)`; `lintegral_unfold_U` gives
`2∫_ℍ Ψ dμ`, and Tonelli in real coordinates gives the right side.
-/
import RamanujanTau.RankinError.Coset
import RamanujanTau.EisensteinReal.Mellin

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Real Filter Topology MeasureTheory Set ModularGroup
open RamanujanTau.RankinSelberg RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal

lemma hp_re' {y : ℝ} (hy : 0 < y) (x : ℝ) : (hp hy x).re = x := by
  simp [UpperHalfPlane.re, hp]

lemma measurable_hfun_uncurry : Measurable fun q : ℝ × ℝ => hfun q.1 q.2 := by
  unfold hfun
  refine Measurable.ennreal_tsum fun g => ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp ?_)
  fun_prop

lemma measurable_hfun (t : ℝ) : Measurable (hfun t) :=
  measurable_hfun_uncurry.comp (measurable_const.prodMk measurable_id)

/-- `Ψ_t(w) = 1_{strip}(w) G(w) h_t(Im w)`. -/
noncomputable def Psi (t : ℝ) (w : ℍ) : ℝ≥0∞ :=
  strip.indicator (1 : ℍ → ℝ≥0∞) w * (ENNReal.ofReal (G w) * hfun t w.im)

lemma measurable_Psi (t : ℝ) : Measurable (Psi t) := by
  unfold Psi
  exact (measurable_one.indicator measurableSet_strip).mul
    ((ENNReal.measurable_ofReal.comp continuous_G.measurable).mul
      ((measurable_hfun t).comp measurable_im_H))

/-- The pointwise identity on `𝓕`. -/
lemma ofReal_gR_theta {p : ℝ × ℝ} (hp : p ∈ Freg) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal (gR p * (theta p.1 p.2 t - 1)) =
      ENNReal.ofReal (1 / p.2 ^ 2) * ∑' γ : SL(2, ℤ), Psi t (γ • toH p) := by
  have hy := Freg_im hp
  have hy0 : 0 < p.2 := by linarith
  set z := toH p with hz
  have hzre : z.re = p.1 := toH_re hy0
  have hzim : z.im = p.2 := toH_im hy0
  set R : ℝ≥0∞ := ∑' γ : SL(2, ℤ), strip.indicator (1 : ℍ → ℝ≥0∞) (γ • z) * hfun t (γ • z).im
    with hR
  have hsum := summable_theta p.1 hy0 ht
  have hc := theta_coset z t
  rw [hzre, hzim] at hc
  have hfin : (1 : ℝ≥0∞) + R = ENNReal.ofReal (theta p.1 p.2 t) := by
    rw [← hc, theta, ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) hsum]
  have hRtop : R ≠ ⊤ := by
    intro h; rw [h] at hfin; simp at hfin
  have hθ : theta p.1 p.2 t - 1 = R.toReal := by
    have := congrArg ENNReal.toReal hfin
    rw [ENNReal.toReal_add ENNReal.one_ne_top hRtop, ENNReal.toReal_ofReal (theta_nonneg _ _ _),
      ENNReal.toReal_one] at this
    linarith
  have hG : gR p = G z * (1 / p.2 ^ 2) := by
    rw [gR, hz, toH_gpt (by linarith)]; ring
  have hPsi : ∑' γ : SL(2, ℤ), Psi t (γ • z) = ENNReal.ofReal (G z) * R := by
    rw [hR, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun γ => ?_
    unfold Psi
    rw [G_smul]; ring
  rw [hPsi, hθ, hG, mul_comm (G z), mul_assoc, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (G_pos z).le, ENNReal.ofReal_toReal hRtop]

/-- `𝓕` with the right edge removed. -/
def Freg' : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ -(1 / 2 : ℝ) ≤ p.1 ∧ p.1 < 1 / 2 ∧ 1 ≤ p.1 ^ 2 + p.2 ^ 2}

lemma measurableSet_Freg' : MeasurableSet Freg' := by
  have h3 : Measurable fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 := by fun_prop
  exact (measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_const).inter
        (measurableSet_le measurable_const h3)))

lemma Freg'_ae_eq : (Freg' : Set (ℝ × ℝ)) =ᵐ[volume] Freg := by
  have hsub : Freg' ⊆ Freg := fun p hp => ⟨hp.1, abs_le.2 ⟨hp.2.1, hp.2.2.1.le⟩, hp.2.2.2⟩
  have hline : volume ({(1 / 2 : ℝ)} ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  refine (ae_eq_set).2 ⟨?_, ?_⟩
  · rw [diff_eq_empty.2 hsub]; simp
  · refine measure_mono_null (fun p hp => ?_) hline
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hp
    refine ⟨?_, mem_univ _⟩
    simp only [Freg', mem_setOf_eq, not_and] at h4
    have := abs_le.1 h2
    simp only [mem_singleton_iff]
    by_contra hne
    exact h4 h1 this.1 (lt_of_le_of_ne this.2 hne) h3

lemma toH_mem_Uset {p : ℝ × ℝ} (hy : 0 < p.2) : toH p ∈ Uset ↔ p ∈ Freg' := by
  simp only [Uset, Freg', mem_setOf_eq, toH_re hy, Complex.normSq_apply]
  rw [coe_toH hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
    zero_add]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨hy, h1, h2, by nlinarith⟩
  · rintro ⟨-, h1, h2, h3⟩; exact ⟨h1, h2, by nlinarith⟩

lemma measurable_tsum_Psi (t : ℝ) : Measurable fun w : ℍ => ∑' γ : SL(2, ℤ), Psi t (γ • w) :=
  Measurable.ennreal_tsum fun γ => (measurable_Psi t).comp (measurePreserving_sl γ).measurable

/-- The strip side: `∫_ℍ Ψ_t dμ = ∫₀^∞ I(v) h_t(v) dv / v²`. -/
lemma lintegral_Psi (t : ℝ) :
    ∫⁻ w, Psi t w = ∫⁻ v in Ioi 0, ENNReal.ofReal (Ihor v) * hfun t v * ENNReal.ofReal (1 / v ^ 2) := by
  rw [lintegral_H _ (measurable_Psi t)]
  set F : ℝ × ℝ → ℝ≥0∞ := fun p => Psi t (toH p) * ENNReal.ofReal (1 / p.2 ^ 2) with hF
  have hFm : Measurable F :=
    ((measurable_Psi t).comp measurable_toH).mul
      (ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_snd.pow_const 2)))
  have hset : {p : ℝ × ℝ | 0 < p.2} = (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
    ext p; simp
  rw [hset, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod_symm _ hFm.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have e : ∀ x : ℝ, F (x, y) = (Ico (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (G (hp hy0 x))) x *
      (hfun t y * ENNReal.ofReal (1 / y ^ 2)) := by
    intro x
    simp only [hF, Psi, toH_hp hy0, hp_im]
    by_cases hx : x ∈ Ico (0 : ℝ) 1
    · have hs : hp hy0 x ∈ strip := by
        simp only [strip, mem_setOf_eq, hp_re']; exact ⟨hx.1, hx.2⟩
      rw [indicator_of_mem hs, indicator_of_mem hx]; simp only [Pi.one_apply, one_mul]; ring
    · have hs : hp hy0 x ∉ strip := by
        simp only [strip, mem_setOf_eq, hp_re']; exact fun h => hx ⟨h.1, h.2⟩
      rw [indicator_of_notMem hs, indicator_of_notMem hx]; simp
  simp_rw [e]
  have hmx : Measurable fun x => ENNReal.ofReal (G (hp hy0 x)) :=
    ENNReal.measurable_ofReal.comp (continuous_G_hp hy0).measurable
  rw [lintegral_mul_const _ (hmx.indicator measurableSet_Ico),
    lintegral_indicator measurableSet_Ico, setLIntegral_congr Ico_ae_eq_Ioc, ← mul_assoc]
  congr 1
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [Ihor, dif_pos hy0, intervalIntegral.integral_of_le zero_le_one]
  · exact ((continuous_G_hp hy0).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · exact Eventually.of_forall fun x => (G_pos _).le

/-- **The unfolding identity (U)**, for every `t > 0`, in `[0, ∞]`. -/
theorem unfold_theta {t : ℝ} (ht : 0 < t) :
    ∫⁻ p in Freg, ENNReal.ofReal (gR p * (theta p.1 p.2 t - 1)) =
      2 * ∫⁻ v in Ioi 0, ENNReal.ofReal (Ihor v) * hfun t v * ENNReal.ofReal (1 / v ^ 2) := by
  rw [← lintegral_Psi, ← lintegral_unfold_U _ (measurable_Psi t),
    lintegral_H _ ((measurable_one.indicator measurableSet_Uset).mul (measurable_tsum_Psi t))]
  rw [setLIntegral_congr_fun measurableSet_Freg (fun p hp => ofReal_gR_theta hp t ht),
    ← setLIntegral_congr Freg'_ae_eq, ← lintegral_indicator measurableSet_Freg',
    ← lintegral_indicator (measurableSet_lt measurable_const measurable_snd)]
  congr 1; funext p
  by_cases hy : 0 < p.2
  · rw [indicator_of_mem (show p ∈ {p : ℝ × ℝ | 0 < p.2} from hy)]
    by_cases hF : p ∈ Freg'
    · rw [indicator_of_mem hF, indicator_of_mem ((toH_mem_Uset hy).2 hF)]
      simp only [Pi.one_apply, one_mul]; ring
    · rw [indicator_of_notMem hF, indicator_of_notMem (fun h => hF ((toH_mem_Uset hy).1 h))]
      simp
  · rw [indicator_of_notMem (show p ∉ {p : ℝ × ℝ | 0 < p.2} from hy),
      indicator_of_notMem (fun h : p ∈ Freg' => hy h.1)]

end RamanujanTau.RankinError

#print axioms RamanujanTau.RankinError.unfold_theta
