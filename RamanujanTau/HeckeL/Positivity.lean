/-
# Positivity of `Λ` on the real axis; the real zeros of `L(Δ,s)`

`Δ(it)` is real (its q-expansion has real coefficients), nonzero (`discriminant_ne_zero`) and
eventually positive (`Δ(it)/q → 1`), hence positive for all `t > 0` by the intermediate value
theorem.  So `Λ(σ) = ∫₀^∞ Δ(it) t^{σ−1} dt > 0` for every real `σ`, and

    L(Δ, σ) = 0  ⟺  σ ∈ {0, −1, −2, …}        (σ ∈ ℝ).

In particular `L(Δ, 6) > 0` (the central value does not vanish).
-/
import RamanujanTau.HeckeL.Main

set_option autoImplicit false

namespace RamanujanTau.HeckeL

open Complex ModularForm Filter Asymptotics Set MeasureTheory LSeries Topology
open UpperHalfPlane hiding I
open scoped MatrixGroups Real

local notation "𝕢" => Function.Periodic.qParam

/-- `u(t) = Re Δ(it)`. -/
noncomputable def heckeU (t : ℝ) : ℝ := (heckeF t).re

lemma heckeF_im {t : ℝ} (ht : 0 < t) : (heckeF t).im = 0 := by
  have h := Complex.imCLM.hasSum (hasSum_heckeF ht)
  have h0 : (fun n : ℕ => Complex.imCLM (tauC n * (Real.exp (-(2 * π * n) * t) : ℂ))) = 0 := by
    funext n
    simp only [tauC, Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_im, Complex.intCast_im,
      mul_zero, zero_mul, add_zero, Pi.zero_apply]
  rw [h0] at h
  exact (h.unique hasSum_zero)

lemma heckeF_real {t : ℝ} (ht : 0 < t) : heckeF t = (heckeU t : ℂ) :=
  Complex.ext (by simp [heckeU]) (by simp [heckeF_im ht])

lemma heckeU_ne_zero {t : ℝ} (ht : 0 < t) : heckeU t ≠ 0 := by
  intro h
  have := heckeF_real ht
  rw [h, Complex.ofReal_zero, heckeF_eq ht] at this
  exact discriminant_ne_zero _ this

lemma tendsto_ofComplex_tI :
    Tendsto (fun t : ℝ => ofComplex ((t : ℂ) * I)) atTop atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  refine tendsto_id.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  simp only [Function.comp_apply, id]
  rw [ofComplex_apply_of_im_pos (by simpa using ht)]
  show t = ((t : ℂ) * I).im
  simp

lemma heckeU_eventually_pos : ∀ᶠ t in atTop, 0 < heckeU t := by
  have hP := tendsto_atImInfty_tprod_one_sub_eta_q_pow.comp tendsto_ofComplex_tI
  have hre := (Complex.continuous_re.tendsto 1).comp hP
  simp only [Complex.one_re] at hre
  filter_upwards [hre.eventually (lt_mem_nhds (show (0:ℝ) < 1 by norm_num)),
    eventually_gt_atTop (0:ℝ)] with t h1 ht
  simp only [Function.comp_apply] at h1
  have hz : ofComplex ((t : ℂ) * I) = pt ht := by
    rw [ofComplex_apply_of_im_pos (by simpa using ht)]; rfl
  rw [hz] at h1
  have hq : 𝕢 1 ((pt ht : ℍ) : ℂ) = ((Real.exp (-(2 * π) * t) : ℝ) : ℂ) := by
    unfold Function.Periodic.qParam
    rw [Complex.ofReal_exp, pt_coe]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]; ring
  have hΔ := discriminant_eq_q_prod (pt ht)
  rw [hq] at hΔ
  rw [heckeU, heckeF_eq ht]
  show 0 < (discriminant (pt ht)).re
  rw [hΔ, Complex.re_ofReal_mul]
  exact mul_pos (Real.exp_pos _) h1

/-- **`Δ(it) > 0`** for every `t > 0`. -/
theorem heckeU_pos {t : ℝ} (ht : 0 < t) : 0 < heckeU t := by
  by_contra hneg
  push Not at hneg
  have hlt : heckeU t < 0 := lt_of_le_of_ne hneg (heckeU_ne_zero ht)
  obtain ⟨t₁, hpos, ht₁⟩ := (heckeU_eventually_pos.and (eventually_ge_atTop t)).exists
  have hcont : ContinuousOn heckeU (Icc t t₁) :=
    (Complex.continuous_re.comp_continuousOn continuousOn_heckeF).mono
      fun x hx => lt_of_lt_of_le ht hx.1
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc ht₁ hcont ⟨hlt.le, hpos.le⟩
  exact heckeU_ne_zero (lt_of_lt_of_le ht hc.1) hc0

/-- On the real axis `Λ(σ) = ∫₀^∞ u(t) t^{σ−1} dt`. -/
lemma heckeLambda_ofReal (σ : ℝ) :
    heckeLambda σ = ((∫ t in Ioi (0:ℝ), t ^ (σ - 1) * heckeU t : ℝ) : ℂ) := by
  have hI := integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0:ℝ)))
    (f := fun t => t ^ (σ - 1) * heckeU t)
  rw [heckeLambda_eq_mellin, mellin]
  refine Eq.trans ?_ hI
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp only [smul_eq_mul]
  rw [heckeF_real ht, show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow ht.le, ← Complex.ofReal_mul]
  rfl

/-- **`Λ(σ) > 0` for every real `σ`.** -/
theorem heckeLambda_pos (σ : ℝ) :
    (heckeLambda σ).im = 0 ∧ 0 < (heckeLambda σ).re := by
  rw [heckeLambda_ofReal]
  refine ⟨by simp, ?_⟩
  rw [Complex.ofReal_re]
  have hconv : MellinConvergent heckeF (σ : ℂ) := (heckePair.hasMellin σ).1
  have hint : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * heckeU t) (Ioi 0) := by
    have h := hconv.re
    refine h.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    show Complex.re _ = _
    rw [smul_eq_mul, heckeF_real ht, show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow ht.le, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
  · have : Ioi (0:ℝ) ⊆ Function.support (fun t : ℝ => t ^ (σ - 1) * heckeU t) ∩ Ioi 0 :=
      fun t (ht : 0 < t) => ⟨(mul_pos (Real.rpow_pos_of_pos ht _) (heckeU_pos ht)).ne', ht⟩
    refine lt_of_lt_of_le ?_ (measure_mono this)
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    exact (mul_pos (Real.rpow_pos_of_pos ht _) (heckeU_pos ht)).le

/-- `Λ(−n) = Λ(12 + n) > 0`: the trivial zeros of `L(Δ,s)` are not zeros of `Λ`. -/
theorem heckeLambda_neg_nat_ne_zero (n : ℕ) : heckeLambda (-n) ≠ 0 := by
  intro h
  have := (heckeLambda_pos (-(n:ℝ))).2
  push_cast at this
  rw [h] at this
  simp at this

/-- **The real zeros of `L(Δ,s)` are exactly `0, −1, −2, …`.** -/
theorem tauL_real_eq_zero_iff (σ : ℝ) : tauL σ = 0 ↔ ∃ n : ℕ, σ = -n := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hG : Gamma (σ : ℂ) ≠ 0 := Complex.Gamma_ne_zero fun m hm => hne m (by exact_mod_cast hm)
    have hΛ : heckeLambda σ ≠ 0 := fun h0 => by
      have := (heckeLambda_pos σ).2; rw [h0] at this; simp at this
    rw [tauL] at h
    exact mul_ne_zero (mul_ne_zero (two_pi_cpow_ne_zero _) (inv_ne_zero hG)) hΛ h
  · rintro ⟨n, rfl⟩
    push_cast
    exact tauLSeries_zeros_trivial n

/-- **`L(Δ,σ) > 0` for real `σ > 0`**; in particular the central value `L(Δ,6)` is positive. -/
theorem tauL_pos {σ : ℝ} (hσ : 0 < σ) : (tauL σ).im = 0 ∧ 0 < (tauL σ).re := by
  have hG : Gamma (σ : ℂ) = ((Real.Gamma σ : ℝ) : ℂ) := (Complex.Gamma_ofReal σ)
  have h2 : (2 * π : ℂ) ^ (σ : ℂ) = (((2 * π) ^ σ : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl
  obtain ⟨him, hre⟩ := heckeLambda_pos σ
  have hΛ : heckeLambda σ = ((heckeLambda σ).re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [tauL, hG, h2, hΛ, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  refine ⟨by simp, ?_⟩
  rw [Complex.ofReal_re]
  have := Real.Gamma_pos_of_pos hσ
  positivity

theorem tauLSeries_center_pos : (tauL 6).im = 0 ∧ 0 < (tauL 6).re := by
  exact_mod_cast tauL_pos (show (0:ℝ) < 6 by norm_num)

/-- `L(Δ, σ) = ∑ τ(n) n^{−σ} > 0` for real `σ > 7`, in particular `≠ 0`. -/
theorem LSeries_tau_real_pos {σ : ℝ} (hσ : 7 < σ) :
    (LSeries tauC σ).im = 0 ∧ 0 < (LSeries tauC σ).re := by
  rw [← tauL_eq_LSeries (by simpa using hσ)]
  exact tauL_pos (by linarith)

end RamanujanTau.HeckeL
