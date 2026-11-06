/-
# The Mellin mean-square lower bound for the Rankin–Selberg error term

`mellin_mean_sq_lower`: for Rankin–Selberg data (`RSDataM`, any real `c`) there is `K > 0` with

    ∫₁^∞ |R(x)|² x^{−2σ−1} dx ≥ K/(σ − 3/8)          (σ = 3/8 + δ, 0 < δ ≤ 1/32),

as a lower integral (`∫⁻`, so no integrability hypothesis: if the integral diverges the
statement is trivial). Proof: if the integral converges at `σ`, then by AM–GM the Mellin integral
`∫ R x^{−s−1}` converges absolutely on `Re s > σ`; the `L²` norm of `h_{σ'}` (`σ' = 3/8 + 2δ`) is
the Mellin mean square at `σ'` (`hfun_sq`), which is `≤` the one at `σ`; apply `core_lower`.
-/
import RamanujanTau.RankinOmegaPM.Core

set_option autoImplicit false

namespace RamanujanTau.RankinOmegaPM

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open RamanujanTau.RankinOmega
open scoped Real Interval FourierTransform ENNReal

/-- `Ioi 0` versus `Ioi 1` for functions vanishing on `(−∞, 1)`. -/
lemma ioi_zero_one {F : ℝ → ℝ} (hF : ∀ t, t < 1 → F t = 0) :
    (IntegrableOn F (Ioi 0) ↔ IntegrableOn F (Ioi 1)) ∧
      ∫ x in Ioi 0, F x = ∫ x in Ioi 1, F x := by
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
  have hdiff : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioi (0 : ℝ) \ Ioi 1 → F x = 0 := by
    have h1 : ∀ᵐ x : ℝ ∂volume, x ∈ ({1} : Set ℝ)ᶜ :=
      compl_mem_ae_iff.mpr (measure_singleton 1)
    filter_upwards [h1] with x hx1 hx
    have hx1' : x ≠ 1 := hx1
    have : x ≤ 1 := not_lt.1 hx.2
    exact hF x (lt_of_le_of_ne this hx1')
  refine ⟨⟨fun h => h.mono_set hsub, fun h => ?_⟩, ?_⟩
  · have e : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
    rw [e]
    refine IntegrableOn.union ?_ h
    have h0 : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioc 0 1) := integrableOn_zero
    refine h0.congr_fun_ae ?_
    have h1 : ∀ᵐ x : ℝ ∂volume, x ∈ ({1} : Set ℝ)ᶜ :=
      compl_mem_ae_iff.mpr (measure_singleton 1)
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h1] with x hx1 hx
    have hx1' : x ≠ 1 := hx1
    exact (hF x (lt_of_le_of_ne hx.2 hx1')).symm
  · exact setIntegral_eq_of_subset_of_ae_diff_eq_zero measurableSet_Ioi.nullMeasurableSet hsub
      hdiff

section Data

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ)
variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

/-- The weighted square `|R(x)|² x^{−2σ−1}`. -/
noncomputable def fsq (a : ℕ → ℝ) (c σ : ℝ) (x : ℝ) : ℝ := ‖Rf a c x‖ ^ 2 * x ^ (-(2 * σ) - 1)

lemma fsq_nonneg (c σ : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ fsq a c σ x := by
  unfold fsq; have := Real.rpow_nonneg hx (-(2 * σ) - 1); positivity

lemma fsq_of_lt_one (c σ : ℝ) : ∀ t, t < 1 → fsq a c σ t = 0 := by
  intro t ht; simp [fsq, Rf_of_lt_one c ht]

lemma measurable_fsq (c σ : ℝ) : Measurable (fsq a c σ) := by
  unfold fsq
  exact ((measurable_Rf c).norm.pow_const 2).mul (measurable_id.pow_const _)

/-- **`L²` norm of `h_σ` = the Mellin mean square at `σ`.** -/
lemma hfun_sq (c σ : ℝ) (hI : IntegrableOn (fsq a c σ) (Ioi 1)) :
    MemLp (hfun a c σ) 2 ∧ ∫ u, ‖hfun a c σ u‖ ^ 2 = ∫ x in Ioi 1, fsq a c σ x := by
  have hI0 : IntegrableOn (fsq a c σ) (Ioi 0) := ((ioi_zero_one (fsq_of_lt_one c σ)).1).2 hI
  set ψ : ℝ → ℂ := fun t => ((‖Rf a c t‖ ^ 2 : ℝ) : ℂ) with hψ
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (-(((2 * σ : ℝ)) : ℂ) - 1) • ψ t =
      ((fsq a c σ t : ℝ) : ℂ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [hψ, smul_eq_mul]
    rw [show ((fsq a c σ t : ℝ) : ℂ) = ((‖Rf a c t‖ ^ 2 : ℝ) : ℂ) *
        ((t ^ (-(2 * σ) - 1) : ℝ) : ℂ) by simp [fsq], Complex.ofReal_cpow ht0.le]
    push_cast; ring
  have hmc : MellinConvergent ψ (-(((2 * σ : ℝ)) : ℂ)) := by
    unfold MellinConvergent
    exact (show IntegrableOn (fun t => ((fsq a c σ t : ℝ) : ℂ)) (Ioi (0 : ℝ)) volume from
      hI0.ofReal (𝕜 := ℂ)).congr_fun (fun t ht => (hpt t ht).symm) measurableSet_Ioi
  have hint := TauOmegaPM.integrable_of_mc hmc
  have hpu : ∀ u : ℝ, Real.exp ((2 * σ) * u) • ψ (Real.exp (-u)) =
      ((‖hfun a c σ u‖ ^ 2 : ℝ) : ℂ) := by
    intro u
    have hn : ‖RankinOmega.hfun a c σ u‖ = Real.exp (σ * u) * ‖Rf a c (Real.exp (-u))‖ := by
      rw [RankinOmega.hfun, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [hn, Complex.real_smul]
    simp only [hψ]
    rw [← Complex.ofReal_mul]
    congr 1
    rw [mul_pow, ← Real.exp_nat_mul]
    push_cast; ring_nf
  have hsq : Integrable (fun u => ‖hfun a c σ u‖ ^ 2) := by
    have := hint.re
    refine this.congr (Eventually.of_forall fun u => ?_)
    show RCLike.re (Real.exp ((2 * σ) * u) • ψ (Real.exp (-u))) = _
    rw [hpu, RCLike.re_to_complex, Complex.ofReal_re]
  refine ⟨(memLp_two_iff_integrable_sq_norm (measurable_hfun a c σ).aestronglyMeasurable).2 hsq, ?_⟩
  have hm := mellin_eq_fourier ψ (s := -(((2 * σ : ℝ)) : ℂ))
  have hre : (-(((2 * σ : ℝ)) : ℂ)).re = -(2 * σ) := by simp
  have him : (-(((2 * σ : ℝ)) : ℂ)).im = 0 := by simp
  rw [hre, him, zero_div, Real.fourier_real_eq_integral_exp_smul] at hm
  have h2 : ∀ v : ℝ, Complex.exp (↑(-2 * π * v * 0) * I) •
      (Real.exp (-(-(2 * σ)) * v) • ψ (Real.exp (-v))) = ((‖hfun a c σ v‖ ^ 2 : ℝ) : ℂ) := by
    intro v; rw [← hpu v]; simp
  simp_rw [h2] at hm
  rw [integral_complex_ofReal] at hm
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hpt, integral_complex_ofReal] at hm
  rw [← (ioi_zero_one (fsq_of_lt_one c σ)).2]
  exact_mod_cast hm.symm

/-- `t^{−σ'−1}|R| ≤ ½(|R|²t^{−2σ−1} + t^{−2(σ'−σ)−1})`. -/
lemma amgm_rpow {r t σ σ' : ℝ} (ht : 0 < t) :
    t ^ (-σ' - 1) * r ≤ (r ^ 2 * t ^ (-(2 * σ) - 1) + t ^ (-(2 * (σ' - σ)) - 1)) / 2 := by
  set A := r * t ^ (-σ - 1 / 2) with hA
  set B := t ^ (-(σ' - σ) - 1 / 2) with hB
  have hAB : t ^ (-σ' - 1) * r = A * B := by
    rw [hA, hB, mul_assoc, ← Real.rpow_add ht]; ring_nf
  have hA2 : A ^ 2 = r ^ 2 * t ^ (-(2 * σ) - 1) := by
    rw [hA, mul_pow, sq (t ^ _), ← Real.rpow_add ht]; ring_nf
  have hB2 : B ^ 2 = t ^ (-(2 * (σ' - σ)) - 1) := by
    rw [hB, sq, ← Real.rpow_add ht]; ring_nf
  rw [hAB, ← hA2, ← hB2]
  nlinarith [sq_nonneg (A - B)]

/-- Mean-square convergence at `σ` gives absolute Mellin convergence on `Re s > σ`. -/
lemma mc_of_fsq (c σ : ℝ) (hI : IntegrableOn (fsq a c σ) (Ioi 1)) :
    ∀ s : ℂ, σ < s.re → MellinConvergent (Rf a c) (-s) := by
  intro s hs
  have hI0 : IntegrableOn (fsq a c σ) (Ioi 0) := ((ioi_zero_one (fsq_of_lt_one c σ)).1).2 hI
  set η : ℝ := s.re - σ with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hJ : IntegrableOn (fun t : ℝ => t ^ (-(2 * η) - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hJ' : IntegrableOn ((Ici (1 : ℝ)).indicator (fun t : ℝ => t ^ (-(2 * η) - 1))) (Ioi 0) := by
    have : IntegrableOn (fun t : ℝ => t ^ (-(2 * η) - 1)) (Ici 1) :=
      (integrableOn_Ici_iff_integrableOn_Ioi (b := (1 : ℝ))
        (f := fun t : ℝ => t ^ (-(2 * η) - 1))).2 hJ
    exact (this.integrable_indicator measurableSet_Ici).integrableOn
  unfold MellinConvergent
  refine ((hI0.add hJ').div_const 2).mono' ?_ ?_
  · exact ((Complex.measurable_ofReal.pow_const _).smul (measurable_Rf c)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [Pi.add_apply, sub_re, neg_re, one_re]
    rcases lt_or_ge t 1 with h1 | h1
    · rw [Rf_of_lt_one c h1, norm_zero, mul_zero, fsq_of_lt_one c σ t h1,
        indicator_of_notMem (show t ∉ Ici (1 : ℝ) by simpa using h1)]
      norm_num
    · rw [indicator_of_mem (show t ∈ Ici (1 : ℝ) from h1)]
      have := amgm_rpow (r := ‖Rf a c t‖) (σ := σ) (σ' := s.re) ht0
      rw [show s.re - σ = η from hη.symm] at this
      simpa [fsq] using this

include d habs in
/-- **The Mellin mean-square lower bound** (abstract Rankin–Selberg data, any real `c`).
`∫₁^∞ |R(x)|² x^{−2σ−1} dx ≥ K/(σ − 3/8)` for `σ = 3/8 + δ`, `0 < δ ≤ 1/32`. -/
theorem mellin_mean_sq_lower (hm : 1 ≤ m) (hne : ∃ n, 0 < n ∧ a n ≠ 0) (c : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 32 →
      ENNReal.ofReal (K / δ) ≤
        ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (‖Rf a c x‖ ^ 2 * x ^ (-(2 * (3 / 8 + δ)) - 1)) := by
  obtain ⟨n0, hn0, hlow, ha0⟩ := exists_first hne
  obtain ⟨K2, hK2, hcore⟩ := core_lower d habs hm hn0 hlow ha0 c
  refine ⟨K2 / 16, by positivity, fun δ hδ0 hδ1 => ?_⟩
  set σ : ℝ := 3 / 8 + δ with hσ
  show ENNReal.ofReal (K2 / 16 / δ) ≤ ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (fsq a c σ x)
  by_cases hI : IntegrableOn (fsq a c σ) (Ioi 1)
  · rw [← ofReal_integral_eq_lintegral_ofReal hI
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx =>
        fsq_nonneg c σ (le_of_lt (lt_trans zero_lt_one hx))))]
    refine ENNReal.ofReal_le_ofReal ?_
    set σ' : ℝ := 3 / 8 + 2 * δ with hσ'
    have hle : ∀ x ∈ Ioi (1 : ℝ), fsq a c σ' x ≤ fsq a c σ x := by
      intro x hx
      have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
      unfold fsq
      have : x ^ (-(2 * σ') - 1) ≤ x ^ (-(2 * σ) - 1) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by rw [hσ, hσ']; linarith)
      have := sq_nonneg ‖Rf a c x‖
      gcongr
    have hI' : IntegrableOn (fsq a c σ') (Ioi 1) := by
      refine hI.mono' (measurable_fsq c σ').aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun x hx => ?_
      rw [Real.norm_of_nonneg (fsq_nonneg c σ' (le_of_lt (lt_trans zero_lt_one hx)))]
      exact hle x hx
    obtain ⟨hmem, heq⟩ := hfun_sq c σ' hI'
    have hconv : ∀ s : ℂ, 3 / 8 + (2 * δ) / 2 < s.re → MellinConvergent (Rf a c) (-s) := by
      intro s hs
      exact mc_of_fsq c σ hI s (by rw [hσ]; linarith)
    have hc := hcore (2 * δ) (by positivity) (by linarith) hconv (by rw [← hσ']; exact hmem)
    rw [← hσ', heq] at hc
    have hmono : ∫ x in Ioi 1, fsq a c σ' x ≤ ∫ x in Ioi 1, fsq a c σ x :=
      setIntegral_mono_on hI' hI measurableSet_Ioi hle
    have e : K2 / (8 * (2 * δ)) = K2 / 16 / δ := by field_simp; ring
    rw [e] at hc
    linarith
  · have htop : ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (fsq a c σ x) = ⊤ := by
      by_contra hne
      apply hI
      refine ⟨(measurable_fsq c σ).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal ((ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun x hx => fsq_nonneg c σ (le_of_lt (lt_trans zero_lt_one hx))))]
      exact lt_top_iff_ne_top.2 hne
    rw [htop]; exact le_top

end Data

end RamanujanTau.RankinOmegaPM
