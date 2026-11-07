import RamanujanTau.ThetaLift.HeckeHalf
import RamanujanTau.DiscriminantQExpansion
import RamanujanTau.TheoremA.HalfIntegral

/-!
# The expansion of `G/η^j`

Writing `η = q^(1/24) E` with `E = ∏(1 - qⁿ)`, the function `G·E^(-j)` is one-periodic, holomorphic and
bounded at infinity, and its `q`-expansion is the formal coordinate `coordOf ℓ a`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open UpperHalfPlane ModularForm Filter Asymptotics Complex Function
open scoped MatrixGroups Manifold Real Topology

noncomputable section

local notation "𝕢" => Periodic.qParam

/-- Periodicity on `ℍ` extends through `ofComplex`. -/
lemma periodic_of {f : ℍ → ℂ} (h : ∀ t : ℍ, f ((1 : ℝ) +ᵥ t) = f t) :
    Periodic (f ∘ ofComplex) (1 : ℝ) := by
  intro z
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + (1 : ℝ)).im := by simpa using hz
    simp only [comp_apply, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz']
    rw [← h ⟨z, hz⟩]
    congr 1
    ext
    simp [add_comm]
  · have hz' : ¬ 0 < (z + (1 : ℝ)).im := by simpa using hz
    simp only [comp_apply, ofComplex_apply_of_im_nonpos (not_lt.mp hz),
      ofComplex_apply_of_im_nonpos (not_lt.mp hz')]

/-- The three properties that make the `q`-expansion well behaved. -/
structure Good (f : ℍ → ℂ) : Prop where
  per : Periodic (f ∘ ofComplex) (1 : ℝ)
  holo : MDiff f
  bdd : IsBoundedAtImInfty f

lemma Good.mul {f g : ℍ → ℂ} (hf : Good f) (hg : Good g) : Good (f * g) where
  per := by
    intro z
    have h1 := hf.per z
    have h2 := hg.per z
    simp only [comp_apply, Pi.mul_apply] at h1 h2 ⊢
    rw [h1, h2]
  holo := hf.holo.mul hg.holo
  bdd := hf.bdd.mul hg.bdd

lemma good_one : Good (1 : ℍ → ℂ) where
  per := fun _ => rfl
  holo := mdifferentiable_const
  bdd := atImInfty.const_boundedAtFilter 1

lemma Good.pow {f : ℍ → ℂ} (hf : Good f) (n : ℕ) : Good (f ^ n) := by
  induction n with
  | zero => simpa using good_one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

lemma Good.analytic {f : ℍ → ℂ} (hf : Good f) : AnalyticAt ℂ (cuspFunction (1 : ℝ) f) 0 :=
  analyticAt_cuspFunction_zero one_pos hf.per hf.holo hf.bdd

lemma qExp_mul {f g : ℍ → ℂ} (hf : Good f) (hg : Good g) :
    qExpansion (1 : ℝ) (f * g) = qExpansion (1 : ℝ) f * qExpansion (1 : ℝ) g :=
  qExpansion_mul hf.analytic hg.analytic

/-- The cusp function agrees with any holomorphic function of `q` representing `f`. -/
lemma cusp_eq_of {f : ℍ → ℂ} (hf : Good f) {E : ℂ → ℂ}
    (hE : DifferentiableOn ℂ E (Metric.ball 0 1)) (h : ∀ t : ℍ, f t = E (𝕢 (1 : ℝ) t)) {q : ℂ}
    (hq : ‖q‖ < 1) : cuspFunction (1 : ℝ) f q = E q := by
  have hne : ∀ {q : ℂ}, ‖q‖ < 1 → q ≠ 0 → cuspFunction (1 : ℝ) f q = E q := by
    intro q hq hq0
    have him : 0 < (Periodic.invQParam (1 : ℝ) q).im :=
      Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq hq0
    have hqz : 𝕢 (1 : ℝ) (Periodic.invQParam (1 : ℝ) q) = q :=
      Periodic.qParam_right_inv one_ne_zero hq0
    rw [UpperHalfPlane.cuspFunction, Periodic.cuspFunction_eq_of_nonzero _ _ hq0, comp_apply,
      ofComplex_apply_of_im_pos him, h]
    change E (𝕢 (1 : ℝ) (Periodic.invQParam (1 : ℝ) q)) = _
    rw [hqz]
  by_cases hq0 : q = 0
  · subst hq0
    have hc1 : ContinuousAt (cuspFunction (1 : ℝ) f) 0 := hf.analytic.continuousAt
    have hc2 : ContinuousAt E 0 :=
      (hE.differentiableAt (Metric.ball_mem_nhds 0 one_pos)).continuousAt
    refine tendsto_nhds_unique (hc1.tendsto.mono_left nhdsWithin_le_nhds)
      ((hc2.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))).congr' ?_)
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with x hx hb
    exact (hne (by simpa using hb) hx).symm
  · exact hne hq hq0

/-- The product `E = ∏(1 - qⁿ)` on `ℍ`. -/
def eP (t : ℍ) : ℂ := ∏' n : ℕ, (1 - eta_q n t)

/-- The analytic function of `q` underlying `E`. -/
def eQ (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1))

lemma eP_eq (t : ℍ) : eP t = eQ (𝕢 (1 : ℝ) t) := by
  unfold eP eQ
  refine tprod_congr fun n => ?_
  rw [eta_q_eq_pow]
  simp [Periodic.qParam]

lemma eQ_diff : DifferentiableOn ℂ eQ (Metric.ball 0 1) := differentiableOn_tprod_one_sub_pow

lemma qParam_vadd (t : ℍ) : 𝕢 (1 : ℝ) (((1 : ℝ) +ᵥ t : ℍ) : ℂ) = 𝕢 (1 : ℝ) t := by
  have e : (((1 : ℝ) +ᵥ t : ℍ) : ℂ) = (t : ℂ) + 1 := by simp [add_comm]
  rw [e]
  simp only [Periodic.qParam, ofReal_one, div_one]
  rw [mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma norm_eP_pow (t : ℍ) : ‖eP t‖ ^ 24 = ‖∏' n, (1 - eta_q n t) ^ 24‖ := by
  rw [← norm_pow]
  congr 1
  have hm : Multipliable fun n : ℕ => 1 - (𝕢 (1 : ℝ) t) ^ (n + 1) :=
    multipliable_one_sub_pow (by simpa using norm_qParam_lt_one 1 t)
  rw [eP_eq, eQ, ← hm.tprod_pow 24]

lemma eP_ne (t : ℍ) : eP t ≠ 0 := eta_tprod_ne_zero t.2

/-- `E` tends to a unit in norm, so `E` and `1/E` are bounded at infinity. -/
lemma eP_bounds : ∀ᶠ t in atImInfty, ‖eP t‖ ≤ 2 ∧ ‖(eP t)⁻¹‖ ≤ 2 := by
  have h := tendsto_atImInfty_tprod_one_sub_eta_q_pow.eventually
    (Metric.ball_mem_nhds 1 (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [h] with t ht
  have hsub : ‖∏' n, (1 - eta_q n t) ^ 24 - 1‖ < 1 / 2 := by rwa [Complex.dist_eq] at ht
  have h1 := norm_sub_norm_le (∏' n, (1 - eta_q n t) ^ 24) 1
  have h2 := norm_sub_norm_le 1 (∏' n, (1 - eta_q n t) ^ 24)
  rw [norm_one] at h1 h2
  rw [norm_sub_rev 1] at h2
  rw [← norm_eP_pow] at h1 h2
  have hp : 0 < ‖eP t‖ := norm_pos_iff.mpr (eP_ne t)
  have hup : ‖eP t‖ ≤ 2 := by
    by_contra hc
    have : (2 : ℝ) ^ 24 ≤ ‖eP t‖ ^ 24 := pow_le_pow_left₀ (by norm_num) (not_le.mp hc).le 24
    norm_num at this
    linarith
  have hlo : (1 : ℝ) / 2 ≤ ‖eP t‖ := by
    by_contra hc
    have : ‖eP t‖ ^ 24 ≤ (1 / 2 : ℝ) ^ 24 := pow_le_pow_left₀ hp.le (not_le.mp hc).le 24
    norm_num at this
    linarith
  refine ⟨hup, ?_⟩
  rw [norm_inv, inv_le_comm₀ hp (by norm_num)]
  linarith

lemma good_eP : Good eP where
  per := by
    apply periodic_of
    intro t
    rw [eP_eq, eP_eq, qParam_vadd]
  holo := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    have h : DifferentiableOn ℂ (fun z : ℂ => eQ (𝕢 (1 : ℝ) z)) upperHalfPlaneSet := by
      refine eQ_diff.comp (by fun_prop) fun z hz => ?_
      simpa using norm_qParam_lt_one 1 ⟨z, hz⟩
    refine h.congr fun z hz => ?_
    simp only [comp_apply, ofComplex_apply_of_im_pos hz, eP_eq]
  bdd := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eP_bounds] with t ht
    simpa using ht.1

/-- The inverse of `E`. -/
def ePi (t : ℍ) : ℂ := (eP t)⁻¹

lemma good_ePi : Good ePi where
  per := by
    intro z
    have h := good_eP.per z
    simp only [comp_apply, ePi] at h ⊢
    rw [h]
  holo := by
    have h := good_eP.holo
    rw [UpperHalfPlane.mdifferentiable_iff] at h ⊢
    refine (h.inv fun z hz => ?_).congr fun z hz => ?_
    · exact eP_ne _
    · rfl
  bdd := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eP_bounds] with t ht
    simpa [ePi] using ht.2

/-- **The `q`-expansion of `E` is the formal product.** -/
theorem qExp_eP : qExpansion (1 : ℝ) eP = PowerSeries.map (Int.castRingHom ℂ) MockTheta5.JTP.qfacInf := by
  ext n
  have hev : cuspFunction (1 : ℝ) eP =ᶠ[𝓝 0] eQ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
    exact cusp_eq_of good_eP eQ_diff eP_eq (by simpa using hq)
  let QN : ℕ → Polynomial ℤ := fun N => ∏ k ∈ Finset.range N, (1 - Polynomial.X ^ (k + 1))
  let GN : ℕ → ℂ → ℂ := fun N q => ((QN N).map (Int.castRingHom ℂ)).eval q
  have hGN : ∀ N q, GN N q = ∏ k ∈ Finset.range N, (1 - q ^ (k + 1)) := by
    intro N q
    simp [GN, QN, Polynomial.map_prod, Polynomial.eval_prod]
  have htlu : TendstoLocallyUniformlyOn GN eQ atTop (Metric.ball (0 : ℂ) 1) := by
    have hP := multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
    convert hP using 1
    funext N q
    rw [hGN]
  have hcoe : ∀ N, ((QN N : Polynomial ℤ) : PowerSeries ℤ) = MockTheta5.Bailey.qfac N := by
    intro N
    simp only [QN]
    rw [MockTheta5.Bailey.qfac, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp
  have hQ : ∀ {N : ℕ}, n + 1 ≤ N → (QN N).coeff n = PowerSeries.coeff n MockTheta5.JTP.qfacInf := by
    intro N hN
    rw [← Polynomial.coeff_coe, hcoe, MockTheta5.JTP.coeff_qfacInf hN]
  rw [qExpansion_coeff, (DiscriminantBridge.eventuallyEq_iteratedDeriv hev n).eq_of_nhds]
  have hlim := (DiscriminantBridge.tlu_iteratedDeriv Metric.isOpen_ball n htlu
    (fun N => (Polynomial.differentiable _).differentiableOn)).tendsto_at
      (Metric.mem_ball_self one_pos)
  have hconst : ∀ᶠ N in atTop, iteratedDeriv n (GN N) 0 =
      n.factorial * ((PowerSeries.coeff n MockTheta5.JTP.qfacInf : ℤ) : ℂ) := by
    filter_upwards [eventually_ge_atTop (n + 1)] with N hN
    rw [show GN N = fun q => ((QN N).map (Int.castRingHom ℂ)).eval q from rfl,
      DiscriminantBridge.iteratedDeriv_poly_zero, Polynomial.coeff_map, hQ hN, eq_intCast]
  have := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (EventuallyEq.symm hconst))
  rw [this, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_mul]
  simp

/-- The periodic part of `G/η^j`. -/
def hP {k' : ℤ} (G : CuspForm 𝒮ℒ k') (j : ℕ) : ℍ → ℂ := G * ePi ^ j

lemma good_cusp {k' : ℤ} (G : CuspForm 𝒮ℒ k') : Good G where
  per := SlashInvariantFormClass.periodic_comp_ofComplex G one_mem_strictPeriods_SL
  holo := CuspFormClass.holo G
  bdd := ModularFormClass.bdd_at_infty G

lemma good_hP {k' : ℤ} (G : CuspForm 𝒮ℒ k') (j : ℕ) : Good (hP G j) :=
  (good_cusp G).mul (good_ePi.pow j)

lemma qExp_pow {f : ℍ → ℂ} (hf : Good f) (n : ℕ) :
    qExpansion (1 : ℝ) (f ^ n) = qExpansion (1 : ℝ) f ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    ext m
    have hev : cuspFunction (1 : ℝ) (1 : ℍ → ℂ) =ᶠ[𝓝 0] fun _ => 1 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
      exact cusp_eq_of good_one (differentiableOn_const 1) (fun _ => rfl) (by simpa using hq)
    rw [qExpansion_coeff, (DiscriminantBridge.eventuallyEq_iteratedDeriv hev m).eq_of_nhds]
    cases m with
    | zero => simp
    | succ m => simp [iteratedDeriv_const, PowerSeries.coeff_one]
  | succ n ih =>
    rw [pow_succ, qExp_mul (hf.pow n) hf, ih, pow_succ]

/-- **The `q`-expansion of `G·E^(-j)` is the formal coordinate.** -/
theorem qExp_hP {k' : ℤ} (G : CuspForm 𝒮ℒ k') (j : ℕ) {a : PowerSeries ℤ}
    (ha : PowerSeries.map (Int.castRingHom ℂ) a = qExpansion (1 : ℝ) G) :
    qExpansion (1 : ℝ) (hP G j) = PowerSeries.map (Int.castRingHom ℂ)
      (a * MockTheta5.JTP.partitionGF ^ j) := by
  have hprod : hP G j * eP ^ j = G := by
    ext t
    have h0 := eP_ne t
    simp only [hP, Pi.mul_apply, Pi.pow_apply, ePi]
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ h0, one_pow, mul_one]
  have h1 := qExp_mul (good_hP G j) (good_eP.pow j)
  rw [hprod, qExp_pow good_eP, qExp_eP, ← ha, ← map_pow] at h1
  have hinv : MockTheta5.JTP.qfacInf * MockTheta5.JTP.partitionGF = 1 := by
    rw [MockTheta5.JTP.partitionGF]
    exact Ring.mul_inverse_cancel _ MockTheta5.JTP.isUnit_qfacInf
  have hinv' : MockTheta5.JTP.qfacInf ^ j * MockTheta5.JTP.partitionGF ^ j = 1 := by
    rw [← mul_pow, hinv, one_pow]
  rw [map_mul, map_pow _ _ j, h1, mul_assoc, ← map_pow, ← map_mul, hinv', map_one, mul_one]

/-- The coefficients of `G·E^(-j)`. -/
def cA {k' : ℤ} (G : CuspForm 𝒮ℒ k') (j : ℕ) (n : ℕ) : ℂ := (qExpansion (1 : ℝ) (hP G j)).coeff n

lemma hasSum_hP {k' : ℤ} (G : CuspForm 𝒮ℒ k') (j : ℕ) (t : ℍ) :
    HasSum (fun m : ℕ => cA G j m * 𝕢 (1 : ℝ) t ^ m) (hP G j t) := by
  have h := hasSum_qExpansion one_pos (good_hP G j).per (good_hP G j).holo (good_hP G j).bdd t
  simpa [cA, smul_eq_mul] using h

/-- The function `G/η^j` in terms of its periodic part. -/
lemma cusp_div_eta {k' : ℤ} (G : CuspForm 𝒮ℒ k') (j : ℕ) (t : ℍ) :
    G t / η (t : ℂ) ^ j = (𝕢 (24 : ℝ) t)⁻¹ ^ j * hP G j t := by
  have h0 := eP_ne t
  have hq : 𝕢 (24 : ℝ) (t : ℂ) ≠ 0 := Periodic.qParam_ne_zero _
  have he : η (t : ℂ) = 𝕢 (24 : ℝ) t * eP t := rfl
  have hq' := pow_ne_zero j hq
  have h0' := pow_ne_zero j h0
  simp only [hP, Pi.mul_apply, Pi.pow_apply, ePi]
  rw [he, mul_pow, inv_pow, inv_pow]
  field_simp

lemma norm_qParam24 (t : ℍ) : ‖𝕢 (24 : ℝ) (t : ℂ)‖ = Real.exp (-(2 * π * t.im / 24)) := by
  rw [Periodic.norm_qParam]
  congr 1
  simp only [UpperHalfPlane.coe_im]
  ring

/-- The Hecke bound for the periodic part. -/
lemma norm_hP_le {k' : ℤ} (G : CuspForm 𝒮ℒ k') {j : ℕ} (hj : j < 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℍ, ‖hP G j t‖ ≤ C * t.im ^ (-((k' : ℝ) / 2 - j / 4)) := by
  obtain ⟨C, hC0, hC⟩ := hecke_half G hj
  refine ⟨C, hC0, fun t => ?_⟩
  have hq : 𝕢 (24 : ℝ) (t : ℂ) ≠ 0 := Periodic.qParam_ne_zero _
  have e : hP G j t = 𝕢 (24 : ℝ) t ^ j * (G t / η (t : ℂ) ^ j) := by
    have hq' := pow_ne_zero j hq
    rw [cusp_div_eta, inv_pow]
    field_simp
  have hq1 : ‖𝕢 (24 : ℝ) (t : ℂ)‖ ≤ 1 := by
    rw [norm_qParam24]
    apply Real.exp_le_one_iff.mpr
    have := t.im_pos
    have := Real.pi_pos
    have : 0 ≤ 2 * π * t.im / 24 := by positivity
    linarith
  rw [e, norm_mul, norm_pow]
  calc _ ≤ 1 * ‖G t / η (t : ℂ) ^ j‖ := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) hq1
    _ ≤ _ := by rw [one_mul]; exact hC t

/-- **Polynomial growth of the coefficients.** -/
theorem norm_cA_le {k' : ℤ} (G : CuspForm 𝒮ℒ k') {j : ℕ} (hj : j < 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ‖cA G j n‖ ≤ C * (n : ℝ) ^ ((k' : ℝ) / 2 - j / 4) := by
  obtain ⟨C, hC0, hC⟩ := norm_hP_le G hj
  refine ⟨Real.exp (2 * π) * C, by positivity, fun n hn => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : (0 : ℝ) < 1 / n := by positivity
  have hg := good_hP G j
  have hbd : ∀ u ∈ Set.uIoc (0 : ℝ) 1, ‖1 / 𝕢 (1 : ℝ) ((u : ℂ) + ((1 / n : ℝ) : ℂ) * Complex.I) ^ n *
      hP G j ⟨(u : ℂ) + ((1 / n : ℝ) : ℂ) * Complex.I, by simpa using ht⟩‖ ≤
        Real.exp (2 * π) * C * (n : ℝ) ^ ((k' : ℝ) / 2 - j / 4) := by
    intro u _
    have h1 := hC ⟨(u : ℂ) + ((1 / n : ℝ) : ℂ) * Complex.I, by simpa using ht⟩
    have him : (⟨(u : ℂ) + ((1 / n : ℝ) : ℂ) * Complex.I, by simpa using ht⟩ : ℍ).im = 1 / n := by
      simp [UpperHalfPlane.im]
    rw [him] at h1
    have hpow : ((1 : ℝ) / n) ^ (-((k' : ℝ) / 2 - j / 4)) = (n : ℝ) ^ ((k' : ℝ) / 2 - j / 4) := by
      rw [one_div, Real.inv_rpow hnR.le, Real.rpow_neg hnR.le, inv_inv]
    rw [hpow] at h1
    have hq : ‖1 / 𝕢 (1 : ℝ) ((u : ℂ) + ((1 / n : ℝ) : ℂ) * Complex.I) ^ n‖ = Real.exp (2 * π) := by
      rw [norm_div, norm_one, norm_pow, Periodic.norm_qParam, ← Real.exp_nat_mul, one_div,
        ← Real.exp_neg]
      congr 1
      simp
      field_simp
    rw [norm_mul, hq, mul_assoc]
    gcongr
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [cA, qExpansion_coeff_eq_intervalIntegral one_pos hg.per hg.holo hg.bdd n ht]
  simpa using hI

end

end RamanujanTau.ThetaLift
