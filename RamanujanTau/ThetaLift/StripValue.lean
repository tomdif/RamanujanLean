import RamanujanTau.ThetaLift.StripG

/-!
# The integral of `H_g` over the strip

Fourier in `u` selects the coefficient `cX x`, and the sum over `x` is exchanged with the integral in `v`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex Polynomial MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real ComplexConjugate MatrixGroups

noncomputable section

variable {k' : ℤ} (G : CuspForm 𝒮ℒ k') (j : ℕ) {N : ℕ} (hN : 0 < N) (lam : ℕ) (ξ y : ℝ)

/-- The part of a term of the seed which does not depend on `u`. -/
def sZ (ξ y : ℝ) (g : ℤ) (v : ℝ) (x : ℤ) : ℂ :=
  ((Real.exp (-(6 * π * (g : ℝ) ^ 2 * y ^ 2 / v)) * Real.exp (-(2 * π * ((x : ℝ) ^ 2 / 24) * v)) : ℝ) : ℂ) *
    (chiZ x : ℂ) * cexp (2 * π * I * (x * (g * ξ)))

lemma sv_split (ξ y : ℝ) (g : ℤ) (u : ℝ) {v : ℝ} (hv : 0 < v) (x : ℤ) :
    sv ξ y g ((zUV u hv : ℍ) : ℂ) x = sZ ξ y g v x * cexp (2 * π * I * ((x : ℂ) ^ 2 / 24) * u) := by
  have him : ((zUV u hv : ℍ) : ℂ).im = v := by simp [zUV]
  have hcoe : ((zUV u hv : ℍ) : ℂ) = (u : ℂ) + v * I := rfl
  have e1 : cexp (-(6 * π * g ^ 2 * y ^ 2 / (v : ℂ))) =
      ((Real.exp (-(6 * π * (g : ℝ) ^ 2 * y ^ 2 / v)) : ℝ) : ℂ) := by
    rw [ofReal_exp]
    congr 1
    push_cast
    ring
  have e2 : cexp (2 * π * I * (x ^ 2 * ((u : ℂ) + v * I) / 24 + x * (g * ξ))) =
      ((Real.exp (-(2 * π * ((x : ℝ) ^ 2 / 24) * v)) : ℝ) : ℂ) * cexp (2 * π * I * (x * (g * ξ))) *
        cexp (2 * π * I * ((x : ℂ) ^ 2 / 24) * u) := by
    rw [ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (2 * (π : ℂ) * (x ^ 2 / 24) * v) * Complex.I_sq
  unfold sv sZ
  rw [him, hcoe, e1, e2]
  push_cast
  ring

lemma norm_sZ (ξ y : ℝ) (g : ℤ) (v : ℝ) (x : ℤ) :
    ‖sZ ξ y g v x‖ = Real.exp (-(6 * π * (g : ℝ) ^ 2 * y ^ 2 / v)) *
      Real.exp (-(2 * π * ((x : ℝ) ^ 2 / 24) * v)) * ‖(chiZ x : ℂ)‖ := by
  unfold sZ
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have e : 2 * (π : ℂ) * I * (x * (g * ξ)) = ((2 * π * (x * (g * ξ)) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [e, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The value of the integral of a single `x`-term against `conj 𝔽`. -/
lemma integral_xTerm {hj : j < 24} (hNj : (24 : ℤ) ∣ (N : ℤ) * j + 1) (g : ℤ) {v : ℝ} (hv : 0 < v)
    (x : ℤ) (r : ℂ) :
    ∫ u in (0 : ℝ)..1, conj (fF G j hN (zUV u hv)) *
        (sZ ξ y g v x * cexp (2 * π * I * ((x : ℂ) ^ 2 / 24) * u) * r) =
      sZ ξ y g v x * r * (cX G j N x * ((Real.exp (-(2 * π * ((x : ℝ) ^ 2 / 24) * v)) : ℝ) : ℂ)) := by
  by_cases hχ : chiZ x = 0
  · simp [sZ, hχ]
  have hx := sq_sub_one_of_chi x hχ
  have h := fourier_u G j (hj := hj) hN hv hx hNj
  have e : (fun u : ℝ => conj (fF G j hN (zUV u hv)) *
      (sZ ξ y g v x * cexp (2 * π * I * ((x : ℂ) ^ 2 / 24) * u) * r)) = fun u : ℝ =>
      (sZ ξ y g v x * r) * (conj (fF G j hN (zUV u hv)) * cexp (2 * π * I * ((x : ℂ) ^ 2 / 24) * u)) := by
    funext u
    ring
  rw [e, intervalIntegral.integral_const_mul, h]

/-- The bound on the Fourier coefficient by the supremum of `𝔽`. -/
lemma norm_cX_le {hj : j < 24} (hNj : (24 : ℤ) ∣ (N : ℤ) * j + 1) {M v : ℝ} (hv : 0 < v)
    (hM : ∀ z : ℍ, z.im = v → ‖fF G j hN z‖ ≤ M) {x : ℤ} (hx : chiZ x ≠ 0) :
    ‖cX G j N x‖ * Real.exp (-(2 * π * ((x : ℝ) ^ 2 / 24) * v)) ≤ M := by
  have h := fourier_u G j (hj := hj) hN hv (sq_sub_one_of_chi x hx) hNj
  have hb : ∀ u ∈ Set.uIoc (0 : ℝ) 1, ‖conj (fF G j hN (zUV u hv)) *
      cexp (2 * π * I * ((x : ℂ) ^ 2 / 24) * u)‖ ≤ M := by
    intro u _
    have e : 2 * (π : ℂ) * I * ((x : ℂ) ^ 2 / 24) * u = ((2 * π * ((x : ℝ) ^ 2 / 24) * u : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [norm_mul, Complex.norm_conj, e, Complex.norm_exp_ofReal_mul_I, mul_one]
    refine hM _ ?_
    change ((u : ℂ) + v * I).im = v
    simp
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hI
  simpa using hI

/-- **The integral over a horizontal line.** -/
theorem hasSum_line {hj : j < 24} (hNj : (24 : ℤ) ∣ (N : ℤ) * j + 1) (g : ℤ) {v : ℝ} (hv : 0 < v) :
    HasSum (fun x : ℤ => sZ ξ y g v x * ((rR lam g y v x : ℝ) : ℂ) *
        (cX G j N x * ((Real.exp (-(2 * π * ((x : ℝ) ^ 2 / 24) * v)) : ℝ) : ℂ)))
      (∫ u in (0 : ℝ)..1, conj (fF G j hN (zUV u hv)) * hFz lam ξ y g (zUV u hv)) := by
  obtain ⟨K, CF, hK0, hCF0, hF, hB⟩ := strip_bound G j hN lam ξ y (hj := hj)
  have hzim : ∀ u : ℝ, ((zUV u hv : ℍ) : ℂ).im = v := fun u => by simp [zUV]
  have hzim' : ∀ u : ℝ, (zUV u hv).im = v := hzim
  have hcont : Continuous fun u : ℝ => conj (fF G j hN (zUV u hv)) := by
    refine Complex.continuous_conj.comp ((continuous_fF G j hN).comp ?_)
    refine isEmbedding_coe.continuous_iff.mpr ?_
    change Continuous fun u : ℝ => (u : ℂ) + v * I
    fun_prop
  let f : ℤ → C(ℝ, ℂ) := fun x =>
    { toFun := fun u => conj (fF G j hN (zUV u hv)) *
        (sZ ξ y g v x * cexp (2 * π * I * ((x : ℂ) ^ 2 / 24) * u) * ((rR lam g y v x : ℝ) : ℂ))
      continuous_toFun := by
        refine hcont.mul ?_
        fun_prop }
  have hS0 : Summable fun x : ℤ => ‖sZ ξ y g v x * ((rR lam g y v x : ℝ) : ℂ)‖ := by
    have h := (hB g (z := ((zUV 0 hv : ℍ) : ℂ)) (zUV 0 hv).2).1
    rw [hzim] at h
    refine h.congr fun x => ?_
    rw [sv_split]
    simp
  have hM : 0 ≤ mF CF k' j v := by
    have := hF (zUV 0 hv)
    rw [hzim'] at this
    exact (norm_nonneg _).trans this
  have hnorm : Summable fun x : ℤ => ‖(f x).restrict
      (⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_) (hS0.mul_left (mF CF k' j v))
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun u => ?_
    rw [ContinuousMap.restrict_apply]
    change ‖conj (fF G j hN (zUV _ hv)) * (sZ ξ y g v x * cexp (2 * π * I * ((x : ℂ) ^ 2 / 24) * _) *
      ((rR lam g y v x : ℝ) : ℂ))‖ ≤ _
    have e : ∀ t : ℝ, ‖cexp (2 * π * I * ((x : ℂ) ^ 2 / 24) * t)‖ = 1 := by
      intro t
      have e' : 2 * (π : ℂ) * I * ((x : ℂ) ^ 2 / 24) * t = ((2 * π * ((x : ℝ) ^ 2 / 24) * t : ℝ) : ℂ) * I := by
        push_cast
        ring
      rw [e', Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, e, mul_one, Complex.norm_conj]
    have h1 := hF (zUV (u : ℝ) hv)
    rw [hzim'] at h1
    gcongr
  have hsum := intervalIntegral.hasSum_intervalIntegral_of_summable_norm hnorm
  have hpt : ∀ u : ℝ, ∑' x : ℤ, (f x) u =
      conj (fF G j hN (zUV u hv)) * hFz lam ξ y g (zUV u hv) := by
    intro u
    change ∑' x : ℤ, conj (fF G j hN (zUV u hv)) *
      (sZ ξ y g v x * cexp (2 * π * I * ((x : ℂ) ^ 2 / 24) * u) * ((rR lam g y v x : ℝ) : ℂ)) = _
    rw [tsum_mul_left, hFz_eq]
    congr 1
    refine tsum_congr fun x => ?_
    rw [sv_split, hzim]
  rw [funext hpt] at hsum
  convert hsum using 1
  funext x
  exact (integral_xTerm G j hN ξ y (hj := hj) hNj g hv x _).symm

/-- The real integrand in `v` attached to `x` and `g`. -/
def vT (lam : ℕ) (g : ℤ) (y v : ℝ) (x : ℤ) : ℝ :=
  v ^ ((lam : ℝ) - 3 / 2) * Real.exp (-(6 * π * (g : ℝ) ^ 2 * y ^ 2 / v) - π * (x : ℝ) ^ 2 * v / 6) *
    rR lam g y v x

/-- The constant attached to `x` and `g`. -/
def cf (ξ : ℝ) (g : ℤ) (x : ℤ) : ℂ :=
  (chiZ x : ℂ) * (cX G j N x * cexp (2 * π * I * (x * (g * ξ))))

/-- The integrand after the integral in `u`. -/
lemma line_term (g : ℤ) {v : ℝ} (hv : 0 < v) (x : ℤ) :
    ((v ^ 2)⁻¹ * v ^ ((lam : ℝ) + 1 / 2) : ℝ) * (sZ ξ y g v x * ((rR lam g y v x : ℝ) : ℂ) *
        (cX G j N x * ((Real.exp (-(2 * π * ((x : ℝ) ^ 2 / 24) * v)) : ℝ) : ℂ))) =
      cf G j ξ g x (N := N) * ((vT lam g y v x : ℝ) : ℂ) := by
  have hpw : (v ^ 2)⁻¹ * v ^ ((lam : ℝ) + 1 / 2) = v ^ ((lam : ℝ) - 3 / 2) := by
    rw [← Real.rpow_two, ← Real.rpow_neg hv.le, ← Real.rpow_add hv]
    congr 1
    ring
  have hexp : Real.exp (-(6 * π * (g : ℝ) ^ 2 * y ^ 2 / v) - π * (x : ℝ) ^ 2 * v / 6) =
      Real.exp (-(6 * π * (g : ℝ) ^ 2 * y ^ 2 / v)) * Real.exp (-(2 * π * ((x : ℝ) ^ 2 / 24) * v)) *
        Real.exp (-(2 * π * ((x : ℝ) ^ 2 / 24) * v)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  unfold cf vT sZ
  rw [hpw, hexp]
  push_cast
  ring

include hN in
/-- The bound in `v` for the sum over `x`. -/
lemma line_bound {hj : j < 24} (hNj : (24 : ℤ) ∣ (N : ℤ) * j + 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : ℤ) {v : ℝ} (_ : 0 < v),
      (Summable fun x : ℤ => ‖cf G j ξ g x (N := N) * ((vT lam g y v x : ℝ) : ℂ)‖) ∧
      ∑' x : ℤ, ‖cf G j ξ g x (N := N) * ((vT lam g y v x : ℝ) : ℂ)‖ ≤
        K * bF k' j lam v * Real.exp (-(9 * π * y ^ 2 / 2 * (g : ℝ) ^ 2 / v)) := by
  obtain ⟨K, CF, hK0, hCF0, hF, hB⟩ := strip_bound G j hN lam ξ y (hj := hj)
  refine ⟨K, hK0, fun g v hv => ?_⟩
  have hzim : ((zUV 0 hv : ℍ) : ℂ).im = v := by simp [zUV]
  obtain ⟨hS, h1⟩ := hB g (z := ((zUV 0 hv : ℍ) : ℂ)) (zUV 0 hv).2
  rw [hzim] at hS h1
  have hMF : ∀ z : ℍ, z.im = v → ‖fF G j hN z‖ ≤ mF CF k' j v := fun z hz => by
    have := hF z
    rwa [hz] at this
  have hpw : (v ^ 2)⁻¹ * v ^ ((lam : ℝ) + 1 / 2) = v ^ ((lam : ℝ) - 3 / 2) := by
    rw [← Real.rpow_two, ← Real.rpow_neg hv.le, ← Real.rpow_add hv]
    congr 1
    ring
  have hM : 0 ≤ mF CF k' j v := (norm_nonneg _).trans (hMF (zUV 0 hv) hzim)
  have hle : ∀ x : ℤ, ‖cf G j ξ g x (N := N) * ((vT lam g y v x : ℝ) : ℂ)‖ ≤
      (v ^ 2)⁻¹ * (v ^ ((lam : ℝ) + 1 / 2) * (mF CF k' j v *
        ‖sv ξ y g ((zUV 0 hv : ℍ) : ℂ) x * ((rR lam g y v x : ℝ) : ℂ)‖)) := by
    intro x
    by_cases hχ : chiZ x = 0
    · have h0 : cf G j ξ g x (N := N) = 0 := by simp [cf, hχ]
      rw [h0, zero_mul, norm_zero]
      positivity
    have hc := norm_cX_le G j hN (hj := hj) hNj hv hMF hχ
    have hsv : ‖sv ξ y g ((zUV 0 hv : ℍ) : ℂ) x‖ = ‖sZ ξ y g v x‖ := by
      rw [sv_split]
      simp
    have e : 2 * (π : ℂ) * I * (x * (g * ξ)) = ((2 * π * (x * (g * ξ)) : ℝ) : ℂ) * I := by
      push_cast
      ring
    have hL : ‖cf G j ξ g x (N := N) * ((vT lam g y v x : ℝ) : ℂ)‖ =
        (v ^ 2)⁻¹ * v ^ ((lam : ℝ) + 1 / 2) * ((‖cX G j N x‖ *
          Real.exp (-(2 * π * ((x : ℝ) ^ 2 / 24) * v))) * (‖sZ ξ y g v x‖ * |rR lam g y v x|)) := by
      rw [hpw, norm_sZ]
      unfold cf vT
      rw [norm_mul, norm_mul, norm_mul, e, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
        Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (by positivity : 0 ≤ v ^ ((lam : ℝ) - 3 / 2))]
      have hexp : Real.exp (-(6 * π * (g : ℝ) ^ 2 * y ^ 2 / v) - π * (x : ℝ) ^ 2 * v / 6) =
          Real.exp (-(6 * π * (g : ℝ) ^ 2 * y ^ 2 / v)) * Real.exp (-(2 * π * ((x : ℝ) ^ 2 / 24) * v)) *
            Real.exp (-(2 * π * ((x : ℝ) ^ 2 / 24) * v)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
    rw [hL, norm_mul, hsv, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    gcongr
  have hS2 := (hS.mul_left (mF CF k' j v)).mul_left (v ^ ((lam : ℝ) + 1 / 2)) |>.mul_left (v ^ 2)⁻¹
  have hS3 := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hS2
  refine ⟨hS3, (hS3.tsum_le_tsum hle hS2).trans (le_trans (le_of_eq ?_) h1)⟩
  rw [tsum_mul_left, tsum_mul_left, tsum_mul_left]

lemma measurable_vT (lam : ℕ) (g : ℤ) (y : ℝ) (x : ℤ) : Measurable fun v : ℝ => vT lam g y v x := by
  have := measurable_ev (hermite lam)
  unfold vT rR
  fun_prop

lemma pt_eq (u : ℝ) {v : ℝ} (hv : 0 < v) : pt (u, v) = zUV u hv := by
  have hc : 0 < ((u : ℂ) + v * I).im := by simpa using hv
  apply UpperHalfPlane.ext
  change (ofComplex ((u : ℂ) + v * I) : ℂ) = (u : ℂ) + v * I
  rw [ofComplex_apply_of_im_pos hc]

/-- **The integral of `H_g` over the strip.** -/
theorem strip_value {hj : j < 24} (hNj : (24 : ℤ) ∣ (N : ℤ) * j + 1) (hy : 0 < y) {g : ℤ} (hg : g ≠ 0) :
    HasSum (fun x : ℤ => cf G j ξ g x (N := N) * ((∫ v in Ioi (0 : ℝ), vT lam g y v x : ℝ) : ℂ))
      (∫ z in stripSet, Hg G j hN lam ξ y g z) := by
  have hπ := Real.pi_pos
  obtain ⟨K, hK0, hK⟩ := line_bound G j hN lam ξ y (hj := hj) hNj
  have hgsq : (0 : ℝ) < (g : ℝ) ^ 2 := by
    have : (g : ℝ) ≠ 0 := by exact_mod_cast hg
    positivity
  have hβ : 0 < 9 * π * y ^ 2 / 2 * (g : ℝ) ^ 2 := by positivity
  have hB : IntegrableOn (fun v : ℝ => K * bF k' j lam v *
      Real.exp (-(9 * π * y ^ 2 / 2 * (g : ℝ) ^ 2 / v))) (Ioi 0) := by
    have h : IntegrableOn (fun v : ℝ => K * (v ^ (0 : ℝ) * bF k' j lam v *
        Real.exp (-(9 * π * y ^ 2 / 2 * (g : ℝ) ^ 2 / v)))) (Ioi 0) :=
      (integrableOn_bF k' j lam 0 hβ).const_mul K
    refine h.congr_fun (fun v _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_zero, one_mul]
    ring
  have hval : ∀ v ∈ Ioi (0 : ℝ), ∫ u in Ico (0 : ℝ) 1, tr' (Hg G j hN lam ξ y g) (u, v) =
      ∑' x : ℤ, cf G j ξ g x (N := N) * ((vT lam g y v x : ℝ) : ℂ) := by
    intro v hv
    have hv' : 0 < v := hv
    have hline := hasSum_line G j hN lam ξ y (hj := hj) hNj g hv'
    have hterm : ∀ u : ℝ, tr' (Hg G j hN lam ξ y g) (u, v) =
        ((v ^ 2)⁻¹ * v ^ ((lam : ℝ) + 1 / 2) : ℝ) *
          (conj (fF G j hN (zUV u hv')) * hFz lam ξ y g (zUV u hv')) := by
      intro u
      unfold tr'
      rw [pt_eq u hv']
      simp only
      unfold Hg
      have him : (zUV u hv').im = v := by
        change ((u : ℂ) + v * I).im = v
        simp
      rw [him, Complex.real_smul]
      push_cast
      ring
    simp only [hterm]
    rw [integral_const_mul, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      ← hline.tsum_eq, ← tsum_mul_left]
    exact tsum_congr fun x => line_term G j lam ξ y g hv' x
  rw [integral_strip, integral_rect (integrableOn_tr_Hg G j hN lam ξ y (hj := hj) hy hg),
    setIntegral_congr_fun measurableSet_Ioi hval]
  have hm : ∀ x : ℤ, AEStronglyMeasurable
      (fun v : ℝ => cf G j ξ g x (N := N) * ((vT lam g y v x : ℝ) : ℂ)) (volume.restrict (Ioi 0)) := by
    intro x
    exact ((Complex.measurable_ofReal.comp (measurable_vT lam g y x)).const_mul _).aestronglyMeasurable
  have hs : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      Summable (fun x : ℤ => ‖cf G j ξ g x (N := N) * ((vT lam g y v x : ℝ) : ℂ)‖) ∧
        ∑' x : ℤ, ‖cf G j ξ g x (N := N) * ((vT lam g y v x : ℝ) : ℂ)‖ ≤
          K * bF k' j lam v * Real.exp (-(9 * π * y ^ 2 / 2 * (g : ℝ) ^ 2 / v)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact hK g hv
  obtain ⟨hint, hsum⟩ := tsum_integral_of_bound hB hm hs
  convert hsum using 2 with x
  rw [integral_const_mul, integral_complex_ofReal]

end

end RamanujanTau.ThetaLift
