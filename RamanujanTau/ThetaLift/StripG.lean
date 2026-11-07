import RamanujanTau.ThetaLift.StripBounds

/-!
# The integrand on the strip

For each `g`, the function `H_g(z) = v^(λ+1/2) conj(𝔽(z)) ∂^λ_σ 𝔾_g(z;0)` is dominated on the strip, and so
is the sum over `g ≠ 0`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex Polynomial MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real ComplexConjugate MatrixGroups

noncomputable section

variable {k' : ℤ} (G : CuspForm 𝒮ℒ k') (j : ℕ) {N : ℕ} (hN : 0 < N) (lam : ℕ) (ξ y : ℝ)

/-- The Hermite theta series on `ℍ`. -/
def hFz (g : ℤ) (z : ℍ) : ℂ := iteratedDeriv lam (seed ξ y g (z : ℂ)) 0

lemma hFz_eq (g : ℤ) (z : ℍ) :
    hFz lam ξ y g z = ∑' x : ℤ, sv ξ y g (z : ℂ) x * ((rR lam g y (z : ℂ).im x : ℝ) : ℂ) :=
  (hasSum_hF ξ y lam g z.2).tsum_eq.symm

lemma measurable_ev (P : ℤ[X]) : Measurable (ev P) :=
  (continuous_iff_continuousAt.mpr fun x => (hasDerivAt_ev P x).continuousAt).measurable

lemma measurable_hFz (g : ℤ) : Measurable (hFz lam ξ y g) := by
  have h : hFz lam ξ y g = fun z : ℍ => ∑' x : ℤ, sv ξ y g (z : ℂ) x * ((rR lam g y (z : ℂ).im x : ℝ) : ℂ) :=
    funext (hFz_eq lam ξ y g)
  rw [h]
  refine Measurable.tsum fun x => ?_
  have h1 : Measurable fun w : ℂ => sv ξ y g w x := by
    unfold sv
    fun_prop
  have h2 : Measurable fun v : ℝ => rR lam g y v x := by
    unfold rR
    have := measurable_ev (hermite lam)
    fun_prop
  have h3 : Measurable fun z : ℍ => (z : ℂ) := measurable_coe
  exact (h1.comp h3).mul (Complex.measurable_ofReal.comp (h2.comp (Complex.measurable_im.comp h3)))

/-- The integrand attached to `g`. -/
def Hg (g : ℤ) (z : ℍ) : ℂ :=
  ((z.im ^ ((lam : ℝ) + 1 / 2) : ℝ) : ℂ) * (conj (fF G j hN z) * hFz lam ξ y g z)

lemma measurable_Hg (g : ℤ) : Measurable (Hg G j hN lam ξ y g) := by
  have h1 : Measurable fun z : ℍ => z.im := UpperHalfPlane.continuous_im.measurable
  have h2 : Measurable (fF G j hN) := (continuous_fF G j hN).measurable
  have h3 := measurable_hFz lam ξ y g
  unfold Hg
  exact (Complex.measurable_ofReal.comp (h1.pow_const _)).mul
    ((Complex.continuous_conj.measurable.comp h2).mul h3)

/-- The exponent of the common factor. -/
def pE' (lam : ℕ) : ℝ := (lam : ℝ) / 2 - 5 / 2

/-- The Hecke exponent. -/
def eH (k' : ℤ) (j : ℕ) : ℝ := (k' : ℝ) / 2 - j / 4

/-- The common factor, in `v`. -/
def bF (k' : ℤ) (j lam : ℕ) (v : ℝ) : ℝ :=
  (v ^ (pE' lam - eH k' j) + v ^ pE' lam) * Real.exp (-(2 * π / 24 * v))

/-- The bound for `𝔽` as a function of `v`. -/
def mF (C : ℝ) (k' : ℤ) (j : ℕ) (v : ℝ) : ℝ :=
  C * (v ^ (-((k' : ℝ) / 2 - j / 4)) + 1) * Real.exp (-(2 * π / 24 * v))

/-- **The bound in product form.** -/
theorem strip_bound {hj : j < 24} : ∃ (K CF : ℝ), 0 ≤ K ∧ 0 ≤ CF ∧
    (∀ z : ℍ, ‖fF G j hN z‖ ≤ mF CF k' j z.im) ∧
    ∀ (g : ℤ) {z : ℂ} (_ : 0 < z.im),
      (Summable fun x : ℤ => ‖sv ξ y g z x * ((rR lam g y z.im x : ℝ) : ℂ)‖) ∧
      (z.im ^ 2)⁻¹ * (z.im ^ ((lam : ℝ) + 1 / 2) * (mF CF k' j z.im *
        ∑' x : ℤ, ‖sv ξ y g z x * ((rR lam g y z.im x : ℝ) : ℂ)‖)) ≤
        K * bF k' j lam z.im * Real.exp (-(9 * π * y ^ 2 / 2 * (g : ℝ) ^ 2 / z.im)) := by
  obtain ⟨CF, hCF0, hCF⟩ := norm_fF_le G j (hj := hj) hN
  obtain ⟨CT, hCT0, hCT⟩ := norm_hF_le lam
  have hπ := Real.pi_pos
  refine ⟨CF * CT * √(3 / π) ^ lam * (48 / π), CF, by positivity, hCF0, hCF,
    fun g z hz => ?_⟩
  obtain ⟨h1, hS⟩ := hCT ξ y g hz
  refine ⟨hS, ?_⟩
  set v := z.im with hvdef
  have hv : 0 < v := hz
  have hsq : √(3 / (π * v)) = √(3 / π) * v ^ (-(1 / 2 : ℝ)) := by
    have e1 : 3 / (π * v) = 3 / π * v⁻¹ := by field_simp
    rw [e1, Real.sqrt_mul (by positivity), Real.sqrt_inv, Real.sqrt_eq_rpow v, Real.rpow_neg hv.le]
  have hpw : (v ^ 2)⁻¹ * v ^ ((lam : ℝ) + 1 / 2) * (v ^ (-(1 / 2 : ℝ))) ^ lam * v⁻¹ = v ^ pE' lam := by
    have a1 : (v ^ 2)⁻¹ = v ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hv.le, Real.rpow_two]
    have a2 : (v ^ (-(1 / 2 : ℝ))) ^ lam = v ^ (-((lam : ℝ) / 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le]
      congr 1
      ring
    have a3 : v⁻¹ = v ^ (-1 : ℝ) := (Real.rpow_neg_one v).symm
    rw [a1, a2, a3, ← Real.rpow_add hv, ← Real.rpow_add hv, ← Real.rpow_add hv]
    congr 1
    unfold pE'
    ring
  have hsplit : v ^ (pE' lam - eH k' j) + v ^ pE' lam =
      v ^ pE' lam * (v ^ (-((k' : ℝ) / 2 - j / 4)) + 1) := by
    rw [sub_eq_add_neg, Real.rpow_add hv]
    unfold eH
    ring
  have hP : 0 ≤ v ^ ((lam : ℝ) + 1 / 2) := by positivity
  have hM : 0 ≤ mF CF k' j v := by unfold mF; positivity
  calc _ ≤ (v ^ 2)⁻¹ * (v ^ ((lam : ℝ) + 1 / 2) * (mF CF k' j v *
        (CT * √(3 / (π * v)) ^ lam * Real.exp (-(9 * π * y ^ 2 / 2 * (g : ℝ) ^ 2 / v)) *
          (48 / (π * v))))) := by
        gcongr
    _ = _ := by
      unfold bF mF
      rw [hsplit, hsq, mul_pow, ← hpw]
      field_simp

/-- **The bound on the integrand.** -/
theorem norm_Hg_le {hj : j < 24} : ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : ℤ) (z : ℍ),
    ((z.im ^ 2)⁻¹) * ‖Hg G j hN lam ξ y g z‖ ≤
      K * bF k' j lam z.im * Real.exp (-(9 * π * y ^ 2 / 2 * (g : ℝ) ^ 2 / z.im)) := by
  obtain ⟨K, CF, hK0, hCF0, hF, hB⟩ := strip_bound G j hN lam ξ y (hj := hj)
  refine ⟨K, hK0, fun g z => ?_⟩
  obtain ⟨hS, h1⟩ := hB g (z := (z : ℂ)) z.2
  have hzv : (z : ℂ).im = z.im := rfl
  rw [hzv] at h1 hS
  have hT : ‖hFz lam ξ y g z‖ ≤ ∑' x : ℤ, ‖sv ξ y g (z : ℂ) x * ((rR lam g y z.im x : ℝ) : ℂ)‖ := by
    rw [hFz_eq, hzv]
    exact norm_tsum_le_tsum_norm hS
  have hv := z.im_pos
  have hHg : ‖Hg G j hN lam ξ y g z‖ = z.im ^ ((lam : ℝ) + 1 / 2) *
      (‖fF G j hN z‖ * ‖hFz lam ξ y g z‖) := by
    unfold Hg
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [hHg]
  refine le_trans ?_ h1
  have hs0 : 0 ≤ ∑' x : ℤ, ‖sv ξ y g (z : ℂ) x * ((rR lam g y z.im x : ℝ) : ℂ)‖ :=
    tsum_nonneg fun _ => norm_nonneg _
  have hM := hF z
  have hM0 : 0 ≤ mF CF k' j z.im := (norm_nonneg _).trans hM
  gcongr

/-- The bound at parameter `β`, with a further power of `v`. -/
lemma integrableOn_bF (k' : ℤ) (j lam : ℕ) (q : ℝ) {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun v : ℝ => v ^ q * bF k' j lam v * Real.exp (-(β / v))) (Ioi 0) := by
  have hc : 0 < 2 * π / 24 := by
    have := Real.pi_pos
    positivity
  have h1 := integrableOn_rpow_exp (pE' lam - eH k' j + q) hβ hc
  have h2 := integrableOn_rpow_exp (pE' lam + q) hβ hc
  refine (h1.add h2).congr_fun (fun v hv => ?_) measurableSet_Ioi
  have hv' : 0 < v := hv
  simp only [Pi.add_apply]
  unfold bF
  rw [Real.rpow_add hv', Real.rpow_add hv', sub_eq_add_neg (-(β / v)), Real.exp_add]
  ring

/-- The summed bound over `g ≠ 0`. -/
lemma sum_g_bound {B v : ℝ} (hB : 0 < B) (hv : 0 < v) :
    Summable (fun g : ℤ => if g = 0 then (0 : ℝ) else Real.exp (-(B * (g : ℝ) ^ 2 / v))) ∧
      ∑' g : ℤ, (if g = 0 then (0 : ℝ) else Real.exp (-(B * (g : ℝ) ^ 2 / v))) ≤
        Real.exp (-(B / 2 / v)) * (4 * v / B) := by
  have ha : 0 < B / (2 * v) := by positivity
  obtain ⟨hS, hb⟩ := gauss_ne_zero_bound ha
  have hle : ∀ g : ℤ, (if g = 0 then (0 : ℝ) else Real.exp (-(B * (g : ℝ) ^ 2 / v))) ≤
      Real.exp (-(B / 2 / v)) * (if g = 0 then 0 else Real.exp (-(B / (2 * v)) * (g : ℝ) ^ 2)) := by
    intro g
    by_cases hg : g = 0
    · simp [hg]
    rw [if_neg hg, if_neg hg, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : (1 : ℝ) ≤ (g : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ g ^ 2 := by
        have := sq_nonneg g
        have h2 : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
        omega
      exact_mod_cast this
    have e : -(B / 2 / v) + -(B / (2 * v)) * (g : ℝ) ^ 2 = -(B / (2 * v) * (1 + (g : ℝ) ^ 2)) := by
      field_simp
      ring
    have e2 : -(B * (g : ℝ) ^ 2 / v) = -(B / (2 * v) * (2 * (g : ℝ) ^ 2)) := by
      field_simp
    rw [e, e2]
    have := mul_le_mul_of_nonneg_left (by linarith : 1 + (g : ℝ) ^ 2 ≤ 2 * (g : ℝ) ^ 2) ha.le
    linarith
  have hSK := hS.mul_left (Real.exp (-(B / 2 / v)))
  have hS2 : Summable (fun g : ℤ => if g = 0 then (0 : ℝ) else Real.exp (-(B * (g : ℝ) ^ 2 / v))) :=
    Summable.of_nonneg_of_le (fun g => by split_ifs <;> positivity) hle hSK
  refine ⟨hS2, (hS2.tsum_le_tsum hle hSK).trans ?_⟩
  rw [tsum_mul_left]
  have he := Real.exp_pos (-(B / 2 / v))
  have e3 : 4 * v / B = 2 / (B / (2 * v)) := by field_simp; norm_num
  rw [e3]
  exact mul_le_mul_of_nonneg_left hb he.le

/-- The total integrand. -/
def fTot (ψg : ℤ → ℂ) (z : ℍ) : ℂ := ∑' g : ℤ, ψg g * Hg G j hN lam ξ y g z

/-- The dominating function of the total integrand. -/
def dTot (K B : ℝ) (k' : ℤ) (j lam : ℕ) (v : ℝ) : ℝ :=
  K * (4 / B) * (v ^ (1 : ℝ) * bF k' j lam v * Real.exp (-(B / 2 / v)))

lemma integrableOn_dTot (K : ℝ) {B : ℝ} (hB : 0 < B) (k' : ℤ) (j lam : ℕ) :
    IntegrableOn (dTot K B k' j lam) (Ioi 0) :=
  (integrableOn_bF k' j lam 1 (by positivity : 0 < B / 2)).const_mul _

lemma pt_im {p : ℝ × ℝ} (hv : 0 < p.2) : (pt p).im = p.2 := by
  have hc : 0 < ((p.1 : ℂ) + p.2 * I).im := by simpa using hv
  change (ofComplex ((p.1 : ℂ) + p.2 * I) : ℂ).im = p.2
  rw [ofComplex_apply_of_im_pos hc]
  simp

/-- Integrability on the rectangle from a bound in `v`. -/
lemma integrableOn_tr'_of_bound {f : ℍ → ℂ} (hf : Measurable f) {D : ℝ → ℝ}
    (hD : IntegrableOn D (Ioi 0)) (hb : ∀ z : ℍ, (z.im ^ 2)⁻¹ * ‖f z‖ ≤ D z.im) :
    IntegrableOn (tr' f) rect := by
  refine integrableOn_rect hD ?_ fun p hp => ?_
  · have : Measurable (tr' f) := by
      unfold tr'
      exact (measurable_snd.pow_const 2).inv.smul (hf.comp measurable_pt)
    exact this.aestronglyMeasurable
  · have hv : 0 < p.2 := hp.2
    have h := hb (pt p)
    rw [pt_im hv] at h
    unfold tr'
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact h

/-- Integrability on the strip from a bound in `v`. -/
lemma integrableOn_strip_of_bound {f : ℍ → ℂ} (hf : Measurable f) {D : ℝ → ℝ}
    (hD : IntegrableOn D (Ioi 0)) (hb : ∀ z : ℍ, (z.im ^ 2)⁻¹ * ‖f z‖ ≤ D z.im) :
    IntegrableOn f stripSet :=
  integrableOn_strip (integrableOn_tr'_of_bound hf hD hb)

/-- **The sum over `g` on the strip.** -/
theorem strip_total {hj : j < 24} (hy : 0 < y) {ψg : ℤ → ℂ} (h1 : ∀ g, ‖ψg g‖ ≤ 1) (h0 : ψg 0 = 0) :
    (∀ g : ℤ, g ≠ 0 → IntegrableOn (Hg G j hN lam ξ y g) stripSet) ∧
      IntegrableOn (fTot G j hN lam ξ y ψg) stripSet ∧
      HasSum (fun g : ℤ => ψg g * ∫ z in stripSet, Hg G j hN lam ξ y g z)
        (∫ z in stripSet, fTot G j hN lam ξ y ψg z) := by
  obtain ⟨K, hK0, hK⟩ := norm_Hg_le G j hN lam ξ y (hj := hj)
  have hπ := Real.pi_pos
  set B := 9 * π * y ^ 2 / 2 with hBdef
  have hB : 0 < B := by positivity
  have hg : ∀ g : ℤ, g ≠ 0 → IntegrableOn (Hg G j hN lam ξ y g) stripSet := by
    intro g hg0
    have hgsq : (0 : ℝ) < (g : ℝ) ^ 2 := by
      have : (g : ℝ) ≠ 0 := by exact_mod_cast hg0
      positivity
    have hβ : 0 < B * (g : ℝ) ^ 2 := by positivity
    refine integrableOn_strip_of_bound (measurable_Hg G j hN lam ξ y g)
      ((integrableOn_bF k' j lam 0 hβ).const_mul K) fun z => ?_
    have hv := z.im_pos
    refine (hK g z).trans (le_of_eq ?_)
    simp only [Real.rpow_zero, one_mul]
    ring
  have hbound : ∀ z : ℍ, Summable (fun g : ℤ => ‖ψg g * Hg G j hN lam ξ y g z‖) ∧
      ∑' g : ℤ, ‖ψg g * Hg G j hN lam ξ y g z‖ ≤ z.im ^ 2 * dTot K B k' j lam z.im := by
    intro z
    have hv := z.im_pos
    have hbF0 : 0 ≤ bF k' j lam z.im := by unfold bF; positivity
    obtain ⟨hS, hsum⟩ := sum_g_bound hB hv
    set W := z.im ^ 2 * (K * bF k' j lam z.im) with hW
    have hW0 : 0 ≤ W := by positivity
    have hle : ∀ g : ℤ, ‖ψg g * Hg G j hN lam ξ y g z‖ ≤
        W * (if g = 0 then 0 else Real.exp (-(B * (g : ℝ) ^ 2 / z.im))) := by
      intro g
      by_cases hg0 : g = 0
      · simp [hg0, h0]
      rw [if_neg hg0, norm_mul]
      have h2 := hK g z
      have hv2 : 0 < z.im ^ 2 := by positivity
      rw [inv_mul_le_iff₀ hv2] at h2
      calc _ ≤ 1 * ‖Hg G j hN lam ξ y g z‖ := by gcongr; exact h1 g
        _ ≤ _ := by rw [one_mul]; refine h2.trans (le_of_eq ?_); rw [hW]; ring
    have hSK := hS.mul_left W
    have hS2 := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hSK
    refine ⟨hS2, (hS2.tsum_le_tsum hle hSK).trans ?_⟩
    rw [tsum_mul_left]
    refine (mul_le_mul_of_nonneg_left hsum hW0).trans (le_of_eq ?_)
    unfold dTot
    rw [Real.rpow_one, hW]
    field_simp
  have hBz : IntegrableOn (fun z : ℍ => z.im ^ 2 * dTot K B k' j lam z.im) stripSet := by
    have hm : Measurable fun z : ℍ => z.im ^ 2 * dTot K B k' j lam z.im := by
      have him : Measurable fun z : ℍ => z.im := UpperHalfPlane.continuous_im.measurable
      unfold dTot bF
      fun_prop
    have hc := integrableOn_strip_of_bound (f := fun z : ℍ => ((z.im ^ 2 * dTot K B k' j lam z.im : ℝ) : ℂ))
      (Complex.measurable_ofReal.comp hm) (integrableOn_dTot K hB k' j lam) fun z => ?_
    · exact hc.re
    · have hv := z.im_pos
      have hbF0 : 0 ≤ dTot K B k' j lam z.im := by unfold dTot bF; positivity
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      refine le_of_eq ?_
      field_simp
  have hmeas : ∀ g : ℤ, AEStronglyMeasurable (fun z => ψg g * Hg G j hN lam ξ y g z)
      (volume.restrict stripSet) := fun g =>
    ((measurable_Hg G j hN lam ξ y g).const_mul _).aestronglyMeasurable
  obtain ⟨-, hsum⟩ := tsum_integral_of_bound hBz hmeas (ae_of_all _ hbound)
  refine ⟨hg, ?_, ?_⟩
  · refine Integrable.mono' hBz ?_ (ae_of_all _ fun z => ?_)
    · have : Measurable (fTot G j hN lam ξ y ψg) := by
        unfold fTot
        exact Measurable.tsum fun g => (measurable_Hg G j hN lam ξ y g).const_mul _
      exact this.aestronglyMeasurable
    · exact (norm_tsum_le_tsum_norm (hbound z).1).trans (hbound z).2
  · simp only [integral_const_mul] at hsum
    exact hsum

/-- The rectangle integrand attached to `g ≠ 0` is integrable. -/
lemma integrableOn_tr_Hg {hj : j < 24} (hy : 0 < y) {g : ℤ} (hg0 : g ≠ 0) :
    IntegrableOn (tr' (Hg G j hN lam ξ y g)) rect := by
  obtain ⟨K, hK0, hK⟩ := norm_Hg_le G j hN lam ξ y (hj := hj)
  have hπ := Real.pi_pos
  have hgsq : (0 : ℝ) < (g : ℝ) ^ 2 := by
    have : (g : ℝ) ≠ 0 := by exact_mod_cast hg0
    positivity
  have hβ : 0 < 9 * π * y ^ 2 / 2 * (g : ℝ) ^ 2 := by positivity
  refine integrableOn_tr'_of_bound (measurable_Hg G j hN lam ξ y g)
    ((integrableOn_bF k' j lam 0 hβ).const_mul K) fun z => ?_
  refine (hK g z).trans (le_of_eq ?_)
  simp only [Real.rpow_zero, one_mul]
  ring

end

end RamanujanTau.ThetaLift
