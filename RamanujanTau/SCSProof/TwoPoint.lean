/-
# The two-point invariant `Ψ(z,w) = (z − w̄)¹² Δ(z) conj Δ(w)`

* `Psi_smul`: `Ψ(γz, γw) = Ψ(z, w)` for `γ ∈ SL₂(ℤ)` (diagonal action).
* `norm_Psi_le`: `‖Ψ(z,w)‖ ≤ M² (|z − w̄|² / (Im z Im w))⁶`.
* `coeff_Psi`: the diagonal horocycle coefficient, with `w = x + yζ`:
  `∫₀¹ Ψ(x+iy, x+yζ) e(−hx) dx = y¹² (i − ζ̄)¹² e^{−2πhy} G_h(2πy(1 + iζ̄))`,
  `G_h(W) = Σ_n τ(n)τ(n+h) e^{−nW}`.
-/
import RamanujanTau.SCSProof.Kloost
import RamanujanTau.Subconvexity.Shifted

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open Complex ModularForm MeasureTheory
open UpperHalfPlane hiding I
open scoped MatrixGroups ComplexConjugate Real
open RamanujanTau.RankinSelberg RamanujanTau.TauSigns

local notation "𝕢" => Function.Periodic.qParam

/-- The two-point function `Ψ(z,w) = (z − w̄)¹² Δ(z) conj Δ(w)`. -/
noncomputable def Psi (z w : ℍ) : ℂ := ((z : ℂ) - conj (w : ℂ)) ^ 12 * Δf z * conj (Δf w)

/-- `G_h(W) = Σ_n τ(n)τ(n+h) e^{−nW}`. -/
noncomputable def Gh (h : ℕ) (W : ℂ) : ℂ :=
  ∑' n : ℕ, ((tau n * tau (n + h) : ℤ) : ℂ) * cexp (-(n : ℂ) * W)

/-- The point `x + yζ ∈ ℍ`. -/
def aff {y : ℝ} (hy : 0 < y) (x : ℝ) (ζ : ℍ) : ℍ :=
  ⟨(x : ℂ) + y * (ζ : ℂ), by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add,
      zero_mul, add_zero]
    exact mul_pos hy ζ.im_pos⟩

lemma aff_coe {y : ℝ} (hy : 0 < y) (x : ℝ) (ζ : ℍ) :
    ((aff hy x ζ : ℍ) : ℂ) = (x : ℂ) + y * (ζ : ℂ) := rfl

/-! ### Invariance -/

lemma denom_ne_zero' (γ : SL(2, ℤ)) (z : ℍ) : ((γ 1 0 : ℂ) * (z : ℂ) + γ 1 1) ≠ 0 := by
  have := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) z
  simpa [UpperHalfPlane.denom] using this

lemma coe_smul_sl (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp

lemma det_sl (γ : SL(2, ℤ)) : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := γ.2
  rw [Matrix.det_fin_two] at h
  have : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ℂ) = 1 := by rw [h]; simp
  push_cast at this; exact this

/-- `γz − conj(γw) = (z − w̄) / (j(γ,z) · conj j(γ,w))`. -/
lemma smul_sub_conj (γ : SL(2, ℤ)) (z w : ℍ) :
    ((γ • z : ℍ) : ℂ) - conj ((γ • w : ℍ) : ℂ) =
      ((z : ℂ) - conj (w : ℂ)) /
        (((γ 1 0 : ℂ) * z + γ 1 1) * conj ((γ 1 0 : ℂ) * w + γ 1 1)) := by
  have hz := denom_ne_zero' γ z
  have hw := denom_ne_zero' γ w
  have hw' : conj ((γ 1 0 : ℂ) * w + γ 1 1) ≠ 0 := (map_ne_zero _).2 hw
  rw [coe_smul_sl, coe_smul_sl, map_div₀]
  simp only [map_add, map_mul, map_intCast]
  have hw'' : (γ 1 0 : ℂ) * conj (w : ℂ) + γ 1 1 ≠ 0 := by
    simpa [map_add, map_mul, map_intCast] using hw'
  rw [div_sub_div _ _ hz hw'', div_eq_div_iff (mul_ne_zero hz hw'') (mul_ne_zero hz hw'')]
  have hd := det_sl γ
  linear_combination ((γ 1 0 : ℂ) * z + γ 1 1) * ((γ 1 0 : ℂ) * conj (w : ℂ) + γ 1 1) *
    ((z : ℂ) - conj (w : ℂ)) * hd

lemma Delta_smul (γ : SL(2, ℤ)) (z : ℍ) :
    Δf (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ 12 * Δf z := by
  have hmem : ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hD := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hmem z
  have e : (γ • z : ℍ) = ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) • z := (ModularGroup.sl_moeb γ z)
  rw [e]
  refine hD.trans ?_
  congr 1

/-- **Invariance**: `Ψ(γz, γw) = Ψ(z, w)`. -/
theorem Psi_smul (γ : SL(2, ℤ)) (z w : ℍ) : Psi (γ • z) (γ • w) = Psi z w := by
  unfold Psi
  rw [smul_sub_conj, Delta_smul, Delta_smul]
  have hz := denom_ne_zero' γ z
  have hw := denom_ne_zero' γ w
  have hw' : conj ((γ 1 0 : ℂ) * w + γ 1 1) ≠ 0 := (map_ne_zero _).2 hw
  have hz' : (z : ℂ) * γ 1 0 + γ 1 1 ≠ 0 := by rw [mul_comm]; exact hz
  rw [div_pow, map_mul, map_pow]
  field_simp

/-! ### Size -/

/-- `‖Ψ(z,w)‖ ≤ M (|z − w̄|² / (Im z Im w))⁶`. -/
theorem norm_Psi_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ z w : ℍ,
    ‖Psi z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6 := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound (CuspForm.discriminant : CuspForm 𝒮ℒ 12)
  have hC0 : 0 ≤ C := by
    have := hC UpperHalfPlane.I
    exact le_trans (norm_nonneg _) (by simpa using this)
  refine ⟨C ^ 2, by positivity, fun z w => ?_⟩
  have hz := hC z
  have hw := hC w
  have hzi := z.im_pos
  have hwi := w.im_pos
  have e12 : (((12 : ℤ) : ℝ) / 2) = 6 := by norm_num
  rw [e12] at hz hw
  have hz' : ‖Δf z‖ ≤ C / z.im ^ 6 := by
    rw [← Real.rpow_natCast]; simpa using hz
  have hw' : ‖Δf w‖ ≤ C / w.im ^ 6 := by
    rw [← Real.rpow_natCast]; simpa using hw
  unfold Psi
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_conj]
  have hn : ‖(z : ℂ) - conj (w : ℂ)‖ ^ 12 =
      Complex.normSq ((z : ℂ) - conj (w : ℂ)) ^ 6 := by
    rw [Complex.normSq_eq_norm_sq, ← pow_mul]
  rw [hn]
  calc Complex.normSq ((z : ℂ) - conj (w : ℂ)) ^ 6 * ‖Δf z‖ * ‖Δf w‖
      ≤ Complex.normSq ((z : ℂ) - conj (w : ℂ)) ^ 6 * (C / z.im ^ 6) * (C / w.im ^ 6) := by
        gcongr
    _ = C ^ 2 * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6 := by
        field_simp

/-! ### The diagonal horocycle coefficient -/

lemma qParam_one (u : ℂ) : 𝕢 1 u = cexp (2 * π * I * u) := by
  simp [Function.Periodic.qParam]

lemma norm_qParam_one (u : ℂ) : ‖𝕢 1 u‖ = Real.exp (-2 * π * u.im) := by
  rw [qParam_one, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- **Diagonal horocycle coefficient of `Ψ`.** -/
theorem coeff_Psi (h : ℕ) {y : ℝ} (hy : 0 < y) (ζ : ℍ) :
    ∫ x in (0 : ℝ)..1, Psi (hp hy x) (aff hy x ζ) * cexp (-2 * π * I * h * x) =
      ((y : ℂ) * (I - conj (ζ : ℂ))) ^ 12 * (Real.exp (-2 * π * h * y) : ℂ) *
        Gh h (2 * π * y * (1 + I * conj (ζ : ℂ))) := by
  set f := (CuspForm.discriminant : CuspForm 𝒮ℒ 12)
  set a : ℕ → ℂ := fun n => ((tau n : ℤ) : ℂ)
  have ha : ∀ n, (qExpansion 1 f).coeff n = a n := fun n =>
    TauBound.qExpansion_discriminant_coeff_tau n
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL
  have hq : ∀ x : ℝ, HasSum (fun n => a n * 𝕢 1 ((aff hy x ζ : ℍ) : ℂ) ^ n) (f (aff hy x ζ)) := by
    intro x
    have := hasSum_qExpansion one_pos hper (ModularFormClass.holo f)
      (ModularFormClass.bdd_at_infty f) (aff hy x ζ)
    simpa only [smul_eq_mul, ha] using this
  set r := Real.exp (-2 * π * (y * ζ.im)) with hr
  have hnq : ∀ x : ℝ, ‖𝕢 1 ((aff hy x ζ : ℍ) : ℂ)‖ = r := by
    intro x
    rw [norm_qParam_one, aff_coe]
    simp [hr, Complex.mul_im]
  have hsum : Summable (fun n => ‖a n‖ * r ^ n) := by
    have := (summable_norm_iff.mpr (hq 0).summable)
    refine this.congr fun n => ?_
    rw [norm_mul, norm_pow, hnq]
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  set B := C / y ^ (((12 : ℤ) : ℝ) / 2)
  have hB : ∀ x, ‖f (hp hy x)‖ ≤ B := fun x => by
    have := hC (hp hy x); rwa [hp_im] at this
  set E : ℝ → ℂ := fun x => cexp (-2 * π * I * h * x)
  have hE : ∀ x : ℝ, ‖E x‖ = 1 := by
    intro x
    simp only [E, Complex.norm_exp]
    simp [Complex.mul_re]
  have hzw : ∀ x : ℝ, ((hp hy x : ℍ) : ℂ) - conj ((aff hy x ζ : ℍ) : ℂ) =
      (y : ℂ) * (I - conj (ζ : ℂ)) := by
    intro x
    rw [hp_coe, aff_coe]
    simp only [map_add, map_mul, Complex.conj_ofReal]
    ring
  set K : ℂ := ((y : ℂ) * (I - conj (ζ : ℂ))) ^ 12
  have hPsi : ∀ x : ℝ, Psi (hp hy x) (aff hy x ζ) * cexp (-2 * π * I * h * x) =
      K * (f (hp hy x) * conj (f (aff hy x ζ)) * cexp (-2 * π * I * h * x)) := by
    intro x; unfold Psi; rw [hzw]; ring
  simp_rw [hPsi]
  rw [intervalIntegral.integral_const_mul]
  set Fn : ℕ → ℝ → ℂ := fun n x =>
    f (hp hy x) * conj (a n * 𝕢 1 ((aff hy x ζ : ℍ) : ℂ) ^ n) * E x
  have hcontf : Continuous (fun x : ℝ => f (hp hy x)) :=
    (ModularFormClass.holo f).continuous.comp (continuous_hp hy)
  have hcontq : Continuous (fun x : ℝ => 𝕢 1 ((aff hy x ζ : ℍ) : ℂ)) := by
    show Continuous fun x : ℝ => 𝕢 1 ((x : ℂ) + y * (ζ : ℂ))
    simp_rw [qParam_one]
    fun_prop
  have hcontE : Continuous E := by
    show Continuous fun x : ℝ => cexp (-2 * π * I * h * x); fun_prop
  have hDCT : HasSum (fun n => ∫ x in (0 : ℝ)..1, Fn n x)
      (∫ x in (0 : ℝ)..1, f (hp hy x) * conj (f (aff hy x ζ)) * E x) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => B * (‖a n‖ * r ^ n)) (fun n => ?_) (fun n => ?_) ?_
      intervalIntegrable_const ?_
    · exact ((hcontf.mul (continuous_conj.comp
        (continuous_const.mul (hcontq.pow n)))).mul hcontE).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x _ => ?_
      simp only [Fn, norm_mul, Complex.norm_conj, norm_pow, hnq, hE, mul_one]
      gcongr
      exact hB x
    · exact Filter.Eventually.of_forall fun x _ => hsum.mul_left B
    · refine Filter.Eventually.of_forall fun x _ => ?_
      exact ((hasSum_conj'.mpr (hq x)).mul_left (f (hp hy x))).mul_right _
  have hterm : ∀ n, ∫ x in (0 : ℝ)..1, Fn n x =
      (Real.exp (-2 * π * h * y) : ℂ) *
        (((tau n * tau (n + h) : ℤ) : ℂ) * cexp (-(n : ℂ) * (2 * π * y * (1 + I * conj (ζ : ℂ))))) := by
    intro n
    have hcoef := ModularFormClass.qExpansion_coeff_eq_intervalIntegral f one_pos
      one_mem_strictPeriods_SL (n + h) hy
    rw [ha] at hcoef
    set c0 : ℂ := a n * cexp (-2 * π * I * n * y * conj (ζ : ℂ)) *
      Real.exp (-2 * π * (n + h) * y)
    have hpt : ∀ x : ℝ, Fn n x = c0 *
        (1 / 𝕢 1 ((x : ℂ) + y * I) ^ (n + h) * f (hp hy x)) := by
      intro x
      simp only [Fn, c0, E, map_mul, map_pow, qParam_one, aff_coe]
      have hc : conj (a n) = a n := by simp [a]
      rw [hc]
      rw [← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, one_div,
        ← Complex.exp_neg]
      have : (Real.exp (-2 * π * (n + h) * y) : ℂ) = cexp (-2 * π * (n + h) * y) := by
        push_cast; rfl
      rw [this]
      simp only [map_mul, map_add, Complex.conj_ofReal, map_ofNat, Complex.conj_I]
      have e3 : cexp (↑n * (2 * ↑π * -I * (↑x + ↑y * conj (ζ : ℂ)))) *
          cexp (-2 * ↑π * I * ↑h * ↑x) =
          cexp (-2 * π * I * n * y * conj (ζ : ℂ)) * cexp (-2 * π * (n + h) * y) *
            cexp (-(↑(n + h) * (2 * ↑π * I * (↑x + ↑y * I)))) := by
        rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast
        linear_combination (2 * π * y * (n + h) : ℂ) * Complex.I_sq
      linear_combination (a n * f (hp hy x)) * e3
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul]
    have : (∫ x in (0 : ℝ)..1, 1 / 𝕢 1 ((x : ℂ) + y * I) ^ (n + h) *
        f (hp hy x)) = a (n + h) := by
      rw [hcoef]; simp [hp]
    rw [this]
    simp only [c0, a]
    have : (Real.exp (-2 * π * (n + h) * y) : ℂ) =
        (Real.exp (-2 * π * h * y) : ℂ) * cexp (-2 * π * n * y) := by
      push_cast; rw [← Complex.exp_add]; congr 1; ring
    rw [this]
    push_cast
    have e2 : cexp (-2 * π * I * n * y * conj (ζ : ℂ)) * cexp (-2 * π * n * y) =
        cexp (-(n : ℂ) * (2 * π * y * (1 + I * conj (ζ : ℂ)))) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [← e2]
    ring
  simp_rw [hterm] at hDCT
  have key : (∫ x in (0 : ℝ)..1, f (hp hy x) * conj (f (aff hy x ζ)) *
      cexp (-2 * π * I * h * x)) = _ := hDCT.tsum_eq.symm
  rw [key, tsum_mul_left]
  simp only [Gh, K]
  ring

end RamanujanTau.SCSProof
