/-
# The weight-`k` two-point invariant `Ψ_f(z,w) = (z − w̄)^k f(z) conj f(w)`

Weight-parametric copy of `SCSProof.TwoPoint` (the `Δ`-specific geometric core of the shifted
convolution argument) for an arbitrary `f ∈ S_k(SL₂(ℤ))`:

* `PsiF_smul`: `Ψ_f(γz, γw) = Ψ_f(z, w)` for `γ ∈ SL₂(ℤ)`;
* `norm_PsiF_le`: `‖Ψ_f(z,w)‖ ≤ M (|z − w̄|² / (Im z Im w))^{k/2}`;
* `coeff_PsiF`: with `w = x + yζ`,
  `∫₀¹ Ψ_f(x+iy, x+yζ) e(−hx) dx = (y(i − ζ̄))^k e^{−2πhy} G^f_h(2πy(1 + iζ̄))`,
  `G^f_h(W) = Σ_n conj a_f(n) a_f(n+h) e^{−nW}` (for real coefficients: `Σ a(n)a(n+h)e^{−nW}`).

At `k = 12`, `f = Δ` these are `SCSProof.Psi_smul`, `norm_Psi_le`, `coeff_Psi`.
-/
import RamanujanTau.SubconvexGeneral.Defs
import RamanujanTau.SCSProof.TwoPoint

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral

open Complex MeasureTheory
open UpperHalfPlane hiding I
open scoped MatrixGroups ComplexConjugate Real
open RamanujanTau.RankinSelberg RamanujanTau.SCSProof RamanujanTau.HeckeConvexGeneral

local notation "𝕢" => Function.Periodic.qParam

variable {k : ℕ}

/-- `Ψ_f(z,w) = (z − w̄)^k f(z) conj f(w)`. -/
noncomputable def PsiF (f : CuspForm 𝒮ℒ (k : ℤ)) (z w : ℍ) : ℂ :=
  ((z : ℂ) - conj (w : ℂ)) ^ k * f z * conj (f w)

/-- `G^f_h(W) = Σ_n conj a_f(n) a_f(n+h) e^{−nW}`. -/
noncomputable def GhF (f : CuspForm 𝒮ℒ (k : ℤ)) (h : ℕ) (W : ℂ) : ℂ :=
  ∑' n : ℕ, conj (coef f n) * coef f (n + h) * cexp (-(n : ℂ) * W)

lemma f_smul (f : CuspForm 𝒮ℒ (k : ℤ)) (γ : SL(2, ℤ)) (z : ℍ) :
    f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ k * f z := by
  have hmem : ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hD := SlashInvariantForm.slash_action_eqn'' f hmem z
  have e : (γ • z : ℍ) = ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) • z := (ModularGroup.sl_moeb γ z)
  rw [e]
  refine hD.trans ?_
  rw [zpow_natCast]
  congr 2

/-- **Invariance**: `Ψ_f(γz, γw) = Ψ_f(z, w)`. -/
theorem PsiF_smul (f : CuspForm 𝒮ℒ (k : ℤ)) (γ : SL(2, ℤ)) (z w : ℍ) :
    PsiF f (γ • z) (γ • w) = PsiF f z w := by
  unfold PsiF
  rw [smul_sub_conj, f_smul, f_smul]
  have hz := denom_ne_zero' γ z
  have hw := denom_ne_zero' γ w
  have hw' : conj ((γ 1 0 : ℂ) * w + γ 1 1) ≠ 0 := (map_ne_zero _).2 hw
  have hz' : (z : ℂ) * γ 1 0 + γ 1 1 ≠ 0 := by rw [mul_comm]; exact hz
  rw [div_pow, map_mul, map_pow, mul_pow]
  have h1 := pow_ne_zero k hz
  have h2 := pow_ne_zero k hw'
  have h3 := pow_ne_zero k hz'
  field_simp

/-- **Size**: `‖Ψ_f(z,w)‖ ≤ M (|z − w̄|² / (Im z Im w))^{k/2}`. -/
theorem norm_PsiF_le (f : CuspForm 𝒮ℒ (k : ℤ)) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z w : ℍ,
    ‖PsiF f z w‖ ≤
      M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ ((k : ℝ) / 2) := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  have hC0 : 0 ≤ C := by
    have := hC UpperHalfPlane.I
    exact le_trans (norm_nonneg _) (by simpa using this)
  refine ⟨C ^ 2, by positivity, fun z w => ?_⟩
  have hz := hC z
  have hw := hC w
  have hzi := z.im_pos
  have hwi := w.im_pos
  have ek : (((k : ℤ) : ℝ) / 2) = (k : ℝ) / 2 := by norm_num
  rw [ek] at hz hw
  set e : ℝ := (k : ℝ) / 2
  have hz' : ‖f z‖ ≤ C / z.im ^ e := by simpa using hz
  have hw' : ‖f w‖ ≤ C / w.im ^ e := by simpa using hw
  unfold PsiF
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_conj]
  set q := Complex.normSq ((z : ℂ) - conj (w : ℂ))
  have hq0 : 0 ≤ q := Complex.normSq_nonneg _
  have hn : ‖(z : ℂ) - conj (w : ℂ)‖ ^ k = q ^ e := by
    have hq : q = ‖(z : ℂ) - conj (w : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq _
    rw [hq, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast]
    congr 1; simp only [e]; push_cast; ring
  rw [hn]
  have hqe : 0 ≤ q ^ e := by positivity
  calc q ^ e * ‖f z‖ * ‖f w‖ ≤ q ^ e * (C / z.im ^ e) * (C / w.im ^ e) := by
        gcongr
    _ = C ^ 2 * (q ^ e / (z.im ^ e * w.im ^ e)) := by ring
    _ = C ^ 2 * (q / (z.im * w.im)) ^ e := by
        rw [Real.div_rpow hq0 (by positivity), Real.mul_rpow hzi.le hwi.le]

/-- **Diagonal horocycle coefficient of `Ψ_f`.** -/
theorem coeff_PsiF (f : CuspForm 𝒮ℒ (k : ℤ)) (h : ℕ) {y : ℝ} (hy : 0 < y) (ζ : ℍ) :
    ∫ x in (0 : ℝ)..1, PsiF f (hp hy x) (aff hy x ζ) * cexp (-2 * π * I * h * x) =
      ((y : ℂ) * (I - conj (ζ : ℂ))) ^ k * (Real.exp (-2 * π * h * y) : ℂ) *
        GhF f h (2 * π * y * (1 + I * conj (ζ : ℂ))) := by
  set a : ℕ → ℂ := fun n => coef f n
  have ha : ∀ n, (qExpansion 1 f).coeff n = a n := fun n => rfl
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
  set B := C / y ^ (((k : ℤ) : ℝ) / 2)
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
  set K : ℂ := ((y : ℂ) * (I - conj (ζ : ℂ))) ^ k
  have hPsi : ∀ x : ℝ, PsiF f (hp hy x) (aff hy x ζ) * cexp (-2 * π * I * h * x) =
      K * (f (hp hy x) * conj (f (aff hy x ζ)) * cexp (-2 * π * I * h * x)) := by
    intro x; unfold PsiF; rw [hzw]; ring
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
        (conj (a n) * a (n + h) * cexp (-(n : ℂ) * (2 * π * y * (1 + I * conj (ζ : ℂ))))) := by
    intro n
    have hcoef := ModularFormClass.qExpansion_coeff_eq_intervalIntegral f one_pos
      one_mem_strictPeriods_SL (n + h) hy
    rw [ha] at hcoef
    set c0 : ℂ := conj (a n) * cexp (-2 * π * I * n * y * conj (ζ : ℂ)) *
      Real.exp (-2 * π * (n + h) * y)
    have hpt : ∀ x : ℝ, Fn n x = c0 *
        (1 / 𝕢 1 ((x : ℂ) + y * I) ^ (n + h) * f (hp hy x)) := by
      intro x
      simp only [Fn, c0, E, map_mul, map_pow, qParam_one, aff_coe]
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
      linear_combination (conj (a n) * f (hp hy x)) * e3
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul]
    have : (∫ x in (0 : ℝ)..1, 1 / 𝕢 1 ((x : ℂ) + y * I) ^ (n + h) *
        f (hp hy x)) = a (n + h) := by
      rw [hcoef]; simp [hp]
    rw [this]
    simp only [c0]
    have : (Real.exp (-2 * π * (n + h) * y) : ℂ) =
        (Real.exp (-2 * π * h * y) : ℂ) * cexp (-2 * π * n * y) := by
      push_cast; rw [← Complex.exp_add]; congr 1; ring
    rw [this]
    have e2 : cexp (-2 * π * I * n * y * conj (ζ : ℂ)) * cexp (-2 * π * n * y) =
        cexp (-(n : ℂ) * (2 * π * y * (1 + I * conj (ζ : ℂ)))) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [← e2]
    ring
  simp_rw [hterm] at hDCT
  have key : (∫ x in (0 : ℝ)..1, f (hp hy x) * conj (f (aff hy x ζ)) *
      cexp (-2 * π * I * h * x)) = _ := hDCT.tsum_eq.symm
  rw [key, tsum_mul_left]
  simp only [GhF, K, a]
  ring

end RamanujanTau.SubconvexGeneral
