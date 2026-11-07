/-
# The diagonal horocycle coefficient of `Ψ_{a,b}`

With `w = x + yζ`:

    ∫₀¹ Ψ_{a,b}(x+iy, x+yζ) e(−ℓx) dx = (y(i − ζ̄))¹² e^{−2πℓy} G_{a,b,ℓ}(2πy(1 + iζ̄)),
    G_{a,b,ℓ}(W) = Σ_{n ≥ 0} τ(n) cA(a, bn+ℓ) e^{−bnW},

and `cA(a, bn+ℓ) = τ(m)` exactly when `am = bn + ℓ` (`m ≥ 0`), so `G` carries the two-sided
shifted sum `Σ_{am − bn = ℓ} τ(m)τ(n)`.
-/
import RamanujanTau.SCS2Coprime.Fourier

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open Complex ModularForm MeasureTheory
open UpperHalfPlane hiding I
open scoped MatrixGroups ComplexConjugate Real
open RamanujanTau.RankinSelberg RamanujanTau.SCSProof

local notation "𝕢" => Function.Periodic.qParam

/-- `G_{a,b,ℓ}(W) = Σ_n τ(n) cA(a, bn+ℓ) e^{−bnW}`. -/
noncomputable def GAB (a b : ℕ+) (ℓ : ℤ) (W : ℂ) : ℂ :=
  ∑' n : ℕ, ((tau n : ℤ) : ℂ) * cA a ((b : ℤ) * n + ℓ) * cexp (-((b : ℂ) * n) * W)

/-- **Diagonal horocycle coefficient of `Ψ_{a,b}`.** -/
theorem coeff_PsiAB (a b : ℕ+) (ℓ : ℤ) {y : ℝ} (hy : 0 < y) (ζ : ℍ) :
    ∫ x in (0 : ℝ)..1, PsiAB a b (hp hy x) (aff hy x ζ) * cexp (-2 * π * I * ℓ * x) =
      ((y : ℂ) * (I - conj (ζ : ℂ))) ^ 12 * (Real.exp (-2 * π * ℓ * y) : ℂ) *
        GAB a b ℓ (2 * π * y * (1 + I * conj (ζ : ℂ))) := by
  set f := (CuspForm.discriminant : CuspForm 𝒮ℒ 12)
  set t : ℕ → ℂ := fun n => ((tau n : ℤ) : ℂ)
  have ha : ∀ n, (qExpansion 1 f).coeff n = t n := fun n =>
    TauBound.qExpansion_discriminant_coeff_tau n
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL
  have hq : ∀ x : ℝ, HasSum (fun n => t n * 𝕢 1 ((scl b (aff hy x ζ) : ℍ) : ℂ) ^ n)
      (f (scl b (aff hy x ζ))) := by
    intro x
    have := hasSum_qExpansion one_pos hper (ModularFormClass.holo f)
      (ModularFormClass.bdd_at_infty f) (scl b (aff hy x ζ))
    simpa only [smul_eq_mul, ha] using this
  set r := Real.exp (-2 * π * (b * (y * ζ.im))) with hr
  have hnq : ∀ x : ℝ, ‖𝕢 1 ((scl b (aff hy x ζ) : ℍ) : ℂ)‖ = r := by
    intro x
    rw [norm_qParam_one, scl_coe, aff_coe]
    simp [hr, Complex.mul_im]
  have hsum : Summable (fun n => ‖t n‖ * r ^ n) := by
    have := (summable_norm_iff.mpr (hq 0).summable)
    refine this.congr fun n => ?_
    rw [norm_mul, norm_pow, hnq]
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  set B := C / (a * y) ^ (((12 : ℤ) : ℝ) / 2)
  have hB : ∀ x, ‖f (scl a (hp hy x))‖ ≤ B := fun x => by
    have := hC (scl a (hp hy x)); rwa [scl_im, hp_im] at this
  set E : ℝ → ℂ := fun x => cexp (-2 * π * I * ℓ * x)
  have hE : ∀ x : ℝ, ‖E x‖ = 1 := by
    intro x; simp only [E, Complex.norm_exp]; simp [Complex.mul_re]
  have hzw : ∀ x : ℝ, ((hp hy x : ℍ) : ℂ) - conj ((aff hy x ζ : ℍ) : ℂ) =
      (y : ℂ) * (I - conj (ζ : ℂ)) := by
    intro x
    rw [hp_coe, aff_coe]
    simp only [map_add, map_mul, Complex.conj_ofReal]
    ring
  set K : ℂ := ((y : ℂ) * (I - conj (ζ : ℂ))) ^ 12
  have hPsi : ∀ x : ℝ, PsiAB a b (hp hy x) (aff hy x ζ) * cexp (-2 * π * I * ℓ * x) =
      K * (f (scl a (hp hy x)) * conj (f (scl b (aff hy x ζ))) * cexp (-2 * π * I * ℓ * x)) := by
    intro x; unfold PsiAB; rw [hzw]; ring
  simp_rw [hPsi]
  rw [intervalIntegral.integral_const_mul]
  set Fn : ℕ → ℝ → ℂ := fun n x =>
    f (scl a (hp hy x)) * conj (t n * 𝕢 1 ((scl b (aff hy x ζ) : ℍ) : ℂ) ^ n) * E x
  have hcontf : Continuous (fun x : ℝ => f (scl a (hp hy x))) := by
    have h1 : Continuous fun x : ℝ => scl a (hp hy x) := by
      have : Continuous fun x : ℝ => ((scl a (hp hy x) : ℍ) : ℂ) := by
        show Continuous fun x : ℝ => (a : ℂ) * ((x : ℂ) + y * I); fun_prop
      exact continuous_induced_rng.2 this
    exact (ModularFormClass.holo f).continuous.comp h1
  have hcontq : Continuous (fun x : ℝ => 𝕢 1 ((scl b (aff hy x ζ) : ℍ) : ℂ)) := by
    show Continuous fun x : ℝ => 𝕢 1 ((b : ℂ) * ((x : ℂ) + y * (ζ : ℂ)))
    simp_rw [qParam_one]; fun_prop
  have hcontE : Continuous E := by
    show Continuous fun x : ℝ => cexp (-2 * π * I * ℓ * x); fun_prop
  have hDCT : HasSum (fun n => ∫ x in (0 : ℝ)..1, Fn n x)
      (∫ x in (0 : ℝ)..1, f (scl a (hp hy x)) * conj (f (scl b (aff hy x ζ))) * E x) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => B * (‖t n‖ * r ^ n)) (fun n => ?_) (fun n => ?_) ?_
      intervalIntegrable_const ?_
    · exact ((hcontf.mul (continuous_conj.comp
        (continuous_const.mul (hcontq.pow n)))).mul hcontE).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x _ => ?_
      simp only [Fn, norm_mul, Complex.norm_conj, norm_pow, hnq, hE, mul_one]
      gcongr
      exact hB x
    · exact Filter.Eventually.of_forall fun x _ => hsum.mul_left B
    · refine Filter.Eventually.of_forall fun x _ => ?_
      exact ((hasSum_conj'.mpr (hq x)).mul_left (f (scl a (hp hy x)))).mul_right _
  have hterm : ∀ n, ∫ x in (0 : ℝ)..1, Fn n x =
      (Real.exp (-2 * π * ℓ * y) : ℂ) *
        (t n * cA a ((b : ℤ) * n + ℓ) *
          cexp (-((b : ℂ) * n) * (2 * π * y * (1 + I * conj (ζ : ℂ))))) := by
    intro n
    have hfour := fourier_Delta_scl a ((b : ℤ) * n + ℓ) hy
    set c0 : ℂ := t n * cexp (-2 * π * I * (b * n) * y * conj (ζ : ℂ))
    have hpt : ∀ x : ℝ, Fn n x = c0 *
        (f (scl a (hp hy x)) * cexp (-2 * π * I * (((b : ℤ) * n + ℓ : ℤ) : ℂ) * x)) := by
      intro x
      simp only [Fn, c0, E, map_mul, map_pow, qParam_one, scl_coe, aff_coe]
      have hc : conj (t n) = t n := by simp [t]
      rw [hc, ← Complex.exp_conj, ← Complex.exp_nat_mul]
      simp only [map_mul, map_add, Complex.conj_ofReal, map_ofNat, Complex.conj_I, map_natCast]
      have e3 : cexp (↑n * (2 * ↑π * -I * ((b : ℂ) * (↑x + ↑y * conj (ζ : ℂ))))) *
          cexp (-2 * ↑π * I * ↑ℓ * ↑x) =
          cexp (-2 * π * I * (b * n) * y * conj (ζ : ℂ)) *
            cexp (-2 * π * I * (((b : ℤ) * n + ℓ : ℤ) : ℂ) * x) := by
        rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
      linear_combination (t n * f (scl a (hp hy x))) * e3
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, hfour]
    simp only [c0]
    have e4 : (Real.exp (-2 * π * (((b : ℤ) * n + ℓ : ℤ) : ℝ) * y) : ℂ) =
        (Real.exp (-2 * π * ℓ * y) : ℂ) * cexp (-2 * π * (b * n) * y) := by
      push_cast; rw [← Complex.exp_add]; congr 1; ring
    rw [e4]
    have e2 : cexp (-2 * π * I * (b * n) * y * conj (ζ : ℂ)) * cexp (-2 * π * (b * n) * y) =
        cexp (-((b : ℂ) * n) * (2 * π * y * (1 + I * conj (ζ : ℂ)))) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [← e2]
    ring
  simp_rw [hterm] at hDCT
  have key : (∫ x in (0 : ℝ)..1, f (scl a (hp hy x)) * conj (f (scl b (aff hy x ζ))) *
      cexp (-2 * π * I * ℓ * x)) = _ := hDCT.tsum_eq.symm
  rw [key, tsum_mul_left]
  simp only [GAB, K, t]
  ring

end RamanujanTau.SCS2Coprime
