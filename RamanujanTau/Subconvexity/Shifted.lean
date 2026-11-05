/-
# Horocycle Fourier coefficients of `y¹²|Δ|²` are shifted convolution sums

For `h ∈ ℕ` and `y > 0` (`r = e^{−2πy}`, `q = 𝕢(x+iy)`):

    ∫₀¹ Δ(x+iy) · conj Δ(x+iy) · q^{−h} dx = ∑ₙ τ(n) τ(n+h) r^{2n},

i.e. (since `q^{−h} = e^{2πhy} e(−hx)`)
`∫₀¹ |Δ(x+iy)|² e(−hx) dx = ∑ₙ τ(n)τ(n+h) e^{−2π(2n+h)y}`.  This is `RankinSelberg`'s Parseval
identity (`h = 0`) off the diagonal: the `h`-th Fourier coefficient of the `Γ`-invariant function
`y¹²|Δ(z)|²` along the horocycle `Im z = y` is the shifted convolution sum `D_h`.  It is the
precise statement behind route (b) of `docs/SUBCONVEXITY.md`: localizing the critical-line mean
square to windows of length `H < T` needs nontrivial bounds for these `h ≠ 0` coefficients, which
the `h = 0` (Rankin–Selberg / Zagier) asymptotics used by `CriticalMeanSquareAsymp` do not give.
-/
import RamanujanTau.Subconvexity.Wilton

set_option autoImplicit false

namespace RamanujanTau.Subconvexity

open Complex ModularForm MeasureTheory
open UpperHalfPlane hiding I
open scoped MatrixGroups ComplexConjugate Real
open RamanujanTau.RankinSelberg RamanujanTau.TauSigns

local notation "𝕢" => Function.Periodic.qParam

/-- **Shifted Parseval identity on a horocycle**:
`∑ₙ τ(n)τ(n+h) e^{−4πny} = ∫₀¹ Δ(x+iy) conj Δ(x+iy) 𝕢(x+iy)^{−h} dx`. -/
theorem hasSum_shifted_parseval (h : ℕ) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => ((tau n * tau (n + h) : ℤ) : ℂ) * ((Real.exp (-2 * π * y) ^ (2 * n) : ℝ) : ℂ))
      (∫ x in (0 : ℝ)..1, Δf (hp hy x) * conj (Δf (hp hy x)) *
        (1 / 𝕢 1 ((x : ℂ) + y * I)) ^ h) := by
  set f := (CuspForm.discriminant : CuspForm 𝒮ℒ 12)
  set r := Real.exp (-2 * π * y) with hr
  set a : ℕ → ℂ := fun n => ((tau n : ℤ) : ℂ)
  have ha : ∀ n, (qExpansion 1 f).coeff n = a n := fun n =>
    TauBound.qExpansion_discriminant_coeff_tau n
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL
  have hq : ∀ x : ℝ, HasSum (fun n => a n * 𝕢 1 ((x : ℂ) + y * I) ^ n) (f (hp hy x)) := by
    intro x
    have := hasSum_qExpansion one_pos hper (ModularFormClass.holo f)
      (ModularFormClass.bdd_at_infty f) (hp hy x)
    simp only [smul_eq_mul, ha] at this
    simpa [hp_coe] using this
  have hsum : Summable (fun n => ‖a n‖ * r ^ n) := by
    have := (summable_norm_iff.mpr (hq 0).summable)
    refine this.congr fun n => ?_
    rw [norm_mul, norm_pow, norm_qParam_hp]
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  set B := C / y ^ (((12 : ℤ) : ℝ) / 2)
  have hB : ∀ x, ‖f (hp hy x)‖ ≤ B := fun x => by
    have := hC (hp hy x); rwa [hp_im] at this
  set E : ℝ := Real.exp (2 * π * y) ^ h
  have hE : ∀ x : ℝ, ‖(1 / 𝕢 1 ((x : ℂ) + y * I)) ^ h‖ = E := by
    intro x; rw [norm_pow, norm_inv_qParam]
  set Fn : ℕ → ℝ → ℂ := fun n x =>
    f (hp hy x) * conj (a n * 𝕢 1 ((x : ℂ) + y * I) ^ n) * (1 / 𝕢 1 ((x : ℂ) + y * I)) ^ h
  have hcontf : Continuous (fun x : ℝ => f (hp hy x)) :=
    (ModularFormClass.holo f).continuous.comp (continuous_hp hy)
  have hcontq : Continuous (fun x : ℝ => 𝕢 1 ((x : ℂ) + y * I)) := by
    unfold Function.Periodic.qParam; fun_prop
  have hcontw : Continuous (fun x : ℝ => 1 / 𝕢 1 ((x : ℂ) + y * I)) :=
    continuous_const.div hcontq fun x => Complex.exp_ne_zero _
  have hDCT : HasSum (fun n => ∫ x in (0 : ℝ)..1, Fn n x)
      (∫ x in (0 : ℝ)..1, f (hp hy x) * conj (f (hp hy x)) *
        (1 / 𝕢 1 ((x : ℂ) + y * I)) ^ h) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => B * (‖a n‖ * r ^ n) * E) (fun n => ?_) (fun n => ?_) ?_
      intervalIntegrable_const ?_
    · exact ((hcontf.mul (continuous_conj.comp
        (continuous_const.mul (hcontq.pow n)))).mul (hcontw.pow h)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x _ => ?_
      simp only [Fn, norm_mul, Complex.norm_conj, norm_pow, norm_qParam_hp]
      rw [← norm_pow, hE x]
      gcongr
      exact hB x
    · exact Filter.Eventually.of_forall fun x _ => (hsum.mul_left B).mul_right E
    · refine Filter.Eventually.of_forall fun x _ => ?_
      exact ((hasSum_conj'.mpr (hq x)).mul_left (f (hp hy x))).mul_right _
  have hterm : ∀ n, ∫ x in (0 : ℝ)..1, Fn n x =
      ((tau n * tau (n + h) : ℤ) : ℂ) * ((r ^ (2 * n) : ℝ) : ℂ) := by
    intro n
    have hcoef := ModularFormClass.qExpansion_coeff_eq_intervalIntegral f one_pos
      one_mem_strictPeriods_SL (n + h) hy
    rw [ha] at hcoef
    have hpt : ∀ x : ℝ, Fn n x = (conj (a n) * ((r ^ (2 * n) : ℝ) : ℂ)) *
        (1 / 𝕢 1 ((x : ℂ) + y * I) ^ (n + h) * f ⟨(x : ℂ) + y * I, by simpa using hy⟩) := by
      intro x
      simp only [Fn, map_mul, conj_qParam_pow x n]
      rw [← hr]; simp only [hp]
      rw [pow_add]
      ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul]
    have : (∫ x in (0 : ℝ)..1, 1 / 𝕢 1 ((x : ℂ) + y * I) ^ (n + h) *
        f ⟨(x : ℂ) + y * I, by simpa using hy⟩) = a (n + h) := by
      rw [hcoef]; simp
    rw [this]
    have hc : conj (a n) = a n := by simp [a]
    rw [hc]
    simp only [a]
    push_cast
    ring
  simp_rw [hterm] at hDCT
  simpa [hr] using hDCT

end RamanujanTau.Subconvexity
