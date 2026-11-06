/-
# Fourier coefficients of `Δ(az)` along a horizontal segment

* `integral_cexp_int`: `∫₀¹ e(kx) dx = [k = 0]` for `k ∈ ℤ`;
* **`fourier_Delta_scl`**: for `a ∈ ℕ⁺`, `N ∈ ℤ`, `y > 0`,
  `∫₀¹ Δ(a(x+iy)) e(−Nx) dx = cA a N · e^{−2πNy}`, where `cA a N = τ(N/a)` if `a ∣ N`, `N ≥ 0`,
  and `0` otherwise.
-/
import RamanujanTau.SCS2Coprime.TwoPointAB

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open Complex ModularForm MeasureTheory
open UpperHalfPlane hiding I
open scoped MatrixGroups ComplexConjugate Real
open RamanujanTau.RankinSelberg RamanujanTau.SCSProof

local notation "𝕢" => Function.Periodic.qParam

lemma integral_cexp_int (k : ℤ) :
    ∫ x in (0 : ℝ)..1, cexp (2 * π * I * k * x) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp
  · have hc : (2 * π * I * k : ℂ) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hπ, this, Complex.I_ne_zero]
    have := integral_exp_mul_complex (a := 0) (b := 1) hc
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero] at this
    rw [this]
    have h1 : cexp (2 * π * I * k) = 1 := by
      rw [show (2 * π * I * k : ℂ) = k * (2 * π * I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [h1]; simp

open Classical in
/-- `τ(N/a)` if `a ∣ N` and `N ≥ 0`, else `0`. -/
noncomputable def cA (a : ℕ+) (N : ℤ) : ℂ :=
  if (a : ℤ) ∣ N ∧ 0 ≤ N then ((tau (N / a).toNat : ℤ) : ℂ) else 0

/-- **Fourier coefficient of `Δ(a·)` on `Im z = y`.** -/
theorem fourier_Delta_scl (a : ℕ+) (N : ℤ) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..1, Δf (scl a (hp hy x)) * cexp (-2 * π * I * N * x) =
      cA a N * (Real.exp (-2 * π * N * y) : ℂ) := by
  set f := (CuspForm.discriminant : CuspForm 𝒮ℒ 12)
  set t : ℕ → ℂ := fun n => ((tau n : ℤ) : ℂ)
  have ha : ∀ n, (qExpansion 1 f).coeff n = t n := fun n =>
    TauBound.qExpansion_discriminant_coeff_tau n
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL
  have hq : ∀ x : ℝ, HasSum (fun m => t m * 𝕢 1 ((scl a (hp hy x) : ℍ) : ℂ) ^ m)
      (f (scl a (hp hy x))) := by
    intro x
    have := hasSum_qExpansion one_pos hper (ModularFormClass.holo f)
      (ModularFormClass.bdd_at_infty f) (scl a (hp hy x))
    simpa only [smul_eq_mul, ha] using this
  have hA : (0 : ℝ) < a := by exact_mod_cast a.pos
  set r := Real.exp (-2 * π * (a * y)) with hr
  have hnq : ∀ x : ℝ, ‖𝕢 1 ((scl a (hp hy x) : ℍ) : ℂ)‖ = r := by
    intro x
    rw [norm_qParam_one, scl_coe, hp_coe]
    simp [hr, Complex.mul_im]
  have hsum : Summable (fun m => ‖t m‖ * r ^ m) := by
    have := (summable_norm_iff.mpr (hq 0).summable)
    refine this.congr fun m => ?_
    rw [norm_mul, norm_pow, hnq]
  set E : ℝ → ℂ := fun x => cexp (-2 * π * I * N * x)
  have hE : ∀ x : ℝ, ‖E x‖ = 1 := by
    intro x; simp only [E, Complex.norm_exp]; simp [Complex.mul_re]
  set Fm : ℕ → ℝ → ℂ := fun m x => t m * 𝕢 1 ((scl a (hp hy x) : ℍ) : ℂ) ^ m * E x
  have hcontq : Continuous (fun x : ℝ => 𝕢 1 ((scl a (hp hy x) : ℍ) : ℂ)) := by
    show Continuous fun x : ℝ => 𝕢 1 ((a : ℂ) * ((x : ℂ) + y * I))
    simp_rw [qParam_one]; fun_prop
  have hcontE : Continuous E := by show Continuous fun x : ℝ => cexp (-2 * π * I * N * x); fun_prop
  have hDCT : HasSum (fun m => ∫ x in (0 : ℝ)..1, Fm m x)
      (∫ x in (0 : ℝ)..1, f (scl a (hp hy x)) * E x) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun m _ => ‖t m‖ * r ^ m) (fun m => ?_) (fun m => ?_) ?_ intervalIntegrable_const ?_
    · exact ((continuous_const.mul (hcontq.pow m)).mul hcontE).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x _ => ?_
      simp only [Fm, norm_mul, norm_pow, hnq, hE, mul_one, le_refl]
    · exact Filter.Eventually.of_forall fun x _ => hsum
    · exact Filter.Eventually.of_forall fun x _ => (hq x).mul_right _
  have hterm : ∀ m : ℕ, ∫ x in (0 : ℝ)..1, Fm m x =
      if (a : ℤ) * m = N then t m * (Real.exp (-2 * π * N * y) : ℂ) else 0 := by
    intro m
    have hpt : ∀ x : ℝ, Fm m x = t m * (Real.exp (-2 * π * (a * m) * y) : ℂ) *
        cexp (2 * π * I * (((a : ℤ) * m - N : ℤ) : ℂ) * x) := by
      intro x
      simp only [Fm, E, qParam_one, scl_coe, hp_coe]
      rw [← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
      have : (Real.exp (-2 * π * (a * m) * y) : ℂ) = cexp (-2 * π * (a * m) * y) := by
        push_cast; rfl
      rw [this, mul_assoc (t m) (cexp _), ← Complex.exp_add]
      congr 2
      push_cast
      linear_combination (2 * π * a * m * y : ℂ) * Complex.I_sq
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, integral_cexp_int]
    by_cases hm : (a : ℤ) * m = N
    · rw [if_pos (by rw [hm]; ring), if_pos hm, mul_one]
      congr 2
      rw [← hm]; push_cast; ring
    · rw [if_neg (by intro h; apply hm; linarith), if_neg hm, mul_zero]
  simp_rw [hterm] at hDCT
  rw [← hDCT.tsum_eq]
  -- the single surviving index
  by_cases hN : (a : ℤ) ∣ N ∧ 0 ≤ N
  · obtain ⟨⟨j, hj⟩, hN0⟩ := hN
    have hj0 : 0 ≤ j := by
      by_contra h
      push_neg at h
      have : (a : ℤ) * j < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast a.pos) h
      omega
    have hidx : ∀ m : ℕ, ((a : ℤ) * m = N ↔ m = j.toNat) := by
      intro m
      constructor
      · intro h
        have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast a.ne_zero
        have : (m : ℤ) = j := mul_left_cancel₀ ha0 (h.trans hj)
        omega
      · intro h; subst h; rw [hj, Int.toNat_of_nonneg hj0]
    simp_rw [hidx]
    rw [tsum_ite_eq]
    unfold cA
    rw [if_pos ⟨⟨j, hj⟩, hN0⟩]
    have : N / (a : ℤ) = j := by
      rw [hj]; exact Int.mul_ediv_cancel_left j (by exact_mod_cast a.ne_zero)
    rw [this]
  · have hz : ∀ m : ℕ, ¬ ((a : ℤ) * m = N) := by
      intro m h
      exact hN ⟨⟨m, h.symm⟩, by rw [← h]; positivity⟩
    simp_rw [hz, if_false, tsum_zero]
    unfold cA
    rw [if_neg hN, zero_mul]

end RamanujanTau.SCS2Coprime
