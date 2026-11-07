import RamanujanTau.ThetaLift.HermiteIntegral
import RamanujanTau.ThetaLift.TaylorExtract
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Elementary bounds for the strip integral

A Gaussian bound for Hermite polynomials, the Appell expansion, integrability of `v^p exp(-β/v - γv)`,
and a bound for Gaussian sums over nonzero integers.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex Polynomial MeasureTheory Set
open scoped Real Nat

noncomputable section

/-- A monomial is dominated by a Gaussian. -/
lemma abs_pow_le_gauss (i : ℕ) (r : ℝ) :
    |r| ^ i ≤ (1 + 16 ^ i * (i ! : ℝ)) * Real.exp (r ^ 2 / 16) := by
  have h1 : 1 ≤ Real.exp (r ^ 2 / 16) := Real.one_le_exp (by positivity)
  have h2 : (r ^ 2 / 16) ^ i / (i ! : ℝ) ≤ Real.exp (r ^ 2 / 16) :=
    Real.pow_div_factorial_le_exp _ (by positivity) i
  have h3 : (r ^ 2) ^ i ≤ 16 ^ i * (i ! : ℝ) * Real.exp (r ^ 2 / 16) := by
    have hf : (0 : ℝ) < (i ! : ℝ) := by exact_mod_cast Nat.factorial_pos i
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h2
    linarith
  have h4 : |r| ^ i ≤ 1 + (r ^ 2) ^ i := by
    rcases le_total |r| 1 with h | h
    · have := pow_le_one₀ (abs_nonneg r) h (n := i)
      have : 0 ≤ (r ^ 2) ^ i := by positivity
      linarith
    · have h5 : |r| ≤ r ^ 2 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg r]
      have := pow_le_pow_left₀ (abs_nonneg r) h5 i
      linarith
  nlinarith

/-- **A Gaussian bound for an integer polynomial.** -/
theorem ev_gauss_bound (P : ℤ[X]) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |ev P r| ≤ C * Real.exp (r ^ 2 / 16) := by
  refine ⟨∑ i ∈ P.support, |(P.coeff i : ℝ)| * (1 + 16 ^ i * (i ! : ℝ)), by positivity, fun r => ?_⟩
  have h : ev P r = ∑ i ∈ P.support, (P.coeff i : ℝ) * r ^ i := by
    unfold ev
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def]
    simp
  rw [h, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_pow, mul_assoc]
  gcongr
  exact abs_pow_le_gauss i r

/-- **The Appell expansion of the Hermite polynomials.** -/
theorem hermite_appell (n : ℕ) (s t : ℂ) :
    aeval (s + t) (hermite n) = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℂ) * t ^ (n - k) * aeval s (hermite k) := by
  have hf : ContDiff ℂ n (fun τ : ℂ => cexp (t * τ)) := by fun_prop
  have hg : ContDiff ℂ n (fun τ : ℂ => cexp (s * τ - 1 ^ 2 * τ ^ 2 / 2)) := by fun_prop
  have hprod := iteratedDeriv_mul (x := (0 : ℂ)) (n := n) hf.contDiffAt hg.contDiffAt
  have hleft : (fun τ : ℂ => cexp (t * τ)) * (fun τ : ℂ => cexp (s * τ - 1 ^ 2 * τ ^ 2 / 2)) =
      fun τ => cexp ((s + t) * τ - 1 ^ 2 * τ ^ 2 / 2) := by
    funext τ
    simp only [Pi.mul_apply]
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hleft, iteratedDeriv_gauss _ 1 one_ne_zero] at hprod
  simp only [one_pow, one_mul, mul_zero, div_one, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div, Complex.exp_zero, mul_one] at hprod
  rw [hprod, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hexp : iteratedDeriv (n + 1 - 1 - i) (fun τ : ℂ => cexp (t * τ)) 0 = t ^ (n - i) := by
    have h := iteratedDeriv_exp_lin t 0 (n - i) 0
    simp only [add_zero, mul_zero, Complex.exp_zero, mul_one] at h
    simp [h]
  have hgauss := iteratedDeriv_gauss s 1 one_ne_zero (n - (n + 1 - 1 - i)) 0
  simp only [one_pow, one_mul, mul_zero, sub_zero, div_one, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div, Complex.exp_zero, mul_one] at hgauss
  have hnk : n - (n + 1 - 1 - i) = i := by omega
  rw [hexp, hgauss, hnk]
  rw [show n + 1 - 1 - i = n - i by omega, Nat.choose_symm hi']

/-- **Integrability of `v^p exp(-β/v - γv)`.** -/
theorem integrableOn_rpow_exp (p : ℝ) {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) :
    IntegrableOn (fun v : ℝ => v ^ p * Real.exp (-(β / v) - γ * v)) (Ioi 0) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-1 - p)
  have hs : -1 < p + n := by linarith
  have hI := (integrableOn_rpow_mul_exp_neg_mul_rpow hs (le_refl 1) hγ).const_mul
    ((n ! : ℝ) / β ^ n)
  refine Integrable.mono' hI ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro v hv
    have hv' : v ≠ 0 := (mem_Ioi.mp hv).ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := simp [hv'])
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv' : 0 < v := hv
    have hf : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have h1 : (β / v) ^ n / (n ! : ℝ) ≤ Real.exp (β / v) :=
      Real.pow_div_factorial_le_exp _ (by positivity) n
    have h2 : Real.exp (-(β / v)) ≤ (n ! : ℝ) / β ^ n * v ^ n := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
      refine le_trans (le_of_eq ?_) h1
      rw [div_pow]
      field_simp
    have e : Real.exp (-(β / v) - γ * v) = Real.exp (-(β / v)) * Real.exp (-(γ * v)) := by
      rw [sub_eq_add_neg, Real.exp_add]
    rw [Real.norm_of_nonneg (by positivity), e, Real.rpow_add hv', Real.rpow_natCast, Real.rpow_one,
      neg_mul]
    have hp : 0 ≤ v ^ p := by positivity
    calc _ ≤ v ^ p * (((n ! : ℝ) / β ^ n * v ^ n) * Real.exp (-(γ * v))) := by gcongr
      _ = _ := by ring

/-- **A Gaussian sum over nonzero integers.** -/
theorem gauss_ne_zero_bound {a : ℝ} (ha : 0 < a) :
    Summable (fun x : ℤ => if x = 0 then (0 : ℝ) else Real.exp (-a * (x : ℝ) ^ 2)) ∧
      ∑' x : ℤ, (if x = 0 then (0 : ℝ) else Real.exp (-a * (x : ℝ) ^ 2)) ≤ 2 / a := by
  set f0 : ℤ → ℝ := fun x => if x = 0 then (0 : ℝ) else Real.exp (-a * (x : ℝ) ^ 2) with hf0
  have hr0 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo := (summable_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-a))
  have hle : ∀ n : ℕ, Real.exp (-a * ((n : ℝ) + 1) ^ 2) ≤ Real.exp (-a) * Real.exp (-a) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg ha.le hn, mul_nonneg ha.le (mul_nonneg hn hn)]
  have hS : Summable fun n : ℕ => Real.exp (-a * ((n : ℝ) + 1) ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hle hgeo
  have hval : ∑' n : ℕ, Real.exp (-a * ((n : ℝ) + 1) ^ 2) ≤ 1 / a := by
    refine (hS.tsum_le_tsum hle hgeo).trans ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    have h1 : a + 1 ≤ Real.exp a := Real.add_one_le_exp a
    have h2 : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
    rw [div_eq_mul_inv, ← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by linarith) ha]
    nlinarith [Real.exp_pos a, Real.exp_pos (-a)]
  set S := ∑' n : ℕ, Real.exp (-a * ((n : ℝ) + 1) ^ 2) with hSdef
  have hneg : HasSum (fun n : ℕ => f0 (-((n : ℤ) + 1))) S := by
    have e : (fun n : ℕ => f0 (-((n : ℤ) + 1))) = fun n : ℕ => Real.exp (-a * ((n : ℝ) + 1) ^ 2) := by
      funext n
      have hne : (-((n : ℤ) + 1)) ≠ 0 := by omega
      simp only [hf0, if_neg hne]
      push_cast
      congr 2
      ring
    rw [e]
    exact hS.hasSum
  have hpos : HasSum (fun n : ℕ => f0 (n : ℤ)) S := by
    have e : (fun n : ℕ => f0 ((n + 1 : ℕ) : ℤ)) = fun n : ℕ => Real.exp (-a * ((n : ℝ) + 1) ^ 2) := by
      funext n
      have hne : ((n + 1 : ℕ) : ℤ) ≠ 0 := by omega
      simp only [hf0, if_neg hne]
      push_cast
      rfl
    have h1 : HasSum (fun n : ℕ => f0 ((n + 1 : ℕ) : ℤ)) S := by
      rw [e]
      exact hS.hasSum
    have h2 := (hasSum_nat_add_iff (f := fun n : ℕ => f0 (n : ℤ)) 1).mp h1
    simpa [hf0] using h2
  have hall := HasSum.of_nat_of_neg_add_one hpos hneg
  refine ⟨hall.summable, ?_⟩
  rw [hall.tsum_eq]
  have : (2 : ℝ) / a = 1 / a + 1 / a := by ring
  linarith

end

end RamanujanTau.ThetaLift
