/-
# The theta function of the lattice `ℤ + ℤz` and its transformation law

For `z = x + iy` (`y > 0`) put `Q(m,n) = |mz + n|²/y = (n + mx)²/y + m²y` and
`Θ(t) = ∑_{(m,n) ∈ ℤ²} exp(−π t Q(m,n))`. Then (`theta_inv`)

    Θ(1/t) = t · Θ(t)        (t > 0),

by Poisson summation (`Complex.tsum_exp_neg_quadratic`) in `n`, then in `m`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Complex Real Filter Topology

/-- `Q(m,n) = (n + m x)²/y + m² y`. -/
noncomputable def Qf (x y : ℝ) (p : ℤ × ℤ) : ℝ := (p.2 + p.1 * x) ^ 2 / y + p.1 ^ 2 * y

/-- `Θ(t) = ∑ exp(−π t Q)`. -/
noncomputable def theta (x y t : ℝ) : ℝ := ∑' p : ℤ × ℤ, rexp (-π * t * Qf x y p)

lemma summable_gauss {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Summable fun n : ℤ => rexp (-π * a * (n + c) ^ 2) := by
  have h := (summable_jacobiTheta₂_term_iff ((a * c : ℝ) * I) ((a : ℂ) * I)).2 (by simpa using ha)
  have h2 := h.norm.mul_right (rexp (-(π * a * c ^ 2)))
  refine h2.congr fun n => ?_
  rw [norm_jacobiTheta₂_term, ← Real.exp_add]
  congr 1
  simp
  ring

/-- Poisson summation for a shifted Gaussian. -/
lemma poisson_shift {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ((∑' n : ℤ, rexp (-π * a * (n + c) ^ 2) : ℝ) : ℂ) =
      ((a ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑' k : ℤ, ((rexp (-π * k ^ 2 / a) : ℝ) : ℂ) * cexp (2 * π * I * k * c) := by
  have haC : 0 < (a : ℂ).re := by simpa using ha
  have h := Complex.tsum_exp_neg_quadratic haC (-(a : ℂ) * c)
  rw [Complex.ofReal_tsum]
  have e1 : ∀ n : ℤ, ((rexp (-π * a * (n + c) ^ 2) : ℝ) : ℂ) =
      cexp (-π * a * c ^ 2) * cexp (-π * a * n ^ 2 + 2 * π * (-(a : ℂ) * c) * n) := by
    intro n
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  simp_rw [e1]
  rw [tsum_mul_left, h, ← mul_assoc, mul_comm (cexp _), mul_assoc, ← tsum_mul_left]
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  congr 1
  · rw [one_div, Real.rpow_neg ha.le, Complex.ofReal_inv, Complex.ofReal_cpow ha.le]
    norm_num
  · congr 1; funext k
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring

lemma tsum_gauss_le {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∑' n : ℤ, rexp (-π * a * (n + c) ^ 2) ≤
      a ^ (-(1 / 2 : ℝ)) * ∑' k : ℤ, rexp (-π * (k : ℝ) ^ 2 / a) := by
  have h := congrArg norm (poisson_shift ha c)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ => (Real.exp_pos _).le),
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
  rw [h]
  gcongr
  have hs : Summable fun k : ℤ => rexp (-π * (k : ℝ) ^ 2 / a) := by
    have := summable_gauss (a := 1 / a) (by positivity) 0
    refine this.congr fun k => ?_
    congr 1; ring
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · refine hs.congr fun k => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [show (2 * π * I * k * c : ℂ) = ((2 * π * k * c : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  · congr 1; funext k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [show (2 * π * I * k * c : ℂ) = ((2 * π * k * c : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]

lemma theta_term (x : ℝ) {y : ℝ} (hy : y ≠ 0) (t : ℝ) (p : ℤ × ℤ) :
    rexp (-π * t * Qf x y p) =
      rexp (-π * (t * y) * ((p.1 : ℝ) + 0) ^ 2) * rexp (-π * (t / y) * ((p.2 : ℝ) + p.1 * x) ^ 2) := by
  rw [← Real.exp_add]; congr 1; unfold Qf; field_simp; ring

lemma summable_gauss0 {a : ℝ} (ha : 0 < a) : Summable fun n : ℤ => rexp (-π * a * ((n : ℝ) + 0) ^ 2) :=
  summable_gauss ha 0

lemma summable_theta (x : ℝ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    Summable fun p : ℤ × ℤ => rexp (-π * t * Qf x y p) := by
  have hf : 0 ≤ fun p : ℤ × ℤ => rexp (-π * t * Qf x y p) := fun p => (Real.exp_pos _).le
  refine (summable_prod_of_nonneg hf).2 ⟨fun m => ?_, ?_⟩
  · simp_rw [theta_term x hy.ne' t]
    exact (summable_gauss (by positivity) _).mul_left _
  · simp_rw [theta_term x hy.ne' t, tsum_mul_left]
    have hb : ∀ m : ℤ, ∑' n : ℤ, rexp (-π * (t / y) * ((n : ℝ) + m * x) ^ 2) ≤
        (t / y) ^ (-(1 / 2 : ℝ)) * ∑' k : ℤ, rexp (-π * (k : ℝ) ^ 2 / (t / y)) :=
      fun m => tsum_gauss_le (by positivity) _
    refine ((summable_gauss0 (a := t * y) (by positivity)).mul_right
      ((t / y) ^ (-(1 / 2 : ℝ)) * ∑' k : ℤ, rexp (-π * (k : ℝ) ^ 2 / (t / y)))).of_nonneg_of_le
      (fun m => mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun _ => (Real.exp_pos _).le))
      (fun m => mul_le_mul_of_nonneg_left (hb m) (Real.exp_pos _).le)

lemma theta_eq_iter (x : ℝ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    theta x y t = ∑' m : ℤ, rexp (-π * (t * y) * ((m : ℝ) + 0) ^ 2) *
      ∑' n : ℤ, rexp (-π * (t / y) * ((n : ℝ) + m * x) ^ 2) := by
  unfold theta
  rw [(summable_theta x hy ht).tsum_prod]
  congr 1; funext m
  simp_rw [theta_term x hy.ne' t, tsum_mul_left]

lemma norm_cexp_phase (r : ℝ) : ‖cexp (2 * π * I * r)‖ = 1 := by
  rw [show (2 * π * I * r : ℂ) = ((2 * π * r : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- **Transformation law** `Θ(1/t) = t Θ(t)`. -/
theorem theta_inv (x : ℝ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    theta x y (1 / t) = t * theta x y t := by
  have ht' : 0 < 1 / t := by positivity
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = t * y := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = y / t := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  -- step 1: Poisson in `n`
  have s1 : ((theta x y t : ℝ) : ℂ) = ((t / y) ^ (-(1 / 2 : ℝ)) : ℝ) *
      ∑' m : ℤ, ∑' k : ℤ, (((rexp (-π * a * ((m : ℝ) + 0) ^ 2)) * rexp (-π * b * ((k : ℝ) + 0) ^ 2) : ℝ) : ℂ) *
        cexp (2 * π * I * k * (m * x : ℝ)) := by
    rw [theta_eq_iter x hy ht]
    simp only [← ha]
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
    congr 1; funext m
    rw [Complex.ofReal_mul, poisson_shift (a := t / y) (by positivity) (m * x), ← mul_assoc,
      mul_comm _ ((((t / y) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ), mul_assoc, ← tsum_mul_left]
    congr 1; congr 1; funext k
    have : -π * (k : ℝ) ^ 2 / (t / y) = -π * b * ((k : ℝ) + 0) ^ 2 := by
      rw [hb, add_zero]; field_simp
    rw [this]; push_cast; ring
  -- step 2: swap the sums
  have hsumm : Summable (Function.uncurry fun (m k : ℤ) =>
      (((rexp (-π * a * ((m : ℝ) + 0) ^ 2)) * rexp (-π * b * ((k : ℝ) + 0) ^ 2) : ℝ) : ℂ) *
        cexp (2 * π * I * k * (m * x : ℝ))) := by
    have hA := summable_gauss0 ha0
    have hB := summable_gauss0 hb0
    have hprod := summable_mul_of_summable_norm (f := fun m : ℤ => rexp (-π * a * ((m : ℝ) + 0) ^ 2))
      (g := fun k : ℤ => rexp (-π * b * ((k : ℝ) + 0) ^ 2))
      (by simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hA)
      (by simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hB)
    refine Summable.of_norm_bounded hprod (fun p => ?_)
    simp only [Function.uncurry, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    rw [show (2 * π * I * (p.2 : ℂ) * ((p.1 * x : ℝ) : ℂ)) = 2 * π * I * ((p.2 * (p.1 * x) : ℝ) : ℂ)
      by push_cast; ring, norm_cexp_phase, mul_one]
  rw [← hsumm.tsum_comm] at s1
  -- step 3: Poisson in `m`
  have hpq : ((((1 / a) ^ (1 / 2 : ℝ)) : ℝ) : ℂ) * ((((1 / a) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]; norm_num
  have s3 : ∀ k : ℤ, ∑' m : ℤ, (((rexp (-π * a * ((m : ℝ) + 0) ^ 2)) *
      rexp (-π * b * ((k : ℝ) + 0) ^ 2) : ℝ) : ℂ) * cexp (2 * π * I * k * (m * x : ℝ)) =
      ((rexp (-π * b * ((k : ℝ) + 0) ^ 2) : ℝ) : ℂ) * ((((1 / a) ^ (1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((∑' n : ℤ, rexp (-π * (1 / a) * ((n : ℝ) + k * x) ^ 2) : ℝ) : ℂ) := by
    intro k
    rw [poisson_shift (a := 1 / a) (by positivity) (k * x)]
    set S : ℂ := ∑' j : ℤ, ((rexp (-π * j ^ 2 / (1 / a)) : ℝ) : ℂ) * cexp (2 * π * I * j * (k * x : ℝ))
    set E : ℂ := ((rexp (-π * b * ((k : ℝ) + 0) ^ 2) : ℝ) : ℂ)
    have hL : ∑' m : ℤ, (((rexp (-π * a * ((m : ℝ) + 0) ^ 2)) *
        rexp (-π * b * ((k : ℝ) + 0) ^ 2) : ℝ) : ℂ) * cexp (2 * π * I * k * (m * x : ℝ)) = E * S := by
      rw [← tsum_mul_left]
      congr 1; funext m
      have e : -π * (m : ℝ) ^ 2 / (1 / a) = -π * a * ((m : ℝ) + 0) ^ 2 := by
        rw [add_zero]; field_simp
      rw [e, Complex.ofReal_mul]
      have : (2 * π * I * (k : ℂ) * ((m * x : ℝ) : ℂ)) = 2 * π * I * (m : ℂ) * ((k * x : ℝ) : ℂ) := by
        push_cast; ring
      rw [this]; ring
    rw [hL]
    linear_combination (-(E * S)) * hpq
  simp_rw [s3] at s1
  -- step 4: recognise `Θ(1/t)`
  have s4 := theta_eq_iter x hy ht'
  have e1 : 1 / t * y = b := by rw [hb]; ring
  have e2 : 1 / t / y = 1 / a := by rw [ha]; field_simp
  simp only [e1, e2] at s4
  have hc : ((t / y) ^ (-(1 / 2 : ℝ)) * (1 / a) ^ (1 / 2 : ℝ) : ℝ) = 1 / t := by
    rw [ha, Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), ← Real.mul_rpow
      (by positivity) (by positivity)]
    rw [show (t / y)⁻¹ * (1 / (t * y)) = (1 / t) ^ 2 by field_simp]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have : ((theta x y t : ℝ) : ℂ) = ((1 / t * theta x y (1 / t) : ℝ) : ℂ) := by
    rw [s1, s4, ← hc, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_tsum, mul_assoc,
      ← tsum_mul_left, ← tsum_mul_left]
    rw [← tsum_mul_left]
    congr 1; funext k
    push_cast; ring
  have h2 := Complex.ofReal_injective this
  rw [h2]; field_simp

end RamanujanTau.RankinError
