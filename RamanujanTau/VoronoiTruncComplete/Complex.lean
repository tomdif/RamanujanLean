/-
# `VData` for the real and imaginary parts of the coefficients of any level-one cusp form

For `f ∈ S_k(SL₂(ℤ))`, `k = 2m`, with complex coefficients `c(n) = coef f n` and any `w ∈ ℂ`, the
real sequence `b(n) = Re(w c(n))` satisfies `VData m b`.  No basis of real forms is needed.

* `G f z = Σ c(n) e^{−2πnz} = f(iz)` satisfies `G(z) = (−1)^m z^{−2m} G(1/z)` (`G_modular`, the
  complex-coefficient form of `Dq_modular_cusp`).
* `Re c = (c + c̄)/2`, and `conj(e^{−2πn z̄}) = e^{−2πnz}`, so
  `D_b(z) = (wG(z) + conj(wG(z̄)))/2` (`Dq_re_eq`).  Because `z ↦ z̄` commutes with `z ↦ 1/z` and
  `(z̄)^{2m}` conjugates to `z^{2m}`, the relation for `G` gives the relation for `D_b`.
* Rankin: `b(n)² ≤ ‖w‖² ‖c(n)‖²`.

`w = 1` gives `Re c(n)` (`vdata_re`) and `w = −i` gives `Im c(n)` (`vdata_im`).
-/
import RamanujanTau.VoronoiTruncGeneral.Cusp

set_option autoImplicit false

namespace RamanujanTau.VoronoiTruncComplete

open Complex ModularForm Filter Set
open UpperHalfPlane hiding I
open RamanujanTau.HeckeConvexGeneral RamanujanTau.VoronoiTruncGeneral
open scoped MatrixGroups Real ComplexConjugate

variable {k : ℕ}

/-- `G(z) = Σ c(n) e^{−2πnz}` (`= f(iz)` for `Re z > 0`). -/
noncomputable def G (f : CuspForm 𝒮ℒ (k : ℤ)) (z : ℂ) : ℂ :=
  ∑' n : ℕ, coef f n * cexp (-2 * π * n * z)

lemma G_eq (f : CuspForm 𝒮ℒ (k : ℤ)) {z : ℂ} (hz : 0 < z.re) : G f z = f (ptz hz) :=
  (hasSum_coef_exp f hz).tsum_eq

/-- The modular relation for complex coefficients. -/
theorem G_modular {m : ℕ} (hk : k = 2 * m) (f : CuspForm 𝒮ℒ (k : ℤ)) {z : ℂ} (hz : 0 < z.re) :
    G f z = (-1 : ℂ) ^ m * ((z ^ (2 * m))⁻¹ * G f z⁻¹) := by
  subst hk
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  rw [G_eq f hz, G_eq f (re_inv_pos' hz), cusp_S f hz]
  have hI : (I * z) ^ (2 * m) = (-1 : ℂ) ^ m * z ^ (2 * m) := by
    rw [mul_pow, pow_mul, I_sq]
  rw [hI]
  have hz2 : z ^ (2 * m) ≠ 0 := pow_ne_zero _ hz0
  have h1 : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by rw [← mul_pow]; simp
  rw [show (-1 : ℂ) ^ m * ((z ^ (2 * m))⁻¹ * ((-1) ^ m * z ^ (2 * m) * f (ptz hz))) =
      ((-1) ^ m * (-1) ^ m) * ((z ^ (2 * m))⁻¹ * z ^ (2 * m)) * f (ptz hz) by ring, h1,
    inv_mul_cancel₀ hz2]
  ring

lemma conj_re_pos {z : ℂ} (hz : 0 < z.re) : 0 < (conj z).re := by simpa using hz

/-- `D_b(z) = (wG(z) + conj(wG(z̄)))/2` for `b(n) = Re(w c(n))`. -/
lemma Dq_re_eq (f : CuspForm 𝒮ℒ (k : ℤ)) (w : ℂ) {z : ℂ} (hz : 0 < z.re) :
    Dq (fun n => (w * coef f n).re) z = (w * G f z + conj (w * G f (conj z))) / 2 := by
  have h1 := (hasSum_coef_exp f hz).mul_left w
  have h2 := Complex.hasSum_conj'.2 ((hasSum_coef_exp f (conj_re_pos hz)).mul_left w)
  have h3 := (h1.add h2).div_const 2
  rw [← G_eq f hz, ← G_eq f (conj_re_pos hz)] at h3
  unfold Dq
  refine (h3.congr_fun fun n => ?_).tsum_eq
  have hre : (((w * coef f n).re : ℝ) : ℂ) = (w * coef f n + conj (w * coef f n)) / 2 := by
    rw [Complex.re_eq_add_conj]
  have hex : conj (cexp (-2 * π * n * conj z)) = cexp (-2 * π * n * z) := by
    rw [← Complex.exp_conj]; congr 1; simp [map_mul, map_neg, map_ofNat]
  rw [hre, ← mul_assoc w (coef f n) (cexp (-2 * π * n * conj z)),
    map_mul (starRingEnd ℂ) (w * coef f n) (cexp (-2 * π * n * conj z)), hex]
  ring

/-- **`VData` for `Re(w c(n))`.** -/
theorem vdata_re_mul {m : ℕ} (hk : k = 2 * m) (hm : 2 ≤ m) (f : CuspForm 𝒮ℒ (k : ℤ)) (w : ℂ) :
    VData m (fun n => (w * coef f n).re) where
  two_le := hm
  zero := by simp [coef_zero]
  modular := by
    intro z hz
    have hzi := re_inv_pos' hz
    rw [Dq_re_eq f w hz, Dq_re_eq f w hzi, G_modular hk f hz,
      G_modular hk f (conj_re_pos hz)]
    have e : (conj z)⁻¹ = conj (z⁻¹) := by rw [map_inv₀]
    rw [e]
    simp only [map_mul, map_pow, map_inv₀, map_neg, map_one, Complex.conj_conj]
    ring
  rankin := by
    obtain ⟨B, hB0, hB⟩ := exists_sum_sq_div_le f (by omega)
    refine ⟨‖w‖ ^ 2 * B, by positivity, fun N => ?_⟩
    have h := sum_sq_le f (by omega) hB N
    rw [← hk]
    have hle : ∀ n, (w * coef f n).re ^ 2 ≤ ‖w‖ ^ 2 * ‖coef f n‖ ^ 2 := fun n => by
      rw [← mul_pow, ← norm_mul, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
    calc ∑ n ∈ Finset.Icc 1 N, (w * coef f n).re ^ 2
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖w‖ ^ 2 * ‖coef f n‖ ^ 2 := Finset.sum_le_sum fun n _ => hle n
      _ = ‖w‖ ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖coef f n‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ‖w‖ ^ 2 * (B * (N : ℝ) ^ k) := by gcongr
      _ = ‖w‖ ^ 2 * B * (N : ℝ) ^ k := by ring

/-- `VData` for the real parts `Re c(n)` (no reality assumption on `f`). -/
theorem vdata_re {m : ℕ} (hk : k = 2 * m) (hm : 2 ≤ m) (f : CuspForm 𝒮ℒ (k : ℤ)) :
    VData m (fun n => (coef f n).re) := by
  have h := vdata_re_mul hk hm f 1
  simp only [one_mul] at h
  exact h

/-- `VData` for the imaginary parts `Im c(n)`. -/
theorem vdata_im {m : ℕ} (hk : k = 2 * m) (hm : 2 ≤ m) (f : CuspForm 𝒮ℒ (k : ℤ)) :
    VData m (fun n => (coef f n).im) := by
  have h := vdata_re_mul hk hm f (-I)
  have e : (fun n => (-I * coef f n).re) = fun n => (coef f n).im := by
    funext n; simp
  rw [e] at h
  exact h

/-- A cusp form all of whose coefficients vanish is zero. -/
theorem eq_zero_of_coef (f : CuspForm 𝒮ℒ (k : ℤ)) (h : ∀ n, coef f n = 0) : f = 0 := by
  refine CuspForm.ext fun t => ?_
  have hz : 0 < (-I * (t : ℂ)).re := by simpa using t.im_pos
  have hp : ptz hz = t := by
    apply UpperHalfPlane.ext
    show I * (-I * (t : ℂ)) = t
    rw [← mul_assoc, mul_neg, I_mul_I]; ring
  have hs := hasSum_coef_exp f hz
  simp only [h, zero_mul] at hs
  rw [hp] at hs
  rw [hs.unique hasSum_zero]
  rfl

end RamanujanTau.VoronoiTruncComplete
