/-
# `VData` for every level-one cusp form with real coefficients

For `f ∈ S_k(SL₂(ℤ))`, `k = 2m`, with real q-expansion coefficients `a(n)`:

* `hasSum_Dq_cusp`: `Σ a(n) e^{−2πnz} = f(iz)` for `Re z > 0`;
* `Dq_modular_cusp`: `D(z) = (−1)^m z^{−2m} D(1/z)` (from `f(−1/τ) = τ^k f(τ)` at `τ = iz`:
  `(iz)^{−k} = i^{−2m} z^{−2m} = (−1)^m z^{−2m}`);
* `vdata_of_cusp`: the three hypotheses of `VData m a` (Rankin's bound from
  `HeckeConvexGeneral.sum_sq_le`).
-/
import RamanujanTau.VoronoiTruncGeneral.Data
import RamanujanTau.HeckeConvexGeneral.Main

set_option autoImplicit false

namespace RamanujanTau.VoronoiTruncGeneral

open Complex ModularForm Filter Set
open UpperHalfPlane hiding I
open RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups Real

local notation "𝕢" => Function.Periodic.qParam

variable {k : ℕ}

/-- The point `iz ∈ ℍ` for `Re z > 0`. -/
def ptz {z : ℂ} (hz : 0 < z.re) : ℍ := ⟨I * z, by simpa using hz⟩

lemma hasSum_coef_exp (f : CuspForm 𝒮ℒ (k : ℤ)) {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun n : ℕ => coef f n * cexp (-2 * π * n * z)) (f (ptz hz)) := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL
  have h := hasSum_qExpansion one_pos hper (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) (ptz hz)
  refine h.congr_fun fun n => ?_
  rw [smul_eq_mul]
  unfold coef
  congr 1
  have hq : 𝕢 1 ((ptz hz : ℍ) : ℂ) = cexp (-2 * π * z) := by
    unfold Function.Periodic.qParam
    congr 1
    show 2 * π * I * (I * z) / ((1 : ℝ) : ℂ) = _
    push_cast
    ring_nf
    rw [I_sq]; ring
  rw [hq, ← Complex.exp_nat_mul]
  congr 1; ring

lemma re_inv_pos' {z : ℂ} (hz : 0 < z.re) : 0 < (z⁻¹).re := by
  rw [inv_re]
  have : 0 < Complex.normSq z := Complex.normSq_pos.2 (by intro h; rw [h] at hz; simp at hz)
  positivity

/-- `f(i/z) = (iz)^k f(iz)`. -/
lemma cusp_S (f : CuspForm 𝒮ℒ (k : ℤ)) {z : ℂ} (hz : 0 < z.re) :
    f (ptz (re_inv_pos' hz)) = (I * z) ^ k * f (ptz hz) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hS : ModularGroup.S • ptz hz = ptz (re_inv_pos' hz) := by
    apply UpperHalfPlane.ext
    rw [modular_S_smul]
    show (-(I * z))⁻¹ = I * z⁻¹
    field_simp
    rw [I_sq]
  have h := SlashInvariantForm.slash_action_eqn'' (Γ := 𝒮ℒ) f
    (γ := Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S)
    (MonoidHom.mem_range.mpr ⟨ModularGroup.S, rfl⟩) (ptz hz)
  have hs : (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S) • ptz hz = ModularGroup.S • ptz hz :=
    rfl
  rw [hs, hS] at h
  rw [h]
  congr 1
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S) (ptz hz) = I * z := by
    simp [denom, ModularGroup.S, ptz]
  rw [hd, zpow_natCast]

/-- The modular relation for the coefficients of a cusp form of weight `2m`. -/
theorem Dq_modular_cusp {m : ℕ} (hk : k = 2 * m) (f : CuspForm 𝒮ℒ (k : ℤ)) {a : ℕ → ℝ}
    (ha : ∀ n, coef f n = (a n : ℂ)) {z : ℂ} (hz : 0 < z.re) :
    Dq a z = (-1 : ℂ) ^ m * ((z ^ (2 * m))⁻¹ * Dq a z⁻¹) := by
  subst hk
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hD : ∀ {w : ℂ} (hw : 0 < w.re), Dq a w = f (ptz hw) := by
    intro w hw
    unfold Dq
    simp_rw [← ha]
    exact (hasSum_coef_exp f hw).tsum_eq
  rw [hD hz, hD (re_inv_pos' hz), cusp_S f hz]
  have hI : (I * z) ^ (2 * m) = (-1 : ℂ) ^ m * z ^ (2 * m) := by
    rw [mul_pow, pow_mul, I_sq]
  rw [hI]
  have hz2 : z ^ (2 * m) ≠ 0 := pow_ne_zero _ hz0
  have h1 : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by rw [← mul_pow]; simp
  rw [show (-1 : ℂ) ^ m * ((z ^ (2 * m))⁻¹ * ((-1) ^ m * z ^ (2 * m) * f (ptz hz))) =
      ((-1) ^ m * (-1) ^ m) * ((z ^ (2 * m))⁻¹ * z ^ (2 * m)) * f (ptz hz) by ring, h1,
    inv_mul_cancel₀ hz2]
  ring

/-- **`VData` for a cusp form of weight `2m ≥ 4` with real coefficients.** -/
theorem vdata_of_cusp {m : ℕ} (hk : k = 2 * m) (hm : 2 ≤ m) (f : CuspForm 𝒮ℒ (k : ℤ)) {a : ℕ → ℝ}
    (ha : ∀ n, coef f n = (a n : ℂ)) : VData m a where
  two_le := hm
  zero := by
    have := coef_zero f
    rw [ha] at this; exact_mod_cast this
  modular := fun z hz => Dq_modular_cusp hk f ha hz
  rankin := by
    obtain ⟨B, hB0, hB⟩ := exists_sum_sq_div_le f (by omega)
    refine ⟨B, hB0, fun N => ?_⟩
    have h := sum_sq_le f (by omega) hB N
    rw [← hk]
    have e : ∀ n, ‖coef f n‖ ^ 2 = a n ^ 2 := fun n => by
      rw [ha, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp_rw [e] at h
    exact h

/-- Real coefficients from `Im a(n) = 0`. -/
lemma coef_eq_re (f : CuspForm 𝒮ℒ (k : ℤ)) (hreal : ∀ n, (coef f n).im = 0) (n : ℕ) :
    coef f n = (((coef f n).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [hreal n])

end RamanujanTau.VoronoiTruncGeneral
