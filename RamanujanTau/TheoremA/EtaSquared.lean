import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Tactic

/-!
# Exact transformations of eta squared

Using eta squared makes the weight integral. Words in S and integer powers
of T carry an exact twelfth-root multiplier, avoiding square-root branch
calculations for each proposed even-exponent eta quotient.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open Complex hiding eta
open ModularForm ModularGroup
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Real
local notation "𝕢" => Function.Periodic.qParam

noncomputable def etaSquared (z : ℍ) : ℂ := eta z ^ 2
noncomputable def phase (n : ℤ) : ℂ := Complex.exp (π * I * n / 6)

lemma phase_zero : phase 0 = 1 := by simp [phase]

lemma phase_add (a b : ℤ) : phase (a + b) = phase a * phase b := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma phase_eq_one_of_dvd {n : ℤ} (hn : 12 ∣ n) : phase n = 1 := by
  obtain ⟨m, rfl⟩ := hn
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I m using 1
  congr 1
  push_cast
  ring

lemma qParam_add_int (z : ℂ) (n : ℤ) : 𝕢 1 (z + n) = 𝕢 1 z := by
  unfold Function.Periodic.qParam
  norm_num only [Complex.ofReal_one]
  rw [div_one, div_one, mul_add, Complex.exp_add,
    show 2 * (π : ℂ) * I * n = n * (2 * π * I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma eta_add_int (z : ℂ) (n : ℤ) :
    eta (z + n) = Complex.exp (π * I * n / 12) * eta z := by
  unfold eta
  simp only [eta_q, qParam_add_int]
  have hq : 𝕢 24 (z + n) = Complex.exp (π * I * n / 12) * 𝕢 24 z := by
    unfold Function.Periodic.qParam
    rw [← Complex.exp_add]
    congr 1
    norm_num
    ring
  rw [hq, mul_assoc]

lemma sqrt_sq_of_ne_zero {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ^ 2 = z := by
  simp only [Complex.sqrt]
  rw [sq, ← Complex.cpow_add _ _ hz]
  norm_num

theorem slash_S : etaSquared ∣[(1 : ℤ)] S = phase (-3) • etaSquared := by
  have hp : phase (-3) = -I := by
    unfold phase
    rw [show (π : ℂ) * I * (-3 : ℤ) / 6 = -π / 2 * I by push_cast; ring]
    exact Complex.exp_neg_pi_div_two_mul_I
  ext z
  have he : eta (-(z : ℂ)⁻¹) = (Complex.sqrt I)⁻¹ * (Complex.sqrt z * eta z) := by
    simpa [neg_div] using eta_comp_eq_csqrt_I_inv z.im_pos
  rw [SL_slash_apply, hp]
  simp only [etaSquared, modular_S_smul, inv_neg, he, mul_pow, inv_pow,
    sqrt_sq_of_ne_zero I_ne_zero, sqrt_sq_of_ne_zero z.ne_zero,
    ModularGroup.denom_S, zpow_neg_one, Pi.smul_apply, smul_eq_mul]
  rw [inv_I]
  field_simp [z.ne_zero]

theorem slash_T_zpow (n : ℤ) :
    etaSquared ∣[(1 : ℤ)] (T ^ n : SL(2, ℤ)) = phase n • etaSquared := by
  ext z
  have hp : Complex.exp (π * I * n / 12) ^ 2 = phase n := by
    rw [← Complex.exp_nat_mul]
    unfold phase
    congr 1
    norm_num
    ring
  rw [SL_slash_apply]
  change eta (↑((T ^ n : SL(2, ℤ)) • z) : ℂ) ^ 2 * denom (T ^ n : SL(2, ℤ)) z ^ (-1 : ℤ) =
    phase n * eta z ^ 2
  rw [coe_T_zpow_smul_eq, eta_add_int, mul_pow, hp]
  have hd : denom (T ^ n : SL(2, ℤ)) z = 1 := by simp [denom, coe_T_zpow, -map_zpow]
  rw [hd]
  simp

inductive Step where
  | s
  | t (n : ℤ)
  deriving DecidableEq

def Step.matrix : Step → SL(2, ℤ)
  | .s => S
  | .t n => T ^ n

def Step.exponent : Step → ℤ
  | .s => -3
  | .t n => n

def wordMatrix (w : List Step) : SL(2, ℤ) := (w.map Step.matrix).prod
def wordExponent (w : List Step) : ℤ := (w.map Step.exponent).sum

theorem slash_step (a : Step) : etaSquared ∣[(1 : ℤ)] a.matrix = phase a.exponent • etaSquared := by
  cases a
  · exact slash_S
  · exact slash_T_zpow _

/-- A word certificate gives the exact multiplier on the actual eta function. -/
theorem slash_word (w : List Step) :
    etaSquared ∣[(1 : ℤ)] wordMatrix w = phase (wordExponent w) • etaSquared := by
  induction w with
  | nil => simp [wordMatrix, wordExponent, phase_zero]
  | cons a w ih =>
    simp only [wordMatrix, List.map_cons, List.prod_cons, wordExponent, List.sum_cons]
    rw [SlashAction.slash_mul, slash_step, SL_smul_slash]
    change phase a.exponent • (etaSquared ∣[(1 : ℤ)] wordMatrix w) = _
    rw [ih, smul_smul, ← phase_add]
    rfl

end RamanujanTau.TheoremA.EtaSquared
