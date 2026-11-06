/-
# The modular relation `Σ τ(n) e^{−2πnz} = z^{−12} Σ τ(n) e^{−2πn/z}` (`Re z > 0`)
-/
import RamanujanTau.HeckeL.Basic

set_option autoImplicit false

namespace RamanujanTau.VoronoiTrunc

open Complex ModularForm Filter Set
open UpperHalfPlane hiding I
open scoped MatrixGroups Real

local notation "𝕢" => Function.Periodic.qParam

/-- `D(z) = Σ τ(n) e^{−2πnz}` (`= Δ(iz)`). -/
noncomputable def Dq (z : ℂ) : ℂ := ∑' n : ℕ, tauC n * cexp (-2 * π * n * z)

/-- The point `iz ∈ ℍ` for `Re z > 0`. -/
def ptz {z : ℂ} (hz : 0 < z.re) : ℍ := ⟨I * z, by simpa using hz⟩

lemma hasSum_Dq {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun n : ℕ => tauC n * cexp (-2 * π * n * z)) (RamanujanTau.HeckeL.Δf (ptz hz)) := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) one_mem_strictPeriods_SL
  have h := hasSum_qExpansion one_pos hper
    (ModularFormClass.holo (CuspForm.discriminant : CuspForm 𝒮ℒ 12))
    (ModularFormClass.bdd_at_infty (CuspForm.discriminant : CuspForm 𝒮ℒ 12)) (ptz hz)
  refine h.congr_fun fun n => ?_
  have hc : (qExpansion 1 CuspForm.discriminant).coeff n = tauC n :=
    heckeData.coeff_discriminant n
  rw [hc, smul_eq_mul]
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

lemma Dq_eq {z : ℂ} (hz : 0 < z.re) : Dq z = RamanujanTau.HeckeL.Δf (ptz hz) :=
  (hasSum_Dq hz).tsum_eq

lemma re_inv_pos {z : ℂ} (hz : 0 < z.re) : 0 < (z⁻¹).re := by
  rw [inv_re]
  have : 0 < Complex.normSq z := Complex.normSq_pos.2 (by intro h; rw [h] at hz; simp at hz)
  positivity

/-- **The modular relation** `D(z) = z^{−12} D(1/z)` for `Re z > 0`. -/
theorem Dq_modular {z : ℂ} (hz : 0 < z.re) : Dq z = (z ^ 12)⁻¹ * Dq z⁻¹ := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hzi := re_inv_pos hz
  have hS : ModularGroup.S • ptz hz = ptz hzi := by
    apply UpperHalfPlane.ext
    rw [modular_S_smul]
    show (-(I * z))⁻¹ = I * z⁻¹
    field_simp
    rw [I_sq]
  have h := congrFun discriminant_S_invariant (ptz hz)
  rw [SL_slash_apply, ModularGroup.denom_S] at h
  rw [Dq_eq hz, Dq_eq hzi, ← hS]
  show RamanujanTau.HeckeL.Δf (ptz hz) = (z ^ 12)⁻¹ *
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) (ModularGroup.S • ptz hz)
  have h' : (CuspForm.discriminant : CuspForm 𝒮ℒ 12) (ModularGroup.S • ptz hz) *
      ((ptz hz : ℂ)) ^ (-(12 : ℤ)) = (CuspForm.discriminant : CuspForm 𝒮ℒ 12) (ptz hz) := h
  have hpt : ((ptz hz : ℍ) : ℂ) = I * z := rfl
  rw [hpt] at h'
  have hI : (I * z) ^ (-(12 : ℤ)) = (z ^ 12)⁻¹ := by
    rw [zpow_neg, show ((12 : ℤ)) = ((12 : ℕ) : ℤ) by rfl, zpow_natCast, mul_pow,
      show (12 : ℕ) = 4 * 3 by rfl, pow_mul I, I_pow_four]
    simp
  rw [hI] at h'
  show (CuspForm.discriminant : CuspForm 𝒮ℒ 12) (ptz hz) = _
  rw [← h']; ring

end RamanujanTau.VoronoiTrunc
