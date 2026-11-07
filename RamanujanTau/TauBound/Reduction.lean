/-
# Reducing `PoincareFormula` to a statement about one cusp form

`poincareFormula_of_cuspForm`: if some weight-12 level-1 cusp form `f` has
`a_n(f) = [n = 1] + ∑_{c≥1} c^{-12} S(1,n;c) K(n,c;1/n)` for all `n ≥ 1`, and `a_1(f) ≠ 0`,
then `PoincareFormula` holds (with `λ = a_1(f)`), because `S₁₂(SL₂(ℤ)) = ℂ Δ` (Mathlib)
and `a_n(Δ) = τ(n)` (repo bridge).
-/
import RamanujanTau.TauBound.Endgame
import RamanujanTau.DiscriminantQExpansion
import RamanujanTau.TauBridge
import Mathlib.NumberTheory.ModularForms.DimensionFormulas.LevelOne

set_option autoImplicit false

namespace RamanujanTau.TauBound

open ModularForm UpperHalfPlane
open scoped MatrixGroups

/-- The unfolded-coefficient property of a cusp form `f` (the content of Poincaré's
construction of `P₁`, Petersson 1932 / Iwaniec Thm 3.4 specialised to `SL₂(ℤ)`, `k = 12`). -/
def HasPoincareCoeffs (f : CuspForm 𝒮ℒ 12) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    HasSum (fun c : ℕ => ((c + 1 : ℕ) : ℂ) ^ (-12 : ℤ) * kloosterman 1 n (c + 1) *
        kInt n (c + 1) (1 / n))
      ((qExpansion 1 f).coeff n - if n = 1 then 1 else 0)

lemma qExpansion_discriminant_coeff_tau (n : ℕ) :
    (qExpansion 1 CuspForm.discriminant).coeff n = ((tau n : ℤ) : ℂ) := by
  rw [tau_eq_tauPS, ← DiscriminantBridge.qExpansion_discriminant_coeff]; rfl

/-- **Reduction.** A cusp form with Poincaré coefficients and nonzero first coefficient gives
`PoincareFormula`. -/
theorem poincareFormula_of_cuspForm (f : CuspForm 𝒮ℒ 12) (hf : HasPoincareCoeffs f)
    (h1 : (qExpansion 1 f).coeff 1 ≠ 0) : PoincareFormula := by
  obtain ⟨μ, hμ⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve f
  have hcoeff : ∀ n, (qExpansion 1 f).coeff n = μ * (tau n : ℂ) := by
    intro n
    rw [← hμ]
    have h := qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero
      CuspForm.discriminant one_pos one_mem_strictPeriods_SL) μ
    rw [show ((μ • CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ℍ → ℂ) =
      μ • (CuspForm.discriminant : ℍ → ℂ) from rfl, h]
    rw [PowerSeries.coeff_smul, smul_eq_mul]
    congr 1
    exact qExpansion_discriminant_coeff_tau n
  refine ⟨μ, ?_, fun n hn => ?_⟩
  · intro h0; apply h1; rw [hcoeff, h0, zero_mul]
  · have := hf n hn
    rwa [hcoeff] at this

end RamanujanTau.TauBound
