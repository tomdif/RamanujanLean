/-
# Rankin–Selberg for every level-one cusp form: imports, the `Δ` consistency check, axioms

Build: `nice -n 10 lake build RamanujanTau.RankinSelbergGeneral.Main`.
-/
import RamanujanTau.RankinSelbergGeneral.Instances

set_option autoImplicit false

namespace RamanujanTau.RankinSelbergGeneral

open Finset Real Filter Topology
open RamanujanTau.RankinSelberg hiding G G_smul continuous_G G_pos
open scoped MatrixGroups

/-- For `f = Δ`, the general `G_f` is the `G` of `RankinSelberg/`. -/
lemma Gf_discriminant : Gf (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) =
    RankinSelberg.G := rfl

/-- For `f = Δ`, the general `‖f‖²` is `EisensteinReal.petNormSq`. -/
lemma petNormSqF_discriminant :
    petNormSqF (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) =
      EisensteinReal.petNormSq := rfl

/-- **Consistency:** the general theorem at `f = Δ` re-proves
`EisensteinReal.rankinSelberg_asymptotic_zagier_unconditional` (same constant). -/
theorem rankinSelberg_asymptotic_discriminant :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11) / N) atTop
      (𝓝 (3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ))) := by
  have h := rankinSelberg_asymptotic (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) (by norm_num)
  rw [petNormSqF_discriminant] at h
  refine h.congr fun N => ?_
  congr 1
  refine sum_congr rfl fun n _ => ?_
  unfold coeffSq
  have e := TauBound.qExpansion_discriminant_coeff_tau n
  erw [e, Complex.norm_intCast, sq_abs]

end RamanujanTau.RankinSelbergGeneral

#print axioms RamanujanTau.RankinSelbergGeneral.horocycle_tendsto
#print axioms RamanujanTau.RankinSelbergGeneral.tendsto_sum_coeffSq
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_asymptotic
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_asymptotic_Gamma
#print axioms RamanujanTau.RankinSelbergGeneral.petNormSqF_pos
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_asymptotic_pos
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_two_sided
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_isTheta
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_intForm
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_deltaE
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_weight16
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_weight18
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_weight20
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_weight22
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_weight26
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_asymptotic_discriminant
