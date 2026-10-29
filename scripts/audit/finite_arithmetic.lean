import RamanujanTau.FiniteArithmetic.Orbit
import RamanujanTau.FiniteArithmetic.Partition29
import RamanujanTau.FiniteArithmetic.AllPowers29
import RamanujanTau.FiniteArithmetic.Complete29
import RamanujanTau.FiniteArithmetic.Evaluate29Powers
import RamanujanTau.FiniteArithmetic.WeightedTilings
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic
namespace Examples

instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

/-- The scalar and starting value recorded by the prime-29 experiment.
This certifies this finite orbit only; identification with the arithmetic
Theta operator is a separate proof obligation. -/
def theta29 : Module.End (ZMod 29) (ZMod 29) := LinearMap.mulLeft (ZMod 29) 23

theorem theta29_survives : ∀ n : ℕ, (theta29 ^ n) 8 ≠ 0 := by
  apply (orbit_nonzero_iff (K := ZMod 29) theta29 8).mpr
  norm_num [theta29, Module.finrank_self]
  decide +kernel

/-- A singular operator with a surviving orbit. Invertibility of the whole
operator is strictly stronger than the orbit certificate needs. -/
def projection : Module.End ℚ (Fin 2 → ℚ) where
  toFun v := fun i => if i = 0 then v 0 else 0
  map_add' := by intros; ext i; by_cases hi : i = 0 <;> simp [hi]
  map_smul' := by intros; ext i; by_cases hi : i = 0 <;> simp [hi]

def live : Fin 2 → ℚ := ![1, 0]
def killed : Fin 2 → ℚ := ![0, 1]

theorem projection_survives : ∀ n : ℕ, (projection ^ n) live ≠ 0 := by
  apply (orbit_nonzero_iff projection live).mpr
  simp only [Module.finrank_pi, Fintype.card_fin]
  intro h
  have h0 := congrFun h (0 : Fin 2)
  norm_num [pow_succ, Module.End.mul_apply, projection, live] at h0

theorem projection_not_injective : ¬ Function.Injective projection := by
  intro h
  have he : projection killed = projection 0 := by
    ext i
    simp [projection, killed]
  have h1 := congrFun (h he) (1 : Fin 2)
  norm_num [killed] at h1

end Examples

namespace Examples

/-- A finite recurrence certificate over a ring which is not a field. -/
def compositeStep : Module.End (ZMod 9) (ZMod 9) := LinearMap.mulLeft (ZMod 9) 2

theorem composite_relation :
    (compositeStep ^ 2) 1 =
      ∑ i : Fin 2, (![1, 6] : Fin 2 → ZMod 9) i • (compositeStep ^ (i : ℕ)) 1 := by
  decide +kernel

theorem composite_recurrence (n : ℕ) :
    (compositeStep ^ (n + 2)) 1 =
      ∑ i : Fin 2, (![1, 6] : Fin 2 → ZMod 9) i •
        (compositeStep ^ (n + (i : ℕ))) 1 :=
  relation_for_all_iterates compositeStep 1 2 ![1, 6] composite_relation n

end Examples
end RamanujanTau.FiniteArithmetic

open RamanujanTau.FiniteArithmetic

-- Boundary cases and independent small counting values, evaluated in the kernel.
example : WeightedTilings.evaluate (1 : ℤ) 1 0 = 1 := by decide +kernel
example : WeightedTilings.evaluate (1 : ℤ) 1 10 = 89 := by decide +kernel
example : WeightedTilings.evaluate (2 : ℤ) 3 8 = 4921 := by decide +kernel
example : WeightedTilings.count (2 : ℤ) 3 8 = 4921 := by
  rw [← WeightedTilings.evaluate_correct]
  decide +kernel

example : Partition29.residue 0 = 8 := by decide +kernel
example : Partition29.residue 1 = 24 := by decide +kernel

-- Kernel evaluation at a large exponent is separate from proving its
-- identification with the partition count, which uses `residue_correct`.
example : Partition29.residue 1000000000000 = 27 := by decide +kernel
example : Evaluate29Powers.evaluate 1 8 24 1000000000000 = 27 := by decide +kernel

#print axioms RamanujanTau.FiniteArithmetic.U_eq_of_certificate
#print axioms RamanujanTau.FiniteArithmetic.Cert29.seed
#print axioms RamanujanTau.FiniteArithmetic.Cert29.even_step
#print axioms RamanujanTau.FiniteArithmetic.Cert29.odd_step
#print axioms RamanujanTau.FiniteArithmetic.Partition29.partition_count
#print axioms RamanujanTau.FiniteArithmetic.Partition29.explicit_family
#print axioms RamanujanTau.FiniteArithmetic.Partition29.residue_correct
#print axioms RamanujanTau.FiniteArithmetic.Cert29Image.D_f
#print axioms RamanujanTau.FiniteArithmetic.Image29.D_image
#print axioms RamanujanTau.FiniteArithmetic.envelope_reduction
#print axioms RamanujanTau.FiniteArithmetic.lift_padic
#print axioms RamanujanTau.FiniteArithmetic.lift_padic_mem
#print axioms RamanujanTau.FiniteArithmetic.Divided29.odd_padic_mem
#print axioms RamanujanTau.FiniteArithmetic.Error29.tail_killed
#print axioms RamanujanTau.FiniteArithmetic.ErrorDynamics29.divided_step
#print axioms RamanujanTau.FiniteArithmetic.Cert29Error.obs_YF
#print axioms RamanujanTau.FiniteArithmetic.Cert29Error.obs_YG
#print axioms RamanujanTau.FiniteArithmetic.Cert29Error.obs_Phi
#print axioms RamanujanTau.FiniteArithmetic.CertifyError29.data
#print axioms RamanujanTau.FiniteArithmetic.Complete29.threshold
#print axioms RamanujanTau.FiniteArithmetic.Complete29.even_exact
#print axioms RamanujanTau.FiniteArithmetic.Complete29.partition_count_obstruction
#print axioms RamanujanTau.FiniteArithmetic.Complete29.partition_threshold
#print axioms RamanujanTau.FiniteArithmetic.AllPowers29.bounds
#print axioms RamanujanTau.FiniteArithmetic.AllPowers29.odd_padic
#print axioms RamanujanTau.FiniteArithmetic.AllPowers29.series_padic
#print axioms RamanujanTau.FiniteArithmetic.AllPowers29.partition_padic
#print axioms RamanujanTau.FiniteArithmetic.AllPowers29.partition_residues
#print axioms RamanujanTau.FiniteArithmetic.AllPowers29.partition_residues_iterate
#print axioms RamanujanTau.FiniteArithmetic.Evaluate29Powers.initial_isUnit
#print axioms RamanujanTau.FiniteArithmetic.Evaluate29Powers.count_eq
#print axioms RamanujanTau.FiniteArithmetic.Evaluate29Powers.evaluate_correct
#print axioms RamanujanTau.FiniteArithmetic.matrixPower_eq
#print axioms RamanujanTau.FiniteArithmetic.WeightedTilings.count_one_one
#print axioms RamanujanTau.FiniteArithmetic.WeightedTilings.certified_recurrence
#print axioms RamanujanTau.FiniteArithmetic.WeightedTilings.evaluate_correct

#print axioms RamanujanTau.FiniteArithmetic.OrbitModel.recurrence
#print axioms RamanujanTau.FiniteArithmetic.OrbitModel.observed_recurrence
#print axioms RamanujanTau.FiniteArithmetic.observed_zero_iff
#print axioms RamanujanTau.FiniteArithmetic.orbit_nonzero_iff
#print axioms RamanujanTau.FiniteArithmetic.orbit_eventually_zero_iff
#print axioms RamanujanTau.FiniteArithmetic.OrbitModel.nonzero_forever
#print axioms RamanujanTau.FiniteArithmetic.Examples.theta29_survives
#print axioms RamanujanTau.FiniteArithmetic.Examples.projection_survives
#print axioms RamanujanTau.FiniteArithmetic.Examples.projection_not_injective
#print axioms RamanujanTau.FiniteArithmetic.Examples.composite_recurrence
