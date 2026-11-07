import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular
import Mathlib.Tactic

/-!
# Twelve translates at level six

Explicit representatives arranged in the cusp-width blocks 1, 6, 3, 2.
The right actions of S and T, and each representative's period, are checked
over the integers by Lean's kernel. These certificates suffice to construct
the level-one product without assuming an index or dimension formula.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.LevelSix
open Matrix CongruenceSubgroup ModularGroup
open scoped MatrixGroups

def cuspTwo : SL(2, ℤ) := ⟨!![1, 0; 2, 1], by decide⟩
def cuspThree : SL(2, ℤ) := ⟨!![1, 0; 3, 1], by decide⟩

def rep : Fin 12 → SL(2, ℤ) :=
  ![1, S, S * T, S * T ^ 2, S * T ^ 3, S * T ^ 4, S * T ^ 5,
    cuspTwo, cuspTwo * T, cuspTwo * T ^ 2, cuspThree, cuspThree * T]

def width : Fin 12 → ℕ := ![1, 6, 6, 6, 6, 6, 6, 3, 3, 3, 2, 2]

def permS : Equiv.Perm (Fin 12) :=
  { toFun := ![1, 0, 6, 9, 10, 7, 2, 5, 11, 3, 4, 8]
    invFun := ![1, 0, 6, 9, 10, 7, 2, 5, 11, 3, 4, 8]
    left_inv := by decide
    right_inv := by decide }

def permT : Equiv.Perm (Fin 12) :=
  { toFun := ![0, 2, 3, 4, 5, 6, 1, 8, 9, 7, 11, 10]
    invFun := ![0, 6, 1, 2, 3, 4, 5, 9, 7, 8, 11, 10]
    left_inv := by decide
    right_inv := by decide }

theorem correctionS_mem (i : Fin 12) : rep i * S * (rep (permS i))⁻¹ ∈ Gamma0 6 := by
  revert i
  change ∀ i, ((rep i * S * (rep (permS i))⁻¹) 1 0 : ZMod 6) = 0
  decide +kernel

theorem correctionT_mem (i : Fin 12) : rep i * T * (rep (permT i))⁻¹ ∈ Gamma0 6 := by
  revert i
  change ∀ i, ((rep i * T * (rep (permT i))⁻¹) 1 0 : ZMod 6) = 0
  decide +kernel

theorem period_mem (i : Fin 12) : rep i * T ^ width i * (rep i)⁻¹ ∈ Gamma0 6 := by
  revert i
  change ∀ i, ((rep i * T ^ width i * (rep i)⁻¹) 1 0 : ZMod 6) = 0
  decide +kernel

theorem width_pos (i : Fin 12) : 0 < width i := by revert i; decide

theorem inverse_width_sum : ∑ i : Fin 12, (width i : ℚ)⁻¹ = 4 := by
  norm_num [width, Fin.sum_univ_succ]

end RamanujanTau.TheoremA.LevelSix
