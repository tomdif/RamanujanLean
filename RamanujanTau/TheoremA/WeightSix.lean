import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# The weight-six operator obstruction

The polynomial `(B + 9)(A² + 6A + 32)` excludes the joint eigenpair
`(A, B) = (4, 9)` in characteristic at least five. This avoids lifting
individual eigenvectors or assuming a semisimple reduction.

The integer matrices below model the classical old/new basis of the
three-dimensional weight-six cusp space at level six. Their polynomial
identity is checked here. Identifying these matrices with the actual Hecke
action, including its integral structure, is NOT proved in this file.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA

open Matrix

/-- Expected `U₂` matrix in the basis `(g(z), g(2z), h(z))`, where the
normalized newforms `g`, `h` have levels three and six, respectively. -/
def weightSixU2 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-6, 1, 0; -32, 0, 0; 0, 0, 4]

/-- Expected `U₃` matrix in the same basis. -/
def weightSixU3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![9, 0, 0; 0, 9, 0; 0, 0, -9]

/-- An exact integer certificate; no modular-form identification is claimed. -/
theorem weightSix_matrix_identity :
    (weightSixU3 + 9 • (1 : Matrix (Fin 3) (Fin 3) ℤ)) *
      (weightSixU2 ^ 2 + 6 • weightSixU2 + 32 • 1) = 0 := by
  decide +kernel

section Obstruction
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- Evaluation of the cusp-space annihilator on the forbidden eigenpair. -/
theorem cusp_polynomial_on_eigenvector (A B : Module.End K M) (v : M)
    (ha : A v = (4 : K) • v) (hb : B v = (9 : K) • v) :
    (((B + (9 : K) • 1) *
      (A ^ 2 + (6 : K) • A + (32 : K) • 1)) : Module.End K M) v =
      (1296 : K) • v := by
  simp [pow_two, Module.End.mul_apply, ha, hb, map_smul, smul_smul, ← add_smul]
  norm_num

/-- The pointwise form of the obstruction applies to a form in weight six,
without requiring the polynomial to annihilate the surrounding q-series space. -/
theorem eigenvector_eq_zero_of_annihilated (A B : Module.End K M) (v : M)
    (hpoly : (((B + (9 : K) • 1) *
      (A ^ 2 + (6 : K) • A + (32 : K) • 1)) : Module.End K M) v = 0)
    (hc : (1296 : K) ≠ 0)
    (ha : A v = (4 : K) • v) (hb : B v = (9 : K) • v) : v = 0 := by
  have h := cusp_polynomial_on_eigenvector A B v ha hb
  rw [hpoly] at h
  exact (smul_eq_zero.mp h.symm).resolve_left hc

/-- No simultaneous `(4,9)` eigenvector survives an annihilating polynomial
whose value there is nonzero. No diagonalization hypothesis is used. -/
theorem no_weightSix_eigenpair (A B : Module.End K M)
    (hpoly : (B + (9 : K) • 1) * (A ^ 2 + (6 : K) • A + (32 : K) • 1) = 0)
    (hc : (1296 : K) ≠ 0) (v : M)
    (ha : A v = (4 : K) • v) (hb : B v = (9 : K) • v) : v = 0 := by
  exact eigenvector_eq_zero_of_annihilated A B v (by rw [hpoly]; rfl) hc ha hb

/-- The scalar obstruction is a unit in every residue field of characteristic
`p ≥ 5`, not just in the prime field. -/
theorem obstruction_scalar_ne_zero (p : ℕ) [CharP K p]
    (hp5 : 5 ≤ p) : (1296 : K) ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hdiv
    omega
  have h3 : (3 : K) ≠ 0 := by
    intro h
    have hdiv : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num : 0 < 3) hdiv
    omega
  have he : (1296 : K) = 2 ^ 4 * 3 ^ 4 := by norm_num
  rw [he]
  exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)

end Obstruction
end RamanujanTau.TheoremA
