import RamanujanTau.TheoremA.ModularWeightSixAction
import RamanujanTau.TheoremA.BinaryFiltration
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The full weight-six obstruction, over every coefficient ring

The actual Hecke matrices imply (U₂−1)(U₂−32)(U₃+9)(U₂²+6U₂+32)=0
on every series in the degree-six binary model. Its value at (4,9) is
−108864, nonzero in every characteristic at least thirteen. This avoids
requiring a separate cusp-lifting theorem for a weight-six representative.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open Matrix

def fullWeightSixPolynomial {S : Type*} [Ring S] (A B : S) : S :=
  (A - 1) * (A - 32) * (B + 9) * (A ^ 2 + 6 * A + 32)

theorem map_fullWeightSixPolynomial {S T : Type*} [Ring S] [Ring T]
    (φ : S →+* T) (A B : S) :
    φ (fullWeightSixPolynomial A B) = fullWeightSixPolynomial (φ A) (φ B) := by
  simp [fullWeightSixPolynomial, map_ofNat]

theorem fullWeightSixPolynomial_intertwines {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (E : V →ₗ[R] W) (A B : Module.End R W) (a b : Module.End R V)
    (hA : ∀ v, A (E v) = E (a v)) (hB : ∀ v, B (E v) = E (b v)) (v : V) :
    fullWeightSixPolynomial A B (E v) = E (fullWeightSixPolynomial a b v) := by
  simp only [fullWeightSixPolynomial, pow_two, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.add_apply, Module.End.one_apply, Module.End.ofNat_apply,
    map_sub, map_add, map_nsmul, hA, hB]

noncomputable def modularWeightSixAnnihilator {R : Type*} [CommRing R] :
    Module.End R (PowerSeries R) := fullWeightSixPolynomial (uOperator 2) (uOperator 3)

/-- The full modular-space relation holds over arbitrary coefficient rings. -/
theorem modularWeightSixAnnihilator_evenCombination {R : Type*} [CommRing R]
    (c : Fin 7 → R) : modularWeightSixAnnihilator (evenCombination 3 c) = 0 := by
  let A := (Int.castRingHom R).mapMatrix modularWeightSixU2
  let B := (Int.castRingHom R).mapMatrix modularWeightSixU3
  have hM : fullWeightSixPolynomial A B = 0 := by
    have h := congrArg ((Int.castRingHom R).mapMatrix) modularWeightSix_matrix_identity
    simpa only [fullWeightSixPolynomial, map_mul, map_sub, map_one, map_ofNat,
      map_add, map_pow, map_zero] using h
  let a : Module.End R (Fin 7 → R) := Matrix.toLinAlgEquiv' A
  let b : Module.End R (Fin 7 → R) := Matrix.toLinAlgEquiv' B
  have hL : fullWeightSixPolynomial a b = 0 := by
    have h := congrArg (Matrix.toLinAlgEquiv' : Matrix (Fin 7) (Fin 7) R ≃ₐ[R]
      Module.End R (Fin 7 → R)) hM
    simpa only [fullWeightSixPolynomial, map_mul, map_sub, map_one, map_ofNat,
      map_add, map_pow, map_zero] using h
  have h := fullWeightSixPolynomial_intertwines (evenCombinationLinear (R := R) 3)
    (uOperator 2) (uOperator 3) a b
    (fun v => modularWeightSix_U2_action v) (fun v => modularWeightSix_U3_action v) c
  rw [hL, LinearMap.zero_apply, map_zero] at h
  exact h

theorem BinaryRep.modularWeightSix_annihilator {F : Type*} [Field F]
    {f : PowerSeries F} (hf : BinaryRep f 3) : modularWeightSixAnnihilator f = 0 := by
  obtain ⟨P, hP, rfl⟩ := hf
  rw [homogeneous_eq_binaryPolynomial 3 P hP, binaryEv_binaryPolynomial]
  exact modularWeightSixAnnihilator_evenCombination _

theorem fullWeightSixPolynomial_on_eigenvector {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] (A B : Module.End F V) (v : V)
    (hA : A v = (4 : F) • v) (hB : B v = (9 : F) • v) :
    fullWeightSixPolynomial A B v = (-108864 : F) • v := by
  simp only [fullWeightSixPolynomial, pow_two, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.add_apply, Module.End.one_apply, Module.End.ofNat_apply,
    map_sub, map_add, map_nsmul, map_smul, hA, hB]
  module

theorem fullWeightSix_scalar_ne_zero {F : Type*} [Field F] {p : ℕ} [CharP F p]
    (hp13 : 13 ≤ p) : (-108864 : F) ≠ 0 := by
  have h2 : (2 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two (by omega : p ≠ 2)
  have h3 : (3 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_three (by omega : p ≠ 3)
  have h7 : (7 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F (by decide : Nat.Prime 7)
    (by omega : p ≠ 7)
  have he : (-108864 : F) = -(2 ^ 6 * 3 ^ 5 * 7) := by ring
  rw [he]
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)) h7)

/-- The forbidden joint eigenpair cannot occur even in the full weight-six model. -/
theorem eq_zero_of_binary_weightSix_eigenpair {F : Type*} [Field F]
    {p : ℕ} [CharP F p] (hp13 : 13 ≤ p) (f : PowerSeries F) (hf : BinaryRep f 3)
    (h2 : uOperator 2 f = (4 : F) • f) (h3 : uOperator 3 f = (9 : F) • f) : f = 0 := by
  have h := fullWeightSixPolynomial_on_eigenvector (uOperator 2) (uOperator 3) f h2 h3
  change modularWeightSixAnnihilator f = _ at h
  rw [hf.modularWeightSix_annihilator] at h
  exact (smul_eq_zero.mp h.symm).resolve_left (fullWeightSix_scalar_ne_zero hp13)

end RamanujanTau.TheoremA
