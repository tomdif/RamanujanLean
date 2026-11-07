import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Tactic

/-!
# The bad-prime coset permutation for Γ₀(N)

For a prime `p ∣ N`, the matrices `[1 j; 0 p]`, indexed by `ZMod p`,
are permuted on the right by Γ₀(N), up to left multiplication by Γ₀(N).
This supplies the invariance calculation for the actual `U_p` operator.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.BadPrime
open Matrix CongruenceSubgroup
open scoped MatrixGroups

variable {p N : ℕ} [hp : Fact p.Prime]

lemma lower_left_zero (hN : p ∣ N) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    (γ 1 0 : ZMod p) = 0 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
  have hdiv : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  exact dvd_trans (by exact_mod_cast hN) hdiv

lemma diagonal_product (hN : p ∣ N) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    (γ 0 0 : ZMod p) * (γ 1 1 : ZMod p) = 1 := by
  have h := γ.property
  rw [det_fin_two] at h
  have hz := congrArg (Int.castRingHom (ZMod p)) h
  simpa [lower_left_zero hN γ hγ] using hz

lemma diagonal_ne_zero (hN : p ∣ N) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    (γ 0 0 : ZMod p) ≠ 0 ∧ (γ 1 1 : ZMod p) ≠ 0 := by
  have h := diagonal_product hN γ hγ
  constructor <;> intro hz <;> simp [hz] at h

/-- The action on the translation index: `j ↦ (b + j d)/a` modulo `p`. -/
noncomputable def perm (hN : p ∣ N) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    Equiv.Perm (ZMod p) :=
  Equiv.ofBijective (fun j => ((γ 0 1 : ZMod p) + j * γ 1 1) / γ 0 0) (by
    apply (Finite.injective_iff_bijective).mp
    intro i j hij
    have ha := (diagonal_ne_zero hN γ hγ).1
    have hd := (diagonal_ne_zero hN γ hγ).2
    exact mul_right_cancel₀ hd (add_left_cancel ((div_left_inj' ha).mp hij)))

lemma perm_apply (hN : p ∣ N) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) (j : ZMod p) :
    perm hN γ hγ j = ((γ 0 1 : ZMod p) + j * γ 1 1) / γ 0 0 := rfl

lemma numerator_dvd (hN : p ∣ N) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) (j : ZMod p) :
    (p : ℤ) ∣ γ 0 1 + (j.val : ℤ) * γ 1 1 -
      (γ 0 0 + (j.val : ℤ) * γ 1 0) * (perm hN γ hγ j).val := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  simp only [ZMod.natCast_zmod_val]
  rw [lower_left_zero hN γ hγ, mul_zero, add_zero, perm_apply]
  have ha := (diagonal_ne_zero hN γ hγ).1
  field_simp
  ring

/-- The integral upper-right entry of the correcting Γ₀(N) matrix. -/
noncomputable def correctionEntry (hN : p ∣ N) (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 N) (j : ZMod p) : ℤ :=
  (γ 0 1 + (j.val : ℤ) * γ 1 1 -
    (γ 0 0 + (j.val : ℤ) * γ 1 0) * (perm hN γ hγ j).val) / p

lemma correctionEntry_mul (hN : p ∣ N) (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 N) (j : ZMod p) :
    correctionEntry hN γ hγ j * p = γ 0 1 + (j.val : ℤ) * γ 1 1 -
      (γ 0 0 + (j.val : ℤ) * γ 1 0) * (perm hN γ hγ j).val :=
  Int.ediv_mul_cancel (numerator_dvd hN γ hγ j)

/-- The correcting matrix has determinant one. -/
noncomputable def correction (hN : p ∣ N) (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 N) (j : ZMod p) : SL(2, ℤ) :=
  ⟨!![γ 0 0 + (j.val : ℤ) * γ 1 0, correctionEntry hN γ hγ j;
      (p : ℤ) * γ 1 0, γ 1 1 - γ 1 0 * (perm hN γ hγ j).val], by
    have he := correctionEntry_mul hN γ hγ j
    have hd := γ.property
    rw [det_fin_two] at hd ⊢
    change (γ 0 0 + (j.val : ℤ) * γ 1 0) *
      (γ 1 1 - γ 1 0 * (perm hN γ hγ j).val) -
      correctionEntry hN γ hγ j * ((p : ℤ) * γ 1 0) = 1
    linear_combination hd - γ 1 0 * he⟩

lemma correction_mem (hN : p ∣ N) (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 N) (j : ZMod p) : correction hN γ hγ j ∈ Gamma0 N := by
  change (((p : ℤ) * γ 1 0 : ℤ) : ZMod N) = 0
  push_cast
  change (γ 1 0 : ZMod N) = 0 at hγ
  rw [hγ, mul_zero]

/-- The determinant-`p` representatives, before embedding into `GL₂`. -/
def representative (p : ℕ) (j : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, j; 0, p]

/-- The exact coset identity, over the integers. -/
theorem representative_mul (hN : p ∣ N) (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 N) (j : ZMod p) :
    representative p j.val * γ.val =
      (correction hN γ hγ j).val * representative p (perm hN γ hγ j).val := by
  have he := correctionEntry_mul hN γ hγ j
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [representative, correction, Matrix.mul_apply, Fin.sum_univ_two] at he ⊢ <;> nlinarith

end RamanujanTau.TheoremA.BadPrime
