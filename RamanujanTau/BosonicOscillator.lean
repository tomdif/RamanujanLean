import RamanujanTau.BosonicOccupation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Derivation.Lie

/-!
# Algebraic bosonic oscillators

The algebraic state space is a polynomial ring with one variable for each
species and positive mode. Its monomial exponents are explicitly equivalent
to `BosonicOccupation.Occupation`. Creation is multiplication by a variable;
annihilation is differentiation. These use the unnormalized monomial basis.

This constructs algebraic operators, not their Hilbert-space completions or
adjoints. The vacuum-energy offset remains a specified input.
-/

set_option autoImplicit false
noncomputable section

namespace BosonicOscillator

open MvPolynomial

/-- `(i,j)` labels species `i` and the positive-energy mode `j+1`. -/
abbrev Mode (k : ℕ) := Fin k × ℕ

def frequency {k : ℕ} (a : Mode k) : ℕ := a.2 + 1

abbrev Exponent (k : ℕ) := Mode k →₀ ℕ

abbrev Space (k : ℕ) := MvPolynomial (Mode k) ℂ

private def succEmbedding : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩

def toOccupation {k : ℕ} (d : Exponent k) : BosonicOccupation.Occupation k where
  modes i := Finsupp.embDomain succEmbedding (d.curry i)
  zero_mode i := by
    apply Finsupp.embDomain_notin_range
    rintro ⟨m, hm⟩
    exact Nat.succ_ne_zero m hm

@[simp] theorem toOccupation_succ {k : ℕ} (d : Exponent k) (i : Fin k) (m : ℕ) :
    (toOccupation d).modes i (m + 1) = d (i, m) :=
  Finsupp.embDomain_apply_self succEmbedding (d.curry i) m

def fromOccupation {k : ℕ} (o : BosonicOccupation.Occupation k) : Exponent k :=
  (Finsupp.equivFunOnFinite.symm fun i =>
    Finsupp.comapDomain Nat.succ (o.modes i) Nat.succ_injective.injOn).uncurry

@[simp] theorem fromOccupation_apply {k : ℕ} (o : BosonicOccupation.Occupation k)
    (i : Fin k) (m : ℕ) : fromOccupation o (i, m) = o.modes i (m + 1) := rfl

def occupationEquiv (k : ℕ) : Exponent k ≃ BosonicOccupation.Occupation k where
  toFun := toOccupation
  invFun := fromOccupation
  left_inv d := by ext ⟨i, m⟩; simp
  right_inv o := by
    apply BosonicOccupation.Occupation.ext
    funext i
    ext m
    cases m with
    | zero => exact (toOccupation _).zero_mode i |>.trans (o.zero_mode i).symm
    | succ m => simp

/-- The algebraic occupation basis; no orthonormal normalization is asserted. -/
def occupationBasis (k : ℕ) : Module.Basis (BosonicOccupation.Occupation k) ℂ (Space k) :=
  (basisMonomials (Mode k) ℂ).reindex (occupationEquiv k)

def exponentEnergy {k : ℕ} (d : Exponent k) : ℕ :=
  d.sum fun a n => frequency a * n

theorem energy_toOccupation {k : ℕ} (d : Exponent k) :
    BosonicOccupation.energy (toOccupation d) = exponentEnergy d := by
  unfold BosonicOccupation.energy BosonicOccupation.modeEnergy toOccupation
  simp only [Finsupp.sum_embDomain]
  change (∑ i, (d.curry i).sum fun m n => (m + 1) * n) =
    d.sum (fun a n => (a.2 + 1) * n)
  rw [← Finsupp.sum_curry_index d (fun _ m n => (m + 1) * n)]
  exact (Finsupp.sum_fintype d.curry
    (fun _ f => f.sum fun m n => (m + 1) * n) (fun _ => by simp)).symm

theorem energy_fromOccupation {k : ℕ} (o : BosonicOccupation.Occupation k) :
    exponentEnergy (fromOccupation o) = BosonicOccupation.energy o := by
  rw [← energy_toOccupation]
  exact congrArg BosonicOccupation.energy ((occupationEquiv k).apply_symm_apply o)

def create {k : ℕ} (a : Mode k) : Space k →ₗ[ℂ] Space k :=
  LinearMap.mulLeft ℂ (X a)

def annihilate {k : ℕ} (a : Mode k) : Space k →ₗ[ℂ] Space k :=
  (pderiv a).toLinearMap

@[simp] theorem create_apply {k : ℕ} (a : Mode k) (p : Space k) :
    create a p = X a * p := rfl

@[simp] theorem annihilate_apply {k : ℕ} (a : Mode k) (p : Space k) :
    annihilate a p = pderiv a p := rfl

theorem create_monomial {k : ℕ} (a : Mode k) (d : Exponent k) (c : ℂ) :
    create a (monomial d c) = monomial (d + Finsupp.single a 1) c := by
  simp [X, monomial_mul, add_comm]

theorem annihilate_monomial {k : ℕ} (a : Mode k) (d : Exponent k) (c : ℂ) :
    annihilate a (monomial d c) = monomial (d - Finsupp.single a 1) (c * d a) :=
  pderiv_monomial

theorem annihilate_vacuum {k : ℕ} (a : Mode k) : annihilate a (1 : Space k) = 0 :=
  pderiv_one

/-- The canonical commutation relation on every algebraic state. -/
theorem annihilate_create {k : ℕ} (a b : Mode k) (p : Space k) :
    annihilate a (create b p) - create b (annihilate a p) =
      if a = b then p else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp
  · simp [pderiv_X_of_ne (Ne.symm h), h]

theorem create_create {k : ℕ} (a b : Mode k) (p : Space k) :
    create a (create b p) = create b (create a p) := by
  simp only [create_apply]
  ring

theorem annihilate_annihilate {k : ℕ} (a b : Mode k) (p : Space k) :
    annihilate a (annihilate b p) = annihilate b (annihilate a p) := by
  have h : ⁅pderiv (R := ℂ) a, pderiv (R := ℂ) b⁆ =
      (0 : Derivation ℂ (Space k) (Space k)) := by
    apply derivation_ext
    intro c
    classical
    simp [Derivation.commutator_apply, pderiv_X, Pi.single_apply, apply_ite]
  have hp := congrArg (fun D : Derivation ℂ (Space k) (Space k) => D p) h
  exact sub_eq_zero.mp hp

/-- The energy derivation, with no vacuum offset. -/
def hamiltonian (k : ℕ) : Derivation ℂ (Space k) (Space k) :=
  mkDerivation ℂ (fun a => (frequency a : ℂ) • X a)

@[simp] theorem hamiltonian_X {k : ℕ} (a : Mode k) :
    hamiltonian k (X a) = (frequency a : ℂ) • X a :=
  mkDerivation_X _ _ _

theorem hamiltonian_vacuum (k : ℕ) : hamiltonian k (1 : Space k) = 0 := by
  exact (hamiltonian k).map_one_eq_zero

theorem hamiltonian_create {k : ℕ} (a : Mode k) (p : Space k) :
    hamiltonian k (create a p) - create a (hamiltonian k p) =
      (frequency a : ℂ) • create a p := by
  simp only [create_apply, (hamiltonian k).leibniz, hamiltonian_X, smul_eq_mul]
  rw [mul_smul_comm]
  simp [mul_comm]

theorem hamiltonian_annihilate {k : ℕ} (a : Mode k) (p : Space k) :
    hamiltonian k (annihilate a p) - annihilate a (hamiltonian k p) =
      -(frequency a : ℂ) • annihilate a p := by
  have h : ⁅hamiltonian k, pderiv (R := ℂ) a⁆ =
      -(frequency a : ℂ) • pderiv (R := ℂ) a := by
    apply derivation_ext
    intro b
    classical
    by_cases hb : b = a
    · subst b
      simp [Derivation.commutator_apply]
    · simp [Derivation.commutator_apply, pderiv_X_of_ne hb]
  exact congrArg (fun D : Derivation ℂ (Space k) (Space k) => D p) h

theorem hamiltonian_monomial_one {k : ℕ} (d : Exponent k) :
    hamiltonian k (monomial d 1) = (exponentEnergy d : ℂ) • monomial d 1 := by
  rw [hamiltonian, mkDerivation_monomial, one_smul]
  have hterm (a : Mode k) :
      monomial (d - Finsupp.single a 1) (d a : ℂ) •
        ((frequency a : ℂ) • X a) =
      ((frequency a * d a : ℕ) : ℂ) • (monomial d 1 : Space k) := by
    have he := X_mul_pderiv_monomial (i := a) (m := d) (r := (1 : ℂ))
    simp only [pderiv_monomial, one_mul] at he
    rw [smul_eq_mul, mul_smul_comm, mul_comm, he]
    simp [Nat.cast_mul, nsmul_eq_mul, smul_eq_C_mul, mul_assoc]
  simp_rw [Finsupp.sum, hterm, ← Finset.sum_smul]
  congr 1
  simp [exponentEnergy, Finsupp.sum]

theorem hamiltonian_monomial {k : ℕ} (d : Exponent k) (c : ℂ) :
    hamiltonian k (monomial d c) = (exponentEnergy d : ℂ) • monomial d c := by
  have hm : (monomial d c : Space k) = c • monomial d 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, Derivation.map_smul, hamiltonian_monomial_one, smul_comm]

theorem hamiltonian_occupation {k : ℕ} (o : BosonicOccupation.Occupation k) :
    hamiltonian k (occupationBasis k o) =
      (BosonicOccupation.energy o : ℂ) • occupationBasis k o := by
  simp only [occupationBasis, Module.Basis.reindex_apply, coe_basisMonomials]
  change hamiltonian k (monomial (fromOccupation o) 1) =
    (BosonicOccupation.energy o : ℂ) • monomial (fromOccupation o) 1
  rw [hamiltonian_monomial_one, energy_fromOccupation]

end BosonicOscillator
