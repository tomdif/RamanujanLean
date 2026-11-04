import RamanujanTau.BosonicSpectrum
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Normalized occupation monomials

Rescale the polynomial occupation basis by the inverse square root of the
product of occupation factorials. The existing creation and annihilation
operators then have the square-root occupation coefficients. Their complete
coordinate matrices are conjugate transposes, without defining either
operator to be the adjoint of the other.
-/

set_option autoImplicit false
noncomputable section

namespace BosonicOscillator

open MvPolynomial

def factorialWeight {k : ℕ} (d : Exponent k) : ℕ :=
  d.prod fun _ n => n.factorial

theorem factorialWeight_pos {k : ℕ} (d : Exponent k) : 0 < factorialWeight d := by
  exact Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem factorialWeight_raise {k : ℕ} (d : Exponent k) (a : Mode k) :
    factorialWeight (d + Finsupp.single a 1) = (d a + 1) * factorialWeight d := by
  classical
  have h₁ := Finsupp.mul_prod_erase' (d + Finsupp.single a 1) a
    (fun _ n => n.factorial) (fun _ => Nat.factorial_zero)
  have h₂ := Finsupp.mul_prod_erase' d a
    (fun _ n => n.factorial) (fun _ => Nat.factorial_zero)
  unfold factorialWeight
  rw [← h₁, ← h₂]
  simp [Finsupp.erase_add, Nat.factorial_succ, mul_assoc]

/-- Nonnegative square roots of natural numbers, regarded as complex scalars. -/
def root (n : ℕ) : ℂ := (Real.sqrt (n : ℝ) : ℂ)

@[simp] theorem star_root (n : ℕ) : star (root n) = root n := by simp [root]

theorem root_sq (n : ℕ) : root n ^ 2 = (n : ℂ) := by
  unfold root
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

theorem root_ne_zero {n : ℕ} (hn : 0 < n) : root n ≠ 0 := by
  unfold root
  have h : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn))
  exact_mod_cast h

theorem root_mul (m n : ℕ) : root (m * n) = root m * root n := by
  simp [root, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m)]

def normalizer {k : ℕ} (d : Exponent k) : ℂ := root (factorialWeight d)

theorem normalizer_ne_zero {k : ℕ} (d : Exponent k) : normalizer d ≠ 0 :=
  root_ne_zero (factorialWeight_pos d)

theorem normalizer_raise {k : ℕ} (d : Exponent k) (a : Mode k) :
    normalizer (d + Finsupp.single a 1) = root (d a + 1) * normalizer d := by
  simp only [normalizer, factorialWeight_raise, root_mul]

/-- The factorial normalization of the full algebraic occupation basis. -/
def normalizedBasis (k : ℕ) : Module.Basis (Exponent k) ℂ (Space k) :=
  (basisMonomials (Mode k) ℂ).isUnitSMul
    (fun d => isUnit_iff_ne_zero.mpr (inv_ne_zero (normalizer_ne_zero d)))

theorem normalizedBasis_apply {k : ℕ} (d : Exponent k) :
    normalizedBasis k d = monomial d (normalizer d)⁻¹ := by
  simp only [normalizedBasis, Module.Basis.isUnitSMul_apply, coe_basisMonomials,
    smul_monomial, smul_eq_mul, mul_one]

theorem normalizedBasis_repr_coeff {k : ℕ} (p : Space k) (d : Exponent k) :
    (normalizedBasis k).repr p d = normalizer d * coeff d p := by
  simp only [normalizedBasis, Module.Basis.repr_isUnitSMul, Units.smul_def,
    Units.val_inv_eq_inv_val, IsUnit.unit_spec, inv_inv, smul_eq_mul]
  rfl

theorem normalizedBasis_repr_ne_zero {k : ℕ} (p : Space k) (d : Exponent k) :
    (normalizedBasis k).repr p d ≠ 0 ↔ coeff d p ≠ 0 := by
  rw [normalizedBasis_repr_coeff, mul_ne_zero_iff]
  simp [normalizer_ne_zero]

theorem create_normalizedBasis {k : ℕ} (a : Mode k) (d : Exponent k) :
    create a (normalizedBasis k d) =
      root (d a + 1) • normalizedBasis k (d + Finsupp.single a 1) := by
  rw [normalizedBasis_apply, create_monomial, normalizedBasis_apply,
    smul_monomial, smul_eq_mul, normalizer_raise]
  congr 1
  field_simp [normalizer_ne_zero d, root_ne_zero (Nat.succ_pos (d a))]

theorem annihilate_normalizedBasis_raise {k : ℕ} (a : Mode k) (d : Exponent k) :
    annihilate a (normalizedBasis k (d + Finsupp.single a 1)) =
      root (d a + 1) • normalizedBasis k d := by
  rw [normalizedBasis_apply, annihilate_monomial, add_tsub_cancel_right,
    Finsupp.add_apply, Finsupp.single_eq_same, normalizer_raise,
    normalizedBasis_apply, smul_monomial, smul_eq_mul]
  congr 1
  rw [← root_sq (d a + 1)]
  field_simp [normalizer_ne_zero d, root_ne_zero (Nat.succ_pos (d a))]

theorem annihilate_normalizedBasis_zero {k : ℕ} (a : Mode k) (d : Exponent k)
    (h : d a = 0) : annihilate a (normalizedBasis k d) = 0 := by
  rw [normalizedBasis_apply, annihilate_monomial]
  simp [h]

theorem hamiltonian_normalizedBasis {k : ℕ} (d : Exponent k) :
    hamiltonian k (normalizedBasis k d) =
      (exponentEnergy d : ℂ) • normalizedBasis k d := by
  simp only [normalizedBasis_apply, hamiltonian_monomial]

/-- Conjugate-transpose coordinates for the independently defined algebraic operators. -/
theorem normalized_coordinate_adjoint {k : ℕ} (a : Mode k) (d e : Exponent k) :
    (normalizedBasis k).repr (annihilate a (normalizedBasis k e)) d =
      star ((normalizedBasis k).repr (create a (normalizedBasis k d)) e) := by
  classical
  by_cases he : e a = 0
  · have hne : e ≠ d + Finsupp.single a 1 := by
      intro h
      have h' := congrArg (fun f : Exponent k => f a) h
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, he] at h'
      omega
    rw [annihilate_normalizedBasis_zero a e he, create_normalizedBasis]
    simp [Ne.symm hne]
  · obtain ⟨f, rfl⟩ : ∃ f : Exponent k, e = f + Finsupp.single a 1 :=
      ⟨e - Finsupp.single a 1, (Finsupp.sub_add_single_one_cancel he).symm⟩
    rw [annihilate_normalizedBasis_raise, create_normalizedBasis]
    by_cases h : f = d
    · subst f
      simp
    · simp [h, Ne.symm h]

end BosonicOscillator
