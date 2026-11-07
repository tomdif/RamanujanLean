import RamanujanTau.BosonicNormalization
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Adjoint creation and annihilation between finite energy shells

The normalized polynomial energy eigenspaces are identified with finite
Euclidean spaces. The shell operators are transported restrictions of the
existing, independently defined algebraic creation and annihilation maps.
Their Hilbert adjoint relation follows from the factorial normalization.

No claim about adjoints of unbounded operators on an infinite Hilbert
completion is made here.
-/

set_option autoImplicit false
noncomputable section

namespace BosonicOscillator

open MvPolynomial
open scoped ComplexConjugate

abbrev EnergyIndex (k n : ℕ) := {d : Exponent k // exponentEnergy d = n}

instance (k n : ℕ) : Fintype (EnergyIndex k n) :=
  Fintype.ofEquiv (BosonicOccupation.State k n) (exponentStateEquiv k n).symm

abbrev NormalizedShell (k n : ℕ) := EuclideanSpace ℂ (EnergyIndex k n)

def normalizedShellIsometry (k n : ℕ) :
    NormalizedShell k n ≃ₗᵢ[ℂ] BosonicOccupation.ShellSpace k n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (exponentStateEquiv k n)

theorem normalized_repr_map_energySpace (k n : ℕ) :
    (EnergySpace k n).map (normalizedBasis k).repr.toLinearMap =
      Finsupp.supported ℂ ℂ {d : Exponent k | exponentEnergy d = n} := by
  ext f
  rw [Submodule.mem_map, Finsupp.mem_supported]
  constructor
  · rintro ⟨p, hp, rfl⟩ d hd
    apply (mem_energySpace p).mp hp d
    exact (normalizedBasis_repr_ne_zero p d).mp (Finsupp.mem_support_iff.mp hd)
  · intro hf
    refine ⟨(normalizedBasis k).repr.symm f, ?_, by simp⟩
    apply (mem_energySpace _).mpr
    intro d hd
    apply hf
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    simpa using (normalizedBasis_repr_ne_zero ((normalizedBasis k).repr.symm f) d).mpr hd

/-- Coordinates in normalized monomials, restricted to an exact energy eigenspace. -/
def normalizedShellEquiv (k n : ℕ) : EnergySpace k n ≃ₗ[ℂ] NormalizedShell k n :=
  ((normalizedBasis k).repr.ofSubmodules _ _ (normalized_repr_map_energySpace k n)).trans
    ((Finsupp.supportedEquivFinsupp {d : Exponent k | exponentEnergy d = n}).trans
      ((Finsupp.linearEquivFunOnFinite ℂ ℂ (EnergyIndex k n)).trans
        (WithLp.linearEquiv 2 ℂ (EnergyIndex k n → ℂ)).symm))

theorem normalizedShellEquiv_apply {k n : ℕ} (p : EnergySpace k n) (d : EnergyIndex k n) :
    normalizedShellEquiv k n p d = (normalizedBasis k).repr p.1 d.1 := rfl

def normalizedEnergyVector {k n : ℕ} (d : EnergyIndex k n) : EnergySpace k n :=
  ⟨normalizedBasis k d.1, by
    rw [EnergySpace, Module.End.mem_eigenspace_iff]
    change hamiltonian k (normalizedBasis k d.1) = (n : ℂ) • normalizedBasis k d.1
    rw [hamiltonian_normalizedBasis, d.2]⟩

theorem normalizedShellEquiv_basis {k n : ℕ} (d : EnergyIndex k n) :
    normalizedShellEquiv k n (normalizedEnergyVector d) =
      EuclideanSpace.basisFun (EnergyIndex k n) ℂ d := by
  classical
  ext e
  rw [normalizedShellEquiv_apply]
  simp [normalizedEnergyVector, EuclideanSpace.basisFun_apply,
    Finsupp.single_apply, Subtype.ext_iff, eq_comm]

theorem normalizedShellEquiv_symm_basis {k n : ℕ} (d : EnergyIndex k n) :
    (normalizedShellEquiv k n).symm (EuclideanSpace.basisFun (EnergyIndex k n) ℂ d) =
      normalizedEnergyVector d := by
  apply (normalizedShellEquiv k n).injective
  rw [LinearEquiv.apply_symm_apply, normalizedShellEquiv_basis]

theorem annihilate_mem_energySpace {k n : ℕ} (a : Mode k) {p : Space k}
    (hp : p ∈ EnergySpace k (n + frequency a)) : annihilate a p ∈ EnergySpace k n := by
  rw [EnergySpace, Module.End.mem_eigenspace_iff] at hp ⊢
  change hamiltonian k p = ((n + frequency a : ℕ) : ℂ) • p at hp
  change hamiltonian k (annihilate a p) = (n : ℂ) • annihilate a p
  have h := hamiltonian_annihilate a p
  rw [hp, map_smul, Nat.cast_add, add_smul] at h
  have h' := sub_eq_iff_eq_add.mp h
  simpa [neg_smul, add_comm, add_left_comm, add_assoc] using h'

def createEnergy {k : ℕ} (a : Mode k) (n : ℕ) :
    EnergySpace k n →ₗ[ℂ] EnergySpace k (n + frequency a) :=
  ((create a).comp (EnergySpace k n).subtype).codRestrict _
    (fun p => create_mem_energySpace a p.2)

def annihilateEnergy {k : ℕ} (a : Mode k) (n : ℕ) :
    EnergySpace k (n + frequency a) →ₗ[ℂ] EnergySpace k n :=
  ((annihilate a).comp (EnergySpace k (n + frequency a)).subtype).codRestrict _
    (fun p => annihilate_mem_energySpace a p.2)

def createShell {k : ℕ} (a : Mode k) (n : ℕ) :
    NormalizedShell k n →ₗ[ℂ] NormalizedShell k (n + frequency a) :=
  (normalizedShellEquiv k (n + frequency a)).toLinearMap ∘ₗ
    createEnergy a n ∘ₗ (normalizedShellEquiv k n).symm.toLinearMap

def annihilateShell {k : ℕ} (a : Mode k) (n : ℕ) :
    NormalizedShell k (n + frequency a) →ₗ[ℂ] NormalizedShell k n :=
  (normalizedShellEquiv k n).toLinearMap ∘ₗ
    annihilateEnergy a n ∘ₗ (normalizedShellEquiv k (n + frequency a)).symm.toLinearMap

theorem createShell_basis_coord {k n : ℕ} (a : Mode k) (d : EnergyIndex k n)
    (e : EnergyIndex k (n + frequency a)) :
    createShell a n (EuclideanSpace.basisFun (EnergyIndex k n) ℂ d) e =
      (normalizedBasis k).repr (create a (normalizedBasis k d.1)) e.1 := by
  simp only [createShell, LinearMap.comp_apply, LinearEquiv.coe_coe,
    normalizedShellEquiv_symm_basis, normalizedShellEquiv_apply]
  rfl

theorem annihilateShell_basis_coord {k n : ℕ} (a : Mode k)
    (e : EnergyIndex k (n + frequency a)) (d : EnergyIndex k n) :
    annihilateShell a n (EuclideanSpace.basisFun (EnergyIndex k (n + frequency a)) ℂ e) d =
      (normalizedBasis k).repr (annihilate a (normalizedBasis k e.1)) d.1 := by
  simp only [annihilateShell, LinearMap.comp_apply, LinearEquiv.coe_coe,
    normalizedShellEquiv_symm_basis, normalizedShellEquiv_apply]
  rfl

private theorem inner_basis_left {k n : ℕ} (d : EnergyIndex k n) (v : NormalizedShell k n) :
    inner ℂ (EuclideanSpace.basisFun (EnergyIndex k n) ℂ d) v = v d := by
  classical
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  simp

private theorem inner_basis_right {k n : ℕ} (v : NormalizedShell k n) (d : EnergyIndex k n) :
    inner ℂ v (EuclideanSpace.basisFun (EnergyIndex k n) ℂ d) = star (v d) := by
  classical
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]
  simp

/-- The actual Hilbert adjoint between the normalized, finite energy shells. -/
theorem annihilateShell_eq_adjoint {k : ℕ} (a : Mode k) (n : ℕ) :
    annihilateShell a n = (createShell a n).adjoint := by
  apply (LinearMap.eq_adjoint_iff_basis
    (EuclideanSpace.basisFun (EnergyIndex k (n + frequency a)) ℂ).toBasis
    (EuclideanSpace.basisFun (EnergyIndex k n) ℂ).toBasis _ _).mpr
  intro e d
  change inner ℂ (annihilateShell a n (EuclideanSpace.basisFun _ ℂ e))
    (EuclideanSpace.basisFun _ ℂ d) =
    inner ℂ (EuclideanSpace.basisFun _ ℂ e)
      (createShell a n (EuclideanSpace.basisFun _ ℂ d))
  rw [inner_basis_right, inner_basis_left, annihilateShell_basis_coord,
    createShell_basis_coord, normalized_coordinate_adjoint, star_star]

theorem shell_inner_adjoint {k : ℕ} (a : Mode k) (n : ℕ)
    (x : NormalizedShell k n) (y : NormalizedShell k (n + frequency a)) :
    inner ℂ (createShell a n x) y = inner ℂ x (annihilateShell a n y) := by
  rw [annihilateShell_eq_adjoint, LinearMap.adjoint_inner_right]

theorem normalizedShell_finrank (k n : ℕ) :
    Module.finrank ℂ (NormalizedShell k n) = ColoredPartitions.count k n := by
  rw [(normalizedShellIsometry k n).toLinearEquiv.finrank_eq,
    BosonicOccupation.shell_finrank]

end BosonicOscillator
