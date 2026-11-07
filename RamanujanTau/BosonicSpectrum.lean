import RamanujanTau.BosonicOscillator
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Energy eigenspaces of the algebraic oscillator model

The Hamiltonian's eigenspaces are exactly the spans of occupation monomials
of the corresponding energy. Their finite dimensions are therefore the
previously proved colored partition counts. These are algebraic eigenspaces;
the linear equivalence to the finite Hilbert shells is not asserted isometric.
-/

set_option autoImplicit false
noncomputable section

namespace BosonicOscillator

open MvPolynomial Filter
open scoped Real Topology

theorem coeff_hamiltonian {k : ℕ} (d : Exponent k) (p : Space k) :
    coeff d (hamiltonian k p) = (exponentEnergy d : ℂ) * coeff d p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    by_cases h : d = s
    · subst s; simp [hamiltonian_monomial]
    · simp [hamiltonian_monomial, coeff_monomial, Ne.symm h]
  | add p q hp hq => simp [hp, hq, mul_add]

def EnergySpace (k n : ℕ) : Submodule ℂ (Space k) :=
  Module.End.eigenspace (hamiltonian k).toLinearMap (n : ℂ)

theorem mem_energySpace {k n : ℕ} (p : Space k) :
    p ∈ EnergySpace k n ↔ ∀ d, coeff d p ≠ 0 → exponentEnergy d = n := by
  rw [EnergySpace, Module.End.mem_eigenspace_iff]
  change (hamiltonian k p = (n : ℂ) • p) ↔ _
  constructor
  · intro h d hd
    have he := congrArg (coeff d) h
    simp only [coeff_hamiltonian, coeff_smul, smul_eq_mul] at he
    exact_mod_cast mul_right_cancel₀ hd he
  · intro h
    ext d
    rw [coeff_hamiltonian, coeff_smul, smul_eq_mul]
    by_cases hd : coeff d p = 0
    · simp [hd]
    · rw [h d hd]

theorem energySpace_eq_supported (k n : ℕ) :
    EnergySpace k n = Finsupp.supported ℂ ℂ {d : Exponent k | exponentEnergy d = n} := by
  ext p
  rw [mem_energySpace]
  change (∀ d, coeff d p ≠ 0 → exponentEnergy d = n) ↔
    ∀ d ∈ p.support, exponentEnergy d = n
  simp only [MvPolynomial.mem_support_iff]

def exponentStateEquiv (k n : ℕ) :
    {d : Exponent k // exponentEnergy d = n} ≃ BosonicOccupation.State k n :=
  (occupationEquiv k).subtypeEquiv (fun d => by
    change exponentEnergy d = n ↔ BosonicOccupation.energy (toOccupation d) = n
    rw [energy_toOccupation])

/-- Exact linear identification with the previously constructed finite shells. -/
def energySpaceEquivShell (k n : ℕ) :
    EnergySpace k n ≃ₗ[ℂ] BosonicOccupation.ShellSpace k n :=
  (LinearEquiv.ofEq _ _ (energySpace_eq_supported k n)).trans
    ((Finsupp.supportedEquivFinsupp {d : Exponent k | exponentEnergy d = n}).trans
      ((Finsupp.domLCongr (exponentStateEquiv k n)).trans
        ((Finsupp.linearEquivFunOnFinite ℂ ℂ (BosonicOccupation.State k n)).trans
          (WithLp.linearEquiv 2 ℂ (BosonicOccupation.State k n → ℂ)).symm)))

instance (k n : ℕ) : FiniteDimensional ℂ (EnergySpace k n) :=
  FiniteDimensional.of_injective (energySpaceEquivShell k n).toLinearMap
    (energySpaceEquivShell k n).injective

theorem energySpace_finrank (k n : ℕ) :
    Module.finrank ℂ (EnergySpace k n) = ColoredPartitions.count k n := by
  rw [(energySpaceEquivShell k n).finrank_eq, BosonicOccupation.shell_finrank]

theorem create_mem_energySpace {k n : ℕ} (a : Mode k) {p : Space k}
    (hp : p ∈ EnergySpace k n) : create a p ∈ EnergySpace k (n + frequency a) := by
  rw [EnergySpace, Module.End.mem_eigenspace_iff] at hp ⊢
  change hamiltonian k p = (n : ℂ) • p at hp
  change hamiltonian k (create a p) = ((n + frequency a : ℕ) : ℂ) • create a p
  have h := hamiltonian_create a p
  rw [hp, map_smul] at h
  rw [Nat.cast_add, add_smul]
  simpa [add_comm] using sub_eq_iff_eq_add.mp h

/-- The unit vacuum offset is explicitly specified. -/
def chargeOperator : Module.End ℂ (Space 24) :=
  (hamiltonian 24).toLinearMap - LinearMap.id

def ChargeEigenspace (n : ℕ) : Submodule ℂ (Space 24) :=
  Module.End.eigenspace chargeOperator (n : ℂ)

theorem chargeEigenspace_eq (n : ℕ) : ChargeEigenspace n = EnergySpace 24 (n + 1) := by
  ext p
  rw [ChargeEigenspace, EnergySpace, Module.End.mem_eigenspace_iff,
    Module.End.mem_eigenspace_iff]
  change hamiltonian 24 p - p = (n : ℂ) • p ↔
    hamiltonian 24 p = ((n + 1 : ℕ) : ℂ) • p
  simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  exact sub_eq_iff_eq_add

instance (n : ℕ) : FiniteDimensional ℂ (ChargeEigenspace n) := by
  rw [chargeEigenspace_eq]
  infer_instance

theorem chargeEigenspace_finrank (n : ℕ) :
    Module.finrank ℂ (ChargeEigenspace n) = ColoredPartitions.degeneracy n := by
  rw [chargeEigenspace_eq, energySpace_finrank]
  rfl

theorem chargeEigenspace_entropy :
    Tendsto (fun n : ℕ => Real.log (Module.finrank ℂ (ChargeEigenspace n) : ℝ) / √n)
      atTop (𝓝 (4 * π)) := by
  simpa only [chargeEigenspace_finrank] using ColoredPartitions.degeneracy_entropy

theorem chargeEigenspace_cardy_ratio :
    Tendsto (fun n : ℕ => Real.log (Module.finrank ℂ (ChargeEigenspace n) : ℝ) /
      Cardy.leadingEntropy 2 n) atTop (𝓝 1) := by
  simpa only [chargeEigenspace_finrank] using ColoredPartitions.degeneracy_cardy_ratio

end BosonicOscillator
