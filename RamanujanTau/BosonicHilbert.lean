import RamanujanTau.BosonicAdjoint
import RamanujanTau.HilbertDiagonal

/-!
# The completed occupation Hilbert space and its Hamiltonian

Square-summable amplitudes on all occupation exponents form a complete
Hilbert space. The previously normalized polynomial states embed densely.
The energy operator on its maximal square-summability domain is self-adjoint
and closed, and extends the existing algebraic Hamiltonian.

The 24-species charge offset remains specified as minus one. This does not
identify the model with a physical string theory or a gravitational system.
-/

set_option autoImplicit false
noncomputable section

namespace BosonicOscillator

open MvPolynomial
open scoped Classical ComplexConjugate

abbrev FockSpace (k : ℕ) := HilbertDiagonal.Space (Exponent k)

def fockBasis (k : ℕ) : HilbertBasis (Exponent k) ℂ (FockSpace k) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

theorem fockBasis_apply {k : ℕ} (d : Exponent k) : fockBasis k d = lp.single 2 d 1 := by
  simp [fockBasis, HilbertBasis.coe_ofRepr]

theorem fockBasis_orthonormal (k : ℕ) : Orthonormal ℂ (fockBasis k) :=
  (fockBasis k).orthonormal

def includeCoefficients (k : ℕ) : (Exponent k →₀ ℂ) →ₗ[ℂ] FockSpace k where
  toFun f := ⟨fun d => f d, (memℓp_zero f.hasFiniteSupport).of_exponent_ge zero_le⟩
  map_add' := by intro f g; ext d; rfl
  map_smul' := by intro c f; ext d; rfl

@[simp] theorem includeCoefficients_apply {k : ℕ} (f : Exponent k →₀ ℂ) (d : Exponent k) :
    includeCoefficients k f d = f d := rfl

def polynomialEmbedding (k : ℕ) : Space k →ₗ[ℂ] FockSpace k :=
  (includeCoefficients k).comp (normalizedBasis k).repr.toLinearMap

@[simp] theorem polynomialEmbedding_apply {k : ℕ} (p : Space k) (d : Exponent k) :
    polynomialEmbedding k p d = (normalizedBasis k).repr p d := rfl

theorem polynomialEmbedding_injective (k : ℕ) : Function.Injective (polynomialEmbedding k) := by
  intro p q h
  apply (normalizedBasis k).repr.injective
  ext d
  exact congrArg (fun x : FockSpace k => x d) h

theorem polynomialEmbedding_basis {k : ℕ} (d : Exponent k) :
    polynomialEmbedding k (normalizedBasis k d) = fockBasis k d := by
  ext e
  simp [fockBasis_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

theorem single_mem_polynomial_range {k : ℕ} (d : Exponent k) (c : ℂ) :
    lp.single 2 d c ∈ LinearMap.range (polynomialEmbedding k) := by
  refine ⟨c • normalizedBasis k d, ?_⟩
  rw [map_smul, polynomialEmbedding_basis, fockBasis_apply, ← lp.single_smul]
  simp

theorem polynomialEmbedding_dense (k : ℕ) : DenseRange (polynomialEmbedding k) := by
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num) x)
  exact Filter.Eventually.of_forall fun s =>
    (LinearMap.range (polynomialEmbedding k)).sum_mem
      (fun d _ => single_mem_polynomial_range d (x d))

theorem fock_expansion {k : ℕ} (x : FockSpace k) :
    HasSum (fun d => lp.single 2 d (x d)) x := lp.hasSum_single (by norm_num) x

/-- The maximal diagonal energy operator on the completed Hilbert space. -/
def fockHamiltonian (k : ℕ) : FockSpace k →ₗ.[ℂ] FockSpace k :=
  HilbertDiagonal.operator (fun d => (exponentEnergy d : ℝ))

theorem fockHamiltonian_domain (k : ℕ) (x : FockSpace k) :
    x ∈ (fockHamiltonian k).domain ↔
      Summable (fun d => ‖(exponentEnergy d : ℂ) * x d‖ ^ 2) := by
  simpa [fockHamiltonian] using
    HilbertDiagonal.mem_domain_iff (fun d : Exponent k => (exponentEnergy d : ℝ)) x

theorem fockHamiltonian_apply {k : ℕ} (x : (fockHamiltonian k).domain) (d : Exponent k) :
    fockHamiltonian k x d = (exponentEnergy d : ℂ) * x.1 d := by
  simp [fockHamiltonian]

theorem fockHamiltonian_dense_domain (k : ℕ) :
    Dense ((fockHamiltonian k).domain : Set (FockSpace k)) :=
  HilbertDiagonal.domain_dense _

theorem fockHamiltonian_self_adjoint (k : ℕ) : IsSelfAdjoint (fockHamiltonian k) :=
  HilbertDiagonal.self_adjoint _

theorem fockHamiltonian_closed (k : ℕ) : (fockHamiltonian k).IsClosed :=
  HilbertDiagonal.closed _

theorem polynomialEmbedding_hamiltonian_coord {k : ℕ} (p : Space k) (d : Exponent k) :
    polynomialEmbedding k (hamiltonian k p) d =
      (exponentEnergy d : ℂ) * polynomialEmbedding k p d := by
  simp only [polynomialEmbedding_apply, normalizedBasis_repr_coeff, coeff_hamiltonian]
  ring

theorem polynomialEmbedding_mem_domain {k : ℕ} (p : Space k) :
    polynomialEmbedding k p ∈ (fockHamiltonian k).domain := by
  change Memℓp (fun d => ((exponentEnergy d : ℝ) : ℂ) * polynomialEmbedding k p d) 2
  have h : (fun d => ((exponentEnergy d : ℝ) : ℂ) * polynomialEmbedding k p d) =
      (polynomialEmbedding k (hamiltonian k p) : Exponent k → ℂ) := by
    funext d
    simpa using (polynomialEmbedding_hamiltonian_coord p d).symm
  rw [h]
  exact lp.memℓp _

theorem fockHamiltonian_extends_polynomial {k : ℕ} (p : Space k) :
    fockHamiltonian k ⟨polynomialEmbedding k p, polynomialEmbedding_mem_domain p⟩ =
      polynomialEmbedding k (hamiltonian k p) := by
  ext d
  rw [fockHamiltonian_apply, polynomialEmbedding_hamiltonian_coord]

/-- The charge offset is a specified input, as in the algebraic model. -/
def fockCharge : FockSpace 24 →ₗ.[ℂ] FockSpace 24 :=
  HilbertDiagonal.operator (fun d => (exponentEnergy d : ℝ) - 1)

theorem fockCharge_self_adjoint : IsSelfAdjoint fockCharge :=
  HilbertDiagonal.self_adjoint _

theorem fockCharge_closed : fockCharge.IsClosed := HilbertDiagonal.closed _

theorem fockCharge_apply (x : fockCharge.domain) (d : Exponent 24) :
    fockCharge x d = ((exponentEnergy d : ℂ) - 1) * x.1 d := by
  simp [fockCharge]

end BosonicOscillator
