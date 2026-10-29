import RamanujanTau.TheoremA.EtaQuotientForms

/-!
# Three weight-two eta quotients at level six

The forms A = η(2z)^12 η(3z)^2 / (η(z)^6 η(6z)^4),
B = η(2z)^4 η(6z)^4 / (η(z)^2 η(3z)^2), and
C = η(z)^2 η(6z)^12 / (η(2z)^4 η(3z)^6) are genuine modular
forms on Γ₀(6). The identity AC = B² follows from their exponent vectors.
Spanning and integral q-expansion properties are separate results.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open ModularForm CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm

def weightTwoExponent (a : Fin 3) (j : Fin 4) : ℤ :=
  match a.val, j.val with
  | 0, 0 => -3 | 0, 1 => 6 | 0, 2 => 1 | 0, _ => -2
  | 1, 0 => -1 | 1, 1 => 2 | 1, 2 => -1 | 1, _ => 2
  | _, 0 => 1 | _, 1 => -2 | _, 2 => -3 | _, _ => 6

theorem weightTwoExponent_sum (a : Fin 3) : ∑ j : Fin 4, weightTwoExponent a j = 2 := by
  revert a
  decide +kernel

theorem weightTwo_phase (a : Fin 3) : PhaseCertificate (weightTwoExponent a) := by
  unfold PhaseCertificate
  revert a
  decide +kernel

theorem weightTwo_cusps (a : Fin 3) : CuspCertificate (weightTwoExponent a) := by
  unfold CuspCertificate
  revert a
  decide +kernel

/-- A, B, C, with their analytic and all-cusp modularity conditions proved. -/
noncomputable def weightTwoForm (a : Fin 3) :
    ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) 2 :=
  quotientModularForm (weightTwoExponent a) (weightTwoExponent_sum a)
    (weightTwo_phase a) (weightTwo_cusps a)

@[simp] theorem weightTwoForm_apply (a : Fin 3) (z : ℍ) :
    weightTwoForm a z = quotientFunction (weightTwoExponent a) z := rfl

theorem weightTwoForm_ne_zero (a : Fin 3) (z : ℍ) : weightTwoForm a z ≠ 0 :=
  quotientFunction_ne_zero _ _

theorem quotientFunction_add (r s : Fin 4 → ℤ) (z : ℍ) :
    quotientFunction (r + s) z = quotientFunction r z * quotientFunction s z := by
  simp only [quotientFunction, Pi.add_apply, zpow_add₀ (scaledEta_ne_zero _ _ _),
    Finset.prod_mul_distrib]

theorem weightTwoExponent_relation :
    weightTwoExponent 0 + weightTwoExponent 2 = weightTwoExponent 1 + weightTwoExponent 1 := by
  ext j
  revert j
  decide +kernel

/-- The conic relation holds as an exact identity of analytic functions. -/
theorem weightTwoForm_relation (z : ℍ) :
    weightTwoForm 0 z * weightTwoForm 2 z = weightTwoForm 1 z ^ 2 := by
  simp only [weightTwoForm_apply, pow_two, ← quotientFunction_add,
    weightTwoExponent_relation]

end RamanujanTau.TheoremA.EtaSquared
