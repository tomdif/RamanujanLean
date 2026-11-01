/-
# Reduction of a positive integral ternary Gram form

Minimizing two positive integer invariants gives a reduced basis without
assuming a lattice reduction algorithm or a compactness theorem.
-/
import RamanujanTau.MultiQuintupleIntegralGram

namespace Ramanujan.MultiQuintuple
namespace TernaryUnimodularBasis

def swap12 (B : TernaryUnimodularBasis) : TernaryUnimodularBasis where
  x := B.y
  y := B.x
  z := B.z
  det_unit := by
    have he : ternaryPointDet B.y B.x B.z = -ternaryPointDet B.x B.y B.z := by
      simp [ternaryPointDet,ternaryDet]; ring
    rw [he]
    rcases B.det_unit with h | h <;> simp [h]

def swap23 (B : TernaryUnimodularBasis) : TernaryUnimodularBasis where
  x := B.x
  y := B.z
  z := B.y
  det_unit := by
    have he : ternaryPointDet B.x B.z B.y = -ternaryPointDet B.x B.y B.z := by
      simp [ternaryPointDet,ternaryDet]; ring
    rw [he]
    rcases B.det_unit with h | h <;> simp [h]

def shear2 (B : TernaryUnimodularBasis) (n : ℤ) : TernaryUnimodularBasis where
  x := B.x
  y := B.y-n • B.x
  z := B.z
  det_unit := by
    have he : ternaryPointDet B.x (B.y-n • B.x) B.z = ternaryPointDet B.x B.y B.z := by
      simp [ternaryPointDet,ternaryDet]; ring
    rw [he]
    exact B.det_unit

def shear3 (B : TernaryUnimodularBasis) (n m : ℤ) : TernaryUnimodularBasis where
  x := B.x
  y := B.y
  z := B.z-n • B.y-m • B.x
  det_unit := by
    have he : ternaryPointDet B.x B.y (B.z-n • B.y-m • B.x) = ternaryPointDet B.x B.y B.z := by
      simp [ternaryPointDet,ternaryDet]; ring
    rw [he]
    exact B.det_unit

theorem shear2_gram (B : TernaryUnimodularBasis) (G : IntegralTernaryGram) (n : ℤ) :
    (B.shear2 n).gram G =
      let H := B.gram G
      ⟨H.a,H.b-2*n*H.d+n^2*H.a,H.c,H.d-n*H.a,H.e,H.f-n*H.e⟩ := by
  ext <;> simp [gram,shear2,IntegralTernaryGram.norm,IntegralTernaryGram.dot] <;> ring

theorem shear3_gram (B : TernaryUnimodularBasis) (G : IntegralTernaryGram) (n m : ℤ) :
    (B.shear3 n m).gram G =
      let H := B.gram G
      ⟨H.a,H.b,H.c+n^2*H.b+m^2*H.a+2*n*m*H.d-2*n*H.f-2*m*H.e,
        H.d,H.e-n*H.d-m*H.a,H.f-n*H.b-m*H.d⟩ := by
  ext <;> simp [gram,shear3,IntegralTernaryGram.norm,IntegralTernaryGram.dot] <;> ring

theorem shear2_a_minor (B : TernaryUnimodularBasis) (G : IntegralTernaryGram) (n : ℤ) :
    ((B.shear2 n).gram G).a = (B.gram G).a ∧
      ((B.shear2 n).gram G).minor = (B.gram G).minor := by
  rw [shear2_gram]
  constructor
  · rfl
  · simp [IntegralTernaryGram.minor]; ring

theorem shear3_a_minor (B : TernaryUnimodularBasis) (G : IntegralTernaryGram) (n m : ℤ) :
    ((B.shear3 n m).gram G).a = (B.gram G).a ∧
      ((B.shear3 n m).gram G).minor = (B.gram G).minor := ⟨rfl,rfl⟩

def Minimal (B : TernaryUnimodularBasis) (G : IntegralTernaryGram) : Prop :=
  (∀ D : TernaryUnimodularBasis, (B.gram G).a ≤ (D.gram G).a) ∧
  (∀ D : TernaryUnimodularBasis, (D.gram G).a=(B.gram G).a →
    (B.gram G).minor ≤ (D.gram G).minor)

theorem exists_minimal (G : IntegralTernaryGram) (hG : G.Positive) :
    ∃ B : TernaryUnimodularBasis, B.Minimal G := by
  classical
  have hexA : ∃ n : ℕ, ∃ B : TernaryUnimodularBasis, (B.gram G).a = (n : ℤ) := by
    refine ⟨(standard.gram G).a.toNat,standard,?_⟩
    exact (Int.toNat_of_nonneg (le_of_lt (IntegralTernaryGram.a_pos (standard.gram_positive G hG)))).symm
  obtain ⟨B0,hB0⟩ := Nat.find_spec hexA
  have hAmin : ∀ D : TernaryUnimodularBasis, (Nat.find hexA : ℤ) ≤ (D.gram G).a := by
    intro D
    have ha := IntegralTernaryGram.a_pos (D.gram_positive G hG)
    have he := Int.toNat_of_nonneg (le_of_lt ha)
    have hh := Nat.find_min' hexA (show ∃ B : TernaryUnimodularBasis,
      (B.gram G).a = ((D.gram G).a.toNat : ℤ) from ⟨D,he.symm⟩)
    have hcast : (Nat.find hexA : ℤ) ≤ ((D.gram G).a.toNat : ℤ) := by exact_mod_cast hh
    rwa [he] at hcast
  have hexM : ∃ n : ℕ, ∃ B : TernaryUnimodularBasis,
      (B.gram G).a=(Nat.find hexA : ℤ) ∧ (B.gram G).minor=(n : ℤ) := by
    refine ⟨(B0.gram G).minor.toNat,B0,hB0,?_⟩
    exact (Int.toNat_of_nonneg (le_of_lt (IntegralTernaryGram.minor_pos (B0.gram_positive G hG)))).symm
  obtain ⟨B,hBA,hBM⟩ := Nat.find_spec hexM
  refine ⟨B,?_,?_⟩
  · intro D
    rw [hBA]
    exact hAmin D
  · intro D hD
    have hm := IntegralTernaryGram.minor_pos (D.gram_positive G hG)
    have he := Int.toNat_of_nonneg (le_of_lt hm)
    have hh := Nat.find_min' hexM (show ∃ E : TernaryUnimodularBasis,
      (E.gram G).a=(Nat.find hexA : ℤ) ∧
        (E.gram G).minor=((D.gram G).minor.toNat : ℤ) from ⟨D,hD.trans hBA,he.symm⟩)
    rw [hBM]
    have hcast : (Nat.find hexM : ℤ) ≤ ((D.gram G).minor.toNat : ℤ) := by exact_mod_cast hh
    rwa [he] at hcast

theorem minimal_of_a_minor {B D : TernaryUnimodularBasis} {G : IntegralTernaryGram}
    (hB : B.Minimal G) (ha : (D.gram G).a=(B.gram G).a)
    (hm : (D.gram G).minor=(B.gram G).minor) : D.Minimal G := by
  constructor
  · intro E
    rw [ha]
    exact hB.1 E
  · intro E hE
    rw [hm]
    exact hB.2 E (hE.trans ha)

end TernaryUnimodularBasis
end Ramanujan.MultiQuintuple
