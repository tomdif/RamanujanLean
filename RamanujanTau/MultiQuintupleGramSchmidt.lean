/-
# Rational Gram--Schmidt coordinates and size reduction
-/
import RamanujanTau.MultiQuintupleGramReduction

namespace Ramanujan.MultiQuintuple
namespace IntegralTernaryGram

def mu (G : IntegralTernaryGram) : ℚ := (G.d : ℚ)/G.a
def nu (G : IntegralTernaryGram) : ℚ := (G.e : ℚ)/G.a
def xi (G : IntegralTernaryGram) : ℚ := ((G.a : ℚ)*G.f-(G.d : ℚ)*G.e)/G.minor
def secondLength (G : IntegralTernaryGram) : ℚ := (G.minor : ℚ)/G.a
def thirdLength (G : IntegralTernaryGram) : ℚ := (G.det : ℚ)/G.minor

theorem secondLength_pos {G : IntegralTernaryGram} (hG : G.Positive) : 0 < G.secondLength := by
  exact div_pos (by exact_mod_cast minor_pos hG) (by exact_mod_cast a_pos hG)

theorem thirdLength_pos {G : IntegralTernaryGram} (hG : G.Positive) (hd : 0 < G.det) :
    0 < G.thirdLength := by
  exact div_pos (by exact_mod_cast hd) (by exact_mod_cast minor_pos hG)

theorem second_identity (G : IntegralTernaryGram) (ha : G.a ≠ 0) :
    G.secondLength+(G.a : ℚ)*G.mu^2 = G.b := by
  have haq : (G.a : ℚ) ≠ 0 := by exact_mod_cast ha
  simp only [secondLength,mu,minor,Int.cast_sub,Int.cast_mul,Int.cast_pow]
  field_simp
  ring

theorem projected_third_identity (G : IntegralTernaryGram) (ha : G.a ≠ 0) (hm : G.minor ≠ 0) :
    (G.a : ℚ)*(G.thirdLength+G.secondLength*G.xi^2) = (G.a : ℚ)*G.c-(G.e : ℚ)^2 := by
  have hmQ : (G.minor : ℚ) ≠ 0 := by exact_mod_cast hm
  have haQ : (G.a : ℚ) ≠ 0 := by exact_mod_cast ha
  unfold thirdLength secondLength xi
  field_simp
  simp only [minor,det,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  ring

theorem determinant_identity (G : IntegralTernaryGram) (ha : G.a ≠ 0) (hm : G.minor ≠ 0) :
    (G.a : ℚ)*G.secondLength*G.thirdLength = G.det := by
  have haQ : (G.a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hmQ : (G.minor : ℚ) ≠ 0 := by exact_mod_cast hm
  unfold secondLength thirdLength
  field_simp

set_option maxHeartbeats 0 in
theorem norm_gram_schmidt (G : IntegralTernaryGram) (ha : G.a ≠ 0) (hm : G.minor ≠ 0)
    (u : TernaryIntPoint) :
    (G.norm u : ℚ) = (G.a : ℚ)*((u.1.1 : ℚ)+G.mu*u.1.2+G.nu*u.2)^2+
      G.secondLength*((u.1.2 : ℚ)+G.xi*u.2)^2+G.thirdLength*(u.2 : ℚ)^2 := by
  have haQ : (G.a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hmQ : (G.minor : ℚ) ≠ 0 := by exact_mod_cast hm
  unfold mu nu xi secondLength thirdLength
  field_simp
  simp only [minor,det,norm,dot,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  ring

def Reduced (G : IntegralTernaryGram) : Prop :=
  |G.mu| ≤ 1/2 ∧ |G.nu| ≤ 1/2 ∧ |G.xi| ≤ 1/2 ∧
    3*(G.a : ℚ) ≤ 4*G.secondLength ∧ 3*G.secondLength ≤ 4*G.thirdLength

end IntegralTernaryGram
namespace TernaryUnimodularBasis
open IntegralTernaryGram

theorem shear2_parameters (B : TernaryUnimodularBasis) (G : IntegralTernaryGram)
    (n : ℤ) (hG : G.Positive) :
    ((B.shear2 n).gram G).mu = (B.gram G).mu-n ∧
    ((B.shear2 n).gram G).nu = (B.gram G).nu ∧
    ((B.shear2 n).gram G).xi = (B.gram G).xi := by
  have ha : ((B.gram G).a : ℚ) ≠ 0 := by exact_mod_cast (a_pos (B.gram_positive G hG)).ne'
  have hm : ((B.gram G).minor : ℚ) ≠ 0 := by exact_mod_cast (minor_pos (B.gram_positive G hG)).ne'
  have hm' := (shear2_a_minor B G n).2
  constructor
  · rw [shear2_gram]
    simp only [mu,Int.cast_sub,Int.cast_mul]
    field_simp <;> ring
  constructor
  · rfl
  · unfold xi
    rw [hm',shear2_gram]
    simp only [Int.cast_sub,Int.cast_mul]
    congr 1
    ring

theorem shear3_parameters (B : TernaryUnimodularBasis) (G : IntegralTernaryGram)
    (n m : ℤ) (hG : G.Positive) :
    ((B.shear3 n m).gram G).mu = (B.gram G).mu ∧
    ((B.shear3 n m).gram G).nu = (B.gram G).nu-n*(B.gram G).mu-m ∧
    ((B.shear3 n m).gram G).xi = (B.gram G).xi-n := by
  have ha : ((B.gram G).a : ℚ) ≠ 0 := by exact_mod_cast (a_pos (B.gram_positive G hG)).ne'
  have hm : ((B.gram G).minor : ℚ) ≠ 0 := by exact_mod_cast (minor_pos (B.gram_positive G hG)).ne'
  have hm' := (shear3_a_minor B G n m).2
  refine ⟨rfl,?_,?_⟩
  · rw [shear3_gram]
    simp only [nu,mu,Int.cast_sub,Int.cast_mul]
    field_simp <;> ring
  · unfold xi
    rw [hm',shear3_gram]
    simp only [Int.cast_sub,Int.cast_mul]
    field_simp
    simp only [minor,Int.cast_sub,Int.cast_mul,Int.cast_pow]
    ring

theorem exists_minimal_size_reduced (G : IntegralTernaryGram) (hG : G.Positive) :
    ∃ B : TernaryUnimodularBasis, B.Minimal G ∧
      |(B.gram G).mu| ≤ 1/2 ∧ |(B.gram G).nu| ≤ 1/2 ∧ |(B.gram G).xi| ≤ 1/2 := by
  obtain ⟨B,hB⟩ := exists_minimal G hG
  let D := B.shear2 (round (B.gram G).mu)
  have hD : D.Minimal G := minimal_of_a_minor hB (shear2_a_minor _ _ _).1 (shear2_a_minor _ _ _).2
  have hmu : |(D.gram G).mu| ≤ 1/2 := by
    rw [(shear2_parameters B G _ hG).1]
    exact abs_sub_round _
  let n := round (D.gram G).xi
  let m := round ((D.gram G).nu-(n : ℚ)*(D.gram G).mu)
  let E := D.shear3 n m
  have hE : E.Minimal G := minimal_of_a_minor hD (shear3_a_minor _ _ _ _).1 (shear3_a_minor _ _ _ _).2
  obtain ⟨heMu,heNu,heXi⟩ := shear3_parameters D G n m hG
  refine ⟨E,hE,?_,?_,?_⟩
  · rw [heMu]
    exact hmu
  · rw [heNu]
    exact abs_sub_round _
  · rw [heXi]
    exact abs_sub_round _

theorem reduced_of_minimal_size_reduced
    (B : TernaryUnimodularBasis) (G : IntegralTernaryGram) (hG : G.Positive)
    (hmin : B.Minimal G) (hmu : |(B.gram G).mu| ≤ 1/2)
    (hnu : |(B.gram G).nu| ≤ 1/2) (hxi : |(B.gram G).xi| ≤ 1/2) :
    (B.gram G).Reduced := by
  let H := B.gram G
  have hH : H.Positive := B.gram_positive G hG
  have haZ : 0 < H.a := a_pos hH
  have hmZ : 0 < H.minor := minor_pos hH
  have ha : (0 : ℚ) < H.a := by exact_mod_cast haZ
  have hb : 0 < H.secondLength := secondLength_pos hH
  have hmu2 : H.mu^2 ≤ (1/2 : ℚ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hmu 2
  have hxi2 : H.xi^2 ≤ (1/2 : ℚ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hxi 2
  have hamu := mul_le_mul_of_nonneg_left hmu2 ha.le
  have hbxi := mul_le_mul_of_nonneg_left hxi2 hb.le
  have hfirst : H.a ≤ H.b := hmin.1 B.swap12
  have hfirstQ : (H.a : ℚ) ≤ H.b := by exact_mod_cast hfirst
  have hsecond := second_identity H haZ.ne'
  have hminor : H.minor ≤ H.a*H.c-H.e^2 := hmin.2 B.swap23 rfl
  have hminorQ : (H.minor : ℚ) ≤ (H.a : ℚ)*H.c-(H.e : ℚ)^2 := by exact_mod_cast hminor
  have hab : (H.a : ℚ)*H.secondLength = H.minor := by
    unfold secondLength
    field_simp
  have hthird := projected_third_identity H haZ.ne' hmZ.ne'
  have hproj : H.secondLength ≤ H.thirdLength+H.secondLength*H.xi^2 := by
    have hscaled : (H.a : ℚ)*H.secondLength ≤ (H.a : ℚ)*(H.thirdLength+H.secondLength*H.xi^2) := by
      rw [hab,hthird]
      exact hminorQ
    nlinarith
  exact ⟨hmu,hnu,hxi,by nlinarith,by nlinarith⟩

/-- Every positive integral ternary form has an integral basis with all
three size-reduction bounds and both successive-length inequalities. -/
theorem exists_reduced (G : IntegralTernaryGram) (hG : G.Positive) :
    ∃ B : TernaryUnimodularBasis, (B.gram G).Reduced := by
  obtain ⟨B,hmin,hmu,hnu,hxi⟩ := exists_minimal_size_reduced G hG
  exact ⟨B,reduced_of_minimal_size_reduced B G hG hmin hmu hnu hxi⟩

end TernaryUnimodularBasis
end Ramanujan.MultiQuintuple
