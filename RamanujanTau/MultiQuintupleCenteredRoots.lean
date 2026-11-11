import RamanujanTau.MultiQuintupleFullConverse

/-!
# Centered representatives suffice for the projective-root search

Every root in the admissible classification is recovered from its projective
scalar by taking centered residues. This is the completeness ingredient of
the reference algorithm in `scripts/classify_sparse_triple.py`.
-/
namespace Ramanujan.MultiQuintuple

def centeredRootResidue (p : ℕ) (a : ℤ) : ℤ :=
  (a + (p : ℤ) / 2) % p - (p : ℤ) / 2

lemma short_root_coordinate_bound (p : ℕ) (hp : 7 ≤ p) (x : ℤ)
    (hx : x*x ≤ 2*(p : ℤ)) :
    -((p : ℤ)/2) ≤ x ∧ x ≤ (p : ℤ)/2 := by
  have hpz : (7 : ℤ) ≤ p := by exact_mod_cast hp
  have hdiv := Int.emod_nonneg (p : ℤ) (by norm_num : (2 : ℤ) ≠ 0)
  have hmod := Int.emod_lt_of_pos (p : ℤ) (by norm_num : (0 : ℤ) < 2)
  have he := Int.mul_ediv_add_emod (p : ℤ) 2
  constructor
  · by_contra h
    have hb : x ≤ -((p : ℤ)/2)-1 := by omega
    have hq : (3 : ℤ) ≤ (p : ℤ)/2 := by omega
    have hs := mul_nonneg (show 0 ≤ -x-((p : ℤ)/2+1) by omega)
      (show 0 ≤ -x+((p : ℤ)/2+1) by omega)
    nlinarith [sq_nonneg ((p : ℤ)/2-3)]
  · by_contra h
    have hb : (p : ℤ)/2+1 ≤ x := by omega
    have hq : (3 : ℤ) ≤ (p : ℤ)/2 := by omega
    have hs := mul_nonneg (show 0 ≤ x-((p : ℤ)/2+1) by omega)
      (show 0 ≤ x+((p : ℤ)/2+1) by omega)
    nlinarith [sq_nonneg ((p : ℤ)/2-3)]

lemma eq_centeredRootResidue (p : ℕ) (hp : 0 < p) (hodd : Odd p)
    (x a : ℤ) (hx : -((p : ℤ)/2) ≤ x ∧ x ≤ (p : ℤ)/2)
    (hcong : (p : ℤ) ∣ x-a) : x = centeredRootResidue p a := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have heq : (p : ℤ) = 2*((p : ℤ)/2)+1 := by
    obtain ⟨k,hk⟩ := hodd
    have hkz : (p : ℤ)=2*(k : ℤ)+1 := by exact_mod_cast hk
    omega
  have hxa : x % (p : ℤ) = a % p := by
    exact (Int.modEq_iff_dvd).mpr (by simpa only [neg_sub] using dvd_neg.mpr hcong)
  have hshift : (x+(p : ℤ)/2) % p = (a+(p : ℤ)/2) % p := by
    conv_lhs => rw [Int.add_emod]
    conv_rhs => rw [Int.add_emod]
    rw [hxa]
  have hr : 0 ≤ x+(p : ℤ)/2 ∧ x+(p : ℤ)/2 < p := by omega
  rw [Int.emod_eq_of_lt hr.1 hr.2] at hshift
  unfold centeredRootResidue
  omega

/-- Each coordinate of any root certificate is forced by its scalar. -/
theorem projectiveRootTarget_centered {p i j k R : ℕ}
    (ha : AdmissibleSparseTriple p i j k)
    (root : ProjectiveRootTargetCertificate p i j k R) :
    root.w1 = centeredRootResidue p (root.lambda*i) ∧
    root.w2 = centeredRootResidue p (root.lambda*j) ∧
    root.w3 = centeredRootResidue p (root.lambda*k) := by
  have hp7 : 7 ≤ p := by
    rcases ha with ⟨_,_,hi,hij,hjk,hk,_⟩
    omega
  have hodd : Odd p := ha.1.odd_of_ne_two (by omega)
  have hnorm := root.hroot
  simp only [ternaryNorm] at hnorm
  have hle : root.w1*root.w1+root.w2*root.w2+root.w3*root.w3 ≤ 2*(p : ℤ) := by
    rcases root.he with he | he <;> rw [he] at hnorm <;> nlinarith
  have bounds (x y z : ℤ) (h : x*x+y*y+z*z ≤ 2*(p : ℤ)) :
      -((p : ℤ)/2) ≤ x ∧ x ≤ (p : ℤ)/2 := by
    exact short_root_coordinate_bound p hp7 x (by nlinarith [sq_nonneg y,sq_nonneg z])
  refine ⟨eq_centeredRootResidue p (by omega) hodd _ _ (bounds _ _ _ hle) ?_,
    eq_centeredRootResidue p (by omega) hodd _ _ (bounds root.w2 root.w1 root.w3 (by linarith)) ?_,
    eq_centeredRootResidue p (by omega) hodd _ _ (bounds root.w3 root.w1 root.w2 (by linarith)) ?_⟩
  · exact ⟨root.a1, by rw [root.hw1]; ring⟩
  · exact ⟨root.a2, by rw [root.hw2]; ring⟩
  · exact ⟨root.a3, by rw [root.hw3]; ring⟩

end Ramanujan.MultiQuintuple
