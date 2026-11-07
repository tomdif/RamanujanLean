/-
# Persistent coefficient vanishing gives the actual primal Gaussian identity
-/
import RamanujanTau.MultiQuintupleThetaRigidity
import RamanujanTau.MultiQuintupleGaussianUniqueness

namespace Ramanujan.MultiQuintuple
open PowerSeries

noncomputable def pointNaturalDegree (p i j k : ℕ) (x : TripleQuintBranchIndex) : ℕ :=
  quintExpHalf (pointB1 x) p i (pointN1 x)+quintExpHalf (pointB2 x) p j (pointN2 x)+
    quintExpHalf (pointB3 x) p k (pointN3 x)

theorem pointTripleExp2_eq_degree {p i j k : ℕ} (ha : AdmissibleSparseTriple p i j k)
    (x : TripleQuintBranchIndex) :
    pointTripleExp2 p i j k x = 2*(pointNaturalDegree p i j k x : ℤ) := by
  obtain ⟨hp,hp3,hi,hij,hjk,hkp,hiso⟩ := ha
  have h1 := quintExp2_eq_two_mul_quintExpHalf (pointB1 x) p i (pointN1 x) hi (by omega)
  have h2 := quintExp2_eq_two_mul_quintExpHalf (pointB2 x) p j (pointN2 x) (by omega) (by omega)
  have h3 := quintExp2_eq_two_mul_quintExpHalf (pointB3 x) p k (pointN3 x) (by omega) hkp
  simp only [pointTripleExp2,tripleQuintExp2,pointNaturalDegree,Nat.cast_add]
  linear_combination h1+h2+h3

theorem pointNaturalDegree_eq_iff {p i j k : ℕ} (ha : AdmissibleSparseTriple p i j k)
    (x : TripleQuintBranchIndex) (K : ℕ) :
    pointNaturalDegree p i j k x=K ↔ pointTripleExp2 p i j k x=2*(K : ℤ) := by
  rw [pointTripleExp2_eq_degree ha x]
  omega

theorem degree_fiber_weight_eq_coefficient {p i j k : ℕ}
    (ha : AdmissibleSparseTriple p i j k) (K : ℕ) :
    (∑' x : (pointNaturalDegree p i j k) ⁻¹' {K}, (pointBranchWeight x : ℂ)) =
      ((coeff K (quintupleSpecialized p i*quintupleSpecialized p j*quintupleSpecialized p k) : ℤ) : ℂ) := by
  classical
  obtain ⟨hp,hp3,hi,hij,hjk,hkp,hiso⟩ := ha
  have ha : AdmissibleSparseTriple p i j k := ⟨hp,hp3,hi,hij,hjk,hkp,hiso⟩
  rw [tsum_subtype ((pointNaturalDegree p i j k) ⁻¹' {K})
    (fun x : TripleQuintBranchIndex => (pointBranchWeight x : ℂ))]
  rw [tsum_eq_sum (s := tripleQuintBranchBox K) (fun x hx => ?_)]
  · rw [coeff_tripleQuintupleSpecialized_eq_finiteBox p i j k K hi (by omega)
      (by omega) (by omega) (by omega) hkp]
    push_cast
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Set.indicator_apply,Set.mem_preimage,Set.mem_singleton_iff,pointContribution]
    by_cases hd : pointNaturalDegree p i j k x=K
    · simp [hd,(pointNaturalDegree_eq_iff ha x K).mp hd]
    · simp [hd,((pointNaturalDegree_eq_iff ha x K).not).mp hd]
  · simp only [Set.indicator_apply,Set.mem_preimage,Set.mem_singleton_iff]
    split_ifs with hd
    · exact False.elim (hx (mem_tripleQuintBranchBox_of_exp p i j k K x hi (by omega)
        (by omega) (by omega) (by omega) hkp ((pointNaturalDegree_eq_iff ha x K).mp hd)))
    · rfl

/-- Any scalar weighting of the coefficient shells in the vanishing
progression sums to zero. This statement includes the Gaussian weighting. -/
theorem persistent_vanishing_weighted_sum {p i j k R : ℕ}
    (ha : AdmissibleSparseTriple p i j k) (hv : PersistentTripleVanishing p i j k R)
    (g : ℕ → ℂ) :
    (∑' x : TripleQuintBranchIndex,
      if pointNaturalDegree p i j k x % p=R then
        (pointBranchWeight x : ℂ)*g (pointNaturalDegree p i j k x) else 0)=0 := by
  classical
  apply tsum_zero_of_fiber_sums_zero _ (pointNaturalDegree p i j k)
  intro K
  have hf : ∀ x : (pointNaturalDegree p i j k) ⁻¹' {K}, pointNaturalDegree p i j k x=K :=
    fun x => x.property
  simp only [hf]
  by_cases hK : K % p=R
  · simp only [hK,if_true]
    rw [tsum_mul_right,degree_fiber_weight_eq_coefficient ha K]
    have hdegree : K=p*(K/p)+R := by have := Nat.mod_add_div K p; omega
    rw [hdegree,hv (K/p)]
    simp
  · simp [hK]

theorem degree_mod_iff_residue {p i j k R : ℕ} (ha : AdmissibleSparseTriple p i j k)
    (hR : R < p) (x : TripleQuintBranchIndex) :
    pointNaturalDegree p i j k x % p=R ↔ InThetaResidueFiber p i j k R x := by
  have hp := ha.1
  obtain ⟨_,hp3,hi,hij,hjk,hkp,hiso⟩ := ha
  have ha : AdmissibleSparseTriple p i j k := ⟨hp,hp3,hi,hij,hjk,hkp,hiso⟩
  rw [← onThetaProgression_iff_inThetaResidueFiber p i j k R x hi (by omega)
    (by omega) (by omega) (by omega) hkp (by exact_mod_cast hp.odd_of_ne_two (by omega)) hR]
  unfold OnThetaProgression
  simp_rw [← pointNaturalDegree_eq_iff ha]
  constructor
  · intro h
    exact ⟨pointNaturalDegree p i j k x/p,by
      have := Nat.mod_add_div (pointNaturalDegree p i j k x) p
      omega⟩
  · rintro ⟨N,hN⟩
    simp [hN,Nat.mod_eq_of_lt hR]

noncomputable def watsonProgressionGaussian (p i j k R : ℕ) (t : ℝ) : ℂ := by
  classical
  exact ∑' x : TripleQuintBranchIndex,
    if InThetaResidueFiber p i j k R x then
      (pointBranchWeight x : ℂ)*Complex.exp
        (-Real.pi*(t : ℂ)*(pointThetaNorm p i j k x : ℂ)/(36*(p : ℂ)^2)) else 0

/-- The Gaussian on the actual eight Watson cosets vanishes at every
parameter when every actual product coefficient in the progression vanishes. -/
theorem persistent_vanishing_primal_gaussian {p i j k R : ℕ}
    (ha : AdmissibleSparseTriple p i j k) (hR : R < p)
    (hv : PersistentTripleVanishing p i j k R) (t : ℝ) :
    watsonProgressionGaussian p i j k R t=0 := by
  classical
  have hh := persistent_vanishing_weighted_sum ha hv (fun K =>
    Complex.exp (-Real.pi*(t : ℂ)*((24*(p : ℤ)*K+tripleThetaOffset p i j k : ℤ) : ℂ)/
      (36*(p : ℂ)^2)))
  convert hh using 1
  apply tsum_congr
  intro x
  simp only [degree_mod_iff_residue ha hR]
  split_ifs
  · congr 2
    have he := pointThetaNorm_eq_squareCompletion p i j k x
    rw [pointTripleExp2_eq_degree ha x] at he
    have he' : pointThetaNorm p i j k x =
        24*(p : ℤ)*(pointNaturalDegree p i j k x : ℤ)+tripleThetaOffset p i j k := by
      linear_combination he
    rw [he']
  · rfl

end Ramanujan.MultiQuintuple
