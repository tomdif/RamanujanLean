import RamanujanTau.MultiQuintupleProjectiveCancellation

/-! An exact delayed first witness for the proposed quarter-prime bound. -/
namespace Ramanujan.MultiQuintuple
open PowerSeries
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private lemma short_index103 (b : Bool) (i : ℕ) (n : ℤ)
    (hi : i=1 ∨ i=22 ∨ i=37) (he : quintExp2 b 103 i n ≤ 4864) :
    n.natAbs ≤ 4 := by
  have hn : -4 ≤ n ∧ n ≤ 4 := by
    rcases hi with rfl | rfl | rfl <;> cases b <;>
      norm_num [quintExp2,quintExpA2,quintExpB2] at he <;>
      constructor <;> by_contra h <;>
      have hside : n ≤ -5 ∨ 5 ≤ n := by omega
    all_goals rcases hside with hside | hside <;>
      nlinarith [sq_nonneg (n+5),sq_nonneg (n-5)]
  omega

private lemma mem_short_box103 (K : ℕ) (hK : K ≤ 2432) (x : TripleQuintBranchIndex)
    (he : pointTripleExp2 103 1 22 37 x = 2*(K : ℤ)) : x ∈ tripleQuintBranchBox 3 := by
  rcases x with ⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩
  simp only [pointTripleExp2,tripleQuintExp2,pointB1,pointB2,pointB3,
    pointN1,pointN2,pointN3] at he
  have h1 := quintExp2_nonneg b1 103 1 n1 (by norm_num) (by norm_num)
  have h2 := quintExp2_nonneg b2 103 22 n2 (by norm_num) (by norm_num)
  have h3 := quintExp2_nonneg b3 103 37 n3 (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at he h1 h2 h3
  have hn1 := short_index103 b1 1 n1 (by simp) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn2 := short_index103 b2 22 n2 (by simp) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn3 := short_index103 b3 37 n3 (by simp) (by norm_num only [Nat.cast_ofNat]; omega)
  rw [tripleQuintBranchBox]
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨mem_quintBranchBox_of_natAbs_le 3 b1 n1 hn1,
    mem_quintBranchBox_of_natAbs_le 3 b2 n2 hn2⟩,
    mem_quintBranchBox_of_natAbs_le 3 b3 n3 hn3⟩

noncomputable def shortCoeff103 (K : ℕ) : ℤ :=
  ∑ x ∈ tripleQuintBranchBox 3, pointContribution 103 1 22 37 K x

lemma coeff_triple103_eq_short (K : ℕ) (hK : K ≤ 2432) :
    coeff K (quintupleSpecialized 103 1 * quintupleSpecialized 103 22 *
      quintupleSpecialized 103 37) = shortCoeff103 K := by
  rw [coeff_tripleQuintupleSpecialized_eq_finiteBox 103 1 22 37 K
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  unfold shortCoeff103
  apply Finset.sum_congr_of_eq_on_inter
  · intro x hx hnx
    by_contra hn
    have he : pointTripleExp2 103 1 22 37 x = 2*(K : ℤ) := by
      by_contra h; simp [pointContribution,h] at hn
    exact hnx (mem_short_box103 K hK x he)
  · intro x hx hnx
    by_contra hn
    have he : pointTripleExp2 103 1 22 37 x = 2*(K : ℤ) := by
      by_contra h; simp [pointContribution,h] at hn
    exact hnx (mem_tripleQuintBranchBox_of_exp 103 1 22 37 K x
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) he)
  · intro x hx hy; rfl

set_option maxHeartbeats 0 in
private theorem checked_values103 : ∀ n : Fin 24,
    shortCoeff103 (103*n.val+63) = if n.val=23 then (-1 : ℤ) else 0 := by
  decide +kernel

/-- The first 23 coefficients in this progression vanish, but the next is -1.
This is a statement about the actual infinite product, not a truncated model. -/
theorem first_witness103 :
    (∀ N : ℕ, N < 23 → coeff (103*N+63) (quintupleSpecialized 103 1 *
      quintupleSpecialized 103 22 * quintupleSpecialized 103 37) = 0) ∧
    coeff (103*23+63) (quintupleSpecialized 103 1 * quintupleSpecialized 103 22 *
      quintupleSpecialized 103 37) = -1 := by
  constructor
  · intro N hN
    rw [coeff_triple103_eq_short _ (by omega)]
    simpa only [ne_of_lt hN,if_false] using checked_values103 ⟨N,by omega⟩
  · rw [coeff_triple103_eq_short _ (by norm_num)]
    exact checked_values103 ⟨23,by omega⟩

end Ramanujan.MultiQuintuple
