import RamanujanTau.MultiQuintupleFourCancellation

/-! An exact seven-step delay for an admissible four-factor product at 17. -/
namespace Ramanujan.MultiQuintuple
open PowerSeries
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private lemma short_index17 (b : Bool) (i : ℕ) (n : ℤ)
    (hi : 1 ≤ i) (hi8 : i ≤ 8) (he : quintExp2 b 17 i n ≤ 248) :
    n.natAbs ≤ 2 := by
  have hn : -2 ≤ n ∧ n ≤ 2 := by
    interval_cases i <;> cases b <;>
      norm_num [quintExp2,quintExpA2,quintExpB2] at he <;>
      constructor <;> by_contra h <;>
      have hside : n ≤ -3 ∨ 3 ≤ n := by omega
    all_goals rcases hside with hside | hside <;>
      nlinarith [sq_nonneg (n+3),sq_nonneg (n-3)]
  omega

private lemma mem_short_box17 (K : ℕ) (hK : K ≤ 124) (x : QuadQuintBranchIndex)
    (he : quadExp2 17 2 3 5 8 x = 2*(K : ℤ)) : x ∈ quadBox 1 := by
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  simp only [quadExp2,pointTripleExp2,tripleQuintExp2,pointB1,pointB2,pointB3,
    pointN1,pointN2,pointN3,quadB4,quadN4] at he
  have h1 := quintExp2_nonneg b1 17 2 n1 (by norm_num) (by norm_num)
  have h2 := quintExp2_nonneg b2 17 3 n2 (by norm_num) (by norm_num)
  have h3 := quintExp2_nonneg b3 17 5 n3 (by norm_num) (by norm_num)
  have h4 := quintExp2_nonneg b4 17 8 n4 (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at he h1 h2 h3 h4
  have hn1 := short_index17 b1 2 n1 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn2 := short_index17 b2 3 n2 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn3 := short_index17 b3 5 n3 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn4 := short_index17 b4 8 n4 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  rw [quadBox,tripleQuintBranchBox]
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨mem_quintBranchBox_of_natAbs_le 1 b1 n1 hn1,
    mem_quintBranchBox_of_natAbs_le 1 b2 n2 hn2⟩,
    mem_quintBranchBox_of_natAbs_le 1 b3 n3 hn3⟩,
    mem_quintBranchBox_of_natAbs_le 1 b4 n4 hn4⟩

noncomputable def four17ShortCoeff (K : ℕ) : ℤ :=
  ∑ x ∈ quadBox 1, quadContribution 17 2 3 5 8 K x

lemma coeff_four17_eq_short (K : ℕ) (hK : K ≤ 124) :
    coeff K (quintupleSpecialized 17 2 * quintupleSpecialized 17 3 *
      quintupleSpecialized 17 5 * quintupleSpecialized 17 8) = four17ShortCoeff K := by
  rw [coeff_quad_eq_finiteBox 17 2 3 5 8 K
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  unfold four17ShortCoeff
  apply Finset.sum_congr_of_eq_on_inter
  · intro x hx hnx
    by_contra hn
    have he : quadExp2 17 2 3 5 8 x = 2*(K : ℤ) := by
      by_contra h; simp [quadContribution,h] at hn
    exact hnx (mem_short_box17 K hK x he)
  · intro x hx hnx
    by_contra hn
    have he : quadExp2 17 2 3 5 8 x = 2*(K : ℤ) := by
      by_contra h; simp [quadContribution,h] at hn
    exact hnx (mem_quadBox_of_exp 17 2 3 5 8 K x
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) he)

  · intro x hx hy; rfl


set_option maxHeartbeats 0 in
private theorem checked_values_four17 : ∀ n : Fin 8,
    four17ShortCoeff (17*n.val+5) = if n.val=7 then (1 : ℤ) else 0 := by
  decide +kernel

/-- The actual four-factor progression has its first nonzero coefficient at N=7. -/
theorem first_witness_four17 :
    (∀ N : ℕ, N < 7 → coeff (17*N+5) (quintupleSpecialized 17 2 *
      quintupleSpecialized 17 3 * quintupleSpecialized 17 5 * quintupleSpecialized 17 8)=0) ∧
    coeff (17*7+5) (quintupleSpecialized 17 2 * quintupleSpecialized 17 3 *
      quintupleSpecialized 17 5 * quintupleSpecialized 17 8)=1 := by
  constructor
  · intro N hN
    rw [coeff_four17_eq_short _ (by omega)]
    simpa only [ne_of_lt hN,if_false] using checked_values_four17 ⟨N,by omega⟩
  · rw [coeff_four17_eq_short _ (by norm_num)]
    exact checked_values_four17 ⟨7,by omega⟩

/-- Even the first seven terms do not certify persistent vanishing for this product. -/
theorem four17_cutoff_six_fails :
    (∀ N : ℕ, N ≤ 6 → coeff (17*N+5) (quintupleSpecialized 17 2 *
      quintupleSpecialized 17 3 * quintupleSpecialized 17 5 * quintupleSpecialized 17 8)=0) ∧
    ¬ (∀ N : ℕ, coeff (17*N+5) (quintupleSpecialized 17 2 *
      quintupleSpecialized 17 3 * quintupleSpecialized 17 5 * quintupleSpecialized 17 8)=0) := by
  refine ⟨fun N hN => first_witness_four17.1 N (by omega),?_⟩
  intro h
  have hh := h 7
  rw [first_witness_four17.2] at hh
  norm_num at hh

end Ramanujan.MultiQuintuple
