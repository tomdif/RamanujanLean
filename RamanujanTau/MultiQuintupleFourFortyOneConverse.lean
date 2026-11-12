import RamanujanTau.MultiQuintupleFourFortyOne

/-! Complete residue classification for the four-factor example at 41. -/
namespace Ramanujan.MultiQuintuple
open PowerSeries
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
-- Keep kernel coefficient checks sequential on memory-limited runners.
set_option Elab.async false

private lemma short_index41 (b : Bool) (i : ℕ) (n : ℤ)
    (hi : 1 ≤ i) (hi9 : i ≤ 9) (he : quintExp2 b 41 i n ≤ 430) :
    n.natAbs ≤ 2 := by
  have hn : -2 ≤ n ∧ n ≤ 2 := by
    interval_cases i <;> cases b <;>
      norm_num [quintExp2,quintExpA2,quintExpB2] at he <;>
      constructor <;> by_contra h <;>
      have hside : n ≤ -3 ∨ 3 ≤ n := by omega
    all_goals rcases hside with hside | hside <;>
      nlinarith [sq_nonneg (n+3),sq_nonneg (n-3)]
  omega

private lemma mem_short_box41 (K : ℕ) (hK : K ≤ 215) (x : QuadQuintBranchIndex)
    (he : quadExp2 41 1 4 5 9 x = 2*(K : ℤ)) : x ∈ quadBox 1 := by
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  simp only [quadExp2,pointTripleExp2,tripleQuintExp2,pointB1,pointB2,pointB3,
    pointN1,pointN2,pointN3,quadB4,quadN4] at he
  have h1 := quintExp2_nonneg b1 41 1 n1 (by norm_num) (by norm_num)
  have h2 := quintExp2_nonneg b2 41 4 n2 (by norm_num) (by norm_num)
  have h3 := quintExp2_nonneg b3 41 5 n3 (by norm_num) (by norm_num)
  have h4 := quintExp2_nonneg b4 41 9 n4 (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at he h1 h2 h3 h4
  have hn1 := short_index41 b1 1 n1 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn2 := short_index41 b2 4 n2 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn3 := short_index41 b3 5 n3 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn4 := short_index41 b4 9 n4 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  rw [quadBox,tripleQuintBranchBox]
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨mem_quintBranchBox_of_natAbs_le 1 b1 n1 hn1,
    mem_quintBranchBox_of_natAbs_le 1 b2 n2 hn2⟩,
    mem_quintBranchBox_of_natAbs_le 1 b3 n3 hn3⟩,
    mem_quintBranchBox_of_natAbs_le 1 b4 n4 hn4⟩

noncomputable def four41ShortCoeff (K : ℕ) : ℤ :=
  ∑ x ∈ quadBox 1, quadContribution 41 1 4 5 9 K x

lemma coeff_four41_eq_short (K : ℕ) (hK : K ≤ 215) :
    coeff K (quintupleSpecialized 41 1 * quintupleSpecialized 41 4 *
      quintupleSpecialized 41 5 * quintupleSpecialized 41 9) = four41ShortCoeff K := by
  rw [coeff_quad_eq_finiteBox 41 1 4 5 9 K
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  unfold four41ShortCoeff
  apply Finset.sum_congr_of_eq_on_inter
  · intro x hx hnx
    by_contra hn
    have he : quadExp2 41 1 4 5 9 x = 2*(K : ℤ) := by
      by_contra h; simp [quadContribution,h] at hn
    exact hnx (mem_short_box41 K hK x he)
  · intro x hx hnx
    by_contra hn
    have he : quadExp2 41 1 4 5 9 x = 2*(K : ℤ) := by
      by_contra h; simp [quadContribution,h] at hn
    exact hnx (mem_quadBox_of_exp 41 1 4 5 9 K x
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) he)

  · intro x hx hy; rfl


set_option maxHeartbeats 0 in
private theorem coefficient41_0 : four41ShortCoeff 0 = (1 : ℤ) := by
  decide +kernel

-- A smaller proved coefficient box keeps the numerical checks inexpensive.
private lemma short_index41_one (b : Bool) (i : ℕ) (n : ℤ)
    (hi : 1 ≤ i) (hi9 : i ≤ 9) (he : quintExp2 b 41 i n ≤ 318) :
    n.natAbs ≤ 1 := by
  have hn : -1 ≤ n ∧ n ≤ 1 := by
    interval_cases i <;> cases b <;>
      norm_num [quintExp2,quintExpA2,quintExpB2] at he <;>
      constructor <;> by_contra h <;>
      have hside : n ≤ -2 ∨ 2 ≤ n := by omega
    all_goals rcases hside with hside | hside <;>
      nlinarith [sq_nonneg (n+2),sq_nonneg (n-2)]
  omega

private lemma mem_short_box41_one (K : ℕ) (hK : K ≤ 159) (x : QuadQuintBranchIndex)
    (he : quadExp2 41 1 4 5 9 x = 2*(K : ℤ)) : x ∈ quadBox 0 := by
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  simp only [quadExp2,pointTripleExp2,tripleQuintExp2,pointB1,pointB2,pointB3,
    pointN1,pointN2,pointN3,quadB4,quadN4] at he
  have h1 := quintExp2_nonneg b1 41 1 n1 (by norm_num) (by norm_num)
  have h2 := quintExp2_nonneg b2 41 4 n2 (by norm_num) (by norm_num)
  have h3 := quintExp2_nonneg b3 41 5 n3 (by norm_num) (by norm_num)
  have h4 := quintExp2_nonneg b4 41 9 n4 (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at he h1 h2 h3 h4
  have hn1 := short_index41_one b1 1 n1 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn2 := short_index41_one b2 4 n2 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn3 := short_index41_one b3 5 n3 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn4 := short_index41_one b4 9 n4 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  rw [quadBox,tripleQuintBranchBox]
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨mem_quintBranchBox_of_natAbs_le 0 b1 n1 hn1,
    mem_quintBranchBox_of_natAbs_le 0 b2 n2 hn2⟩,
    mem_quintBranchBox_of_natAbs_le 0 b3 n3 hn3⟩,
    mem_quintBranchBox_of_natAbs_le 0 b4 n4 hn4⟩

private noncomputable def four41SmallCoeff (K : ℕ) : ℤ :=
  ∑ x ∈ quadBox 0, quadContribution 41 1 4 5 9 K x

private lemma coeff_four41_eq_small (K : ℕ) (hK : K ≤ 159) :
    coeff K (quintupleSpecialized 41 1 * quintupleSpecialized 41 4 *
      quintupleSpecialized 41 5 * quintupleSpecialized 41 9) = four41SmallCoeff K := by
  rw [coeff_quad_eq_finiteBox 41 1 4 5 9 K
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  unfold four41SmallCoeff
  apply Finset.sum_congr_of_eq_on_inter
  · intro x hx hnx
    by_contra hn
    have he : quadExp2 41 1 4 5 9 x = 2*(K : ℤ) := by
      by_contra h; simp [quadContribution,h] at hn
    exact hnx (mem_short_box41_one K hK x he)
  · intro x hx hnx
    by_contra hn
    have he : quadExp2 41 1 4 5 9 x = 2*(K : ℤ) := by
      by_contra h; simp [quadContribution,h] at hn
    exact hnx (mem_quadBox_of_exp 41 1 4 5 9 K x
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) he)

  · intro x hx hy; rfl


set_option maxHeartbeats 0 in
private theorem coefficient41_1 : four41ShortCoeff 1 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 1 (by norm_num),coeff_four41_eq_small 1 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_2 : four41ShortCoeff 84 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 84 (by norm_num),coeff_four41_eq_small 84 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_3 : four41ShortCoeff 44 = (1 : ℤ) := by
  rw [← coeff_four41_eq_short 44 (by norm_num),coeff_four41_eq_small 44 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_4 : four41ShortCoeff 4 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 4 (by norm_num),coeff_four41_eq_small 4 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_5 : four41ShortCoeff 169 = (1 : ℤ) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_6 : four41ShortCoeff 6 = (1 : ℤ) := by
  rw [← coeff_four41_eq_short 6 (by norm_num),coeff_four41_eq_small 6 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_7 : four41ShortCoeff 212 = (1 : ℤ) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_8 : four41ShortCoeff 49 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 49 (by norm_num),coeff_four41_eq_small 49 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_9 : four41ShortCoeff 132 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 132 (by norm_num),coeff_four41_eq_small 132 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_10 : four41ShortCoeff 215 = (-1 : ℤ) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_11 : four41ShortCoeff 52 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 52 (by norm_num),coeff_four41_eq_small 52 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_12 : four41ShortCoeff 94 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 94 (by norm_num),coeff_four41_eq_small 94 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_13 : four41ShortCoeff 13 = (1 : ℤ) := by
  rw [← coeff_four41_eq_short 13 (by norm_num),coeff_four41_eq_small 13 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_14 : four41ShortCoeff 137 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 137 (by norm_num),coeff_four41_eq_small 137 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_15 : four41ShortCoeff 15 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 15 (by norm_num),coeff_four41_eq_small 15 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_16 : four41ShortCoeff 98 = (3 : ℤ) := by
  rw [← coeff_four41_eq_short 98 (by norm_num),coeff_four41_eq_small 98 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_17 : four41ShortCoeff 58 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 58 (by norm_num),coeff_four41_eq_small 58 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_18 : four41ShortCoeff 18 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 18 (by norm_num),coeff_four41_eq_small 18 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_19 : four41ShortCoeff 19 = (1 : ℤ) := by
  rw [← coeff_four41_eq_short 19 (by norm_num),coeff_four41_eq_small 19 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_20 : four41ShortCoeff 61 = (1 : ℤ) := by
  rw [← coeff_four41_eq_short 61 (by norm_num),coeff_four41_eq_small 61 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_22 : four41ShortCoeff 63 = (1 : ℤ) := by
  rw [← coeff_four41_eq_short 63 (by norm_num),coeff_four41_eq_small 63 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_23 : four41ShortCoeff 23 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 23 (by norm_num),coeff_four41_eq_small 23 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_24 : four41ShortCoeff 24 = (1 : ℤ) := by
  rw [← coeff_four41_eq_short 24 (by norm_num),coeff_four41_eq_small 24 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_27 : four41ShortCoeff 27 = (1 : ℤ) := by
  rw [← coeff_four41_eq_short 27 (by norm_num),coeff_four41_eq_small 27 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_28 : four41ShortCoeff 110 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 110 (by norm_num),coeff_four41_eq_small 110 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_29 : four41ShortCoeff 29 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 29 (by norm_num),coeff_four41_eq_small 29 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_31 : four41ShortCoeff 31 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 31 (by norm_num),coeff_four41_eq_small 31 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_32 : four41ShortCoeff 73 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 73 (by norm_num),coeff_four41_eq_small 73 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_33 : four41ShortCoeff 74 = (1 : ℤ) := by
  rw [← coeff_four41_eq_short 74 (by norm_num),coeff_four41_eq_small 74 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_34 : four41ShortCoeff 34 = (1 : ℤ) := by
  rw [← coeff_four41_eq_short 34 (by norm_num),coeff_four41_eq_small 34 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_35 : four41ShortCoeff 35 = (1 : ℤ) := by
  rw [← coeff_four41_eq_short 35 (by norm_num),coeff_four41_eq_small 35 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_36 : four41ShortCoeff 36 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 36 (by norm_num),coeff_four41_eq_small 36 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_37 : four41ShortCoeff 78 = (-1 : ℤ) := by
  rw [← coeff_four41_eq_short 78 (by norm_num),coeff_four41_eq_small 78 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_38 : four41ShortCoeff 38 = (1 : ℤ) := by
  rw [← coeff_four41_eq_short 38 (by norm_num),coeff_four41_eq_small 38 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_39 : four41ShortCoeff 39 = (-2 : ℤ) := by
  rw [← coeff_four41_eq_short 39 (by norm_num),coeff_four41_eq_small 39 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient41_40 : four41ShortCoeff 40 = (1 : ℤ) := by
  rw [← coeff_four41_eq_short 40 (by norm_num),coeff_four41_eq_small 40 (by norm_num)]
  decide +kernel

/-- Every other residue has a nonzero coefficient within five progression steps. -/
theorem four41_residue_or_witness (R : ℕ) (hR : R < 41) :
    (R=21 ∨ R=25 ∨ R=26 ∨ R=30) ∨
    ∃ N : ℕ, N ≤ 5 ∧ coeff (41*N+R) (quintupleSpecialized 41 1 *
      quintupleSpecialized 41 4 * quintupleSpecialized 41 5 * quintupleSpecialized 41 9) ≠ 0 := by
  interval_cases R
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_0 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_1 (by norm_num)
  · right
    refine ⟨2, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_2 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_3 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_4 (by norm_num)
  · right
    refine ⟨4, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_5 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_6 (by norm_num)
  · right
    refine ⟨5, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_7 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_8 (by norm_num)
  · right
    refine ⟨3, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_9 (by norm_num)
  · right
    refine ⟨5, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_10 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_11 (by norm_num)
  · right
    refine ⟨2, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_12 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_13 (by norm_num)
  · right
    refine ⟨3, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_14 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_15 (by norm_num)
  · right
    refine ⟨2, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_16 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_17 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_18 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_19 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_20 (by norm_num)
  · left; norm_num
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_22 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_23 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_24 (by norm_num)
  · left; norm_num
  · left; norm_num
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_27 (by norm_num)
  · right
    refine ⟨2, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_28 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_29 (by norm_num)
  · left; norm_num
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_31 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_32 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_33 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_34 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_35 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_36 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_37 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_38 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_39 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four41_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient41_40 (by norm_num)

/-- Exact classification of persistent vanishing for the four-factor example at 41. -/
theorem four41_persistent_vanishing_iff (R : ℕ) (hR : R < 41) :
    (∀ N : ℕ, coeff (41*N+R) (quintupleSpecialized 41 1 * quintupleSpecialized 41 4 *
      quintupleSpecialized 41 5 * quintupleSpecialized 41 9) = 0) ↔
    R=21 ∨ R=25 ∨ R=26 ∨ R=30 := by
  constructor
  · intro hz
    rcases four41_residue_or_witness R hR with hr | ⟨N,_,hn⟩
    · exact hr
    · exact False.elim (hn (hz N))
  · intro hr N
    rcases hr with rfl | rfl | rfl | rfl
    · exact coeff_four_quintuple_p41_zero 0 N
    · exact coeff_four_quintuple_p41_zero 1 N
    · exact coeff_four_quintuple_p41_zero 2 N
    · exact coeff_four_quintuple_p41_zero 3 N

/-- For this product, checking the first six terms of a residue progression is exact. -/
theorem four41_finite_test_iff (R : ℕ) (hR : R < 41) :
    (∀ N : ℕ, coeff (41*N+R) (quintupleSpecialized 41 1 * quintupleSpecialized 41 4 *
      quintupleSpecialized 41 5 * quintupleSpecialized 41 9) = 0) ↔
    (∀ N : ℕ, N ≤ 5 → coeff (41*N+R) (quintupleSpecialized 41 1 * quintupleSpecialized 41 4 *
      quintupleSpecialized 41 5 * quintupleSpecialized 41 9) = 0) := by
  constructor
  · exact fun h N _ => h N
  · intro h
    apply (four41_persistent_vanishing_iff R hR).mpr
    rcases four41_residue_or_witness R hR with hr | ⟨N,hle,hn⟩
    · exact hr
    · exact False.elim (hn (h N hle))

end Ramanujan.MultiQuintuple
