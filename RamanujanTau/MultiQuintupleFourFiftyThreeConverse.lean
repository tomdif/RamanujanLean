import RamanujanTau.MultiQuintupleFourPlane

/-! Complete residue classification for the four-factor example at 53. -/
namespace Ramanujan.MultiQuintuple
open PowerSeries
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
-- Keep kernel coefficient checks sequential on memory-limited runners.
set_option Elab.async false

private lemma short_index53 (b : Bool) (i : ℕ) (n : ℤ)
    (hi : 1 ≤ i) (hi9 : i ≤ 9) (he : quintExp2 b 53 i n ≤ 896) :
    n.natAbs ≤ 2 := by
  have hn : -2 ≤ n ∧ n ≤ 2 := by
    interval_cases i <;> cases b <;>
      norm_num [quintExp2,quintExpA2,quintExpB2] at he <;>
      constructor <;> by_contra h <;>
      have hside : n ≤ -3 ∨ 3 ≤ n := by omega
    all_goals rcases hside with hside | hside <;>
      nlinarith [sq_nonneg (n+3),sq_nonneg (n-3)]
  omega

private lemma mem_short_box53 (K : ℕ) (hK : K ≤ 448) (x : QuadQuintBranchIndex)
    (he : quadExp2 53 5 2 7 9 x = 2*(K : ℤ)) : x ∈ quadBox 1 := by
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  simp only [quadExp2,pointTripleExp2,tripleQuintExp2,pointB1,pointB2,pointB3,
    pointN1,pointN2,pointN3,quadB4,quadN4] at he
  have h1 := quintExp2_nonneg b1 53 5 n1 (by norm_num) (by norm_num)
  have h2 := quintExp2_nonneg b2 53 2 n2 (by norm_num) (by norm_num)
  have h3 := quintExp2_nonneg b3 53 7 n3 (by norm_num) (by norm_num)
  have h4 := quintExp2_nonneg b4 53 9 n4 (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at he h1 h2 h3 h4
  have hn1 := short_index53 b1 5 n1 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn2 := short_index53 b2 2 n2 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn3 := short_index53 b3 7 n3 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn4 := short_index53 b4 9 n4 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  rw [quadBox,tripleQuintBranchBox]
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨mem_quintBranchBox_of_natAbs_le 1 b1 n1 hn1,
    mem_quintBranchBox_of_natAbs_le 1 b2 n2 hn2⟩,
    mem_quintBranchBox_of_natAbs_le 1 b3 n3 hn3⟩,
    mem_quintBranchBox_of_natAbs_le 1 b4 n4 hn4⟩

noncomputable def four53ShortCoeff (K : ℕ) : ℤ :=
  ∑ x ∈ quadBox 1, quadContribution 53 5 2 7 9 K x

lemma coeff_four53_eq_short (K : ℕ) (hK : K ≤ 448) :
    coeff K (quintupleSpecialized 53 5 * quintupleSpecialized 53 2 *
      quintupleSpecialized 53 7 * quintupleSpecialized 53 9) = four53ShortCoeff K := by
  rw [coeff_quad_eq_finiteBox 53 5 2 7 9 K
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  unfold four53ShortCoeff
  apply Finset.sum_congr_of_eq_on_inter
  · intro x hx hnx
    by_contra hn
    have he : quadExp2 53 5 2 7 9 x = 2*(K : ℤ) := by
      by_contra h; simp [quadContribution,h] at hn
    exact hnx (mem_short_box53 K hK x he)
  · intro x hx hnx
    by_contra hn
    have he : quadExp2 53 5 2 7 9 x = 2*(K : ℤ) := by
      by_contra h; simp [quadContribution,h] at hn
    exact hnx (mem_quadBox_of_exp 53 5 2 7 9 K x
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) he)

  · intro x hx hy; rfl


set_option maxHeartbeats 0 in
private theorem coefficient53_0 : four53ShortCoeff 0 = (1 : ℤ) := by
  decide +kernel

-- A smaller proved coefficient box keeps the numerical checks inexpensive.
private lemma short_index53_one (b : Bool) (i : ℕ) (n : ℤ)
    (hi : 1 ≤ i) (hi9 : i ≤ 9) (he : quintExp2 b 53 i n ≤ 438) :
    n.natAbs ≤ 1 := by
  have hn : -1 ≤ n ∧ n ≤ 1 := by
    interval_cases i <;> cases b <;>
      norm_num [quintExp2,quintExpA2,quintExpB2] at he <;>
      constructor <;> by_contra h <;>
      have hside : n ≤ -2 ∨ 2 ≤ n := by omega
    all_goals rcases hside with hside | hside <;>
      nlinarith [sq_nonneg (n+2),sq_nonneg (n-2)]
  omega

private lemma mem_short_box53_one (K : ℕ) (hK : K ≤ 219) (x : QuadQuintBranchIndex)
    (he : quadExp2 53 5 2 7 9 x = 2*(K : ℤ)) : x ∈ quadBox 0 := by
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  simp only [quadExp2,pointTripleExp2,tripleQuintExp2,pointB1,pointB2,pointB3,
    pointN1,pointN2,pointN3,quadB4,quadN4] at he
  have h1 := quintExp2_nonneg b1 53 5 n1 (by norm_num) (by norm_num)
  have h2 := quintExp2_nonneg b2 53 2 n2 (by norm_num) (by norm_num)
  have h3 := quintExp2_nonneg b3 53 7 n3 (by norm_num) (by norm_num)
  have h4 := quintExp2_nonneg b4 53 9 n4 (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at he h1 h2 h3 h4
  have hn1 := short_index53_one b1 5 n1 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn2 := short_index53_one b2 2 n2 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn3 := short_index53_one b3 7 n3 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn4 := short_index53_one b4 9 n4 (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; omega)
  rw [quadBox,tripleQuintBranchBox]
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨mem_quintBranchBox_of_natAbs_le 0 b1 n1 hn1,
    mem_quintBranchBox_of_natAbs_le 0 b2 n2 hn2⟩,
    mem_quintBranchBox_of_natAbs_le 0 b3 n3 hn3⟩,
    mem_quintBranchBox_of_natAbs_le 0 b4 n4 hn4⟩

private noncomputable def four53SmallCoeff (K : ℕ) : ℤ :=
  ∑ x ∈ quadBox 0, quadContribution 53 5 2 7 9 K x

private lemma coeff_four53_eq_small (K : ℕ) (hK : K ≤ 219) :
    coeff K (quintupleSpecialized 53 5 * quintupleSpecialized 53 2 *
      quintupleSpecialized 53 7 * quintupleSpecialized 53 9) = four53SmallCoeff K := by
  rw [coeff_quad_eq_finiteBox 53 5 2 7 9 K
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  unfold four53SmallCoeff
  apply Finset.sum_congr_of_eq_on_inter
  · intro x hx hnx
    by_contra hn
    have he : quadExp2 53 5 2 7 9 x = 2*(K : ℤ) := by
      by_contra h; simp [quadContribution,h] at hn
    exact hnx (mem_short_box53_one K hK x he)
  · intro x hx hnx
    by_contra hn
    have he : quadExp2 53 5 2 7 9 x = 2*(K : ℤ) := by
      by_contra h; simp [quadContribution,h] at hn
    exact hnx (mem_quadBox_of_exp 53 5 2 7 9 K x
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) he)

  · intro x hx hy; rfl


set_option maxHeartbeats 0 in
private theorem coefficient53_1 : four53ShortCoeff 160 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 160 (by norm_num),coeff_four53_eq_small 160 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_2 : four53ShortCoeff 2 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 2 (by norm_num),coeff_four53_eq_small 2 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_3 : four53ShortCoeff 56 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 56 (by norm_num),coeff_four53_eq_small 56 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_4 : four53ShortCoeff 110 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 110 (by norm_num),coeff_four53_eq_small 110 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_5 : four53ShortCoeff 5 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 5 (by norm_num),coeff_four53_eq_small 5 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_6 : four53ShortCoeff 112 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 112 (by norm_num),coeff_four53_eq_small 112 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_7 : four53ShortCoeff 219 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 219 (by norm_num),coeff_four53_eq_small 219 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_8 : four53ShortCoeff 114 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 114 (by norm_num),coeff_four53_eq_small 114 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_9 : four53ShortCoeff 221 = (1 : ℤ) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_10 : four53ShortCoeff 63 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 63 (by norm_num),coeff_four53_eq_small 63 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_11 : four53ShortCoeff 11 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 11 (by norm_num),coeff_four53_eq_small 11 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_12 : four53ShortCoeff 12 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 12 (by norm_num),coeff_four53_eq_small 12 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_13 : four53ShortCoeff 66 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 66 (by norm_num),coeff_four53_eq_small 66 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_14 : four53ShortCoeff 226 = (1 : ℤ) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_15 : four53ShortCoeff 121 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 121 (by norm_num),coeff_four53_eq_small 121 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_16 : four53ShortCoeff 175 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 175 (by norm_num),coeff_four53_eq_small 175 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_17 : four53ShortCoeff 123 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 123 (by norm_num),coeff_four53_eq_small 123 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_18 : four53ShortCoeff 18 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 18 (by norm_num),coeff_four53_eq_small 18 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_19 : four53ShortCoeff 125 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 125 (by norm_num),coeff_four53_eq_small 125 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_20 : four53ShortCoeff 73 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 73 (by norm_num),coeff_four53_eq_small 73 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_21 : four53ShortCoeff 21 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 21 (by norm_num),coeff_four53_eq_small 21 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_22 : four53ShortCoeff 287 = (-1 : ℤ) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_23 : four53ShortCoeff 23 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 23 (by norm_num),coeff_four53_eq_small 23 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_24 : four53ShortCoeff 448 = (1 : ℤ) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_25 : four53ShortCoeff 78 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 78 (by norm_num),coeff_four53_eq_small 78 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_26 : four53ShortCoeff 132 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 132 (by norm_num),coeff_four53_eq_small 132 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_27 : four53ShortCoeff 80 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 80 (by norm_num),coeff_four53_eq_small 80 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_28 : four53ShortCoeff 81 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 81 (by norm_num),coeff_four53_eq_small 81 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_30 : four53ShortCoeff 83 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 83 (by norm_num),coeff_four53_eq_small 83 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_32 : four53ShortCoeff 138 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 138 (by norm_num),coeff_four53_eq_small 138 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_33 : four53ShortCoeff 86 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 86 (by norm_num),coeff_four53_eq_small 86 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_34 : four53ShortCoeff 352 = (1 : ℤ) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_35 : four53ShortCoeff 35 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 35 (by norm_num),coeff_four53_eq_small 35 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_37 : four53ShortCoeff 37 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 37 (by norm_num),coeff_four53_eq_small 37 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_39 : four53ShortCoeff 39 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 39 (by norm_num),coeff_four53_eq_small 39 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_40 : four53ShortCoeff 40 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 40 (by norm_num),coeff_four53_eq_small 40 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_41 : four53ShortCoeff 41 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 41 (by norm_num),coeff_four53_eq_small 41 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_42 : four53ShortCoeff 413 = (1 : ℤ) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_43 : four53ShortCoeff 43 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 43 (by norm_num),coeff_four53_eq_small 43 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_44 : four53ShortCoeff 97 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 97 (by norm_num),coeff_four53_eq_small 97 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_45 : four53ShortCoeff 45 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 45 (by norm_num),coeff_four53_eq_small 45 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_46 : four53ShortCoeff 46 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 46 (by norm_num),coeff_four53_eq_small 46 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_47 : four53ShortCoeff 47 = (-1 : ℤ) := by
  rw [← coeff_four53_eq_short 47 (by norm_num),coeff_four53_eq_small 47 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_48 : four53ShortCoeff 48 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 48 (by norm_num),coeff_four53_eq_small 48 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_49 : four53ShortCoeff 102 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 102 (by norm_num),coeff_four53_eq_small 102 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_50 : four53ShortCoeff 262 = (-1 : ℤ) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_51 : four53ShortCoeff 157 = (1 : ℤ) := by
  rw [← coeff_four53_eq_short 157 (by norm_num),coeff_four53_eq_small 157 (by norm_num)]
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coefficient53_52 : four53ShortCoeff 317 = (1 : ℤ) := by
  decide +kernel

/-- Every other residue has a nonzero coefficient within eight progression steps. -/
theorem four53_residue_or_witness (R : ℕ) (hR : R < 53) :
    (R=29 ∨ R=31 ∨ R=36 ∨ R=38) ∨
    ∃ N : ℕ, N ≤ 8 ∧ coeff (53*N+R) (quintupleSpecialized 53 5 * quintupleSpecialized 53 2 *
      quintupleSpecialized 53 7 * quintupleSpecialized 53 9) ≠ 0 := by
  interval_cases R
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_0 (by norm_num)
  · right
    refine ⟨3, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_1 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_2 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_3 (by norm_num)
  · right
    refine ⟨2, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_4 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_5 (by norm_num)
  · right
    refine ⟨2, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_6 (by norm_num)
  · right
    refine ⟨4, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_7 (by norm_num)
  · right
    refine ⟨2, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_8 (by norm_num)
  · right
    refine ⟨4, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_9 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_10 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_11 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_12 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_13 (by norm_num)
  · right
    refine ⟨4, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_14 (by norm_num)
  · right
    refine ⟨2, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_15 (by norm_num)
  · right
    refine ⟨3, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_16 (by norm_num)
  · right
    refine ⟨2, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_17 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_18 (by norm_num)
  · right
    refine ⟨2, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_19 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_20 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_21 (by norm_num)
  · right
    refine ⟨5, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_22 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_23 (by norm_num)
  · right
    refine ⟨8, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_24 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_25 (by norm_num)
  · right
    refine ⟨2, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_26 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_27 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_28 (by norm_num)
  · left; norm_num
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_30 (by norm_num)
  · left; norm_num
  · right
    refine ⟨2, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_32 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_33 (by norm_num)
  · right
    refine ⟨6, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_34 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_35 (by norm_num)
  · left; norm_num
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_37 (by norm_num)
  · left; norm_num
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_39 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_40 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_41 (by norm_num)
  · right
    refine ⟨7, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_42 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_43 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_44 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_45 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_46 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_47 (by norm_num)
  · right
    refine ⟨0, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_48 (by norm_num)
  · right
    refine ⟨1, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_49 (by norm_num)
  · right
    refine ⟨4, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_50 (by norm_num)
  · right
    refine ⟨2, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_51 (by norm_num)
  · right
    refine ⟨5, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_52 (by norm_num)

/-- Full persistent-vanishing classification for this fixed product at 53. -/
theorem four53_persistent_vanishing_iff (R : ℕ) (hR : R < 53) :
    (∀ N : ℕ, coeff (53*N+R) (quintupleSpecialized 53 5 * quintupleSpecialized 53 2 *
      quintupleSpecialized 53 7 * quintupleSpecialized 53 9) = 0) ↔
    R=29 ∨ R=31 ∨ R=36 ∨ R=38 := by
  constructor
  · intro hz
    rcases four53_residue_or_witness R hR with hr | ⟨N,_,hn⟩
    · exact hr
    · exact False.elim (hn (hz N))
  · intro hr N
    exact coeff_fourPlane_53 R N hr

/-- Checking the first nine terms is an exact test for this fixed product. -/
theorem four53_finite_test_iff (R : ℕ) (hR : R < 53) :
    (∀ N : ℕ, coeff (53*N+R) (quintupleSpecialized 53 5 * quintupleSpecialized 53 2 *
      quintupleSpecialized 53 7 * quintupleSpecialized 53 9) = 0) ↔
    (∀ N : ℕ, N ≤ 8 → coeff (53*N+R) (quintupleSpecialized 53 5 * quintupleSpecialized 53 2 *
      quintupleSpecialized 53 7 * quintupleSpecialized 53 9) = 0) := by
  constructor
  · exact fun h N _ => h N
  · intro h
    apply (four53_persistent_vanishing_iff R hR).mpr
    rcases four53_residue_or_witness R hR with hr | ⟨N,hle,hn⟩
    · exact hr
    · exact False.elim (hn (h N hle))

end Ramanujan.MultiQuintuple
