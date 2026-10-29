import RamanujanTau.TateCurve.Hasse

/-! Exact Bernoulli value for the weight-28 Hasse lift. Each recursive
value is checked separately so the kernel can reuse earlier results. -/
set_option maxHeartbeats 0
namespace RamanujanTau.FiniteArithmetic.Bernoulli28

private lemma b0 : bernoulli' 0 = (1 : ℚ) / 1 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ]

private lemma b1 : bernoulli' 1 = (1 : ℚ) / 2 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0]

private lemma b2 : bernoulli' 2 = (1 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1]

private lemma b3 : bernoulli' 3 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2]

private lemma b4 : bernoulli' 4 = (-1 : ℚ) / 30 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3]

private lemma b5 : bernoulli' 5 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4]

private lemma b6 : bernoulli' 6 = (1 : ℚ) / 42 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5]

private lemma b7 : bernoulli' 7 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6]

private lemma b8 : bernoulli' 8 = (-1 : ℚ) / 30 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7]

private lemma b9 : bernoulli' 9 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8]

private lemma b10 : bernoulli' 10 = (5 : ℚ) / 66 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]

private lemma b11 : bernoulli' 11 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10]

private lemma b12 : bernoulli' 12 = (-691 : ℚ) / 2730 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]

private lemma b13 : bernoulli' 13 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]

private lemma b14 : bernoulli' 14 = (7 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13]

private lemma b15 : bernoulli' 15 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14]

private lemma b16 : bernoulli' 16 = (-3617 : ℚ) / 510 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]

private lemma b17 : bernoulli' 17 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16]

private lemma b18 : bernoulli' 18 = (43867 : ℚ) / 798 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17]

private lemma b19 : bernoulli' 19 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18]

private lemma b20 : bernoulli' 20 = (-174611 : ℚ) / 330 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19]

private lemma b21 : bernoulli' 21 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20]

private lemma b22 : bernoulli' 22 = (854513 : ℚ) / 138 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21]

private lemma b23 : bernoulli' 23 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22]

private lemma b24 : bernoulli' 24 = (-236364091 : ℚ) / 2730 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23]

private lemma b25 : bernoulli' 25 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24]

private lemma b26 : bernoulli' 26 = (8553103 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25]

private lemma b27 : bernoulli' 27 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26]

private lemma b28 : bernoulli' 28 = (-23749461029 : ℚ) / 870 := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27]

theorem value : bernoulli 28 = (-23749461029 : ℚ) / 870 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), b28]

end RamanujanTau.FiniteArithmetic.Bernoulli28
