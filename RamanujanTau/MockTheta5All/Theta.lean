/-
# The seven theta-function identities behind the remaining fifth-order mock theta identities

Each identity is certified by a few instances of HM (1.4b) `θ_mul`, after writing every theta function and
every product `(q^r;q^M)_∞` as atoms `(q^r;q^{80})_∞`. Certificates were found numerically
(`scripts/mock_theta5_all/gen_theta.py`) and are checked here by `field_simp; ring`.

Notation: `P r M = ιN h1 (Pinf r M) = (q^r;q^M)_∞` in `ℂ((q))`, `q = mono 1 1`.
-/
import RamanujanTau.MTC.ProdId
import RamanujanTau.MTC.Final0

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace MockTheta5All.Theta
open ALz HahnSeries Finset RankProof MTC

lemma h1 : 1 ≤ 1 := le_rfl
lemma h5 : 1 ≤ 5 := by norm_num
lemma h10 : 1 ≤ 10 := by norm_num
lemma h20 : 1 ≤ 20 := by norm_num

/-- the atom `(q^r; q^{80})_∞` in `ℂ((q))`. -/
noncomputable def Aw (r : ℕ) : L := PA h1 r 80

lemma Aw_ne (r : ℕ) (hr : 1 ≤ r) : Aw r ≠ 0 := PA_ne h1 r 80 hr (by norm_num)

lemma monoPow (k : ℕ) : (mono 1 1 : L) ^ k = mono k 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, ih, mono_mul]; push_cast; ring_nf

lemma cv_5_1_m : θ h5 1 (-1) = (Aw 2 * Aw 5 ^ 2 * Aw 8 * Aw 10 ^ 2 * Aw 12 * Aw 15 ^ 2 * Aw 18 * Aw 20 ^ 2 * Aw 22 * Aw 25 ^ 2 * Aw 28 * Aw 30 ^ 2 * Aw 32 * Aw 35 ^ 2 * Aw 38 * Aw 40 ^ 2 * Aw 42 * Aw 45 ^ 2 * Aw 48 * Aw 50 ^ 2 * Aw 52 * Aw 55 ^ 2 * Aw 58 * Aw 60 ^ 2 * Aw 62 * Aw 65 ^ 2 * Aw 68 * Aw 70 ^ 2 * Aw 72 * Aw 75 ^ 2 * Aw 78 * Aw 80 ^ 2) / (Aw 1 * Aw 4 * Aw 5 * Aw 6 * Aw 9 * Aw 10 * Aw 11 * Aw 14 * Aw 15 * Aw 16 * Aw 19 * Aw 20 * Aw 21 * Aw 24 * Aw 25 * Aw 26 * Aw 29 * Aw 30 * Aw 31 * Aw 34 * Aw 35 * Aw 36 * Aw 39 * Aw 40 * Aw 41 * Aw 44 * Aw 45 * Aw 46 * Aw 49 * Aw 50 * Aw 51 * Aw 54 * Aw 55 * Aw 56 * Aw 59 * Aw 60 * Aw 61 * Aw 64 * Aw 65 * Aw 66 * Aw 69 * Aw 70 * Aw 71 * Aw 74 * Aw 75 * Aw 76 * Aw 79 * Aw 80) := by
  rw [θb h1 h5 5 1 8 (by norm_num) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_5_2_m : θ h5 2 (-1) = (Aw 4 * Aw 5 ^ 2 * Aw 6 * Aw 10 ^ 2 * Aw 14 * Aw 15 ^ 2 * Aw 16 * Aw 20 ^ 2 * Aw 24 * Aw 25 ^ 2 * Aw 26 * Aw 30 ^ 2 * Aw 34 * Aw 35 ^ 2 * Aw 36 * Aw 40 ^ 2 * Aw 44 * Aw 45 ^ 2 * Aw 46 * Aw 50 ^ 2 * Aw 54 * Aw 55 ^ 2 * Aw 56 * Aw 60 ^ 2 * Aw 64 * Aw 65 ^ 2 * Aw 66 * Aw 70 ^ 2 * Aw 74 * Aw 75 ^ 2 * Aw 76 * Aw 80 ^ 2) / (Aw 2 * Aw 3 * Aw 5 * Aw 7 * Aw 8 * Aw 10 * Aw 12 * Aw 13 * Aw 15 * Aw 17 * Aw 18 * Aw 20 * Aw 22 * Aw 23 * Aw 25 * Aw 27 * Aw 28 * Aw 30 * Aw 32 * Aw 33 * Aw 35 * Aw 37 * Aw 38 * Aw 40 * Aw 42 * Aw 43 * Aw 45 * Aw 47 * Aw 48 * Aw 50 * Aw 52 * Aw 53 * Aw 55 * Aw 57 * Aw 58 * Aw 60 * Aw 62 * Aw 63 * Aw 65 * Aw 67 * Aw 68 * Aw 70 * Aw 72 * Aw 73 * Aw 75 * Aw 77 * Aw 78 * Aw 80) := by
  rw [θb h1 h5 5 2 8 (by norm_num) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_10_3_m : θ h10 3 (-1) = (Aw 6 * Aw 10 ^ 2 * Aw 14 * Aw 20 ^ 2 * Aw 26 * Aw 30 ^ 2 * Aw 34 * Aw 40 ^ 2 * Aw 46 * Aw 50 ^ 2 * Aw 54 * Aw 60 ^ 2 * Aw 66 * Aw 70 ^ 2 * Aw 74 * Aw 80 ^ 2) / (Aw 3 * Aw 7 * Aw 10 * Aw 13 * Aw 17 * Aw 20 * Aw 23 * Aw 27 * Aw 30 * Aw 33 * Aw 37 * Aw 40 * Aw 43 * Aw 47 * Aw 50 * Aw 53 * Aw 57 * Aw 60 * Aw 63 * Aw 67 * Aw 70 * Aw 73 * Aw 77 * Aw 80) := by
  rw [θb h1 h10 10 3 4 (by norm_num) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_10_4_m : θ h10 4 (-1) = (Aw 8 * Aw 10 ^ 2 * Aw 12 * Aw 20 ^ 2 * Aw 28 * Aw 30 ^ 2 * Aw 32 * Aw 40 ^ 2 * Aw 48 * Aw 50 ^ 2 * Aw 52 * Aw 60 ^ 2 * Aw 68 * Aw 70 ^ 2 * Aw 72 * Aw 80 ^ 2) / (Aw 4 * Aw 6 * Aw 10 * Aw 14 * Aw 16 * Aw 20 * Aw 24 * Aw 26 * Aw 30 * Aw 34 * Aw 36 * Aw 40 * Aw 44 * Aw 46 * Aw 50 * Aw 54 * Aw 56 * Aw 60 * Aw 64 * Aw 66 * Aw 70 * Aw 74 * Aw 76 * Aw 80) := by
  rw [θb h1 h10 10 4 4 (by norm_num) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_10_8_m : θ h10 8 (-1) = (Aw 4 * Aw 10 ^ 2 * Aw 16 * Aw 20 ^ 2 * Aw 24 * Aw 30 ^ 2 * Aw 36 * Aw 40 ^ 2 * Aw 44 * Aw 50 ^ 2 * Aw 56 * Aw 60 ^ 2 * Aw 64 * Aw 70 ^ 2 * Aw 76 * Aw 80 ^ 2) / (Aw 2 * Aw 8 * Aw 10 * Aw 12 * Aw 18 * Aw 20 * Aw 22 * Aw 28 * Aw 30 * Aw 32 * Aw 38 * Aw 40 * Aw 42 * Aw 48 * Aw 50 * Aw 52 * Aw 58 * Aw 60 * Aw 62 * Aw 68 * Aw 70 * Aw 72 * Aw 78 * Aw 80) := by
  rw [θb h1 h10 10 8 4 (by norm_num) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_10_9_m : θ h10 9 (-1) = (Aw 2 * Aw 10 ^ 2 * Aw 18 * Aw 20 ^ 2 * Aw 22 * Aw 30 ^ 2 * Aw 38 * Aw 40 ^ 2 * Aw 42 * Aw 50 ^ 2 * Aw 58 * Aw 60 ^ 2 * Aw 62 * Aw 70 ^ 2 * Aw 78 * Aw 80 ^ 2) / (Aw 1 * Aw 9 * Aw 10 * Aw 11 * Aw 19 * Aw 20 * Aw 21 * Aw 29 * Aw 30 * Aw 31 * Aw 39 * Aw 40 * Aw 41 * Aw 49 * Aw 50 * Aw 51 * Aw 59 * Aw 60 * Aw 61 * Aw 69 * Aw 70 * Aw 71 * Aw 79 * Aw 80) := by
  rw [θb h1 h10 10 9 4 (by norm_num) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_5_1_p : θ h5 1 1 = Aw 1 * Aw 4 * Aw 5 * Aw 6 * Aw 9 * Aw 10 * Aw 11 * Aw 14 * Aw 15 * Aw 16 * Aw 19 * Aw 20 * Aw 21 * Aw 24 * Aw 25 * Aw 26 * Aw 29 * Aw 30 * Aw 31 * Aw 34 * Aw 35 * Aw 36 * Aw 39 * Aw 40 * Aw 41 * Aw 44 * Aw 45 * Aw 46 * Aw 49 * Aw 50 * Aw 51 * Aw 54 * Aw 55 * Aw 56 * Aw 59 * Aw 60 * Aw 61 * Aw 64 * Aw 65 * Aw 66 * Aw 69 * Aw 70 * Aw 71 * Aw 74 * Aw 75 * Aw 76 * Aw 79 * Aw 80 := by
  rw [θu h1 h5 5 1 16 (by norm_num) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_5_2_p : θ h5 2 1 = Aw 2 * Aw 3 * Aw 5 * Aw 7 * Aw 8 * Aw 10 * Aw 12 * Aw 13 * Aw 15 * Aw 17 * Aw 18 * Aw 20 * Aw 22 * Aw 23 * Aw 25 * Aw 27 * Aw 28 * Aw 30 * Aw 32 * Aw 33 * Aw 35 * Aw 37 * Aw 38 * Aw 40 * Aw 42 * Aw 43 * Aw 45 * Aw 47 * Aw 48 * Aw 50 * Aw 52 * Aw 53 * Aw 55 * Aw 57 * Aw 58 * Aw 60 * Aw 62 * Aw 63 * Aw 65 * Aw 67 * Aw 68 * Aw 70 * Aw 72 * Aw 73 * Aw 75 * Aw 77 * Aw 78 * Aw 80 := by
  rw [θu h1 h5 5 2 16 (by norm_num) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_10_1_m : θ h10 1 (-1) = (Aw 2 * Aw 10 ^ 2 * Aw 18 * Aw 20 ^ 2 * Aw 22 * Aw 30 ^ 2 * Aw 38 * Aw 40 ^ 2 * Aw 42 * Aw 50 ^ 2 * Aw 58 * Aw 60 ^ 2 * Aw 62 * Aw 70 ^ 2 * Aw 78 * Aw 80 ^ 2) / (Aw 1 * Aw 9 * Aw 10 * Aw 11 * Aw 19 * Aw 20 * Aw 21 * Aw 29 * Aw 30 * Aw 31 * Aw 39 * Aw 40 * Aw 41 * Aw 49 * Aw 50 * Aw 51 * Aw 59 * Aw 60 * Aw 61 * Aw 69 * Aw 70 * Aw 71 * Aw 79 * Aw 80) := by
  rw [θb h1 h10 10 1 4 (by norm_num) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_10_3_p : θ h10 3 1 = Aw 3 * Aw 7 * Aw 10 * Aw 13 * Aw 17 * Aw 20 * Aw 23 * Aw 27 * Aw 30 * Aw 33 * Aw 37 * Aw 40 * Aw 43 * Aw 47 * Aw 50 * Aw 53 * Aw 57 * Aw 60 * Aw 63 * Aw 67 * Aw 70 * Aw 73 * Aw 77 * Aw 80 := by
  rw [θu h1 h10 10 3 8 (by norm_num) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_20_4_p : θ h20 4 1 = Aw 4 * Aw 16 * Aw 20 * Aw 24 * Aw 36 * Aw 40 * Aw 44 * Aw 56 * Aw 60 * Aw 64 * Aw 76 * Aw 80 := by
  rw [θu h1 h20 20 4 4 (by norm_num) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_20_8_p : θ h20 8 1 = Aw 8 * Aw 12 * Aw 20 * Aw 28 * Aw 32 * Aw 40 * Aw 48 * Aw 52 * Aw 60 * Aw 68 * Aw 72 * Aw 80 := by
  rw [θu h1 h20 20 8 4 (by norm_num) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_20_14_p : θ h20 14 1 = Aw 6 * Aw 14 * Aw 20 * Aw 26 * Aw 34 * Aw 40 * Aw 46 * Aw 54 * Aw 60 * Aw 66 * Aw 74 * Aw 80 := by
  rw [θu h1 h20 20 14 4 (by norm_num) 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_20_18_p : θ h20 18 1 = Aw 2 * Aw 18 * Aw 20 * Aw 22 * Aw 38 * Aw 40 * Aw 42 * Aw 58 * Aw 60 * Aw 62 * Aw 78 * Aw 80 := by
  rw [θu h1 h20 20 18 4 (by norm_num) 18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_10_1_p : θ h10 1 1 = Aw 1 * Aw 9 * Aw 10 * Aw 11 * Aw 19 * Aw 20 * Aw 21 * Aw 29 * Aw 30 * Aw 31 * Aw 39 * Aw 40 * Aw 41 * Aw 49 * Aw 50 * Aw 51 * Aw 59 * Aw 60 * Aw 61 * Aw 69 * Aw 70 * Aw 71 * Aw 79 * Aw 80 := by
  rw [θu h1 h10 10 1 8 (by norm_num) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_10_5_m : θ h10 5 (-1) = (Aw 10 ^ 4 * Aw 20 ^ 2 * Aw 30 ^ 4 * Aw 40 ^ 2 * Aw 50 ^ 4 * Aw 60 ^ 2 * Aw 70 ^ 4 * Aw 80 ^ 2) / (Aw 5 ^ 2 * Aw 10 * Aw 15 ^ 2 * Aw 20 * Aw 25 ^ 2 * Aw 30 * Aw 35 ^ 2 * Aw 40 * Aw 45 ^ 2 * Aw 50 * Aw 55 ^ 2 * Aw 60 * Aw 65 ^ 2 * Aw 70 * Aw 75 ^ 2 * Aw 80) := by
  rw [θb h1 h10 10 5 4 (by norm_num) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_10_5_p : θ h10 5 1 = Aw 5 ^ 2 * Aw 10 * Aw 15 ^ 2 * Aw 20 * Aw 25 ^ 2 * Aw 30 * Aw 35 ^ 2 * Aw 40 * Aw 45 ^ 2 * Aw 50 * Aw 55 ^ 2 * Aw 60 * Aw 65 ^ 2 * Aw 70 * Aw 75 ^ 2 * Aw 80 := by
  rw [θu h1 h10 10 5 8 (by norm_num) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_10_2_m : θ h10 2 (-1) = (Aw 4 * Aw 10 ^ 2 * Aw 16 * Aw 20 ^ 2 * Aw 24 * Aw 30 ^ 2 * Aw 36 * Aw 40 ^ 2 * Aw 44 * Aw 50 ^ 2 * Aw 56 * Aw 60 ^ 2 * Aw 64 * Aw 70 ^ 2 * Aw 76 * Aw 80 ^ 2) / (Aw 2 * Aw 8 * Aw 10 * Aw 12 * Aw 18 * Aw 20 * Aw 22 * Aw 28 * Aw 30 * Aw 32 * Aw 38 * Aw 40 * Aw 42 * Aw 48 * Aw 50 * Aw 52 * Aw 58 * Aw 60 * Aw 62 * Aw 68 * Aw 70 * Aw 72 * Aw 78 * Aw 80) := by
  rw [θb h1 h10 10 2 4 (by norm_num) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_10_7_m : θ h10 7 (-1) = (Aw 6 * Aw 10 ^ 2 * Aw 14 * Aw 20 ^ 2 * Aw 26 * Aw 30 ^ 2 * Aw 34 * Aw 40 ^ 2 * Aw 46 * Aw 50 ^ 2 * Aw 54 * Aw 60 ^ 2 * Aw 66 * Aw 70 ^ 2 * Aw 74 * Aw 80 ^ 2) / (Aw 3 * Aw 7 * Aw 10 * Aw 13 * Aw 17 * Aw 20 * Aw 23 * Aw 27 * Aw 30 * Aw 33 * Aw 37 * Aw 40 * Aw 43 * Aw 47 * Aw 50 * Aw 53 * Aw 57 * Aw 60 * Aw 63 * Aw 67 * Aw 70 * Aw 73 * Aw 77 * Aw 80) := by
  rw [θb h1 h10 10 7 4 (by norm_num) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_10_10_m : θ h10 10 (-1) = 2 * (Aw 20 * Aw 40 ^ 2 * Aw 60 * Aw 80 ^ 2) / (Aw 10 * Aw 30 * Aw 40 * Aw 50 * Aw 70 * Aw 80) := by
  have hr := θ_reflect h10 0 (c := -1) (by norm_num)
  norm_num at hr
  rw [hr, θb0 h1 h10 10 1 (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_10_4_p : θ h10 4 1 = Aw 4 * Aw 6 * Aw 10 * Aw 14 * Aw 16 * Aw 20 * Aw 24 * Aw 26 * Aw 30 * Aw 34 * Aw 36 * Aw 40 * Aw 44 * Aw 46 * Aw 50 * Aw 54 * Aw 56 * Aw 60 * Aw 64 * Aw 66 * Aw 70 * Aw 74 * Aw 76 * Aw 80 := by
  rw [θu h1 h10 10 4 8 (by norm_num) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_10_8_p : θ h10 8 1 = Aw 2 * Aw 8 * Aw 10 * Aw 12 * Aw 18 * Aw 20 * Aw 22 * Aw 28 * Aw 30 * Aw 32 * Aw 38 * Aw 40 * Aw 42 * Aw 48 * Aw 50 * Aw 52 * Aw 58 * Aw 60 * Aw 62 * Aw 68 * Aw 70 * Aw 72 * Aw 78 * Aw 80 := by
  rw [θu h1 h10 10 8 8 (by norm_num) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma cv_10_9_p : θ h10 9 1 = Aw 1 * Aw 9 * Aw 10 * Aw 11 * Aw 19 * Aw 20 * Aw 21 * Aw 29 * Aw 30 * Aw 31 * Aw 39 * Aw 40 * Aw 41 * Aw 49 * Aw 50 * Aw 51 * Aw 59 * Aw 60 * Aw 61 * Aw 69 * Aw 70 * Aw 71 * Aw 79 * Aw 80 := by
  rw [θu h1 h10 10 9 8 (by norm_num) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma M_5_1m_2m : θ h5 1 (-1) * θ h5 2 (-1) = θ h10 3 (-1) * θ h10 4 (-1) - -(mono 1 1 ^ 1) * (θ h10 8 (-1) * θ h10 9 (-1)) := by
  have h := θ_mul h5 1 2 (c1 := (-1)) (c2 := (-1)) (by norm_num) (by norm_num)
  have hm : (mono 1 (-1) : L) = -(mono 1 1 ^ 1) := by rw [monoPow]; simp [mono]
  rw [hm] at h
  generalize (mono 1 1 : L) = m at h ⊢
  norm_num at h
  linear_combination h

lemma M_5_1p_2p : θ h5 1 1 * θ h5 2 1 = θ h10 3 (-1) * θ h10 4 (-1) - (mono 1 1 ^ 1) * (θ h10 8 (-1) * θ h10 9 (-1)) := by
  have h := θ_mul h5 1 2 (c1 := 1) (c2 := 1) one_ne_zero one_ne_zero
  have hm : (mono 1 1 : L) = (mono 1 1 ^ 1) := by rw [monoPow]; simp [mono]
  rw [hm] at h
  generalize (mono 1 1 : L) = m at h ⊢
  norm_num at h
  linear_combination h

lemma M_10_1m_3p : θ h10 1 (-1) * θ h10 3 1 = θ h20 4 1 * θ h20 8 1 - -(mono 1 1 ^ 1) * (θ h20 14 1 * θ h20 18 1) := by
  have h := θ_mul h10 1 3 (c1 := (-1)) (c2 := 1) (by norm_num) one_ne_zero
  have hm : (mono 1 (-1) : L) = -(mono 1 1 ^ 1) := by rw [monoPow]; simp [mono]
  rw [hm] at h
  generalize (mono 1 1 : L) = m at h ⊢
  norm_num at h
  linear_combination h

lemma M_10_1p_3m : θ h10 1 1 * θ h10 3 (-1) = θ h20 4 1 * θ h20 8 1 - (mono 1 1 ^ 1) * (θ h20 14 1 * θ h20 18 1) := by
  have h := θ_mul h10 1 3 (c1 := 1) (c2 := (-1)) one_ne_zero (by norm_num)
  have hm : (mono 1 1 : L) = (mono 1 1 ^ 1) := by rw [monoPow]; simp [mono]
  rw [hm] at h
  generalize (mono 1 1 : L) = m at h ⊢
  norm_num at h
  linear_combination h

lemma M_10_3p_5m : θ h10 3 1 * θ h10 5 (-1) = θ h20 8 1 * θ h20 8 1 - (mono 1 1 ^ 3) * (θ h20 18 1 * θ h20 18 1) := by
  have h := θ_mul h10 3 5 (c1 := 1) (c2 := (-1)) one_ne_zero (by norm_num)
  have hm : (mono 3 1 : L) = (mono 1 1 ^ 3) := by rw [monoPow]; simp [mono]
  rw [hm] at h
  generalize (mono 1 1 : L) = m at h ⊢
  norm_num at h
  linear_combination h

lemma M_10_3m_5p : θ h10 3 (-1) * θ h10 5 1 = θ h20 8 1 * θ h20 8 1 - -(mono 1 1 ^ 3) * (θ h20 18 1 * θ h20 18 1) := by
  have h := θ_mul h10 3 5 (c1 := (-1)) (c2 := 1) (by norm_num) one_ne_zero
  have hm : (mono 3 (-1) : L) = -(mono 1 1 ^ 3) := by rw [monoPow]; simp [mono]
  rw [hm] at h
  generalize (mono 1 1 : L) = m at h ⊢
  norm_num at h
  linear_combination h

lemma M_5_1p_1p : θ h5 1 1 * θ h5 1 1 = θ h10 2 (-1) * θ h10 5 (-1) - (mono 1 1 ^ 1) * (θ h10 7 (-1) * θ h10 10 (-1)) := by
  have h := θ_mul h5 1 1 (c1 := 1) (c2 := 1) one_ne_zero one_ne_zero
  have hm : (mono 1 1 : L) = (mono 1 1 ^ 1) := by rw [monoPow]; simp [mono]
  rw [hm] at h
  generalize (mono 1 1 : L) = m at h ⊢
  norm_num at h
  linear_combination h

lemma M_5_1p_2m : θ h5 1 1 * θ h5 2 (-1) = θ h10 3 1 * θ h10 4 1 - (mono 1 1 ^ 1) * (θ h10 8 1 * θ h10 9 1) := by
  have h := θ_mul h5 1 2 (c1 := 1) (c2 := (-1)) one_ne_zero (by norm_num)
  have hm : (mono 1 1 : L) = (mono 1 1 ^ 1) := by rw [monoPow]; simp [mono]
  rw [hm] at h
  generalize (mono 1 1 : L) = m at h ⊢
  norm_num at h
  linear_combination h

lemma M_5_1m_2p : θ h5 1 (-1) * θ h5 2 1 = θ h10 3 1 * θ h10 4 1 - -(mono 1 1 ^ 1) * (θ h10 8 1 * θ h10 9 1) := by
  have h := θ_mul h5 1 2 (c1 := (-1)) (c2 := 1) (by norm_num) one_ne_zero
  have hm : (mono 1 (-1) : L) = -(mono 1 1 ^ 1) := by rw [monoPow]; simp [mono]
  rw [hm] at h
  generalize (mono 1 1 : L) = m at h ⊢
  norm_num at h
  linear_combination h

lemma ip_5_10 : ιN h1 (Pinf 5 10) = Aw 5 * Aw 15 * Aw 25 * Aw 35 * Aw 45 * Aw 55 * Aw 65 * Aw 75 := by
  rw [ιN_Pinf_split h1 5 10 8 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_10_10 : ιN h1 (Pinf 10 10) = Aw 10 * Aw 20 * Aw 30 * Aw 40 * Aw 50 * Aw 60 * Aw 70 * Aw 80 := by
  rw [ιN_Pinf_split h1 10 10 8 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_1_5 : ιN h1 (Pinf 1 5) = Aw 1 * Aw 6 * Aw 11 * Aw 16 * Aw 21 * Aw 26 * Aw 31 * Aw 36 * Aw 41 * Aw 46 * Aw 51 * Aw 56 * Aw 61 * Aw 66 * Aw 71 * Aw 76 := by
  rw [ιN_Pinf_split h1 1 5 16 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_4_5 : ιN h1 (Pinf 4 5) = Aw 4 * Aw 9 * Aw 14 * Aw 19 * Aw 24 * Aw 29 * Aw 34 * Aw 39 * Aw 44 * Aw 49 * Aw 54 * Aw 59 * Aw 64 * Aw 69 * Aw 74 * Aw 79 := by
  rw [ιN_Pinf_split h1 4 5 16 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_1_1 : ιN h1 (Pinf 1 1) = Aw 1 * Aw 2 * Aw 3 * Aw 4 * Aw 5 * Aw 6 * Aw 7 * Aw 8 * Aw 9 * Aw 10 * Aw 11 * Aw 12 * Aw 13 * Aw 14 * Aw 15 * Aw 16 * Aw 17 * Aw 18 * Aw 19 * Aw 20 * Aw 21 * Aw 22 * Aw 23 * Aw 24 * Aw 25 * Aw 26 * Aw 27 * Aw 28 * Aw 29 * Aw 30 * Aw 31 * Aw 32 * Aw 33 * Aw 34 * Aw 35 * Aw 36 * Aw 37 * Aw 38 * Aw 39 * Aw 40 * Aw 41 * Aw 42 * Aw 43 * Aw 44 * Aw 45 * Aw 46 * Aw 47 * Aw 48 * Aw 49 * Aw 50 * Aw 51 * Aw 52 * Aw 53 * Aw 54 * Aw 55 * Aw 56 * Aw 57 * Aw 58 * Aw 59 * Aw 60 * Aw 61 * Aw 62 * Aw 63 * Aw 64 * Aw 65 * Aw 66 * Aw 67 * Aw 68 * Aw 69 * Aw 70 * Aw 71 * Aw 72 * Aw 73 * Aw 74 * Aw 75 * Aw 76 * Aw 77 * Aw 78 * Aw 79 * Aw 80 := by
  rw [ιN_Pinf_split h1 1 1 80 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_2_2 : ιN h1 (Pinf 2 2) = Aw 2 * Aw 4 * Aw 6 * Aw 8 * Aw 10 * Aw 12 * Aw 14 * Aw 16 * Aw 18 * Aw 20 * Aw 22 * Aw 24 * Aw 26 * Aw 28 * Aw 30 * Aw 32 * Aw 34 * Aw 36 * Aw 38 * Aw 40 * Aw 42 * Aw 44 * Aw 46 * Aw 48 * Aw 50 * Aw 52 * Aw 54 * Aw 56 * Aw 58 * Aw 60 * Aw 62 * Aw 64 * Aw 66 * Aw 68 * Aw 70 * Aw 72 * Aw 74 * Aw 76 * Aw 78 * Aw 80 := by
  rw [ιN_Pinf_split h1 2 2 40 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_8_20 : ιN h1 (Pinf 8 20) = Aw 8 * Aw 28 * Aw 48 * Aw 68 := by
  rw [ιN_Pinf_split h1 8 20 4 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_10_20 : ιN h1 (Pinf 10 20) = Aw 10 * Aw 30 * Aw 50 * Aw 70 := by
  rw [ιN_Pinf_split h1 10 20 4 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_12_20 : ιN h1 (Pinf 12 20) = Aw 12 * Aw 32 * Aw 52 * Aw 72 := by
  rw [ιN_Pinf_split h1 12 20 4 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_20_20 : ιN h1 (Pinf 20 20) = Aw 20 * Aw 40 * Aw 60 * Aw 80 := by
  rw [ιN_Pinf_split h1 20 20 4 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_4_20 : ιN h1 (Pinf 4 20) = Aw 4 * Aw 24 * Aw 44 * Aw 64 := by
  rw [ιN_Pinf_split h1 4 20 4 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_6_20 : ιN h1 (Pinf 6 20) = Aw 6 * Aw 26 * Aw 46 * Aw 66 := by
  rw [ιN_Pinf_split h1 6 20 4 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_14_20 : ιN h1 (Pinf 14 20) = Aw 14 * Aw 34 * Aw 54 * Aw 74 := by
  rw [ιN_Pinf_split h1 14 20 4 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_16_20 : ιN h1 (Pinf 16 20) = Aw 16 * Aw 36 * Aw 56 * Aw 76 := by
  rw [ιN_Pinf_split h1 16 20 4 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_4_4 : ιN h1 (Pinf 4 4) = Aw 4 * Aw 8 * Aw 12 * Aw 16 * Aw 20 * Aw 24 * Aw 28 * Aw 32 * Aw 36 * Aw 40 * Aw 44 * Aw 48 * Aw 52 * Aw 56 * Aw 60 * Aw 64 * Aw 68 * Aw 72 * Aw 76 * Aw 80 := by
  rw [ιN_Pinf_split h1 4 4 20 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_2_4 : ιN h1 (Pinf 2 4) = Aw 2 * Aw 6 * Aw 10 * Aw 14 * Aw 18 * Aw 22 * Aw 26 * Aw 30 * Aw 34 * Aw 38 * Aw 42 * Aw 46 * Aw 50 * Aw 54 * Aw 58 * Aw 62 * Aw 66 * Aw 70 * Aw 74 * Aw 78 := by
  rw [ιN_Pinf_split h1 2 4 20 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_1_10 : ιN h1 (Pinf 1 10) = Aw 1 * Aw 11 * Aw 21 * Aw 31 * Aw 41 * Aw 51 * Aw 61 * Aw 71 := by
  rw [ιN_Pinf_split h1 1 10 8 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_9_10 : ιN h1 (Pinf 9 10) = Aw 9 * Aw 19 * Aw 29 * Aw 39 * Aw 49 * Aw 59 * Aw 69 * Aw 79 := by
  rw [ιN_Pinf_split h1 9 10 8 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_2_10 : ιN h1 (Pinf 2 10) = Aw 2 * Aw 12 * Aw 22 * Aw 32 * Aw 42 * Aw 52 * Aw 62 * Aw 72 := by
  rw [ιN_Pinf_split h1 2 10 8 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_3_10 : ιN h1 (Pinf 3 10) = Aw 3 * Aw 13 * Aw 23 * Aw 33 * Aw 43 * Aw 53 * Aw 63 * Aw 73 := by
  rw [ιN_Pinf_split h1 3 10 8 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_7_10 : ιN h1 (Pinf 7 10) = Aw 7 * Aw 17 * Aw 27 * Aw 37 * Aw 47 * Aw 57 * Aw 67 * Aw 77 := by
  rw [ιN_Pinf_split h1 7 10 8 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_8_10 : ιN h1 (Pinf 8 10) = Aw 8 * Aw 18 * Aw 28 * Aw 38 * Aw 48 * Aw 58 * Aw 68 * Aw 78 := by
  rw [ιN_Pinf_split h1 8 10 8 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_2_5 : ιN h1 (Pinf 2 5) = Aw 2 * Aw 7 * Aw 12 * Aw 17 * Aw 22 * Aw 27 * Aw 32 * Aw 37 * Aw 42 * Aw 47 * Aw 52 * Aw 57 * Aw 62 * Aw 67 * Aw 72 * Aw 77 := by
  rw [ιN_Pinf_split h1 2 5 16 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_3_5 : ιN h1 (Pinf 3 5) = Aw 3 * Aw 8 * Aw 13 * Aw 18 * Aw 23 * Aw 28 * Aw 33 * Aw 38 * Aw 43 * Aw 48 * Aw 53 * Aw 58 * Aw 63 * Aw 68 * Aw 73 * Aw 78 := by
  rw [ιN_Pinf_split h1 3 5 16 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_2_20 : ιN h1 (Pinf 2 20) = Aw 2 * Aw 22 * Aw 42 * Aw 62 := by
  rw [ιN_Pinf_split h1 2 20 4 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_18_20 : ιN h1 (Pinf 18 20) = Aw 18 * Aw 38 * Aw 58 * Aw 78 := by
  rw [ιN_Pinf_split h1 18 20 4 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_4_10 : ιN h1 (Pinf 4 10) = Aw 4 * Aw 14 * Aw 24 * Aw 34 * Aw 44 * Aw 54 * Aw 64 * Aw 74 := by
  rw [ιN_Pinf_split h1 4 10 8 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_6_10 : ιN h1 (Pinf 6 10) = Aw 6 * Aw 16 * Aw 26 * Aw 36 * Aw 46 * Aw 56 * Aw 66 * Aw 76 := by
  rw [ιN_Pinf_split h1 6 10 8 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

lemma ip_5_5 : ιN h1 (Pinf 5 5) = Aw 5 * Aw 10 * Aw 15 * Aw 20 * Aw 25 * Aw 30 * Aw 35 * Aw 40 * Aw 45 * Aw 50 * Aw 55 * Aw 60 * Aw 65 * Aw 70 * Aw 75 * Aw 80 := by
  rw [ιN_Pinf_split h1 5 5 16 (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]

/-- theta identity `phi0`. -/
theorem theta_phi0 : (1 : L) * ((ιN h1 (Pinf 5 10) ^ 2 * ιN h1 (Pinf 10 10)) * (ιN h1 (Pinf 1 5) * ιN h1 (Pinf 4 5))⁻¹) + (1 : L) * ((ιN h1 (Pinf 1 1) ^ 2) * (ιN h1 (Pinf 2 2) * ιN h1 (Pinf 1 5) * ιN h1 (Pinf 4 5))⁻¹) + (-2 : L) * ((ιN h1 (Pinf 8 20) * ιN h1 (Pinf 10 20) * ιN h1 (Pinf 12 20) * ιN h1 (Pinf 20 20)) * (ιN h1 (Pinf 4 20) ^ 2 * ιN h1 (Pinf 6 20) * ιN h1 (Pinf 14 20) * ιN h1 (Pinf 16 20) ^ 2)⁻¹) = 0 := by
  have M_5_1m_2m := M_5_1m_2m; have M_5_1p_2p := M_5_1p_2p
  simp only [cv_5_1_m, cv_5_2_m, cv_10_3_m, cv_10_4_m, cv_10_8_m, cv_10_9_m, cv_5_1_p, cv_5_2_p, cv_10_1_m, cv_10_3_p, cv_20_4_p, cv_20_8_p, cv_20_14_p, cv_20_18_p, cv_10_1_p, cv_10_5_m, cv_10_5_p, cv_10_2_m, cv_10_7_m, cv_10_10_m, cv_10_4_p, cv_10_8_p, cv_10_9_p] at M_5_1m_2m M_5_1p_2p
  rw [ip_5_10, ip_10_10, ip_1_5, ip_4_5, ip_1_1, ip_2_2, ip_8_20, ip_10_20, ip_12_20, ip_20_20, ip_4_20, ip_6_20, ip_14_20, ip_16_20]
  have hm : (mono 1 1 : L) ≠ 0 := by simp [mono]
  have n1 := Aw_ne 1 (by norm_num)
  have n2 := Aw_ne 2 (by norm_num)
  have n3 := Aw_ne 3 (by norm_num)
  have n4 := Aw_ne 4 (by norm_num)
  have n5 := Aw_ne 5 (by norm_num)
  have n6 := Aw_ne 6 (by norm_num)
  have n7 := Aw_ne 7 (by norm_num)
  have n8 := Aw_ne 8 (by norm_num)
  have n9 := Aw_ne 9 (by norm_num)
  have n10 := Aw_ne 10 (by norm_num)
  have n11 := Aw_ne 11 (by norm_num)
  have n12 := Aw_ne 12 (by norm_num)
  have n13 := Aw_ne 13 (by norm_num)
  have n14 := Aw_ne 14 (by norm_num)
  have n15 := Aw_ne 15 (by norm_num)
  have n16 := Aw_ne 16 (by norm_num)
  have n17 := Aw_ne 17 (by norm_num)
  have n18 := Aw_ne 18 (by norm_num)
  have n19 := Aw_ne 19 (by norm_num)
  have n20 := Aw_ne 20 (by norm_num)
  have n21 := Aw_ne 21 (by norm_num)
  have n22 := Aw_ne 22 (by norm_num)
  have n23 := Aw_ne 23 (by norm_num)
  have n24 := Aw_ne 24 (by norm_num)
  have n25 := Aw_ne 25 (by norm_num)
  have n26 := Aw_ne 26 (by norm_num)
  have n27 := Aw_ne 27 (by norm_num)
  have n28 := Aw_ne 28 (by norm_num)
  have n29 := Aw_ne 29 (by norm_num)
  have n30 := Aw_ne 30 (by norm_num)
  have n31 := Aw_ne 31 (by norm_num)
  have n32 := Aw_ne 32 (by norm_num)
  have n33 := Aw_ne 33 (by norm_num)
  have n34 := Aw_ne 34 (by norm_num)
  have n35 := Aw_ne 35 (by norm_num)
  have n36 := Aw_ne 36 (by norm_num)
  have n37 := Aw_ne 37 (by norm_num)
  have n38 := Aw_ne 38 (by norm_num)
  have n39 := Aw_ne 39 (by norm_num)
  have n40 := Aw_ne 40 (by norm_num)
  have n41 := Aw_ne 41 (by norm_num)
  have n42 := Aw_ne 42 (by norm_num)
  have n43 := Aw_ne 43 (by norm_num)
  have n44 := Aw_ne 44 (by norm_num)
  have n45 := Aw_ne 45 (by norm_num)
  have n46 := Aw_ne 46 (by norm_num)
  have n47 := Aw_ne 47 (by norm_num)
  have n48 := Aw_ne 48 (by norm_num)
  have n49 := Aw_ne 49 (by norm_num)
  have n50 := Aw_ne 50 (by norm_num)
  have n51 := Aw_ne 51 (by norm_num)
  have n52 := Aw_ne 52 (by norm_num)
  have n53 := Aw_ne 53 (by norm_num)
  have n54 := Aw_ne 54 (by norm_num)
  have n55 := Aw_ne 55 (by norm_num)
  have n56 := Aw_ne 56 (by norm_num)
  have n57 := Aw_ne 57 (by norm_num)
  have n58 := Aw_ne 58 (by norm_num)
  have n59 := Aw_ne 59 (by norm_num)
  have n60 := Aw_ne 60 (by norm_num)
  have n61 := Aw_ne 61 (by norm_num)
  have n62 := Aw_ne 62 (by norm_num)
  have n63 := Aw_ne 63 (by norm_num)
  have n64 := Aw_ne 64 (by norm_num)
  have n65 := Aw_ne 65 (by norm_num)
  have n66 := Aw_ne 66 (by norm_num)
  have n67 := Aw_ne 67 (by norm_num)
  have n68 := Aw_ne 68 (by norm_num)
  have n69 := Aw_ne 69 (by norm_num)
  have n70 := Aw_ne 70 (by norm_num)
  have n71 := Aw_ne 71 (by norm_num)
  have n72 := Aw_ne 72 (by norm_num)
  have n73 := Aw_ne 73 (by norm_num)
  have n74 := Aw_ne 74 (by norm_num)
  have n75 := Aw_ne 75 (by norm_num)
  have n76 := Aw_ne 76 (by norm_num)
  have n77 := Aw_ne 77 (by norm_num)
  have n78 := Aw_ne 78 (by norm_num)
  have n79 := Aw_ne 79 (by norm_num)
  have n80 := Aw_ne 80 (by norm_num)
  linear_combination (norm := (field_simp; ring)) (1 : L) * ((Aw 3 * Aw 7 * Aw 13 * Aw 17 * Aw 23 * Aw 27 * Aw 33 * Aw 37 * Aw 43 * Aw 47 * Aw 53 * Aw 57 * Aw 63 * Aw 67 * Aw 73 * Aw 77) / (Aw 4 * Aw 6 * Aw 10 * Aw 14 * Aw 16 * Aw 20 * Aw 24 * Aw 26 * Aw 30 * Aw 34 * Aw 36 * Aw 40 * Aw 44 * Aw 46 * Aw 50 * Aw 54 * Aw 56 * Aw 60 * Aw 64 * Aw 66 * Aw 70 * Aw 74 * Aw 76 * Aw 80)) * M_5_1m_2m + (1 : L) * ((Aw 3 * Aw 7 * Aw 13 * Aw 17 * Aw 23 * Aw 27 * Aw 33 * Aw 37 * Aw 43 * Aw 47 * Aw 53 * Aw 57 * Aw 63 * Aw 67 * Aw 73 * Aw 77) / (Aw 4 * Aw 6 * Aw 10 * Aw 14 * Aw 16 * Aw 20 * Aw 24 * Aw 26 * Aw 30 * Aw 34 * Aw 36 * Aw 40 * Aw 44 * Aw 46 * Aw 50 * Aw 54 * Aw 56 * Aw 60 * Aw 64 * Aw 66 * Aw 70 * Aw 74 * Aw 76 * Aw 80)) * M_5_1p_2p

/-- theta identity `F0`. -/
theorem theta_F0 : (2 : L) * (mono 1 1 * ((ιN h1 (Pinf 4 4)) * (ιN h1 (Pinf 2 4) * ιN h1 (Pinf 8 20) * ιN h1 (Pinf 12 20))⁻¹)) + (-1 : L) * ((ιN h1 (Pinf 5 10) ^ 2 * ιN h1 (Pinf 10 10)) * (ιN h1 (Pinf 1 5) * ιN h1 (Pinf 4 5))⁻¹) + (1 : L) * ((ιN h1 (Pinf 1 1) ^ 2) * (ιN h1 (Pinf 2 2) * ιN h1 (Pinf 1 5) * ιN h1 (Pinf 4 5))⁻¹) + (2 : L) * (mono 1 1 ^ 2 * ((ιN h1 (Pinf 20 20)) * (ιN h1 (Pinf 8 20) * ιN h1 (Pinf 10 20) * ιN h1 (Pinf 12 20))⁻¹)) = 0 := by
  have M_10_1m_3p := M_10_1m_3p; have M_5_1m_2m := M_5_1m_2m; have M_5_1p_2p := M_5_1p_2p
  simp only [cv_5_1_m, cv_5_2_m, cv_10_3_m, cv_10_4_m, cv_10_8_m, cv_10_9_m, cv_5_1_p, cv_5_2_p, cv_10_1_m, cv_10_3_p, cv_20_4_p, cv_20_8_p, cv_20_14_p, cv_20_18_p, cv_10_1_p, cv_10_5_m, cv_10_5_p, cv_10_2_m, cv_10_7_m, cv_10_10_m, cv_10_4_p, cv_10_8_p, cv_10_9_p] at M_10_1m_3p M_5_1m_2m M_5_1p_2p
  rw [ip_5_10, ip_10_10, ip_1_5, ip_4_5, ip_1_1, ip_2_2, ip_8_20, ip_10_20, ip_12_20, ip_20_20, ip_4_4, ip_2_4]
  have hm : (mono 1 1 : L) ≠ 0 := by simp [mono]
  have n1 := Aw_ne 1 (by norm_num)
  have n2 := Aw_ne 2 (by norm_num)
  have n3 := Aw_ne 3 (by norm_num)
  have n4 := Aw_ne 4 (by norm_num)
  have n5 := Aw_ne 5 (by norm_num)
  have n6 := Aw_ne 6 (by norm_num)
  have n7 := Aw_ne 7 (by norm_num)
  have n8 := Aw_ne 8 (by norm_num)
  have n9 := Aw_ne 9 (by norm_num)
  have n10 := Aw_ne 10 (by norm_num)
  have n11 := Aw_ne 11 (by norm_num)
  have n12 := Aw_ne 12 (by norm_num)
  have n13 := Aw_ne 13 (by norm_num)
  have n14 := Aw_ne 14 (by norm_num)
  have n15 := Aw_ne 15 (by norm_num)
  have n16 := Aw_ne 16 (by norm_num)
  have n17 := Aw_ne 17 (by norm_num)
  have n18 := Aw_ne 18 (by norm_num)
  have n19 := Aw_ne 19 (by norm_num)
  have n20 := Aw_ne 20 (by norm_num)
  have n21 := Aw_ne 21 (by norm_num)
  have n22 := Aw_ne 22 (by norm_num)
  have n23 := Aw_ne 23 (by norm_num)
  have n24 := Aw_ne 24 (by norm_num)
  have n25 := Aw_ne 25 (by norm_num)
  have n26 := Aw_ne 26 (by norm_num)
  have n27 := Aw_ne 27 (by norm_num)
  have n28 := Aw_ne 28 (by norm_num)
  have n29 := Aw_ne 29 (by norm_num)
  have n30 := Aw_ne 30 (by norm_num)
  have n31 := Aw_ne 31 (by norm_num)
  have n32 := Aw_ne 32 (by norm_num)
  have n33 := Aw_ne 33 (by norm_num)
  have n34 := Aw_ne 34 (by norm_num)
  have n35 := Aw_ne 35 (by norm_num)
  have n36 := Aw_ne 36 (by norm_num)
  have n37 := Aw_ne 37 (by norm_num)
  have n38 := Aw_ne 38 (by norm_num)
  have n39 := Aw_ne 39 (by norm_num)
  have n40 := Aw_ne 40 (by norm_num)
  have n41 := Aw_ne 41 (by norm_num)
  have n42 := Aw_ne 42 (by norm_num)
  have n43 := Aw_ne 43 (by norm_num)
  have n44 := Aw_ne 44 (by norm_num)
  have n45 := Aw_ne 45 (by norm_num)
  have n46 := Aw_ne 46 (by norm_num)
  have n47 := Aw_ne 47 (by norm_num)
  have n48 := Aw_ne 48 (by norm_num)
  have n49 := Aw_ne 49 (by norm_num)
  have n50 := Aw_ne 50 (by norm_num)
  have n51 := Aw_ne 51 (by norm_num)
  have n52 := Aw_ne 52 (by norm_num)
  have n53 := Aw_ne 53 (by norm_num)
  have n54 := Aw_ne 54 (by norm_num)
  have n55 := Aw_ne 55 (by norm_num)
  have n56 := Aw_ne 56 (by norm_num)
  have n57 := Aw_ne 57 (by norm_num)
  have n58 := Aw_ne 58 (by norm_num)
  have n59 := Aw_ne 59 (by norm_num)
  have n60 := Aw_ne 60 (by norm_num)
  have n61 := Aw_ne 61 (by norm_num)
  have n62 := Aw_ne 62 (by norm_num)
  have n63 := Aw_ne 63 (by norm_num)
  have n64 := Aw_ne 64 (by norm_num)
  have n65 := Aw_ne 65 (by norm_num)
  have n66 := Aw_ne 66 (by norm_num)
  have n67 := Aw_ne 67 (by norm_num)
  have n68 := Aw_ne 68 (by norm_num)
  have n69 := Aw_ne 69 (by norm_num)
  have n70 := Aw_ne 70 (by norm_num)
  have n71 := Aw_ne 71 (by norm_num)
  have n72 := Aw_ne 72 (by norm_num)
  have n73 := Aw_ne 73 (by norm_num)
  have n74 := Aw_ne 74 (by norm_num)
  have n75 := Aw_ne 75 (by norm_num)
  have n76 := Aw_ne 76 (by norm_num)
  have n77 := Aw_ne 77 (by norm_num)
  have n78 := Aw_ne 78 (by norm_num)
  have n79 := Aw_ne 79 (by norm_num)
  have n80 := Aw_ne 80 (by norm_num)
  linear_combination (norm := (field_simp; ring)) (-2 : L) * mono 1 1 * ((1) / (Aw 2 * Aw 6 * Aw 8 * Aw 10 * Aw 12 * Aw 14 * Aw 18 * Aw 20 * Aw 22 * Aw 26 * Aw 28 * Aw 30 * Aw 32 * Aw 34 * Aw 38 * Aw 40 * Aw 42 * Aw 46 * Aw 48 * Aw 50 * Aw 52 * Aw 54 * Aw 58 * Aw 60 * Aw 62 * Aw 66 * Aw 68 * Aw 70 * Aw 72 * Aw 74 * Aw 78 * Aw 80)) * M_10_1m_3p + (-1 : L) * ((Aw 3 * Aw 7 * Aw 13 * Aw 17 * Aw 23 * Aw 27 * Aw 33 * Aw 37 * Aw 43 * Aw 47 * Aw 53 * Aw 57 * Aw 63 * Aw 67 * Aw 73 * Aw 77) / (Aw 4 * Aw 6 * Aw 10 * Aw 14 * Aw 16 * Aw 20 * Aw 24 * Aw 26 * Aw 30 * Aw 34 * Aw 36 * Aw 40 * Aw 44 * Aw 46 * Aw 50 * Aw 54 * Aw 56 * Aw 60 * Aw 64 * Aw 66 * Aw 70 * Aw 74 * Aw 76 * Aw 80)) * M_5_1m_2m + (1 : L) * ((Aw 3 * Aw 7 * Aw 13 * Aw 17 * Aw 23 * Aw 27 * Aw 33 * Aw 37 * Aw 43 * Aw 47 * Aw 53 * Aw 57 * Aw 63 * Aw 67 * Aw 73 * Aw 77) / (Aw 4 * Aw 6 * Aw 10 * Aw 14 * Aw 16 * Aw 20 * Aw 24 * Aw 26 * Aw 30 * Aw 34 * Aw 36 * Aw 40 * Aw 44 * Aw 46 * Aw 50 * Aw 54 * Aw 56 * Aw 60 * Aw 64 * Aw 66 * Aw 70 * Aw 74 * Aw 76 * Aw 80)) * M_5_1p_2p

/-- theta identity `psi0`. -/
theorem theta_psi0 : (1 : L) * ((ιN h1 (Pinf 4 4)) * (ιN h1 (Pinf 2 4) * ιN h1 (Pinf 8 20) * ιN h1 (Pinf 12 20))⁻¹) + (-1 : L) * (mono 1 1 * ((ιN h1 (Pinf 20 20)) * (ιN h1 (Pinf 8 20) * ιN h1 (Pinf 10 20) * ιN h1 (Pinf 12 20))⁻¹)) + (-1 : L) * ((ιN h1 (Pinf 1 10) * ιN h1 (Pinf 9 10) * ιN h1 (Pinf 10 10)) * (ιN h1 (Pinf 2 10) * ιN h1 (Pinf 3 10) * ιN h1 (Pinf 7 10) * ιN h1 (Pinf 8 10))⁻¹) = 0 := by
  have M_10_1p_3m := M_10_1p_3m
  simp only [cv_5_1_m, cv_5_2_m, cv_10_3_m, cv_10_4_m, cv_10_8_m, cv_10_9_m, cv_5_1_p, cv_5_2_p, cv_10_1_m, cv_10_3_p, cv_20_4_p, cv_20_8_p, cv_20_14_p, cv_20_18_p, cv_10_1_p, cv_10_5_m, cv_10_5_p, cv_10_2_m, cv_10_7_m, cv_10_10_m, cv_10_4_p, cv_10_8_p, cv_10_9_p] at M_10_1p_3m
  rw [ip_10_10, ip_8_20, ip_10_20, ip_12_20, ip_20_20, ip_4_4, ip_2_4, ip_1_10, ip_9_10, ip_2_10, ip_3_10, ip_7_10, ip_8_10]
  have hm : (mono 1 1 : L) ≠ 0 := by simp [mono]
  have n1 := Aw_ne 1 (by norm_num)
  have n2 := Aw_ne 2 (by norm_num)
  have n3 := Aw_ne 3 (by norm_num)
  have n4 := Aw_ne 4 (by norm_num)
  have n5 := Aw_ne 5 (by norm_num)
  have n6 := Aw_ne 6 (by norm_num)
  have n7 := Aw_ne 7 (by norm_num)
  have n8 := Aw_ne 8 (by norm_num)
  have n9 := Aw_ne 9 (by norm_num)
  have n10 := Aw_ne 10 (by norm_num)
  have n11 := Aw_ne 11 (by norm_num)
  have n12 := Aw_ne 12 (by norm_num)
  have n13 := Aw_ne 13 (by norm_num)
  have n14 := Aw_ne 14 (by norm_num)
  have n15 := Aw_ne 15 (by norm_num)
  have n16 := Aw_ne 16 (by norm_num)
  have n17 := Aw_ne 17 (by norm_num)
  have n18 := Aw_ne 18 (by norm_num)
  have n19 := Aw_ne 19 (by norm_num)
  have n20 := Aw_ne 20 (by norm_num)
  have n21 := Aw_ne 21 (by norm_num)
  have n22 := Aw_ne 22 (by norm_num)
  have n23 := Aw_ne 23 (by norm_num)
  have n24 := Aw_ne 24 (by norm_num)
  have n25 := Aw_ne 25 (by norm_num)
  have n26 := Aw_ne 26 (by norm_num)
  have n27 := Aw_ne 27 (by norm_num)
  have n28 := Aw_ne 28 (by norm_num)
  have n29 := Aw_ne 29 (by norm_num)
  have n30 := Aw_ne 30 (by norm_num)
  have n31 := Aw_ne 31 (by norm_num)
  have n32 := Aw_ne 32 (by norm_num)
  have n33 := Aw_ne 33 (by norm_num)
  have n34 := Aw_ne 34 (by norm_num)
  have n35 := Aw_ne 35 (by norm_num)
  have n36 := Aw_ne 36 (by norm_num)
  have n37 := Aw_ne 37 (by norm_num)
  have n38 := Aw_ne 38 (by norm_num)
  have n39 := Aw_ne 39 (by norm_num)
  have n40 := Aw_ne 40 (by norm_num)
  have n41 := Aw_ne 41 (by norm_num)
  have n42 := Aw_ne 42 (by norm_num)
  have n43 := Aw_ne 43 (by norm_num)
  have n44 := Aw_ne 44 (by norm_num)
  have n45 := Aw_ne 45 (by norm_num)
  have n46 := Aw_ne 46 (by norm_num)
  have n47 := Aw_ne 47 (by norm_num)
  have n48 := Aw_ne 48 (by norm_num)
  have n49 := Aw_ne 49 (by norm_num)
  have n50 := Aw_ne 50 (by norm_num)
  have n51 := Aw_ne 51 (by norm_num)
  have n52 := Aw_ne 52 (by norm_num)
  have n53 := Aw_ne 53 (by norm_num)
  have n54 := Aw_ne 54 (by norm_num)
  have n55 := Aw_ne 55 (by norm_num)
  have n56 := Aw_ne 56 (by norm_num)
  have n57 := Aw_ne 57 (by norm_num)
  have n58 := Aw_ne 58 (by norm_num)
  have n59 := Aw_ne 59 (by norm_num)
  have n60 := Aw_ne 60 (by norm_num)
  have n61 := Aw_ne 61 (by norm_num)
  have n62 := Aw_ne 62 (by norm_num)
  have n63 := Aw_ne 63 (by norm_num)
  have n64 := Aw_ne 64 (by norm_num)
  have n65 := Aw_ne 65 (by norm_num)
  have n66 := Aw_ne 66 (by norm_num)
  have n67 := Aw_ne 67 (by norm_num)
  have n68 := Aw_ne 68 (by norm_num)
  have n69 := Aw_ne 69 (by norm_num)
  have n70 := Aw_ne 70 (by norm_num)
  have n71 := Aw_ne 71 (by norm_num)
  have n72 := Aw_ne 72 (by norm_num)
  have n73 := Aw_ne 73 (by norm_num)
  have n74 := Aw_ne 74 (by norm_num)
  have n75 := Aw_ne 75 (by norm_num)
  have n76 := Aw_ne 76 (by norm_num)
  have n77 := Aw_ne 77 (by norm_num)
  have n78 := Aw_ne 78 (by norm_num)
  have n79 := Aw_ne 79 (by norm_num)
  have n80 := Aw_ne 80 (by norm_num)
  linear_combination (norm := (field_simp; ring)) (-1 : L) * ((1) / (Aw 2 * Aw 6 * Aw 8 * Aw 10 * Aw 12 * Aw 14 * Aw 18 * Aw 20 * Aw 22 * Aw 26 * Aw 28 * Aw 30 * Aw 32 * Aw 34 * Aw 38 * Aw 40 * Aw 42 * Aw 46 * Aw 48 * Aw 50 * Aw 52 * Aw 54 * Aw 58 * Aw 60 * Aw 62 * Aw 66 * Aw 68 * Aw 70 * Aw 72 * Aw 74 * Aw 78 * Aw 80)) * M_10_1p_3m

/-- theta identity `phi1`. -/
theorem theta_phi1 : (1 : L) * ((ιN h1 (Pinf 5 10) ^ 2 * ιN h1 (Pinf 10 10)) * (ιN h1 (Pinf 2 5) * ιN h1 (Pinf 3 5))⁻¹) + (-1 : L) * ((ιN h1 (Pinf 1 1) ^ 2) * (ιN h1 (Pinf 2 2) * ιN h1 (Pinf 2 5) * ιN h1 (Pinf 3 5))⁻¹) + (-2 : L) * (mono 1 1 * ((ιN h1 (Pinf 4 20) * ιN h1 (Pinf 10 20) * ιN h1 (Pinf 16 20) * ιN h1 (Pinf 20 20)) * (ιN h1 (Pinf 2 20) * ιN h1 (Pinf 8 20) ^ 2 * ιN h1 (Pinf 12 20) ^ 2 * ιN h1 (Pinf 18 20))⁻¹)) = 0 := by
  have M_5_1m_2m := M_5_1m_2m; have M_5_1p_2p := M_5_1p_2p
  simp only [cv_5_1_m, cv_5_2_m, cv_10_3_m, cv_10_4_m, cv_10_8_m, cv_10_9_m, cv_5_1_p, cv_5_2_p, cv_10_1_m, cv_10_3_p, cv_20_4_p, cv_20_8_p, cv_20_14_p, cv_20_18_p, cv_10_1_p, cv_10_5_m, cv_10_5_p, cv_10_2_m, cv_10_7_m, cv_10_10_m, cv_10_4_p, cv_10_8_p, cv_10_9_p] at M_5_1m_2m M_5_1p_2p
  rw [ip_5_10, ip_10_10, ip_1_1, ip_2_2, ip_8_20, ip_10_20, ip_12_20, ip_20_20, ip_4_20, ip_16_20, ip_2_5, ip_3_5, ip_2_20, ip_18_20]
  have hm : (mono 1 1 : L) ≠ 0 := by simp [mono]
  have n1 := Aw_ne 1 (by norm_num)
  have n2 := Aw_ne 2 (by norm_num)
  have n3 := Aw_ne 3 (by norm_num)
  have n4 := Aw_ne 4 (by norm_num)
  have n5 := Aw_ne 5 (by norm_num)
  have n6 := Aw_ne 6 (by norm_num)
  have n7 := Aw_ne 7 (by norm_num)
  have n8 := Aw_ne 8 (by norm_num)
  have n9 := Aw_ne 9 (by norm_num)
  have n10 := Aw_ne 10 (by norm_num)
  have n11 := Aw_ne 11 (by norm_num)
  have n12 := Aw_ne 12 (by norm_num)
  have n13 := Aw_ne 13 (by norm_num)
  have n14 := Aw_ne 14 (by norm_num)
  have n15 := Aw_ne 15 (by norm_num)
  have n16 := Aw_ne 16 (by norm_num)
  have n17 := Aw_ne 17 (by norm_num)
  have n18 := Aw_ne 18 (by norm_num)
  have n19 := Aw_ne 19 (by norm_num)
  have n20 := Aw_ne 20 (by norm_num)
  have n21 := Aw_ne 21 (by norm_num)
  have n22 := Aw_ne 22 (by norm_num)
  have n23 := Aw_ne 23 (by norm_num)
  have n24 := Aw_ne 24 (by norm_num)
  have n25 := Aw_ne 25 (by norm_num)
  have n26 := Aw_ne 26 (by norm_num)
  have n27 := Aw_ne 27 (by norm_num)
  have n28 := Aw_ne 28 (by norm_num)
  have n29 := Aw_ne 29 (by norm_num)
  have n30 := Aw_ne 30 (by norm_num)
  have n31 := Aw_ne 31 (by norm_num)
  have n32 := Aw_ne 32 (by norm_num)
  have n33 := Aw_ne 33 (by norm_num)
  have n34 := Aw_ne 34 (by norm_num)
  have n35 := Aw_ne 35 (by norm_num)
  have n36 := Aw_ne 36 (by norm_num)
  have n37 := Aw_ne 37 (by norm_num)
  have n38 := Aw_ne 38 (by norm_num)
  have n39 := Aw_ne 39 (by norm_num)
  have n40 := Aw_ne 40 (by norm_num)
  have n41 := Aw_ne 41 (by norm_num)
  have n42 := Aw_ne 42 (by norm_num)
  have n43 := Aw_ne 43 (by norm_num)
  have n44 := Aw_ne 44 (by norm_num)
  have n45 := Aw_ne 45 (by norm_num)
  have n46 := Aw_ne 46 (by norm_num)
  have n47 := Aw_ne 47 (by norm_num)
  have n48 := Aw_ne 48 (by norm_num)
  have n49 := Aw_ne 49 (by norm_num)
  have n50 := Aw_ne 50 (by norm_num)
  have n51 := Aw_ne 51 (by norm_num)
  have n52 := Aw_ne 52 (by norm_num)
  have n53 := Aw_ne 53 (by norm_num)
  have n54 := Aw_ne 54 (by norm_num)
  have n55 := Aw_ne 55 (by norm_num)
  have n56 := Aw_ne 56 (by norm_num)
  have n57 := Aw_ne 57 (by norm_num)
  have n58 := Aw_ne 58 (by norm_num)
  have n59 := Aw_ne 59 (by norm_num)
  have n60 := Aw_ne 60 (by norm_num)
  have n61 := Aw_ne 61 (by norm_num)
  have n62 := Aw_ne 62 (by norm_num)
  have n63 := Aw_ne 63 (by norm_num)
  have n64 := Aw_ne 64 (by norm_num)
  have n65 := Aw_ne 65 (by norm_num)
  have n66 := Aw_ne 66 (by norm_num)
  have n67 := Aw_ne 67 (by norm_num)
  have n68 := Aw_ne 68 (by norm_num)
  have n69 := Aw_ne 69 (by norm_num)
  have n70 := Aw_ne 70 (by norm_num)
  have n71 := Aw_ne 71 (by norm_num)
  have n72 := Aw_ne 72 (by norm_num)
  have n73 := Aw_ne 73 (by norm_num)
  have n74 := Aw_ne 74 (by norm_num)
  have n75 := Aw_ne 75 (by norm_num)
  have n76 := Aw_ne 76 (by norm_num)
  have n77 := Aw_ne 77 (by norm_num)
  have n78 := Aw_ne 78 (by norm_num)
  have n79 := Aw_ne 79 (by norm_num)
  have n80 := Aw_ne 80 (by norm_num)
  linear_combination (norm := (field_simp; ring)) (1 : L) * ((Aw 1 * Aw 9 * Aw 11 * Aw 19 * Aw 21 * Aw 29 * Aw 31 * Aw 39 * Aw 41 * Aw 49 * Aw 51 * Aw 59 * Aw 61 * Aw 69 * Aw 71 * Aw 79) / (Aw 2 * Aw 8 * Aw 10 * Aw 12 * Aw 18 * Aw 20 * Aw 22 * Aw 28 * Aw 30 * Aw 32 * Aw 38 * Aw 40 * Aw 42 * Aw 48 * Aw 50 * Aw 52 * Aw 58 * Aw 60 * Aw 62 * Aw 68 * Aw 70 * Aw 72 * Aw 78 * Aw 80)) * M_5_1m_2m + (-1 : L) * ((Aw 1 * Aw 9 * Aw 11 * Aw 19 * Aw 21 * Aw 29 * Aw 31 * Aw 39 * Aw 41 * Aw 49 * Aw 51 * Aw 59 * Aw 61 * Aw 69 * Aw 71 * Aw 79) / (Aw 2 * Aw 8 * Aw 10 * Aw 12 * Aw 18 * Aw 20 * Aw 22 * Aw 28 * Aw 30 * Aw 32 * Aw 38 * Aw 40 * Aw 42 * Aw 48 * Aw 50 * Aw 52 * Aw 58 * Aw 60 * Aw 62 * Aw 68 * Aw 70 * Aw 72 * Aw 78 * Aw 80)) * M_5_1p_2p

/-- theta identity `F1`. -/
theorem theta_F1 : (2 : L) * ((ιN h1 (Pinf 4 4)) * (ιN h1 (Pinf 2 4) * ιN h1 (Pinf 4 20) * ιN h1 (Pinf 16 20))⁻¹) + (-1 : L) * ((ιN h1 (Pinf 5 10) ^ 2 * ιN h1 (Pinf 10 10)) * (ιN h1 (Pinf 2 5) * ιN h1 (Pinf 3 5))⁻¹) + (-1 : L) * ((ιN h1 (Pinf 1 1) ^ 2) * (ιN h1 (Pinf 2 2) * ιN h1 (Pinf 2 5) * ιN h1 (Pinf 3 5))⁻¹) + (-2 : L) * (mono 1 1 * ((ιN h1 (Pinf 20 20)) * (ιN h1 (Pinf 4 20) * ιN h1 (Pinf 10 20) * ιN h1 (Pinf 16 20))⁻¹)) = 0 := by
  have M_10_3m_5p := M_10_3m_5p; have M_10_3p_5m := M_10_3p_5m; have M_5_1p_1p := M_5_1p_1p
  simp only [cv_5_1_m, cv_5_2_m, cv_10_3_m, cv_10_4_m, cv_10_8_m, cv_10_9_m, cv_5_1_p, cv_5_2_p, cv_10_1_m, cv_10_3_p, cv_20_4_p, cv_20_8_p, cv_20_14_p, cv_20_18_p, cv_10_1_p, cv_10_5_m, cv_10_5_p, cv_10_2_m, cv_10_7_m, cv_10_10_m, cv_10_4_p, cv_10_8_p, cv_10_9_p] at M_10_3m_5p M_10_3p_5m M_5_1p_1p
  rw [ip_5_10, ip_10_10, ip_1_1, ip_2_2, ip_10_20, ip_20_20, ip_4_20, ip_16_20, ip_4_4, ip_2_4, ip_2_5, ip_3_5]
  have hm : (mono 1 1 : L) ≠ 0 := by simp [mono]
  have n1 := Aw_ne 1 (by norm_num)
  have n2 := Aw_ne 2 (by norm_num)
  have n3 := Aw_ne 3 (by norm_num)
  have n4 := Aw_ne 4 (by norm_num)
  have n5 := Aw_ne 5 (by norm_num)
  have n6 := Aw_ne 6 (by norm_num)
  have n7 := Aw_ne 7 (by norm_num)
  have n8 := Aw_ne 8 (by norm_num)
  have n9 := Aw_ne 9 (by norm_num)
  have n10 := Aw_ne 10 (by norm_num)
  have n11 := Aw_ne 11 (by norm_num)
  have n12 := Aw_ne 12 (by norm_num)
  have n13 := Aw_ne 13 (by norm_num)
  have n14 := Aw_ne 14 (by norm_num)
  have n15 := Aw_ne 15 (by norm_num)
  have n16 := Aw_ne 16 (by norm_num)
  have n17 := Aw_ne 17 (by norm_num)
  have n18 := Aw_ne 18 (by norm_num)
  have n19 := Aw_ne 19 (by norm_num)
  have n20 := Aw_ne 20 (by norm_num)
  have n21 := Aw_ne 21 (by norm_num)
  have n22 := Aw_ne 22 (by norm_num)
  have n23 := Aw_ne 23 (by norm_num)
  have n24 := Aw_ne 24 (by norm_num)
  have n25 := Aw_ne 25 (by norm_num)
  have n26 := Aw_ne 26 (by norm_num)
  have n27 := Aw_ne 27 (by norm_num)
  have n28 := Aw_ne 28 (by norm_num)
  have n29 := Aw_ne 29 (by norm_num)
  have n30 := Aw_ne 30 (by norm_num)
  have n31 := Aw_ne 31 (by norm_num)
  have n32 := Aw_ne 32 (by norm_num)
  have n33 := Aw_ne 33 (by norm_num)
  have n34 := Aw_ne 34 (by norm_num)
  have n35 := Aw_ne 35 (by norm_num)
  have n36 := Aw_ne 36 (by norm_num)
  have n37 := Aw_ne 37 (by norm_num)
  have n38 := Aw_ne 38 (by norm_num)
  have n39 := Aw_ne 39 (by norm_num)
  have n40 := Aw_ne 40 (by norm_num)
  have n41 := Aw_ne 41 (by norm_num)
  have n42 := Aw_ne 42 (by norm_num)
  have n43 := Aw_ne 43 (by norm_num)
  have n44 := Aw_ne 44 (by norm_num)
  have n45 := Aw_ne 45 (by norm_num)
  have n46 := Aw_ne 46 (by norm_num)
  have n47 := Aw_ne 47 (by norm_num)
  have n48 := Aw_ne 48 (by norm_num)
  have n49 := Aw_ne 49 (by norm_num)
  have n50 := Aw_ne 50 (by norm_num)
  have n51 := Aw_ne 51 (by norm_num)
  have n52 := Aw_ne 52 (by norm_num)
  have n53 := Aw_ne 53 (by norm_num)
  have n54 := Aw_ne 54 (by norm_num)
  have n55 := Aw_ne 55 (by norm_num)
  have n56 := Aw_ne 56 (by norm_num)
  have n57 := Aw_ne 57 (by norm_num)
  have n58 := Aw_ne 58 (by norm_num)
  have n59 := Aw_ne 59 (by norm_num)
  have n60 := Aw_ne 60 (by norm_num)
  have n61 := Aw_ne 61 (by norm_num)
  have n62 := Aw_ne 62 (by norm_num)
  have n63 := Aw_ne 63 (by norm_num)
  have n64 := Aw_ne 64 (by norm_num)
  have n65 := Aw_ne 65 (by norm_num)
  have n66 := Aw_ne 66 (by norm_num)
  have n67 := Aw_ne 67 (by norm_num)
  have n68 := Aw_ne 68 (by norm_num)
  have n69 := Aw_ne 69 (by norm_num)
  have n70 := Aw_ne 70 (by norm_num)
  have n71 := Aw_ne 71 (by norm_num)
  have n72 := Aw_ne 72 (by norm_num)
  have n73 := Aw_ne 73 (by norm_num)
  have n74 := Aw_ne 74 (by norm_num)
  have n75 := Aw_ne 75 (by norm_num)
  have n76 := Aw_ne 76 (by norm_num)
  have n77 := Aw_ne 77 (by norm_num)
  have n78 := Aw_ne 78 (by norm_num)
  have n79 := Aw_ne 79 (by norm_num)
  have n80 := Aw_ne 80 (by norm_num)
  linear_combination (norm := (field_simp; ring)) (-1 : L) * ((1) / (Aw 2 * Aw 6 * Aw 8 * Aw 10 * Aw 12 * Aw 14 * Aw 18 * Aw 20 * Aw 22 * Aw 26 * Aw 28 * Aw 30 * Aw 32 * Aw 34 * Aw 38 * Aw 40 * Aw 42 * Aw 46 * Aw 48 * Aw 50 * Aw 52 * Aw 54 * Aw 58 * Aw 60 * Aw 62 * Aw 66 * Aw 68 * Aw 70 * Aw 72 * Aw 74 * Aw 78 * Aw 80)) * M_10_3p_5m + (-1 : L) * ((1) / (Aw 2 * Aw 6 * Aw 8 * Aw 10 * Aw 12 * Aw 14 * Aw 18 * Aw 20 * Aw 22 * Aw 26 * Aw 28 * Aw 30 * Aw 32 * Aw 34 * Aw 38 * Aw 40 * Aw 42 * Aw 46 * Aw 48 * Aw 50 * Aw 52 * Aw 54 * Aw 58 * Aw 60 * Aw 62 * Aw 66 * Aw 68 * Aw 70 * Aw 72 * Aw 74 * Aw 78 * Aw 80)) * M_10_3m_5p + (-1 : L) * ((Aw 3 * Aw 7 * Aw 13 * Aw 17 * Aw 23 * Aw 27 * Aw 33 * Aw 37 * Aw 43 * Aw 47 * Aw 53 * Aw 57 * Aw 63 * Aw 67 * Aw 73 * Aw 77) / (Aw 4 * Aw 6 * Aw 10 * Aw 14 * Aw 16 * Aw 20 * Aw 24 * Aw 26 * Aw 30 * Aw 34 * Aw 36 * Aw 40 * Aw 44 * Aw 46 * Aw 50 * Aw 54 * Aw 56 * Aw 60 * Aw 64 * Aw 66 * Aw 70 * Aw 74 * Aw 76 * Aw 80)) * M_5_1p_1p

/-- theta identity `psi1`. -/
theorem theta_psi1 : (1 : L) * ((ιN h1 (Pinf 4 4)) * (ιN h1 (Pinf 2 4) * ιN h1 (Pinf 4 20) * ιN h1 (Pinf 16 20))⁻¹) + (1 : L) * (mono 1 1 * ((ιN h1 (Pinf 20 20)) * (ιN h1 (Pinf 4 20) * ιN h1 (Pinf 10 20) * ιN h1 (Pinf 16 20))⁻¹)) + (-1 : L) * ((ιN h1 (Pinf 3 10) * ιN h1 (Pinf 7 10) * ιN h1 (Pinf 10 10)) * (ιN h1 (Pinf 1 10) * ιN h1 (Pinf 4 10) * ιN h1 (Pinf 6 10) * ιN h1 (Pinf 9 10))⁻¹) = 0 := by
  have M_10_1m_3p := M_10_1m_3p
  simp only [cv_5_1_m, cv_5_2_m, cv_10_3_m, cv_10_4_m, cv_10_8_m, cv_10_9_m, cv_5_1_p, cv_5_2_p, cv_10_1_m, cv_10_3_p, cv_20_4_p, cv_20_8_p, cv_20_14_p, cv_20_18_p, cv_10_1_p, cv_10_5_m, cv_10_5_p, cv_10_2_m, cv_10_7_m, cv_10_10_m, cv_10_4_p, cv_10_8_p, cv_10_9_p] at M_10_1m_3p
  rw [ip_10_10, ip_10_20, ip_20_20, ip_4_20, ip_16_20, ip_4_4, ip_2_4, ip_1_10, ip_9_10, ip_3_10, ip_7_10, ip_4_10, ip_6_10]
  have hm : (mono 1 1 : L) ≠ 0 := by simp [mono]
  have n1 := Aw_ne 1 (by norm_num)
  have n2 := Aw_ne 2 (by norm_num)
  have n3 := Aw_ne 3 (by norm_num)
  have n4 := Aw_ne 4 (by norm_num)
  have n5 := Aw_ne 5 (by norm_num)
  have n6 := Aw_ne 6 (by norm_num)
  have n7 := Aw_ne 7 (by norm_num)
  have n8 := Aw_ne 8 (by norm_num)
  have n9 := Aw_ne 9 (by norm_num)
  have n10 := Aw_ne 10 (by norm_num)
  have n11 := Aw_ne 11 (by norm_num)
  have n12 := Aw_ne 12 (by norm_num)
  have n13 := Aw_ne 13 (by norm_num)
  have n14 := Aw_ne 14 (by norm_num)
  have n15 := Aw_ne 15 (by norm_num)
  have n16 := Aw_ne 16 (by norm_num)
  have n17 := Aw_ne 17 (by norm_num)
  have n18 := Aw_ne 18 (by norm_num)
  have n19 := Aw_ne 19 (by norm_num)
  have n20 := Aw_ne 20 (by norm_num)
  have n21 := Aw_ne 21 (by norm_num)
  have n22 := Aw_ne 22 (by norm_num)
  have n23 := Aw_ne 23 (by norm_num)
  have n24 := Aw_ne 24 (by norm_num)
  have n25 := Aw_ne 25 (by norm_num)
  have n26 := Aw_ne 26 (by norm_num)
  have n27 := Aw_ne 27 (by norm_num)
  have n28 := Aw_ne 28 (by norm_num)
  have n29 := Aw_ne 29 (by norm_num)
  have n30 := Aw_ne 30 (by norm_num)
  have n31 := Aw_ne 31 (by norm_num)
  have n32 := Aw_ne 32 (by norm_num)
  have n33 := Aw_ne 33 (by norm_num)
  have n34 := Aw_ne 34 (by norm_num)
  have n35 := Aw_ne 35 (by norm_num)
  have n36 := Aw_ne 36 (by norm_num)
  have n37 := Aw_ne 37 (by norm_num)
  have n38 := Aw_ne 38 (by norm_num)
  have n39 := Aw_ne 39 (by norm_num)
  have n40 := Aw_ne 40 (by norm_num)
  have n41 := Aw_ne 41 (by norm_num)
  have n42 := Aw_ne 42 (by norm_num)
  have n43 := Aw_ne 43 (by norm_num)
  have n44 := Aw_ne 44 (by norm_num)
  have n45 := Aw_ne 45 (by norm_num)
  have n46 := Aw_ne 46 (by norm_num)
  have n47 := Aw_ne 47 (by norm_num)
  have n48 := Aw_ne 48 (by norm_num)
  have n49 := Aw_ne 49 (by norm_num)
  have n50 := Aw_ne 50 (by norm_num)
  have n51 := Aw_ne 51 (by norm_num)
  have n52 := Aw_ne 52 (by norm_num)
  have n53 := Aw_ne 53 (by norm_num)
  have n54 := Aw_ne 54 (by norm_num)
  have n55 := Aw_ne 55 (by norm_num)
  have n56 := Aw_ne 56 (by norm_num)
  have n57 := Aw_ne 57 (by norm_num)
  have n58 := Aw_ne 58 (by norm_num)
  have n59 := Aw_ne 59 (by norm_num)
  have n60 := Aw_ne 60 (by norm_num)
  have n61 := Aw_ne 61 (by norm_num)
  have n62 := Aw_ne 62 (by norm_num)
  have n63 := Aw_ne 63 (by norm_num)
  have n64 := Aw_ne 64 (by norm_num)
  have n65 := Aw_ne 65 (by norm_num)
  have n66 := Aw_ne 66 (by norm_num)
  have n67 := Aw_ne 67 (by norm_num)
  have n68 := Aw_ne 68 (by norm_num)
  have n69 := Aw_ne 69 (by norm_num)
  have n70 := Aw_ne 70 (by norm_num)
  have n71 := Aw_ne 71 (by norm_num)
  have n72 := Aw_ne 72 (by norm_num)
  have n73 := Aw_ne 73 (by norm_num)
  have n74 := Aw_ne 74 (by norm_num)
  have n75 := Aw_ne 75 (by norm_num)
  have n76 := Aw_ne 76 (by norm_num)
  have n77 := Aw_ne 77 (by norm_num)
  have n78 := Aw_ne 78 (by norm_num)
  have n79 := Aw_ne 79 (by norm_num)
  have n80 := Aw_ne 80 (by norm_num)
  linear_combination (norm := (field_simp; ring)) (-1 : L) * ((1) / (Aw 2 * Aw 4 * Aw 6 * Aw 10 * Aw 14 * Aw 16 * Aw 18 * Aw 20 * Aw 22 * Aw 24 * Aw 26 * Aw 30 * Aw 34 * Aw 36 * Aw 38 * Aw 40 * Aw 42 * Aw 44 * Aw 46 * Aw 50 * Aw 54 * Aw 56 * Aw 58 * Aw 60 * Aw 62 * Aw 64 * Aw 66 * Aw 70 * Aw 74 * Aw 76 * Aw 78 * Aw 80)) * M_10_1m_3p

/-- theta identity `chi1`. -/
theorem theta_chi1 : (2 : L) * ((ιN h1 (Pinf 10 10)) * (ιN h1 (Pinf 2 10) * ιN h1 (Pinf 5 10) * ιN h1 (Pinf 8 10))⁻¹) + (-1 : L) * ((ιN h1 (Pinf 2 10) * ιN h1 (Pinf 5 10) * ιN h1 (Pinf 8 10) * ιN h1 (Pinf 10 10)) * (ιN h1 (Pinf 1 10) * ιN h1 (Pinf 4 10) ^ 2 * ιN h1 (Pinf 6 10) ^ 2 * ιN h1 (Pinf 9 10))⁻¹) + (-1 : L) * ((ιN h1 (Pinf 1 5) * ιN h1 (Pinf 4 5) * ιN h1 (Pinf 5 5)) * (ιN h1 (Pinf 2 5) ^ 2 * ιN h1 (Pinf 3 5) ^ 2)⁻¹) = 0 := by
  have M_5_1m_2p := M_5_1m_2p; have M_5_1p_2m := M_5_1p_2m
  simp only [cv_5_1_m, cv_5_2_m, cv_10_3_m, cv_10_4_m, cv_10_8_m, cv_10_9_m, cv_5_1_p, cv_5_2_p, cv_10_1_m, cv_10_3_p, cv_20_4_p, cv_20_8_p, cv_20_14_p, cv_20_18_p, cv_10_1_p, cv_10_5_m, cv_10_5_p, cv_10_2_m, cv_10_7_m, cv_10_10_m, cv_10_4_p, cv_10_8_p, cv_10_9_p] at M_5_1m_2p M_5_1p_2m
  rw [ip_5_10, ip_10_10, ip_1_5, ip_4_5, ip_1_10, ip_9_10, ip_2_10, ip_8_10, ip_2_5, ip_3_5, ip_4_10, ip_6_10, ip_5_5]
  have hm : (mono 1 1 : L) ≠ 0 := by simp [mono]
  have n1 := Aw_ne 1 (by norm_num)
  have n2 := Aw_ne 2 (by norm_num)
  have n3 := Aw_ne 3 (by norm_num)
  have n4 := Aw_ne 4 (by norm_num)
  have n5 := Aw_ne 5 (by norm_num)
  have n6 := Aw_ne 6 (by norm_num)
  have n7 := Aw_ne 7 (by norm_num)
  have n8 := Aw_ne 8 (by norm_num)
  have n9 := Aw_ne 9 (by norm_num)
  have n10 := Aw_ne 10 (by norm_num)
  have n11 := Aw_ne 11 (by norm_num)
  have n12 := Aw_ne 12 (by norm_num)
  have n13 := Aw_ne 13 (by norm_num)
  have n14 := Aw_ne 14 (by norm_num)
  have n15 := Aw_ne 15 (by norm_num)
  have n16 := Aw_ne 16 (by norm_num)
  have n17 := Aw_ne 17 (by norm_num)
  have n18 := Aw_ne 18 (by norm_num)
  have n19 := Aw_ne 19 (by norm_num)
  have n20 := Aw_ne 20 (by norm_num)
  have n21 := Aw_ne 21 (by norm_num)
  have n22 := Aw_ne 22 (by norm_num)
  have n23 := Aw_ne 23 (by norm_num)
  have n24 := Aw_ne 24 (by norm_num)
  have n25 := Aw_ne 25 (by norm_num)
  have n26 := Aw_ne 26 (by norm_num)
  have n27 := Aw_ne 27 (by norm_num)
  have n28 := Aw_ne 28 (by norm_num)
  have n29 := Aw_ne 29 (by norm_num)
  have n30 := Aw_ne 30 (by norm_num)
  have n31 := Aw_ne 31 (by norm_num)
  have n32 := Aw_ne 32 (by norm_num)
  have n33 := Aw_ne 33 (by norm_num)
  have n34 := Aw_ne 34 (by norm_num)
  have n35 := Aw_ne 35 (by norm_num)
  have n36 := Aw_ne 36 (by norm_num)
  have n37 := Aw_ne 37 (by norm_num)
  have n38 := Aw_ne 38 (by norm_num)
  have n39 := Aw_ne 39 (by norm_num)
  have n40 := Aw_ne 40 (by norm_num)
  have n41 := Aw_ne 41 (by norm_num)
  have n42 := Aw_ne 42 (by norm_num)
  have n43 := Aw_ne 43 (by norm_num)
  have n44 := Aw_ne 44 (by norm_num)
  have n45 := Aw_ne 45 (by norm_num)
  have n46 := Aw_ne 46 (by norm_num)
  have n47 := Aw_ne 47 (by norm_num)
  have n48 := Aw_ne 48 (by norm_num)
  have n49 := Aw_ne 49 (by norm_num)
  have n50 := Aw_ne 50 (by norm_num)
  have n51 := Aw_ne 51 (by norm_num)
  have n52 := Aw_ne 52 (by norm_num)
  have n53 := Aw_ne 53 (by norm_num)
  have n54 := Aw_ne 54 (by norm_num)
  have n55 := Aw_ne 55 (by norm_num)
  have n56 := Aw_ne 56 (by norm_num)
  have n57 := Aw_ne 57 (by norm_num)
  have n58 := Aw_ne 58 (by norm_num)
  have n59 := Aw_ne 59 (by norm_num)
  have n60 := Aw_ne 60 (by norm_num)
  have n61 := Aw_ne 61 (by norm_num)
  have n62 := Aw_ne 62 (by norm_num)
  have n63 := Aw_ne 63 (by norm_num)
  have n64 := Aw_ne 64 (by norm_num)
  have n65 := Aw_ne 65 (by norm_num)
  have n66 := Aw_ne 66 (by norm_num)
  have n67 := Aw_ne 67 (by norm_num)
  have n68 := Aw_ne 68 (by norm_num)
  have n69 := Aw_ne 69 (by norm_num)
  have n70 := Aw_ne 70 (by norm_num)
  have n71 := Aw_ne 71 (by norm_num)
  have n72 := Aw_ne 72 (by norm_num)
  have n73 := Aw_ne 73 (by norm_num)
  have n74 := Aw_ne 74 (by norm_num)
  have n75 := Aw_ne 75 (by norm_num)
  have n76 := Aw_ne 76 (by norm_num)
  have n77 := Aw_ne 77 (by norm_num)
  have n78 := Aw_ne 78 (by norm_num)
  have n79 := Aw_ne 79 (by norm_num)
  have n80 := Aw_ne 80 (by norm_num)
  linear_combination (norm := (field_simp; ring)) (-1 : L) * ((1) / (Aw 2 * Aw 3 * Aw 4 * Aw 5 * Aw 6 * Aw 7 * Aw 8 * Aw 10 * Aw 12 * Aw 13 * Aw 14 * Aw 15 * Aw 16 * Aw 17 * Aw 18 * Aw 20 * Aw 22 * Aw 23 * Aw 24 * Aw 25 * Aw 26 * Aw 27 * Aw 28 * Aw 30 * Aw 32 * Aw 33 * Aw 34 * Aw 35 * Aw 36 * Aw 37 * Aw 38 * Aw 40 * Aw 42 * Aw 43 * Aw 44 * Aw 45 * Aw 46 * Aw 47 * Aw 48 * Aw 50 * Aw 52 * Aw 53 * Aw 54 * Aw 55 * Aw 56 * Aw 57 * Aw 58 * Aw 60 * Aw 62 * Aw 63 * Aw 64 * Aw 65 * Aw 66 * Aw 67 * Aw 68 * Aw 70 * Aw 72 * Aw 73 * Aw 74 * Aw 75 * Aw 76 * Aw 77 * Aw 78 * Aw 80)) * M_5_1p_2m + (-1 : L) * ((1) / (Aw 2 * Aw 3 * Aw 4 * Aw 5 * Aw 6 * Aw 7 * Aw 8 * Aw 10 * Aw 12 * Aw 13 * Aw 14 * Aw 15 * Aw 16 * Aw 17 * Aw 18 * Aw 20 * Aw 22 * Aw 23 * Aw 24 * Aw 25 * Aw 26 * Aw 27 * Aw 28 * Aw 30 * Aw 32 * Aw 33 * Aw 34 * Aw 35 * Aw 36 * Aw 37 * Aw 38 * Aw 40 * Aw 42 * Aw 43 * Aw 44 * Aw 45 * Aw 46 * Aw 47 * Aw 48 * Aw 50 * Aw 52 * Aw 53 * Aw 54 * Aw 55 * Aw 56 * Aw 57 * Aw 58 * Aw 60 * Aw 62 * Aw 63 * Aw 64 * Aw 65 * Aw 66 * Aw 67 * Aw 68 * Aw 70 * Aw 72 * Aw 73 * Aw 74 * Aw 75 * Aw 76 * Aw 77 * Aw 78 * Aw 80)) * M_5_1m_2p

end MockTheta5All.Theta
