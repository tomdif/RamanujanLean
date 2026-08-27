/-
# Quintuple product identity — completed coefficient collapse

This file closes the general `z`-coefficient gap left after the `N=0` collapse.
For fixed outer coefficient `q^k`, only bilateral indices `m` with `|m| ≤ k+1`
can contribute.  We therefore rewrite `zProj N (thetaA * thetaB)` as one finite
symmetric integer sum.  The affine changes of variable

* `N=3s`:     `m ↦ m+s`,
* `N=3s+2`:   `m ↦ -m+s+1`,
* `N=3s+1`:   `m ↦ -m+2s+1`

respectively reduce the sum to the `N=0` case, reduce it with a minus sign, or
pair it to zero.  This yields `thetaA*thetaB = qfac2InfL*quintTheta` and hence
the full formal quintuple product identity.  No analytic convergence and no `sorry`.
-/
import RamanujanTau.MockTheta5QuintCollapse4
import RamanujanTau.MockTheta5QuintCollapse5
import RamanujanTau.MockTheta5QuintBracket2
import Mathlib.Data.Int.Interval

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-- The nonnegative triangular exponent attached to a `thetaA` z-slice. -/
def quintTriExp (n : ℤ) : ℕ := (n * (n + 1) / 2).toNat

/-- Exponent of the bilateral convolution term indexed by `m`. -/
def quintConvExp (N m : ℤ) : ℕ := m.natAbs ^ 2 + quintTriExp (N - 2 * m)

/-- Sign of the bilateral convolution term. -/
def quintConvSign (N m : ℤ) : ℤ :=
  (-1 : ℤ) ^ N.natAbs * (-1 : ℤ) ^ m.natAbs

/-- Contribution of an integer convolution index to coefficient `q^k`. -/
def quintConvCoeff (N : ℤ) (k : ℕ) (m : ℤ) : ℤ :=
  if k = quintConvExp N m then quintConvSign N m else 0

/-- A symmetric integer interval is a zero term plus paired positive/negative terms. -/
lemma sum_Icc_neg_nat_nat (f : ℤ → ℤ) : ∀ B : ℕ,
    ∑ m ∈ Finset.Icc (-(B : ℤ)) B, f m
      = f 0 + ∑ a ∈ Finset.range B, (f ((a : ℤ) + 1) + f (-((a : ℤ) + 1))) := by
  intro B
  induction B with
  | zero => simp
  | succ B ih =>
      have hset : Finset.Icc (-((B + 1 : ℕ) : ℤ)) (B + 1 : ℤ)
          = insert (-((B + 1 : ℕ) : ℤ))
              (insert ((B + 1 : ℕ) : ℤ) (Finset.Icc (-(B : ℤ)) B)) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        constructor
        · intro hx
          by_cases hleft : x = -((B + 1 : ℕ) : ℤ)
          · exact Or.inl hleft
          by_cases hright : x = ((B + 1 : ℕ) : ℤ)
          · exact Or.inr (Or.inl hright)
          · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
        · rintro (rfl | rfl | hx) <;> omega
      have hleft : -((B + 1 : ℕ) : ℤ) ∉
          insert ((B + 1 : ℕ) : ℤ) (Finset.Icc (-(B : ℤ)) B) := by
        simp only [Finset.mem_insert, Finset.mem_Icc, not_or]
        constructor
        · omega
        · omega
      have hright : ((B + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(B : ℤ)) B := by
        simp only [Finset.mem_Icc, not_and_or]
        exact Or.inr (by omega)
      norm_num [Nat.cast_add, Nat.cast_one] at hset ⊢
      have hleft' : -1 + -(B : ℤ) ∉
          insert ((B : ℤ) + 1) (Finset.Icc (-(B : ℤ)) B) := by simpa using hleft
      have hright' : (B : ℤ) + 1 ∉ Finset.Icc (-(B : ℤ)) B := by simpa using hright
      rw [hset, Finset.sum_insert hleft', Finset.sum_insert hright', ih,
        Finset.sum_range_succ]
      ring

private lemma coeff_C_mul_X_pow (s : ℤ) (e k : ℕ) :
    coeff k (PowerSeries.C s * X ^ e) = if e = k then s else 0 := by
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  split_ifs <;> simp_all

private lemma quintConvCoeff_zero_index (N : ℤ) (k : ℕ) :
    quintConvCoeff N k 0 = coeff k (zProj N thetaA) := by
  rw [zProj_thetaA, coeff_C_mul_X_pow]
  simp [quintConvCoeff, quintConvExp, quintConvSign, quintTriExp, eq_comm]

private lemma natAbs_pos_index (a : ℕ) : ((a : ℤ) + 1).natAbs = a + 1 := by omega

private lemma natAbs_neg_index (a : ℕ) : (-((a : ℤ) + 1)).natAbs = a + 1 := by omega

private lemma quintConvExp_pos (N : ℤ) (a : ℕ) :
    quintConvExp N ((a : ℤ) + 1)
      = (a + 1) ^ 2
        + ((N - 2 * ((a : ℤ) + 1)) * (N - 2 * ((a : ℤ) + 1) + 1) / 2).toNat := by
  simp [quintConvExp, quintTriExp, natAbs_pos_index]

private lemma quintConvExp_neg (N : ℤ) (a : ℕ) :
    quintConvExp N (-((a : ℤ) + 1))
      = (a + 1) ^ 2
        + ((N + 2 * ((a : ℤ) + 1)) * (N + 2 * ((a : ℤ) + 1) + 1) / 2).toNat := by
  rw [quintConvExp, natAbs_neg_index, quintTriExp]
  congr 2

private lemma coeff_per_term_eq_conv (N : ℤ) (k a : ℕ) :
    coeff k (zProj N (thetaA * thetaBTerm a))
      = quintConvCoeff N k ((a : ℤ) + 1) + quintConvCoeff N k (-((a : ℤ) + 1)) := by
  rw [per_term_general, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    map_add, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
  simp only [quintConvCoeff, quintConvSign, quintConvExp_pos, quintConvExp_neg,
    natAbs_pos_index, natAbs_neg_index]
  split_ifs <;> ring

/-- Exact finite bilateral coefficient formula for the theta convolution. -/
lemma coeff_zProj_thetaA_thetaB_eq_conv (N : ℤ) (k : ℕ) :
    coeff k (zProj N (thetaA * thetaB))
      = ∑ m ∈ Finset.Icc (-((k + 1 : ℕ) : ℤ)) (k + 1 : ℤ), quintConvCoeff N k m := by
  rw [coeff_zProj_thetaA_thetaB, map_add, map_sum]
  have hkcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by omega
  rw [← hkcast, sum_Icc_neg_nat_nat]
  simp only [coeff_per_term_eq_conv]
  rw [← quintConvCoeff_zero_index]

/-! ### Quadratic and sign changes of variable -/

/-- Integer-valued version of `quintConvExp`. -/
def quintConvExpZ (N m : ℤ) : ℤ :=
  m ^ 2 + (N - 2 * m) * (N - 2 * m + 1) / 2

private lemma consecutive_even (n : ℤ) : Even (n * (n + 1)) := by
  rcases Int.even_or_odd n with hn | hn
  · exact hn.mul_right (n + 1)
  · exact hn.add_one.mul_left n

private lemma even_s_three_s_add_one (s : ℤ) : Even (s * (3 * s + 1)) := by
  rcases Int.even_or_odd s with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine ⟨a * (6 * a + 1), ?_⟩
    rw [ha]
    ring
  · refine ⟨(2 * a + 1) * (3 * a + 2), ?_⟩
    rw [ha]
    ring

private lemma even_succ_three_s_add_two (s : ℤ) : Even ((s + 1) * (3 * s + 2)) := by
  rcases Int.even_or_odd s with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine ⟨(2 * a + 1) * (3 * a + 1), ?_⟩
    rw [ha]
    ring
  · refine ⟨(a + 1) * (6 * a + 5), ?_⟩
    rw [ha]
    ring

private lemma twice_triangular (n : ℤ) :
    2 * (n * (n + 1) / 2) = n * (n + 1) :=
  Int.two_mul_ediv_two_of_even (consecutive_even n)

private lemma triangular_nonneg (n : ℤ) : 0 ≤ n * (n + 1) / 2 := by
  have hprod : 0 ≤ n * (n + 1) := by
    by_cases hn : 0 ≤ n
    · exact mul_nonneg hn (by omega)
    · have hn1 : n + 1 ≤ 0 := by omega
      exact mul_nonneg_of_nonpos_of_nonpos (by omega) hn1
  exact Int.ediv_nonneg hprod (by norm_num)

private lemma quintConvExpZ_nonneg (N m : ℤ) : 0 ≤ quintConvExpZ N m := by
  exact add_nonneg (sq_nonneg m) (triangular_nonneg (N - 2 * m))

/-- The natural exponent is exactly the nonnegative integer quadratic exponent. -/
lemma quintConvExp_eq_toNat (N m : ℤ) :
    quintConvExp N m = (quintConvExpZ N m).toNat := by
  apply Nat.cast_injective (R := ℤ)
  have hz : (((quintConvExpZ N m).toNat : ℕ) : ℤ) = quintConvExpZ N m :=
    Int.toNat_of_nonneg (quintConvExpZ_nonneg N m)
  rw [hz, quintConvExp, quintTriExp]
  push_cast
  rw [Int.toNat_of_nonneg (triangular_nonneg (N - 2 * m))]
  rw [show quintConvExpZ N m = m ^ 2 + (N - 2 * m) * (N - 2 * m + 1) / 2 from rfl]
  simp [sq_abs]

private lemma half_even {x : ℤ} (hx : Even x) : 2 * (x / 2) = x :=
  Int.two_mul_ediv_two_of_even hx

/-- Quadratic reindexing for z-degree `3s`. -/
lemma quintConvExpZ_three (s m : ℤ) :
    quintConvExpZ (3 * s) (m + s)
      = quintConvExpZ 0 m + s * (3 * s + 1) / 2 := by
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
  simp only [quintConvExpZ]
  have hleft := twice_triangular (3 * s - 2 * (m + s))
  have hzero := twice_triangular (0 - 2 * m)
  have hshift := half_even (even_s_three_s_add_one s)
  linear_combination hleft - hzero - hshift

/-- Quadratic reindexing for z-degree `3s+2`. -/
lemma quintConvExpZ_three_add_two (s m : ℤ) :
    quintConvExpZ (3 * s + 2) (-m + s + 1)
      = quintConvExpZ 0 m + (s + 1) * (3 * s + 2) / 2 := by
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
  simp only [quintConvExpZ]
  have hleft := twice_triangular (3 * s + 2 - 2 * (-m + s + 1))
  have hzero := twice_triangular (0 - 2 * m)
  have hshift := half_even (even_succ_three_s_add_two s)
  linear_combination hleft - hzero - hshift

/-- The `3s+1` involution preserves the quadratic exponent. -/
lemma quintConvExpZ_three_add_one (s m : ℤ) :
    quintConvExpZ (3 * s + 1) (-m + 2 * s + 1)
      = quintConvExpZ (3 * s + 1) m := by
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
  simp only [quintConvExpZ]
  have hleft := twice_triangular (3 * s + 1 - 2 * (-m + 2 * s + 1))
  have hright := twice_triangular (3 * s + 1 - 2 * m)
  linear_combination hleft - hright

private lemma neg_one_natAbs_eq_of_even_sub (a b : ℤ) (h : Even (a - b)) :
    (-1 : ℤ) ^ a.natAbs = (-1 : ℤ) ^ b.natAbs := by
  rcases Int.even_or_odd a with ha | ha <;> rcases Int.even_or_odd b with hb | hb
  · rw [Even.neg_one_pow (Int.natAbs_even.mpr ha),
      Even.neg_one_pow (Int.natAbs_even.mpr hb)]
  · obtain ⟨x, hx⟩ := h
    obtain ⟨y, hy⟩ := ha
    obtain ⟨z, hz⟩ := hb
    omega
  · obtain ⟨x, hx⟩ := h
    obtain ⟨y, hy⟩ := ha
    obtain ⟨z, hz⟩ := hb
    omega
  · rw [Odd.neg_one_pow (Int.natAbs_odd.mpr ha),
      Odd.neg_one_pow (Int.natAbs_odd.mpr hb)]

private lemma neg_one_natAbs_eq_neg_of_odd_sub (a b : ℤ) (h : Odd (a - b)) :
    (-1 : ℤ) ^ a.natAbs = -((-1 : ℤ) ^ b.natAbs) := by
  rcases Int.even_or_odd a with ha | ha <;> rcases Int.even_or_odd b with hb | hb
  · obtain ⟨x, hx⟩ := h
    obtain ⟨y, hy⟩ := ha
    obtain ⟨z, hz⟩ := hb
    omega
  · rw [Even.neg_one_pow (Int.natAbs_even.mpr ha),
      Odd.neg_one_pow (Int.natAbs_odd.mpr hb)]
    norm_num
  · rw [Odd.neg_one_pow (Int.natAbs_odd.mpr ha),
      Even.neg_one_pow (Int.natAbs_even.mpr hb)]
  · obtain ⟨x, hx⟩ := h
    obtain ⟨y, hy⟩ := ha
    obtain ⟨z, hz⟩ := hb
    omega

/-- The convolution sign only depends on the parity of `N+m`. -/
lemma quintConvSign_eq (N m : ℤ) :
    quintConvSign N m = (-1 : ℤ) ^ (N + m).natAbs := by
  rcases Int.even_or_odd N with hN | hN <;> rcases Int.even_or_odd m with hm | hm
  · rw [quintConvSign, Even.neg_one_pow (Int.natAbs_even.mpr hN),
      Even.neg_one_pow (Int.natAbs_even.mpr hm),
      Even.neg_one_pow (Int.natAbs_even.mpr (hN.add hm))]
    norm_num
  · rw [quintConvSign, Even.neg_one_pow (Int.natAbs_even.mpr hN),
      Odd.neg_one_pow (Int.natAbs_odd.mpr hm),
      Odd.neg_one_pow (Int.natAbs_odd.mpr (hN.add_odd hm))]
    norm_num
  · rw [quintConvSign, Odd.neg_one_pow (Int.natAbs_odd.mpr hN),
      Even.neg_one_pow (Int.natAbs_even.mpr hm),
      Odd.neg_one_pow (Int.natAbs_odd.mpr (hN.add_even hm))]
    norm_num
  · rw [quintConvSign, Odd.neg_one_pow (Int.natAbs_odd.mpr hN),
      Odd.neg_one_pow (Int.natAbs_odd.mpr hm),
      Even.neg_one_pow (Int.natAbs_even.mpr (hN.add_odd hm))]
    norm_num

lemma quintConvSign_three (s m : ℤ) :
    quintConvSign (3 * s) (m + s) = quintConvSign 0 m := by
  rw [quintConvSign_eq, quintConvSign_eq]
  apply neg_one_natAbs_eq_of_even_sub
  exact ⟨2 * s, by ring⟩

lemma quintConvSign_three_add_two (s m : ℤ) :
    quintConvSign (3 * s + 2) (-m + s + 1) = -quintConvSign 0 m := by
  rw [quintConvSign_eq, quintConvSign_eq]
  apply neg_one_natAbs_eq_neg_of_odd_sub
  exact ⟨2 * s + 1 - m, by ring⟩

lemma quintConvSign_three_add_one (s m : ℤ) :
    quintConvSign (3 * s + 1) (-m + 2 * s + 1)
      = -quintConvSign (3 * s + 1) m := by
  rw [quintConvSign_eq, quintConvSign_eq]
  apply neg_one_natAbs_eq_neg_of_odd_sub
  exact ⟨s - m, by ring⟩

/-! ### Finite support and termwise reindexing -/

private lemma generalizedPentagonal_nonneg (s : ℤ) : 0 ≤ s * (3 * s + 1) / 2 := by
  have hp : 0 ≤ s * (3 * s + 1) := by
    by_cases hs : 0 ≤ s
    · exact mul_nonneg hs (by nlinarith)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by nlinarith)
  exact Int.ediv_nonneg hp (by norm_num)

private lemma generalizedPentagonal2_nonneg (s : ℤ) :
    0 ≤ (s + 1) * (3 * s + 2) / 2 := by
  have hp : 0 ≤ (s + 1) * (3 * s + 2) := by
    by_cases hs : 0 ≤ s
    · exact mul_nonneg (by omega) (by nlinarith)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by nlinarith)
  exact Int.ediv_nonneg hp (by norm_num)

def quintShiftExp (s : ℤ) : ℕ := (s * (3 * s + 1) / 2).toNat
def quintShiftExp2 (s : ℤ) : ℕ := ((s + 1) * (3 * s + 2) / 2).toNat

lemma quintConvExp_three (s m : ℤ) :
    quintConvExp (3 * s) (m + s) = quintConvExp 0 m + quintShiftExp s := by
  apply Nat.cast_injective (R := ℤ)
  simp only [Nat.cast_add, quintShiftExp]
  rw [quintConvExp_eq_toNat, quintConvExp_eq_toNat,
    Int.toNat_of_nonneg (quintConvExpZ_nonneg (3 * s) (m + s)),
    Int.toNat_of_nonneg (quintConvExpZ_nonneg 0 m),
    Int.toNat_of_nonneg (generalizedPentagonal_nonneg s), quintConvExpZ_three]

lemma quintConvExp_three_add_two (s m : ℤ) :
    quintConvExp (3 * s + 2) (-m + s + 1) = quintConvExp 0 m + quintShiftExp2 s := by
  apply Nat.cast_injective (R := ℤ)
  simp only [Nat.cast_add, quintShiftExp2]
  rw [quintConvExp_eq_toNat, quintConvExp_eq_toNat,
    Int.toNat_of_nonneg (quintConvExpZ_nonneg (3 * s + 2) (-m + s + 1)),
    Int.toNat_of_nonneg (quintConvExpZ_nonneg 0 m),
    Int.toNat_of_nonneg (generalizedPentagonal2_nonneg s), quintConvExpZ_three_add_two]

lemma quintConvExp_three_add_one (s m : ℤ) :
    quintConvExp (3 * s + 1) (-m + 2 * s + 1) = quintConvExp (3 * s + 1) m := by
  rw [quintConvExp_eq_toNat, quintConvExp_eq_toNat, quintConvExpZ_three_add_one]

lemma quintConvCoeff_zero_of_natAbs_gt (N : ℤ) (k : ℕ) (m : ℤ)
    (hm : k < m.natAbs) : quintConvCoeff N k m = 0 := by
  rw [quintConvCoeff]
  split_ifs with he
  · exfalso
    have hsq : m.natAbs ≤ m.natAbs ^ 2 := by nlinarith
    have hle : m.natAbs ^ 2 ≤ quintConvExp N m := by
      simp only [quintConvExp]
      omega
    omega
  · rfl

private lemma natAbs_gt_of_outside (k : ℕ) (m : ℤ)
    (hm : m < -((k + 1 : ℕ) : ℤ) ∨ ((k + 1 : ℕ) : ℤ) < m) :
    k < m.natAbs := by omega

/-- The standard symmetric support interval can be enlarged arbitrarily. -/
lemma sum_quintConvCoeff_eq_Icc (N : ℤ) (k : ℕ) (L U : ℤ)
    (hL : L ≤ -((k + 1 : ℕ) : ℤ)) (hU : ((k + 1 : ℕ) : ℤ) ≤ U) :
    ∑ m ∈ Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ), quintConvCoeff N k m
      = ∑ m ∈ Finset.Icc L U, quintConvCoeff N k m := by
  apply Finset.sum_subset
  · intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    exact ⟨hL.trans hm.1, hm.2.trans hU⟩
  · intro m hmBig hmSmall
    simp only [Finset.mem_Icc] at hmBig hmSmall
    apply quintConvCoeff_zero_of_natAbs_gt
    apply natAbs_gt_of_outside
    omega

lemma quintConvCoeff_three_of_le (s m : ℤ) (k : ℕ) (hk : quintShiftExp s ≤ k) :
    quintConvCoeff (3 * s) k (m + s)
      = quintConvCoeff 0 (k - quintShiftExp s) m := by
  rw [quintConvCoeff, quintConvCoeff, quintConvExp_three, quintConvSign_three]
  split_ifs <;> omega

lemma quintConvCoeff_three_add_two_of_le (s m : ℤ) (k : ℕ) (hk : quintShiftExp2 s ≤ k) :
    quintConvCoeff (3 * s + 2) k (-m + s + 1)
      = -quintConvCoeff 0 (k - quintShiftExp2 s) m := by
  rw [quintConvCoeff, quintConvCoeff, quintConvExp_three_add_two,
    quintConvSign_three_add_two]
  split_ifs <;> omega

lemma quintConvCoeff_three_add_one_pair (s m : ℤ) (k : ℕ) :
    quintConvCoeff (3 * s + 1) k (-m + 2 * s + 1)
      = -quintConvCoeff (3 * s + 1) k m := by
  rw [quintConvCoeff, quintConvCoeff, quintConvExp_three_add_one,
    quintConvSign_three_add_one]
  split_ifs <;> ring

private lemma quintConvCoeff_three_zero_of_lt (s x : ℤ) (k : ℕ)
    (hk : k < quintShiftExp s) : quintConvCoeff (3 * s) k x = 0 := by
  have he := quintConvExp_three s (x - s)
  rw [show x - s + s = x by ring] at he
  rw [quintConvCoeff]
  split_ifs with h
  · omega
  · rfl

private lemma quintConvCoeff_three_add_two_zero_of_lt (s x : ℤ) (k : ℕ)
    (hk : k < quintShiftExp2 s) : quintConvCoeff (3 * s + 2) k x = 0 := by
  have he := quintConvExp_three_add_two s (-x + s + 1)
  rw [show -(-x + s + 1) + s + 1 = x by ring] at he
  rw [quintConvCoeff]
  split_ifs with h
  · omega
  · rfl

/-! ### Every z-slice of the theta convolution -/

/-- The `z^(3s)` slice is a shifted copy of the `N=0` pentagonal collapse. -/
theorem zProj_three_thetaA_thetaB (s : ℤ) :
    zProj (3 * s) (thetaA * thetaB) = X ^ (quintShiftExp s) * qfac2Inf := by
  ext k
  rw [coeff_zProj_thetaA_thetaB_eq_conv, PowerSeries.coeff_X_pow_mul']
  by_cases hk : quintShiftExp s ≤ k
  · rw [if_pos hk, ← zProj_zero_thetaA_thetaB,
      coeff_zProj_thetaA_thetaB_eq_conv]
    let C : ℤ := k + 1 + s.natAbs
    have hCL : -C ≤ -((k + 1 : ℕ) : ℤ) := by
      dsimp [C]
      omega
    have hCU : ((k + 1 : ℕ) : ℤ) ≤ C := by
      dsimp [C]
      omega
    have holdL : -C + s ≤ -((k + 1 : ℕ) : ℤ) := by
      dsimp [C]
      omega
    have holdU : ((k + 1 : ℕ) : ℤ) ≤ C + s := by
      dsimp [C]
      omega
    have hbaseL : -C ≤ -(((k - quintShiftExp s) + 1 : ℕ) : ℤ) := by
      dsimp [C]
      omega
    have hbaseU : ((((k - quintShiftExp s) + 1 : ℕ) : ℤ)) ≤ C := by
      dsimp [C]
      omega
    rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega,
      show ((k - quintShiftExp s : ℕ) : ℤ) + 1
        = (((k - quintShiftExp s) + 1 : ℕ) : ℤ) by omega]
    rw [sum_quintConvCoeff_eq_Icc (3 * s) k (-C + s) (C + s) holdL holdU,
      sum_quintConvCoeff_eq_Icc 0 (k - quintShiftExp s) (-C) C hbaseL hbaseU]
    symm
    refine Finset.sum_nbij' (fun m : ℤ => m + s) (fun x : ℤ => x - s) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    · intro m _
      ring
    · intro x _
      ring
    · intro m _
      exact (quintConvCoeff_three_of_le s m k hk).symm
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro x _
    exact quintConvCoeff_three_zero_of_lt s x k (by omega)

/-- The `z^(3s+2)` slice is the negative shifted `N=0` collapse. -/
theorem zProj_three_add_two_thetaA_thetaB (s : ℤ) :
    zProj (3 * s + 2) (thetaA * thetaB) = -(X ^ (quintShiftExp2 s) * qfac2Inf) := by
  ext k
  rw [coeff_zProj_thetaA_thetaB_eq_conv, map_neg,
    PowerSeries.coeff_X_pow_mul']
  by_cases hk : quintShiftExp2 s ≤ k
  · rw [if_pos hk, ← zProj_zero_thetaA_thetaB,
      coeff_zProj_thetaA_thetaB_eq_conv]
    let C : ℤ := k + 1 + s.natAbs + 1
    have holdL : -C + s + 1 ≤ -((k + 1 : ℕ) : ℤ) := by
      dsimp [C]
      omega
    have holdU : ((k + 1 : ℕ) : ℤ) ≤ C + s + 1 := by
      dsimp [C]
      omega
    have hbaseL : -C ≤ -(((k - quintShiftExp2 s) + 1 : ℕ) : ℤ) := by
      dsimp [C]
      omega
    have hbaseU : ((((k - quintShiftExp2 s) + 1 : ℕ) : ℤ)) ≤ C := by
      dsimp [C]
      omega
    rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega,
      show ((k - quintShiftExp2 s : ℕ) : ℤ) + 1
        = (((k - quintShiftExp2 s) + 1 : ℕ) : ℤ) by omega]
    rw [sum_quintConvCoeff_eq_Icc (3 * s + 2) k (-C + s + 1) (C + s + 1)
        holdL holdU,
      sum_quintConvCoeff_eq_Icc 0 (k - quintShiftExp2 s) (-C) C hbaseL hbaseU]
    rw [← Finset.sum_neg_distrib]
    symm
    refine Finset.sum_nbij' (fun m : ℤ => -m + s + 1) (fun x : ℤ => -x + s + 1)
      ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    · intro m _
      ring
    · intro x _
      ring
    · intro m _
      exact (quintConvCoeff_three_add_two_of_le s m k hk).symm
  · rw [if_neg hk, neg_zero]
    apply Finset.sum_eq_zero
    intro x _
    exact quintConvCoeff_three_add_two_zero_of_lt s x k (by omega)

/-- The missing residue family `z^(3s+1)` cancels by a fixed-point-free affine involution. -/
theorem zProj_three_add_one_thetaA_thetaB (s : ℤ) :
    zProj (3 * s + 1) (thetaA * thetaB) = 0 := by
  ext k
  rw [coeff_zProj_thetaA_thetaB_eq_conv, map_zero]
  let C : ℤ := k + 1 + (2 * s + 1).natAbs
  have hL : -C ≤ -((k + 1 : ℕ) : ℤ) := by
    dsimp [C]
    omega
  have hU : ((k + 1 : ℕ) : ℤ) ≤ 2 * s + 1 + C := by
    dsimp [C]
    omega
  rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega]
  rw [sum_quintConvCoeff_eq_Icc (3 * s + 1) k (-C) (2 * s + 1 + C) hL hU]
  let S := ∑ m ∈ Finset.Icc (-C) (2 * s + 1 + C), quintConvCoeff (3 * s + 1) k m
  have hneg : S = -S := by
    dsimp [S]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_nbij' (fun m : ℤ => -m + 2 * s + 1)
      (fun x : ℤ => -x + 2 * s + 1) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    · intro m _
      ring
    · intro x _
      ring
    · intro m _
      rw [quintConvCoeff_three_add_one_pair]
      ring
  dsimp [S] at hneg ⊢
  omega

/-! ### Matching slices of `quintTheta` -/

private lemma quintShiftExp_natCast (a : ℕ) :
    quintShiftExp (a : ℤ) = a * (3 * a + 1) / 2 := by
  rw [quintShiftExp]
  have hnum : (a : ℤ) * (3 * (a : ℤ) + 1)
      = ((a * (3 * a + 1) : ℕ) : ℤ) := by push_cast; ring
  rw [hnum]
  have hdiv : ((a * (3 * a + 1) : ℕ) : ℤ) / 2
      = (((a * (3 * a + 1) / 2 : ℕ)) : ℤ) :=
    (Int.natCast_div (a * (3 * a + 1)) 2).symm
  rw [hdiv, Int.toNat_natCast]

private lemma quintShiftExp_negSucc (a : ℕ) :
    quintShiftExp (-((a : ℤ) + 1)) = (a + 1) * (3 * a + 2) / 2 := by
  rw [quintShiftExp]
  have heq : (-((a : ℤ) + 1)) * (3 * (-((a : ℤ) + 1)) + 1) / 2
      = (((a + 1) * (3 * a + 2) / 2 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [heq, Int.toNat_natCast]

private lemma quintShiftExp2_natCast (a : ℕ) :
    quintShiftExp2 (a : ℤ) = (a + 1) * (3 * a + 2) / 2 := by
  rw [quintShiftExp2]
  have hnum : ((a : ℤ) + 1) * (3 * (a : ℤ) + 2)
      = (((a + 1) * (3 * a + 2) : ℕ) : ℤ) := by push_cast; ring
  rw [hnum]
  have hdiv : ((((a + 1) * (3 * a + 2) : ℕ) : ℤ)) / 2
      = (((((a + 1) * (3 * a + 2)) / 2 : ℕ)) : ℤ) :=
    (Int.natCast_div ((a + 1) * (3 * a + 2)) 2).symm
  rw [hdiv, Int.toNat_natCast]

private lemma quintShiftExp2_negSuccSucc (a : ℕ) :
    quintShiftExp2 (-((a : ℤ) + 2)) = (a + 1) * (3 * a + 4) / 2 := by
  rw [quintShiftExp2]
  have heq : (-((a : ℤ) + 2) + 1) * (3 * (-((a : ℤ) + 2)) + 2) / 2
      = (((a + 1) * (3 * a + 4) / 2 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [heq, Int.toNat_natCast]

/-- Projection of the quintuple RHS in degrees divisible by three. -/
theorem zProj_three_quintTheta (s : ℤ) :
    zProj (3 * s) quintTheta = X ^ (quintShiftExp s) := by
  ext k
  rw [coeff_zProj, coeff_quintTheta (show k + 1 ≤ k + 1 + s.natAbs by omega),
    ← coeff_zProj, quintFiniteP, zProj_add, zProj_quintBase, zProj_sum]
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · obtain ⟨a, ha⟩ : ∃ a : ℕ, s = -((a : ℤ) + 1) := ⟨s.natAbs - 1, by omega⟩
    subst s
    rw [if_neg (by omega), if_neg (by omega), zero_sub, neg_zero,
      Finset.sum_eq_single a]
    · rw [zProj_quintTermP, if_pos (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
      simp only [sub_zero, zero_sub, add_zero, zero_add, neg_zero]
      rw [quintShiftExp_negSucc]
    · intro b hb hba
      rw [zProj_quintTermP, if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
      simp
    · intro haout
      exact (haout (Finset.mem_range.mpr (by omega))).elim
  · rw [if_pos (by norm_num), if_neg (by norm_num), sub_zero,
      Finset.sum_eq_zero (fun a _ => by
        rw [zProj_quintTermP, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
        simp),
      add_zero, quintShiftExp]
    norm_num
  · lift s to ℕ using hs.le with a
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, a = b + 1 := ⟨a - 1, by omega⟩
    rw [if_neg (by omega), if_neg (by omega), zero_sub, neg_zero,
      Finset.sum_eq_single b]
    · rw [zProj_quintTermP, if_neg (by omega), if_neg (by omega),
        if_pos (by omega), if_neg (by omega)]
      simp only [sub_zero, zero_sub, add_zero, zero_add, neg_zero]
      rw [quintShiftExp_natCast]
      congr 3
    · intro d hd hdb
      rw [zProj_quintTermP, if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
      simp
    · intro hbout
      exact (hbout (Finset.mem_range.mpr (by omega))).elim

/-- Projection of the quintuple RHS in degrees congruent to two modulo three. -/
theorem zProj_three_add_two_quintTheta (s : ℤ) :
    zProj (3 * s + 2) quintTheta = -(X ^ (quintShiftExp2 s)) := by
  ext k
  rw [coeff_zProj, coeff_quintTheta (show k + 1 ≤ k + 2 + s.natAbs by omega),
    ← coeff_zProj, quintFiniteP, zProj_add, zProj_quintBase, zProj_sum]
  rcases lt_trichotomy s (-1) with hs | hs | hs
  · obtain ⟨a, ha⟩ : ∃ a : ℕ, s = -((a : ℤ) + 2) := ⟨s.natAbs - 2, by omega⟩
    subst s
    rw [if_neg (by omega), if_neg (by omega), zero_sub, neg_zero,
      Finset.sum_eq_single a]
    · rw [zProj_quintTermP, if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos (by omega)]
      simp only [sub_zero, zero_sub, add_zero, zero_add, neg_zero, map_neg]
      rw [quintShiftExp2_negSuccSucc]
    · intro b hb hba
      rw [zProj_quintTermP, if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
      simp
    · intro haout
      exact (haout (Finset.mem_range.mpr (by omega))).elim
  · have hs' : s = -1 := by omega
    subst s
    rw [if_neg (by norm_num), if_pos (by norm_num), zero_sub,
      Finset.sum_eq_zero (fun a _ => by
        rw [zProj_quintTermP, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
        simp),
      add_zero, quintShiftExp2]
    norm_num
  · have hs0 : 0 ≤ s := by omega
    lift s to ℕ using hs0 with a
    rw [if_neg (by omega), if_neg (by omega), zero_sub, neg_zero,
      Finset.sum_eq_single a]
    · rw [zProj_quintTermP, if_neg (by omega), if_pos (by omega),
        if_neg (by omega), if_neg (by omega)]
      simp only [sub_zero, zero_sub, add_zero, zero_add, neg_zero, map_neg]
      rw [quintShiftExp2_natCast]
    · intro b hb hba
      rw [zProj_quintTermP, if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
      simp
    · intro haout
      exact (haout (Finset.mem_range.mpr (by omega))).elim

/-- There are no quintuple RHS monomials in z-degrees congruent to one modulo three. -/
theorem zProj_three_add_one_quintTheta (s : ℤ) :
    zProj (3 * s + 1) quintTheta = 0 := by
  ext k
  rw [coeff_zProj, coeff_quintTheta (le_refl (k + 1)), ← coeff_zProj,
    quintFiniteP, zProj_add, zProj_quintBase, zProj_sum,
    if_neg (by omega), if_neg (by omega), zero_sub,
    Finset.sum_eq_zero (fun a _ => by
      rw [zProj_quintTermP, if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
      simp),
    add_zero, neg_zero, map_zero]

/-! ### The completed formal quintuple product identity -/

/-- Every integer lies in exactly one of the three affine residue families used above. -/
private lemma int_eq_three_mul_or_add_one_or_add_two (N : ℤ) :
    (∃ s : ℤ, N = 3 * s) ∨
      (∃ s : ℤ, N = 3 * s + 1) ∨
        (∃ s : ℤ, N = 3 * s + 2) := by
  have hnonneg : 0 ≤ N % 3 := Int.emod_nonneg N (by norm_num)
  have hlt : N % 3 < 3 := Int.emod_lt_of_pos N (by norm_num)
  have hsplit := Int.ediv_mul_add_emod N 3
  interval_cases hrem : N % 3
  · exact Or.inl ⟨N / 3, by omega⟩
  · exact Or.inr (Or.inl ⟨N / 3, by omega⟩)
  · exact Or.inr (Or.inr ⟨N / 3, by omega⟩)

/-- **Theta form of the quintuple product identity.**  The preceding three
coefficient computations cover every Laurent degree and therefore determine the
whole bivariate formal power series. -/
theorem thetaA_mul_thetaB_eq_qfac2InfL_mul_quintTheta :
    thetaA * thetaB = qfac2InfL * quintTheta := by
  refine zProj_ext fun N => ?_
  rcases int_eq_three_mul_or_add_one_or_add_two N with
    ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [zProj_three_thetaA_thetaB, zProj_qfac2InfL_mul,
      zProj_three_quintTheta]
    ring
  · rw [zProj_three_add_one_thetaA_thetaB, zProj_qfac2InfL_mul,
      zProj_three_add_one_quintTheta, mul_zero]
  · rw [zProj_three_add_two_thetaA_thetaB, zProj_qfac2InfL_mul,
      zProj_three_add_two_quintTheta]
    ring

/-- **The formal quintuple product identity.**  This is the five-factor
product itself: the two Jacobi brackets supply its factors, and the common
unit `(q²;q²)_∞` cancels from the theta identity. -/
theorem formal_quintuple_product_identity :
    qfacInfL * qzProdAInf * (PowerSeries.map invertHom qzProdBInf) *
        jtp2ProdInf * (PowerSeries.map invertHom jtp2ProdInf) = quintTheta := by
  apply mul_left_cancel₀ isUnit_qfac2InfL.ne_zero
  calc
    qfac2InfL *
        (qfacInfL * qzProdAInf * (PowerSeries.map invertHom qzProdBInf) *
          jtp2ProdInf * (PowerSeries.map invertHom jtp2ProdInf))
        = (qfacInfL * qzProdAInf * (PowerSeries.map invertHom qzProdBInf)) *
            (qfac2InfL * jtp2ProdInf *
              (PowerSeries.map invertHom jtp2ProdInf)) := by ring
    _ = thetaA * thetaB := by rw [bracket1, bracket2]
    _ = qfac2InfL * quintTheta :=
      thetaA_mul_thetaB_eq_qfac2InfL_mul_quintTheta

end MockTheta5.JTP
