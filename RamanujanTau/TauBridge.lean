/-
# The computable `τ` agrees with `[qⁿ] q∏(1−qᵏ)²⁴`

`RamanujanTau.tau` is defined on coefficient lists (computable, `native_decide`-friendly). This file gives
the lists their power-series meaning (`toPS`). It shows that every list operation is the corresponding ring
operation, and that truncation agrees modulo `X^{d+1}`. Hence

  **`tau_eq_tauPS`:**  `RamanujanTau.tau n = [qⁿ] q ∏_{k≥1} (1 − qᵏ)²⁴`,

so the congruences of `TauCongruences` hold for the computable `τ`.
-/
import RamanujanTau.Basic
import RamanujanTau.TauCongruences
import RamanujanTau.FourSquaresLimit

set_option autoImplicit false

namespace RamanujanTau
open PowerSeries

/-- the power series with coefficient list `l`. -/
noncomputable def toPS (l : List ℤ) : PowerSeries ℤ := mk (coeffList l)

lemma toPS_nil : toPS [] = 0 := by ext n; simp [toPS, coeffList]

lemma toPS_cons (a : ℤ) (l : List ℤ) : toPS (a :: l) = C a + X * toPS l := by
  ext n
  rcases n with _ | n
  · simp [toPS, coeffList]
  · rw [map_add, coeff_C, if_neg (by omega), zero_add, coeff_succ_X_mul, toPS, toPS, coeff_mk, coeff_mk]; rfl

lemma toPS_addList : ∀ p q : List ℤ, toPS (addList p q) = toPS p + toPS q
  | [], q => by rw [addList, toPS_nil, zero_add]
  | a :: as, [] => by simp [addList, toPS_nil]
  | a :: as, b :: bs => by
    rw [addList, toPS_cons, toPS_cons, toPS_cons, toPS_addList as bs, map_add]; ring

lemma toPS_scaleList (c : ℤ) : ∀ p : List ℤ, toPS (scaleList c p) = C c * toPS p
  | [] => by rw [scaleList, toPS_nil, mul_zero]
  | a :: as => by rw [scaleList, toPS_cons, toPS_cons, toPS_scaleList c as, map_mul]; ring

lemma toPS_mulList : ∀ p q : List ℤ, toPS (mulList p q) = toPS p * toPS q
  | [], q => by rw [mulList, toPS_nil, zero_mul]
  | a :: as, q => by
    rw [mulList, toPS_addList, toPS_scaleList, toPS_cons, toPS_cons, toPS_mulList as q, map_zero, zero_add]; ring

lemma toPS_shiftList_one (p : List ℤ) : toPS (shiftList 1 p) = X * toPS p := by
  rw [shiftList, shiftList, toPS_cons, map_zero, zero_add]

lemma coeffList_replicate_append (k m : ℕ) (l : List ℤ) :
    coeffList (List.replicate k 0 ++ l) m = if m < k then 0 else coeffList l (m - k) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rcases m with _ | m
    · simp [List.replicate_succ, coeffList]
    · rw [List.replicate_succ, List.cons_append, coeffList, ih]
      split_ifs <;> first | rfl | omega | (congr 1; omega)

lemma coeffList_single (a : ℤ) (j : ℕ) : coeffList [a] j = if j = 0 then a else 0 := by
  rcases j with _ | j <;> simp [coeffList]

lemma toPS_oneMinusXk (k : ℕ) : toPS (oneMinusXk (k + 1)) = 1 - X ^ (k + 1) := by
  ext n
  rw [toPS, coeff_mk, oneMinusXk, map_sub, coeff_one, coeff_X_pow]
  rcases n with _ | m
  · simp [coeffList]
  · rw [coeffList, coeffList_replicate_append, if_neg (by omega : m + 1 ≠ 0)]
    by_cases hlt : m < k
    · rw [if_pos hlt, if_neg (by omega)]; simp
    · rw [if_neg hlt, coeffList_single]
      by_cases he : m = k
      · subst he; simp
      · rw [if_neg (by omega), if_neg (by omega)]; simp

/-- truncation keeps the coefficients of degree `≤ d`. -/
lemma coeffList_truncList : ∀ (d : ℕ) (p : List ℤ) (k : ℕ),
    coeffList (truncList d p) k = if k ≤ d then coeffList p k else 0
  | _, [], k => by simp [truncList, coeffList]
  | d, a :: as, k => by
    rw [truncList]
    by_cases hd : d = 0
    · subst hd
      rcases k with _ | k <;> simp [coeffList]
    · rw [if_neg hd]
      rcases k with _ | k
      · simp [coeffList]
      · rw [coeffList, coeffList, coeffList_truncList (d - 1) as k]
        split_ifs <;> first | rfl | omega

lemma π_truncList (d : ℕ) (p : List ℤ) : FourSquares.π (d + 1) (toPS (truncList d p)) = FourSquares.π (d + 1) (toPS p) := by
  rw [FourSquares.π_eq_iff, PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [map_sub, toPS, toPS, coeff_mk, coeff_mk, coeffList_truncList, if_pos (by omega), sub_self]

lemma π_euler (d N : ℕ) : FourSquares.π (d + 1) (toPS (eulerProductTrunc d N))
    = FourSquares.π (d + 1) (MockTheta5.Bailey.qfac N) := by
  induction N with
  | zero => simp [eulerProductTrunc, MockTheta5.Bailey.qfac, toPS_cons, toPS_nil]
  | succ N ih =>
    rw [eulerProductTrunc, π_truncList, toPS_mulList, map_mul, ih, toPS_oneMinusXk, FourSquares.qfac_succ' N,
      map_mul]

lemma π_truncPow (d : ℕ) (p : List ℤ) (n : ℕ) : FourSquares.π (d + 1) (toPS (truncPowList d p n))
    = FourSquares.π (d + 1) (toPS p) ^ n := by
  induction n with
  | zero => simp [truncPowList, toPS_cons, toPS_nil]
  | succ n ih => rw [truncPowList, π_truncList, toPS_mulList, map_mul, ih]; ring

/-- **the bridge**: the computable `τ` is `[qⁿ] q∏(1−qᵏ)²⁴`. -/
theorem tau_eq_tauPS (n : ℕ) : tau n = TauCong.tauPS n := by
  have hq : FourSquares.π (n + 1) (MockTheta5.Bailey.qfac n) = FourSquares.π (n + 1) MockTheta5.JTP.qfacInf := by
    rw [← FourSquares.π_qfac (show n + 1 ≤ n + 1 from le_rfl), FourSquares.qfac_succ', map_mul, map_sub, map_one,
      FourSquares.π_X_pow le_rfl, sub_zero, mul_one]
  have h : FourSquares.π (n + 1) (toPS (shiftList 1 (truncPowList n (eulerProductTrunc n n) 24)))
      = FourSquares.π (n + 1) (X * MockTheta5.JTP.qfacInf ^ 24) := by
    rw [toPS_shiftList_one, map_mul, π_truncPow, π_euler, hq, map_mul, map_pow]
  have hc := FourSquares.coeff_eq_of_dvd (FourSquares.π_eq_iff.mp h) (Nat.lt_succ_self n)
  rw [toPS, coeff_mk] at hc
  exact hc

/-- the congruences of `TauCongruences`, for the computable `τ`. -/
theorem tau_odd_iff' (n : ℕ) : Odd (tau n) ↔ ∃ m, n = (2 * m + 1) ^ 2 := by
  rw [tau_eq_tauPS]; exact TauCong.tau_odd_iff n

theorem tau_mod7' {n : ℕ} (hn : n % 7 = 0 ∨ n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6) : (7 : ℤ) ∣ tau n := by
  rw [tau_eq_tauPS]; exact TauCong.tau_mod7 hn

theorem tau_mod23' {n : ℕ} (hn : n % 23 ∈ ({5, 7, 10, 11, 14, 15, 17, 19, 20, 21, 22} : Finset ℕ)) :
    (23 : ℤ) ∣ tau n := by
  rw [tau_eq_tauPS]; exact TauCong.tau_mod23 hn

end RamanujanTau
