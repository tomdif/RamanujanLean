/-
# Euler's expansions (Watson's (E1), (E2))

* `euler_inv`  : `(cX^a; X^b)_∞ · Σ_n cⁿ X^{an}/(X^b;X^b)_n = 1`, i.e. `1/(x;q)_∞ = Σ xⁿ/(q;q)_n`.
* `euler_prod` : `(cX^a; X^b)_∞ = Σ_n (−c)ⁿ X^{an + b·C(n,2)}/(X^b;X^b)_n`, i.e.
  `(x;q)_∞ = Σ (−1)ⁿ q^{C(n,2)} xⁿ/(q;q)_n`.

Both come from the `q`-difference equations `(1 − x) G(x) = G(xq)` and `H(x) = (1 − x) H(xq)`, iterated
`N` times and compared with the partial products.
-/
import RamanujanTau.Watson.Prod

set_option autoImplicit false

namespace Watson
open PowerSeries Finset

/-- `1/(X^b;X^b)_n`. -/
noncomputable abbrev QI (b n : ℕ) : PowerSeries ℤ := Ring.inverse (QF b n)

lemma QF_mul_QI (b n : ℕ) (hb : 1 ≤ b) : QF b n * QI b n = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_FP 1 hb b n)

lemma QI_succ (b n : ℕ) (hb : 1 ≤ b) : (1 - X ^ (b * (n + 1))) * QI b (n + 1) = QI b n := by
  have hu := isUnit_FP 1 hb b n
  have e : QF b n * (1 - X ^ (b * (n + 1))) = QF b (n + 1) := by
    rw [QF, QF, FP_succ]; simp [mul_add, mul_comm b n, add_comm]
  apply hu.mul_left_cancel
  rw [← mul_assoc, e, QF_mul_QI b _ hb, QF_mul_QI b n hb]

/-- term of the `1/(x;q)_∞` expansion. -/
noncomputable def gI (c : ℤ) (a b n : ℕ) : PowerSeries ℤ := ((c ^ n : ℤ) : PowerSeries ℤ) * X ^ (a * n) * QI b n

/-- `Σ_n cⁿ X^{an}/(X^b;X^b)_n`. -/
noncomputable def GI (c : ℤ) (a b : ℕ) : PowerSeries ℤ := osum (gI c a b)

lemma coeff_X_pow_mul_mul {m k : ℕ} (hk : k < m) (f g : PowerSeries ℤ) : coeff k (f * X ^ m * g) = 0 := by
  rw [show f * X ^ m * g = X ^ m * (f * g) by ring, coeff_X_pow_mul', if_neg (by omega)]

lemma LF_gI (c : ℤ) {a : ℕ} (ha : 1 ≤ a) (b : ℕ) : LF (gI c a b) :=
  LF.of_nat fun n k hk => coeff_X_pow_mul_mul (by nlinarith) _ _

lemma GI_rec (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (1 - (c : PowerSeries ℤ) * X ^ a) * GI c a b = GI c (a + b) b := by
  have h1 := LF_gI c ha b
  have h2 := LF_gI c (show 1 ≤ a + b by omega) b
  have key : GI c a b - GI c (a + b) b = (c : PowerSeries ℤ) * X ^ a * GI c a b := by
    rw [GI, GI, ← osum_sub h1 h2, osum_succ (f := fun i => gI c a b i - gI c (a + b) b i) (h1.sub h2)]
    simp only [gI, mul_zero, sub_self, zero_add]
    rw [← osum_smul _ h1]
    refine osum_ext fun m => ?_
    simp only [gI]
    rw [← QI_succ b m hb]
    push_cast
    ring
  linear_combination key

lemma FP_mul_GI (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (N : ℕ) :
    FP c a b N * GI c a b = GI c (a + b * N) b := by
  induction N with
  | zero => simp [FP_zero]
  | succ N ih =>
    rw [FP_succ, mul_comm (FP c a b N), mul_assoc, ih, GI_rec c (by omega) hb]
    ring_nf

lemma GI_sub_one_dvd (c : ℤ) {a : ℕ} (ha : 1 ≤ a) (b : ℕ) : (X : PowerSeries ℤ) ^ a ∣ GI c a b - 1 := by
  rw [X_pow_dvd_iff]
  intro k hk
  rw [GI, osum_succ (LF_gI c ha b), map_sub, map_add, coeff_osum]
  have h0 : gI c a b 0 = 1 := by simp [gI, QI, QF, FP_zero]
  rw [h0, finsum_eq_zero_of_forall_eq_zero (M := ℤ) fun n => by
    simp only [gI]; exact coeff_X_pow_mul_mul (by nlinarith) _ _]
  simp

/-- **Euler (E2)**: `(x;q)_∞ · Σ xⁿ/(q;q)_n = 1`. -/
theorem euler_inv (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : IP c a b * GI c a b = 1 := by
  ext k
  have h1 : coeff k (IP c a b * GI c a b) = coeff k (FP c a b (k + 1) * GI c a b) := by
    rw [mul_comm, mul_comm (FP c a b (k + 1))]
    exact coeff_of_dvd_sub (by rw [← mul_sub]; exact dvd_mul_of_dvd_right (IP_sub_FP_dvd c ha hb _) _)
      (Nat.lt_succ_self k)
  rw [h1, FP_mul_GI c ha hb]
  exact coeff_of_dvd_sub (GI_sub_one_dvd c (by nlinarith) b) (by nlinarith)

lemma GI_eq (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : GI c a b = Ring.inverse (IP c a b) := by
  rw [← one_mul (Ring.inverse _), ← euler_inv c ha hb, mul_comm (IP c a b), mul_assoc,
    Ring.mul_inverse_cancel _ (isUnit_IP c ha hb), mul_one]

/-- term of the `(x;q)_∞` expansion. -/
noncomputable def hP (c : ℤ) (a b n : ℕ) : PowerSeries ℤ :=
  (((-c) ^ n : ℤ) : PowerSeries ℤ) * X ^ (a * n + b * n.choose 2) * QI b n

/-- `Σ_n (−c)ⁿ X^{an + b C(n,2)}/(X^b;X^b)_n`. -/
noncomputable def HP (c : ℤ) (a b : ℕ) : PowerSeries ℤ := osum (hP c a b)

lemma LF_hP (c : ℤ) {a : ℕ} (ha : 1 ≤ a) (b : ℕ) : LF (hP c a b) :=
  LF.of_nat fun n k hk => coeff_X_pow_mul_mul (by nlinarith) _ _

lemma HP_rec (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    HP c a b = (1 - (c : PowerSeries ℤ) * X ^ a) * HP c (a + b) b := by
  have h1 := LF_hP c ha b
  have h2 := LF_hP c (show 1 ≤ a + b by omega) b
  have key : HP c a b - HP c (a + b) b = -((c : PowerSeries ℤ) * X ^ a) * HP c (a + b) b := by
    rw [HP, HP, ← osum_sub h1 h2, osum_succ (f := fun i => hP c a b i - hP c (a + b) b i) (h1.sub h2)]
    simp only [hP, mul_zero, Nat.choose_zero_succ, sub_self, zero_add]
    rw [← osum_smul _ h2]
    refine osum_ext fun m => ?_
    simp only [hP]
    rw [← QI_succ b m hb]
    have hc : (m + 1).choose 2 = m.choose 2 + m := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    rw [hc]
    push_cast
    ring
  linear_combination key

lemma HP_eq_FP_mul (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (N : ℕ) :
    HP c a b = FP c a b N * HP c (a + b * N) b := by
  induction N with
  | zero => simp [FP_zero]
  | succ N ih =>
    rw [ih, HP_rec c (show 1 ≤ a + b * N by nlinarith) hb, FP_succ]
    ring_nf

lemma HP_sub_one_dvd (c : ℤ) {a : ℕ} (ha : 1 ≤ a) (b : ℕ) : (X : PowerSeries ℤ) ^ a ∣ HP c a b - 1 := by
  rw [X_pow_dvd_iff]
  intro k hk
  rw [HP, osum_succ (LF_hP c ha b), map_sub, map_add, coeff_osum]
  have h0 : hP c a b 0 = 1 := by simp [hP, QI, QF, FP_zero]
  rw [h0, finsum_eq_zero_of_forall_eq_zero (M := ℤ) fun n => by
    simp only [hP]; exact coeff_X_pow_mul_mul (by nlinarith) _ _]
  simp

/-- **Euler (E1)**: `(x;q)_∞ = Σ (−1)ⁿ q^{C(n,2)} xⁿ/(q;q)_n`. -/
theorem euler_prod (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : IP c a b = HP c a b := by
  ext k
  rw [HP_eq_FP_mul c ha hb (k + 1), coeff_IP c ha hb (Nat.lt_succ_self k)]
  exact (coeff_mul_of_dvd_sub_one (HP_sub_one_dvd c (by nlinarith) b) (by nlinarith)).symm

end Watson
