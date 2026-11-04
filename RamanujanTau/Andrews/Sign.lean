/-
# The sign pattern of Ramanujan's mock theta function `f(q)` for every `n ≥ 1`

`f(q) = Σ q^{n²}/(−q;q)_n² = Σ α(n) qⁿ`.  **Theorem (`alpha_sign`)**: `(−1)^{n+1} α(n) > 0` for all `n ≥ 1`.

The proof is elementary: no circle method, no finite table beyond `n ≤ 6`.

1. Watson (W1), `MockTheta3.Watson3.watson_W1`: `f(q) = 2φ(−q) − b(q)`, so after `q ↦ −q`
   `(−1)^{n+1} α(n) = [qⁿ] (−q;q²)_∞ ϑ(q) − 2 [qⁿ] φ(q)`, with `ϑ = 1 + 2Σ_{k≥1} q^{k²}` and
   `φ(q) = Σ q^{m²}/(−q²;q²)_m`.
2. `|[qⁿ] 1/(−q²;q²)_m| ≤ [qⁿ] 1/(q²;q²)_m`, so `|[qⁿ] φ| ≤ [qⁿ] Σ q^{m²}/(q²;q²)_m = Q(n)` by Euler
   (`Watson.euler_prod`), where `Q(n) = [qⁿ](−q;q²)_∞` counts partitions into distinct odd parts.
3. Hence `(−1)^{n+1} α(n) ≥ 2Q(n−1) + 2Q(n−4) − Q(n)`.
4. `Q(n) ≤ 2Q(n−1)` for `n ≥ 4` and `Q(m) ≥ 1` for `m ≥ 3` (two shift injections, `Andrews/Order.lean`).
   The cases `n = 1, 2, 3, 6` use `Q(1) = 1, Q(2) = 0, Q(6) = 1` and `[q³]φ = −1`.
-/
import RamanujanTau.Andrews.Order
import RamanujanTau.MockTheta3

set_option autoImplicit false

namespace Andrews
open PowerSeries Finset Watson MockTheta3.Watson3

lemma coeff_osum_range {f : ℕ → PowerSeries ℤ} (h : ∀ n k, k < n → coeff k (f n) = 0) (k : ℕ) :
    coeff k (osum f) = ∑ n ∈ range (k + 1), coeff k (f n) := by
  rw [coeff_osum]
  refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
  simp only [Function.mem_support, coe_range, Set.mem_Iio] at hn ⊢
  by_contra hc; exact hn (h n k (by omega))

lemma NN_osum {f : ℕ → PowerSeries ℤ} (hf : ∀ n, NN (f n)) : NN (osum f) := fun k => by
  rw [coeff_osum]; exact finsum_nonneg fun n => hf n k

lemma coeff_Xsq_mul_lt {m k : ℕ} (hk : k < m) (g : PowerSeries ℤ) : coeff k (X ^ (m ^ 2) * g) = 0 := by
  rw [coeff_X_pow_mul', if_neg (by nlinarith)]

lemma coeff_two_mul (f : PowerSeries ℤ) (k : ℕ) : coeff k (2 * f) = 2 * coeff k f := by
  rw [show (2 : PowerSeries ℤ) = C 2 by simp, coeff_C_mul]

/-! ### distinct odd parts -/

/-- `Q n = [qⁿ](−q;q²)_∞`: partitions of `n` into distinct odd parts. -/
noncomputable def Q (n : ℕ) : ℤ := coeff n (IP (-1) 1 2)

/-- `B n = [qⁿ](−q³;q²)_∞`: partitions of `n` into distinct odd parts `≥ 3`. -/
noncomputable def B (n : ℕ) : ℤ := coeff n (IP (-1) 3 2)

lemma Q_eq {n K : ℕ} (h : n < K) : Q n = coeff n (NP 1 2 K) := coeff_IP (-1) le_rfl (by norm_num) h

lemma B_eq {n K : ℕ} (h : n < K) : B n = coeff n (NP 3 2 K) := coeff_IP (-1) (by norm_num) (by norm_num) h

lemma Q_nonneg (n : ℕ) : 0 ≤ Q n := by rw [Q_eq (Nat.lt_succ_self n)]; exact NN_NP _ _ _ n

lemma B_nonneg (n : ℕ) : 0 ≤ B n := by rw [B_eq (Nat.lt_succ_self n)]; exact NN_NP _ _ _ n

lemma IP_split1 : IP (-1) 1 2 = (1 + X) * IP (-1) 3 2 := by
  rw [IP_split (-1) (a := 1) (b := 2) le_rfl (by norm_num) 1]
  congr 1; simp [FP]

lemma Q_succ (n : ℕ) : Q (n + 1) = B (n + 1) + B n := by
  unfold Q B; rw [IP_split1, add_mul, one_mul, map_add, coeff_succ_X_mul]

lemma coeff_one_nonneg (k : ℕ) : 0 ≤ coeff k (1 : PowerSeries ℤ) := NN_one k

/-- (shift down) `B(m+2) ≤ Q(m)`. -/
lemma B_le_Q (m : ℕ) : B (m + 2) ≤ Q m := by
  have h := NP_shift_low (m + 3) 1 (m + 2)
  rw [show (1 : ℕ) + 2 = 3 from rfl, map_sub, coeff_one, if_neg (by omega), sub_zero, coeff_X_pow_mul',
    if_pos (by omega), Nat.add_sub_cancel, map_sub] at h
  rw [B_eq (K := m + 3) (by omega), Q_eq (K := m + 3 + 1) (by omega)]
  linarith [coeff_one_nonneg m]

/-- (shift up) `B(m+1) ≤ B(m+3)`. -/
lemma B_mono (m : ℕ) : B (m + 1) ≤ B (m + 3) := by
  have h := NP_shift_high 3 (m + 3) (m + 3)
  rw [coeff_X_pow_mul', if_pos (by omega), show m + 3 - 2 = m + 1 by omega, map_sub, map_sub, coeff_one,
    coeff_one, if_neg (by omega), if_neg (by omega), sub_zero, sub_zero] at h
  rw [B_eq (K := m + 3) (by omega), B_eq (K := m + 3 + 1) (by omega)]
  exact h

/-- `Q(n) ≤ 2Q(n−1)` for `n ≥ 4`. -/
lemma Q_le_two (m : ℕ) : Q (m + 4) ≤ 2 * Q (m + 3) := by
  have h1 := Q_succ (m + 3)
  have h2 := Q_succ (m + 2)
  have h3 := B_le_Q (m + 2)
  have h4 := Q_succ (m + 1)
  have h5 := B_mono m
  have h6 := B_nonneg (m + 2)
  simp only [show m + 3 + 1 = m + 4 by ring, show m + 2 + 1 = m + 3 by ring,
    show m + 1 + 1 = m + 2 by ring] at h1 h2 h3 h4
  linarith

lemma B_odd_pos (j : ℕ) : 1 ≤ B (3 + 2 * j) := by
  have h := Dom_factor_NP 3 2 (i := j) (K := 3 + 2 * j + 1) (by omega) (3 + 2 * j)
  rw [map_add, coeff_one, if_neg (by omega), coeff_X_pow, if_pos rfl] at h
  rw [B_eq (K := 3 + 2 * j + 1) (by omega)]; linarith

lemma Q_pos {m : ℕ} (hm : 3 ≤ m) : 1 ≤ Q m := by
  obtain ⟨j, rfl | rfl⟩ : ∃ j, m = 3 + 2 * j ∨ m = 4 + 2 * j := ⟨(m - 3) / 2, by omega⟩
  · have := Q_succ (2 + 2 * j)
    rw [show 2 + 2 * j + 1 = 3 + 2 * j by ring] at this
    linarith [B_odd_pos j, B_nonneg (2 + 2 * j)]
  · have := Q_succ (3 + 2 * j)
    rw [show 3 + 2 * j + 1 = 4 + 2 * j by ring] at this
    linarith [B_odd_pos j, B_nonneg (4 + 2 * j)]

/-- the first coefficients of `(−q;q²)_∞ = (1+q)(1+q³)(1+q⁵)⋯`. -/
lemma Q_low {k : ℕ} (hk : k < 7) :
    Q k = coeff k (1 + X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8 + X ^ 9 : PowerSeries ℤ) := by
  unfold Q
  rw [IP_split (-1) (a := 1) (b := 2) le_rfl (by norm_num) 3,
    coeff_mul_of_dvd_sub_one (IP_sub_one_dvd (-1) (by norm_num) (by norm_num)) (by norm_num; omega)]
  congr 1
  simp [FP, prod_range_succ]; ring

lemma Q_zero : Q 0 = 1 := by rw [Q_low (by norm_num)]; simp
lemma Q_one : Q 1 = 1 := by rw [Q_low (by norm_num)]; simp [coeff_X_pow, coeff_X]
lemma Q_two : Q 2 = 0 := by rw [Q_low (by norm_num)]; simp [coeff_X_pow, coeff_X]
lemma Q_six : Q 6 = 1 := by rw [Q_low (by norm_num)]; simp [coeff_X_pow, coeff_X]

/-! ### the mock theta function `φ(q) = Σ q^{m²}/(−q²;q²)_m` and Euler's bound -/

/-- `φ(q) = Σ q^{m²}/(−q²;q²)_m`. -/
noncomputable def phi3 : PowerSeries ℤ := osum fun m => X ^ (m ^ 2) * Ring.inverse (NP 2 2 m)

lemma expo (m : ℕ) : m + 2 * m.choose 2 = m ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]; nlinarith [ih]

/-- Euler: `Σ q^{m²}/(q²;q²)_m = (−q;q²)_∞`. -/
lemma euler_odd : osum (fun m => X ^ (m ^ 2) * QI 2 m) = IP (-1) 1 2 := by
  rw [euler_prod (-1) le_rfl (by norm_num), HP]
  refine osum_ext fun m => ?_
  simp only [hP, neg_neg, one_pow, Int.cast_one, one_mul]
  rw [expo]

/-- `|[qⁿ] φ| ≤ Q(n)`. -/
lemma abs_phi3_le (n : ℕ) : |coeff n phi3| ≤ Q n := by
  rw [Q, ← euler_odd, phi3, coeff_osum_range (fun m k hk => coeff_Xsq_mul_lt hk _),
    coeff_osum_range (fun m k hk => coeff_Xsq_mul_lt hk _)]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => ?_)
  exact ((ADom_X_pow _).mul (ADom_inv_NP (by norm_num) 2 m)) n

lemma NP221 : NP 2 2 1 = 1 - ((-1 : ℤ) : PowerSeries ℤ) * X ^ 2 := by simp [NP, FP]

/-- `[q³] φ = −1`. -/
lemma phi3_three : coeff 3 phi3 = -1 := by
  rw [phi3, coeff_osum_range (fun m k hk => coeff_Xsq_mul_lt hk _)]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [NP221, inverse_one_sub _ (by norm_num)]
  simp [NP, FP_zero, geo, coeff_X_pow_mul', coeff_one]

/-! ### `q ↦ −q` -/

local notation "R" => rescale (-1 : ℤ)

lemma R_X_pow (e : ℕ) : R (X ^ e) = (((-1) ^ e : ℤ) : PowerSeries ℤ) * X ^ e := by
  rw [map_pow, rescale_neg_one_X, neg_pow]; simp

lemma R_inverse {u : PowerSeries ℤ} (hu : IsUnit u) : R (Ring.inverse u) = Ring.inverse (R u) := by
  refine (inverse_eq_of_mul ?_).symm
  rw [← map_mul, Ring.mul_inverse_cancel _ hu, map_one]

lemma R_osum {f : ℕ → PowerSeries ℤ} (h : ∀ n k, k < n → coeff k (f n) = 0) :
    R (osum f) = osum fun n => R (f n) := by
  ext k
  rw [coeff_rescale, coeff_osum_range h, coeff_osum_range (fun n k hk => by rw [coeff_rescale, h n k hk, mul_zero]),
    mul_sum]
  simp [coeff_rescale]

lemma R_NP22 (m : ℕ) : R (NP 2 2 m) = NP 2 2 m := by
  induction m with
  | zero => simp [NP, FP_zero]
  | succ m ih =>
    rw [NP_succ, map_mul, ih, map_add, map_one, R_X_pow,
      (show Even (2 + 2 * m) from ⟨1 + m, by ring⟩).neg_one_pow]
    simp

lemma R_FP112 (m : ℕ) : R (FP 1 1 2 m) = NP 1 2 m := by
  induction m with
  | zero => simp [NP, FP_zero]
  | succ m ih =>
    rw [FP_succ, map_mul, ih, NP_succ, map_sub, map_one, map_mul, map_intCast, R_X_pow,
      (show Odd (1 + 2 * m) from ⟨m, by ring⟩).neg_one_pow]
    simp

lemma R_IP : R (IP 1 1 2) = IP (-1) 1 2 := by
  ext k
  rw [coeff_rescale, IP, IP, coeff_mk, coeff_mk, ← coeff_rescale, R_FP112]

lemma neg_one_pow_sq (n : ℕ) : ((-1 : ℤ) ^ n) * (-1) ^ (n ^ 2) = 1 := by
  rw [← pow_add, show n + n ^ 2 = n * (n + 1) by ring, (Nat.even_mul_succ_self n).neg_one_pow]

lemma R_Theta : R Θ = 2 * osum (fun n => (X : PowerSeries ℤ) ^ (n ^ 2)) - 1 := by
  rw [Θ, map_sub, map_mul, map_one, map_ofNat,
    R_osum (fun n k hk => by rw [mul_comm]; exact coeff_Xsq_mul_lt hk _)]
  congr 2
  refine osum_ext fun n => ?_
  rw [map_mul, map_pow, map_neg, map_one, R_X_pow, ← mul_assoc,
    show ((-1 : PowerSeries ℤ)) ^ n = (((-1) ^ n : ℤ) : PowerSeries ℤ) by simp, ← Int.cast_mul,
    neg_one_pow_sq]
  simp

lemma R_A1 : R (A 1) = phi3 := by
  have hord : ∀ n k, k < n → coeff k (uA 1 n) = 0 := fun n k hk => by
    rw [uA, mul_comm ((-1 : PowerSeries ℤ) ^ n), mul_assoc]; exact coeff_Xsq_mul_lt hk _
  rw [A, R_osum hord, phi3]
  refine osum_ext fun n => ?_
  rw [uA, map_mul, map_mul, map_pow, map_neg, map_one, R_X_pow, R_inverse (isUnit_NP (by norm_num) 2 n),
    show (1 : ℕ) + 1 = 2 from rfl, R_NP22,
    show ((-1 : PowerSeries ℤ)) ^ n = (((-1) ^ n : ℤ) : PowerSeries ℤ) by simp, ← mul_assoc, ← Int.cast_mul,
    neg_one_pow_sq]
  simp

lemma LF_sq (j : ℕ) : LF (fun n : ℕ => (X : PowerSeries ℤ) ^ ((n + j) ^ 2)) :=
  LF.of_nat fun n k hk => by
    rw [coeff_X_pow, if_neg]
    have : n + j ≤ (n + j) ^ 2 := Nat.le_self_pow two_ne_zero _
    omega

/-- `ϑ(q) = 1 + 2q + 2q⁴ + 2Σ_{n≥3} q^{n²}`. -/
lemma osum_sq : osum (fun n => (X : PowerSeries ℤ) ^ (n ^ 2))
    = 1 + X + X ^ 4 + osum (fun n => (X : PowerSeries ℤ) ^ ((n + 3) ^ 2)) := by
  have e0 : osum (fun n => (X : PowerSeries ℤ) ^ (n ^ 2)) = 1 + osum (fun n => (X : PowerSeries ℤ) ^ ((n + 1) ^ 2)) := by
    have := osum_succ (LF_sq 0)
    simp only [add_zero] at this
    rw [this]; simp
  have e1 : osum (fun n => (X : PowerSeries ℤ) ^ ((n + 1) ^ 2)) = X + osum (fun n => (X : PowerSeries ℤ) ^ ((n + 2) ^ 2)) := by
    rw [osum_succ (LF_sq 1)]
    congr 1; all_goals simp
  have e2 : osum (fun n => (X : PowerSeries ℤ) ^ ((n + 2) ^ 2)) = X ^ 4 + osum (fun n => (X : PowerSeries ℤ) ^ ((n + 3) ^ 2)) := by
    rw [osum_succ (LF_sq 2)]
    congr 1
  rw [e0, e1, e2]; ring

/-! ### the identity `(−1)^{n+1} α(n) = [qⁿ](−q;q²)_∞ ϑ(q) − 2[qⁿ]φ(q)` -/

/-- `α(n) = [qⁿ] f(q)`. -/
noncomputable abbrev α (n : ℕ) : ℤ := coeff n MockTheta3.f3

lemma f3_eq_F1 (n : ℕ) : α n = coeff n (F 1) := by
  rw [α, MockTheta3.f3, coeff_mk, F,
    coeff_osum_range (fun m k hk => by rw [tF, mul_assoc]; exact coeff_Xpow_mul_zero (by nlinarith) _), map_sum]
  refine sum_congr rfl fun k _ => ?_
  have hN : MockTheta3.negPoch k = NP 1 1 k := by
    simp only [MockTheta3.negPoch, NP, FP]
    refine prod_congr rfl fun i _ => ?_
    simp; ring
  rw [tF, hN, show 1 * k + k * (k - 1) = k ^ 2 by cases k <;> simp <;> ring]
  ring_nf

theorem alpha_formula (n : ℕ) :
    (-1) ^ (n + 1) * α n
      = coeff n (IP (-1) 1 2 * (2 * osum (fun n => (X : PowerSeries ℤ) ^ (n ^ 2)) - 1)) - 2 * coeff n phi3 := by
  have hW : F 1 = 2 * A 1 - bR := by rw [← watson_W1]; ring
  have hb : coeff n (R bR) = (-1) ^ n * coeff n bR := coeff_rescale _ _ _
  have ha : coeff n (R (A 1)) = (-1) ^ n * coeff n (A 1) := coeff_rescale _ _ _
  rw [bR, map_mul, R_IP, R_Theta] at hb
  rw [R_A1] at ha
  rw [f3_eq_F1, hW, map_sub, coeff_two_mul, hb, ha, bR]
  ring

/-! ### the sign theorem -/

lemma main_lower (n : ℕ) :
    Q n + 2 * (if 1 ≤ n then Q (n - 1) else 0) + 2 * (if 4 ≤ n then Q (n - 4) else 0) - 2 * coeff n phi3
      ≤ (-1) ^ (n + 1) * α n := by
  rw [alpha_formula, osum_sq]
  have hT : NN (osum fun n => (X : PowerSeries ℤ) ^ ((n + 3) ^ 2)) := NN_osum fun _ => NN_X_pow _
  have hP : NN (IP (-1) 1 2) := fun k => by rw [← Q]; exact Q_nonneg k
  have e : IP (-1) 1 2 * (2 * (1 + X + X ^ 4 + osum fun n => (X : PowerSeries ℤ) ^ ((n + 3) ^ 2)) - 1)
      = IP (-1) 1 2 + 2 * (X ^ 1 * IP (-1) 1 2) + 2 * (X ^ 4 * IP (-1) 1 2)
        + 2 * (IP (-1) 1 2 * osum fun n => (X : PowerSeries ℤ) ^ ((n + 3) ^ 2)) := by ring
  rw [e, map_add, map_add, map_add, coeff_two_mul, coeff_two_mul, coeff_two_mul, coeff_X_pow_mul',
    coeff_X_pow_mul', ← Q]
  have := hP.mul hT n
  simp only [Q] at *
  linarith

/-- **Sign pattern of `f(q)`**: `(−1)^{n+1} α(n) > 0` for every `n ≥ 1`. -/
theorem alpha_sign {n : ℕ} (hn : 1 ≤ n) : 0 < (-1) ^ (n + 1) * α n := by
  have hL := main_lower n
  have hφ := abs_phi3_le n
  have hφ' : coeff n phi3 ≤ Q n := (le_abs_self _).trans hφ
  rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 ∨ (4 ≤ n ∧ n ≠ 6) by omega) with h | h | h | h | ⟨h4, h6⟩
  · subst h; simp only [le_refl, if_true, show ¬ 4 ≤ 1 by norm_num, if_false] at hL
    rw [Q_one, Q_zero] at hL; rw [Q_one] at hφ'; linarith
  · subst h; simp only [show 1 ≤ 2 by norm_num, if_true, show ¬ 4 ≤ 2 by norm_num, if_false] at hL
    rw [Q_two, Q_one] at hL; rw [Q_two] at hφ'; linarith
  · subst h; simp only [show 1 ≤ 3 by norm_num, if_true, show ¬ 4 ≤ 3 by norm_num, if_false] at hL
    rw [phi3_three] at hL; linarith [Q_nonneg 3, Q_nonneg 2]
  · subst h; simp only [show 1 ≤ 6 by norm_num, show 4 ≤ 6 by norm_num, if_true] at hL
    rw [Q_six] at hL hφ'
    have h5 := Q_pos (m := 5) (by norm_num)
    have h2 := Q_nonneg 2
    simp only [show 6 - 1 = 5 by rfl, show 6 - 4 = 2 by rfl] at hL
    linarith
  · simp only [show 1 ≤ n by omega, h4, if_true] at hL
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have hle := Q_le_two m
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 4 = m by omega] at hL
    have hpos : 1 ≤ Q m := by
      rcases (show m = 0 ∨ m = 1 ∨ 3 ≤ m by omega) with h | h | h
      · subst h; rw [Q_zero]
      · subst h; rw [Q_one]
      · exact Q_pos h
    linarith

/-- **Rank-parity form**: for every `n ≥ 1`, `(−1)^{n+1}(N(0,2,n) − N(1,2,n)) > 0`. -/
theorem rank_parity_sign_all {n : ℕ} (hn : 1 ≤ n) :
    0 < (-1) ^ (n + 1) * (((univ.filter fun l : n.Partition => Even (CrankProof.rank l)).card : ℤ)
      - ((univ.filter fun l : n.Partition => ¬ Even (CrankProof.rank l)).card : ℤ)) := by
  rw [← MockTheta3.f3_rank]; exact alpha_sign hn

end Andrews
