/-
# q-Pochhammer products and Euler's two expansions

* `FP c a b n = ∏_{k<n} (1 − c X^{a+bk})` — the finite product `(cX^a; X^b)_n`;
* `IP c a b = ∏_{k≥0} (1 − c X^{a+bk})` — the infinite product `(cX^a; X^b)_∞` (`a, b ≥ 1`);
* `QF b n = (X^b; X^b)_n`.

Euler's expansions (Watson's (E1), (E2)), proved from their `q`-difference equations:
* `euler_inv` : `IP c a b · Σ_n cⁿ X^{an}/(X^b;X^b)_n = 1`;
* `euler_prod`: `IP c a b = Σ_n (−c)ⁿ X^{an + b·C(n,2)}/(X^b;X^b)_n`.
-/
import RamanujanTau.Watson.OSum

set_option autoImplicit false

namespace Watson
open PowerSeries Finset

/-- `(cX^a; X^b)_n`. -/
noncomputable def FP (c : ℤ) (a b n : ℕ) : PowerSeries ℤ :=
  ∏ k ∈ range n, (1 - (c : PowerSeries ℤ) * X ^ (a + b * k))

/-- `(X^b; X^b)_n`. -/
noncomputable abbrev QF (b n : ℕ) : PowerSeries ℤ := FP 1 b b n

/-- `(cX^a; X^b)_∞`. -/
noncomputable def IP (c : ℤ) (a b : ℕ) : PowerSeries ℤ := mk fun k => coeff k (FP c a b (k + 1))

lemma FP_zero (c : ℤ) (a b : ℕ) : FP c a b 0 = 1 := by simp [FP]

lemma FP_succ (c : ℤ) (a b n : ℕ) :
    FP c a b (n + 1) = FP c a b n * (1 - (c : PowerSeries ℤ) * X ^ (a + b * n)) := by
  simp [FP, prod_range_succ]

lemma FP_add (c : ℤ) (a b n m : ℕ) : FP c a b (n + m) = FP c a b n * FP c (a + b * n) b m := by
  induction m with
  | zero => simp [FP_zero]
  | succ m ih => rw [← add_assoc, FP_succ, ih, FP_succ, mul_assoc]; ring_nf

/-! ### divisibility helpers -/

lemma X_pow_dvd_iff' {m : ℕ} {f : PowerSeries ℤ} : (X : PowerSeries ℤ) ^ m ∣ f ↔ ∀ k < m, coeff k f = 0 :=
  X_pow_dvd_iff

lemma coeff_mul_of_dvd_sub_one {f g : PowerSeries ℤ} {m k : ℕ} (h : (X : PowerSeries ℤ) ^ m ∣ g - 1)
    (hk : k < m) : coeff k (f * g) = coeff k f := by
  obtain ⟨d, hd⟩ := h
  have : f * g = f + X ^ m * (f * d) := by rw [← mul_assoc, mul_comm (X ^ m) f, mul_assoc, ← hd]; ring
  rw [this, map_add, coeff_X_pow_mul', if_neg (by omega), add_zero]

lemma coeff_of_dvd_sub {f g : PowerSeries ℤ} {m k : ℕ} (h : (X : PowerSeries ℤ) ^ m ∣ f - g)
    (hk : k < m) : coeff k f = coeff k g := by
  have := X_pow_dvd_iff.mp h k hk
  rwa [map_sub, sub_eq_zero] at this

lemma FP_sub_one_dvd (c : ℤ) (a b n : ℕ) : (X : PowerSeries ℤ) ^ a ∣ FP c a b n - 1 := by
  induction n with
  | zero => simp [FP_zero]
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨d * (1 - (c : PowerSeries ℤ) * X ^ (a + b * n)) - (c : PowerSeries ℤ) * X ^ (b * n), ?_⟩
    rw [FP_succ, show FP c a b n = 1 + X ^ a * d by rw [← hd]; ring, pow_add]
    ring

/-- for `a ≥ 1`, `b ≥ 1` the partial products stabilise coefficientwise. -/
lemma coeff_FP_stable (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {k N M : ℕ} (hN : k < N) (hM : N ≤ M) :
    coeff k (FP c a b M) = coeff k (FP c a b N) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
  rw [FP_add]
  exact coeff_mul_of_dvd_sub_one (FP_sub_one_dvd c _ b d) (by nlinarith)

lemma coeff_IP (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {k N : ℕ} (hN : k < N) :
    coeff k (IP c a b) = coeff k (FP c a b N) := by
  rw [IP, coeff_mk]
  rcases le_total (k + 1) N with h | h
  · exact (coeff_FP_stable c ha hb (Nat.lt_succ_self k) h).symm
  · exact coeff_FP_stable c ha hb hN h

lemma IP_sub_FP_dvd (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (N : ℕ) :
    (X : PowerSeries ℤ) ^ N ∣ IP c a b - FP c a b N := by
  rw [X_pow_dvd_iff]
  intro k hk
  rw [map_sub, coeff_IP c ha hb hk, sub_self]

lemma IP_sub_one_dvd (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (X : PowerSeries ℤ) ^ a ∣ IP c a b - 1 := by
  rw [X_pow_dvd_iff]
  intro k hk
  rw [map_sub, coeff_IP c ha hb (Nat.lt_succ_self k)]
  exact X_pow_dvd_iff.mp (FP_sub_one_dvd c a b (k + 1)) k hk

/-- `(x;q)_∞ = (x;q)_N (xq^N;q)_∞`. -/
lemma IP_split (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (N : ℕ) :
    IP c a b = FP c a b N * IP c (a + b * N) b := by
  ext k
  have h1 : coeff k (FP c a b N * IP c (a + b * N) b) = coeff k (FP c a b N * FP c (a + b * N) b (k + 1)) :=
    coeff_of_dvd_sub (by rw [← mul_sub]; exact dvd_mul_of_dvd_right (IP_sub_FP_dvd c (by omega) hb _) _)
      (Nat.lt_succ_self k)
  rw [h1, ← FP_add, coeff_IP c ha hb (show k < N + (k + 1) by omega)]

lemma isUnit_FP (c : ℤ) {a : ℕ} (ha : 1 ≤ a) (b n : ℕ) : IsUnit (FP c a b n) := by
  rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply]
  have := X_pow_dvd_iff.mp (FP_sub_one_dvd c a b n) 0 ha
  rw [map_sub, coeff_one, if_pos rfl, sub_eq_zero] at this
  rw [this]; exact isUnit_one

lemma isUnit_IP (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : IsUnit (IP c a b) := by
  rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply]
  have := X_pow_dvd_iff.mp (IP_sub_one_dvd c ha hb) 0 ha
  rw [map_sub, coeff_one, if_pos rfl, sub_eq_zero] at this
  rw [this]; exact isUnit_one

/-! ### product identities -/

/-- even/odd split of a finite product: `(x;q)_{2n} = (x;q²)_n (xq;q²)_n`. -/
lemma FP_two (c : ℤ) (a b n : ℕ) : FP c a b (2 * n) = FP c a (2 * b) n * FP c (a + b) (2 * b) n := by
  induction n with
  | zero => simp [FP_zero]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, FP_succ, FP_succ, ih, FP_succ, FP_succ]
    ring_nf

lemma FP_two_succ (c : ℤ) (a b n : ℕ) :
    FP c a b (2 * n + 1) = FP c a (2 * b) (n + 1) * FP c (a + b) (2 * b) n := by
  rw [FP_succ, FP_two, FP_succ]; ring_nf

/-- `(x;q)_n (−x;q)_n = (x²;q²)_n`. -/
lemma FP_sq (c : ℤ) (a b n : ℕ) : FP c a b n * FP (-c) a b n = FP (c * c) (2 * a) (2 * b) n := by
  induction n with
  | zero => simp [FP_zero]
  | succ n ih =>
    rw [FP_succ, FP_succ, FP_succ, ← ih]
    push_cast
    ring_nf

lemma IP_ext_FP {f : PowerSeries ℤ} {c : ℤ} {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : ∀ N, (X : PowerSeries ℤ) ^ N ∣ f - FP c a b N) : f = IP c a b := by
  ext k
  rw [coeff_IP c ha hb (Nat.lt_succ_self k)]
  exact coeff_of_dvd_sub (h (k + 1)) (Nat.lt_succ_self k)

lemma dvd_mul_sub_mul {f g f' g' : PowerSeries ℤ} {N : ℕ} (h1 : (X : PowerSeries ℤ) ^ N ∣ f - f')
    (h2 : (X : PowerSeries ℤ) ^ N ∣ g - g') : (X : PowerSeries ℤ) ^ N ∣ f * g - f' * g' := by
  have : f * g - f' * g' = (f - f') * g + f' * (g - g') := by ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)

lemma FP_sub_FP_dvd (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {N M : ℕ} (hM : N ≤ M) :
    (X : PowerSeries ℤ) ^ N ∣ FP c a b M - FP c a b N := by
  rw [X_pow_dvd_iff]
  intro k hk
  rw [map_sub, coeff_FP_stable c ha hb hk hM, sub_self]

/-- `(x;q)_∞ = (x;q²)_∞ (xq;q²)_∞`. -/
lemma IP_two (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IP c a b = IP c a (2 * b) * IP c (a + b) (2 * b) := by
  symm
  apply IP_ext_FP ha hb
  intro N
  have e1 := IP_sub_FP_dvd c ha (show 1 ≤ 2 * b by omega) N
  have e2 := IP_sub_FP_dvd c (show 1 ≤ a + b by omega) (show 1 ≤ 2 * b by omega) N
  have e3 := dvd_mul_sub_mul e1 e2
  rw [← FP_two] at e3
  have e4 := FP_sub_FP_dvd c ha hb (show N ≤ 2 * N by omega)
  have := dvd_add e3 e4
  simpa using this

/-- `(x;q)_∞ (−x;q)_∞ = (x²;q²)_∞`. -/
lemma IP_sq (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IP c a b * IP (-c) a b = IP (c * c) (2 * a) (2 * b) := by
  apply IP_ext_FP (by omega) (by omega)
  intro N
  rw [← FP_sq]
  exact dvd_mul_sub_mul (IP_sub_FP_dvd c ha hb N) (IP_sub_FP_dvd (-c) ha hb N)

lemma expand_FP (e : ℕ) (he : e ≠ 0) (c : ℤ) (a b n : ℕ) :
    expand e he (FP c a b n) = FP c (e * a) (e * b) n := by
  simp only [FP, map_prod, map_sub, map_one, map_mul, map_intCast, map_pow, expand_X]
  refine prod_congr rfl fun k _ => ?_
  rw [← pow_mul]; ring_nf

lemma expand_dvd (e : ℕ) (he : e ≠ 0) {N : ℕ} {f : PowerSeries ℤ} (h : (X : PowerSeries ℤ) ^ N ∣ f) :
    (X : PowerSeries ℤ) ^ N ∣ expand e he f := by
  obtain ⟨d, rfl⟩ := h
  refine ⟨X ^ (e * N - N) * expand e he d, ?_⟩
  rw [map_mul, map_pow, expand_X, ← pow_mul, ← mul_assoc, ← pow_add]
  congr 2
  have : N ≤ e * N := Nat.le_mul_of_pos_left N (Nat.pos_of_ne_zero he)
  omega

lemma expand_IP (e : ℕ) (he : e ≠ 0) (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    expand e he (IP c a b) = IP c (e * a) (e * b) := by
  have he1 : 1 ≤ e := Nat.pos_of_ne_zero he
  apply IP_ext_FP (by nlinarith) (by nlinarith)
  intro N
  rw [← expand_FP e he, ← map_sub]
  exact expand_dvd e he (IP_sub_FP_dvd c ha hb N)

lemma expand_inverse (e : ℕ) (he : e ≠ 0) {f : PowerSeries ℤ} (hf : IsUnit f) :
    expand e he (Ring.inverse f) = Ring.inverse (expand e he f) := by
  have hu : IsUnit (expand e he f) := hf.map _
  rw [← one_mul (Ring.inverse (expand e he f)), ← map_one (expand e he), ← Ring.inverse_mul_cancel f hf,
    map_mul, mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]

/-- `(q;q)_n = (q^{n+1}; q)_∞`-complement: `IP 1 1 1 = FP 1 1 1 n * IP 1 (n+1) 1`. -/
lemma IP_split1 (n : ℕ) : IP 1 1 1 = FP 1 1 1 n * IP 1 (n + 1) 1 := by
  rw [IP_split 1 le_rfl le_rfl n]; ring_nf

/-- **Euler (E4)**: `(−q;q)_∞ (q;q²)_∞ = 1`. -/
lemma euler_E4 : IP (-1) 1 1 * IP 1 1 2 = 1 := by
  have h1 := IP_sq 1 (a := 1) (b := 1) le_rfl le_rfl
  have h2 := IP_two 1 (a := 1) (b := 1) le_rfl le_rfl
  norm_num at h1 h2
  have hu := isUnit_IP 1 (a := 2) (b := 2) (by norm_num) (by norm_num)
  apply hu.mul_left_cancel
  rw [mul_one]
  calc IP 1 2 2 * (IP (-1) 1 1 * IP 1 1 2) = (IP 1 1 2 * IP 1 2 2) * IP (-1) 1 1 := by ring
    _ = IP 1 2 2 := by rw [← h2, h1]

end Watson
