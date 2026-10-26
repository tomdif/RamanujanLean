/-
# The finite q-binomial theorem (Watson's (E3)) and the even part of Euler's expansion

* `qbinom_inv`: `(cX^a; X^b)_M · Σ_n cⁿ X^{an} (X^{bM}; X^b)_n/(X^b;X^b)_n = 1`, i.e.
  `1/(x;q)_M = Σ xⁿ (q^M;q)_n/(q;q)_n`.
* `euler_even`: `(X^c; X²)_∞ · Σ_n X^{cn}/(q;q)_{2n} = Σ_p X^{p(2p−1)+cp}/(q;q)_{2p}`.

The second one is Watson's step `1/(x;q)_∞ + 1/(−x;q)_∞ = [(x;q)_∞ + (−x;q)_∞]/(x²;q²)_∞` with
`x² = X^c`. We avoid the half-integer power `x = X^{c/2}` by proving it after `q ↦ q²` and cancelling
the (injective) substitution.
-/
import RamanujanTau.Watson.Euler

set_option autoImplicit false

namespace Watson
open PowerSeries Finset

/-! ### (E3) -/

/-- term of the finite q-binomial expansion. -/
noncomputable def kB (c : ℤ) (a b M n : ℕ) : PowerSeries ℤ :=
  ((c ^ n : ℤ) : PowerSeries ℤ) * X ^ (a * n) * FP 1 (b * M) b n * QI b n

noncomputable def KB (c : ℤ) (a b M : ℕ) : PowerSeries ℤ := osum (kB c a b M)

lemma LF_kB (c : ℤ) {a : ℕ} (ha : 1 ≤ a) (b M : ℕ) : LF (kB c a b M) :=
  LF.of_nat fun n k hk => by
    rw [kB, show ((c ^ n : ℤ) : PowerSeries ℤ) * X ^ (a * n) * FP 1 (b * M) b n * QI b n
      = ((c ^ n : ℤ) : PowerSeries ℤ) * X ^ (a * n) * (FP 1 (b * M) b n * QI b n) by ring]
    exact coeff_X_pow_mul_mul (by nlinarith) _ _

lemma KB_rec (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (M : ℕ) :
    (1 - (c : PowerSeries ℤ) * X ^ a) * KB c a b M =
      (1 - (c : PowerSeries ℤ) * X ^ (a + b * M)) * KB c (a + b) b M := by
  have h1 := LF_kB c ha b M
  have h2 := LF_kB c (show 1 ≤ a + b by omega) b M
  have key : KB c a b M - KB c (a + b) b M =
      (c : PowerSeries ℤ) * X ^ a * KB c a b M - (c : PowerSeries ℤ) * X ^ (a + b * M) * KB c (a + b) b M := by
    rw [KB, KB, ← osum_sub h1 h2, osum_succ (f := fun i => kB c a b M i - kB c (a + b) b M i) (h1.sub h2),
      ← osum_smul _ h1, ← osum_smul _ h2, ← osum_sub (h1.mul_left _) (h2.mul_left _)]
    simp only [kB, mul_zero, sub_self, zero_add]
    refine osum_ext fun m => ?_
    rw [← QI_succ b m hb, FP_succ]
    push_cast
    ring
  linear_combination key

lemma FP_mul_KB (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (M N : ℕ) :
    FP c a b N * KB c a b M = FP c (a + b * M) b N * KB c (a + b * N) b M := by
  induction N with
  | zero => simp [FP_zero]
  | succ N ih =>
    rw [FP_succ, FP_succ, mul_comm (FP c a b N), mul_assoc, ih, ← mul_assoc, mul_comm _ (FP c (a + b * M) b N),
      mul_assoc, KB_rec c (show 1 ≤ a + b * N by nlinarith) hb M]
    ring_nf

lemma KB_sub_one_dvd (c : ℤ) {a : ℕ} (ha : 1 ≤ a) (b M : ℕ) : (X : PowerSeries ℤ) ^ a ∣ KB c a b M - 1 := by
  rw [X_pow_dvd_iff]
  intro k hk
  rw [KB, osum_succ (LF_kB c ha b M), map_sub, map_add, coeff_osum]
  have h0 : kB c a b M 0 = 1 := by simp [kB, QI, QF, FP_zero]
  rw [h0, finsum_eq_zero_of_forall_eq_zero (M := ℤ) fun n => by
    simp only [kB]
    rw [show ((c ^ (n + 1) : ℤ) : PowerSeries ℤ) * X ^ (a * (n + 1)) * FP 1 (b * M) b (n + 1) * QI b (n + 1)
      = ((c ^ (n + 1) : ℤ) : PowerSeries ℤ) * X ^ (a * (n + 1)) * (FP 1 (b * M) b (n + 1) * QI b (n + 1)) by ring]
    exact coeff_X_pow_mul_mul (by nlinarith) _ _]
  simp

/-- **(E3)** the finite q-binomial theorem: `(x;q)_M · Σ xⁿ (q^M;q)_n/(q;q)_n = 1`. -/
theorem qbinom_inv (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (M : ℕ) : FP c a b M * KB c a b M = 1 := by
  have hIP : IP c a b * KB c a b M = IP c (a + b * M) b := by
    ext k
    have h1 : coeff k (IP c a b * KB c a b M) = coeff k (FP c a b (k + 1) * KB c a b M) := by
      rw [mul_comm, mul_comm (FP c a b (k + 1))]
      exact coeff_of_dvd_sub (by rw [← mul_sub]; exact dvd_mul_of_dvd_right (IP_sub_FP_dvd c ha hb _) _)
        (Nat.lt_succ_self k)
    rw [h1, FP_mul_KB c ha hb M (k + 1), coeff_IP c (by nlinarith) hb (Nat.lt_succ_self k)]
    exact coeff_mul_of_dvd_sub_one (KB_sub_one_dvd c (by nlinarith) b M) (by nlinarith)
  have hu := isUnit_IP c (show 1 ≤ a + b * M by nlinarith) hb
  apply hu.mul_left_cancel
  calc IP c (a + b * M) b * (FP c a b M * KB c a b M)
      = (FP c a b M * IP c (a + b * M) b) * KB c a b M := by ring
    _ = IP c (a + b * M) b * 1 := by rw [← IP_split c ha hb M, hIP, mul_one]

lemma KB_eq (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (M : ℕ) : KB c a b M = Ring.inverse (FP c a b M) := by
  rw [← one_mul (Ring.inverse _), ← qbinom_inv c ha hb M, mul_comm (FP c a b M), mul_assoc,
    Ring.mul_inverse_cancel _ (isUnit_FP c ha b M), mul_one]

/-! ### the even part of Euler's expansion -/

lemma expand_injective (e : ℕ) (he : e ≠ 0) {f g : PowerSeries ℤ} (h : expand e he f = expand e he g) : f = g := by
  ext k
  have := congrArg (coeff (e * k)) h
  rwa [coeff_expand_mul, coeff_expand_mul] at this

lemma expand_QI (e : ℕ) (he : e ≠ 0) (b n : ℕ) (hb : 1 ≤ b) : expand e he (QI b n) = QI (e * b) n := by
  rw [QI, expand_inverse e he (isUnit_FP 1 hb b n)]
  exact congrArg Ring.inverse (expand_FP e he 1 b b n)

lemma coeff_intCast_mul (r : ℤ) (f : PowerSeries ℤ) (k : ℕ) :
    coeff k ((r : PowerSeries ℤ) * f) = r * coeff k f := by
  rw [show (r : PowerSeries ℤ) = C r by simp, coeff_C_mul]

/-- the even part of `Σ_k (±1)ᵏ tᵏ`-type sums: `Σ_k (1 + (−1)ᵏ) u k = 2 Σ_n u (2n)`. -/
lemma osum_even_part {u : ℕ → PowerSeries ℤ} (hu : LF u) :
    osum (fun k => ((1 + (-1) ^ k : ℤ) : PowerSeries ℤ) * u k) = 2 * osum (fun n => u (2 * n)) := by
  have hv : LF (fun k => ((1 + (-1) ^ k : ℤ) : PowerSeries ℤ) * u k) := by
    intro k
    refine (hu k).subset fun i hi => ?_
    simp only [Function.mem_support, ne_eq, coeff_intCast_mul] at hi ⊢
    intro h; apply hi; simp [h]
  rw [osum_parity hv]
  have h1 : (osum fun n => ((1 + (-1) ^ (2 * n + 1) : ℤ) : PowerSeries ℤ) * u (2 * n + 1)) = 0 := by
    rw [← osum_zero (ι := ℕ)]; refine osum_ext fun n => ?_; simp [pow_succ, pow_mul]
  have hu2 : LF (fun n => u (2 * n)) := hu.comp_injective (e := fun n => 2 * n) (fun a b h => by simp only at h; omega)
  rw [h1, add_zero, ← osum_smul (2 : PowerSeries ℤ) hu2]
  refine osum_ext fun n => ?_
  simp [pow_mul]

lemma choose_two_mul (p : ℕ) : (2 * p).choose 2 = p * (2 * p - 1) := by
  rw [Nat.choose_two_right]
  rcases p with _ | p
  · simp
  · rw [show 2 * (p + 1) - 1 = 2 * p + 1 by omega, show 2 * (p + 1) * (2 * p + 1) = 2 * ((p + 1) * (2 * p + 1)) by ring]
    simp

/-- **the even part of Euler** (Watson's half-integer step):
`(X^c; X²)_∞ · Σ_n X^{cn}/(q;q)_{2n} = Σ_p X^{cp + C(2p,2)}/(q;q)_{2p}`. -/
theorem euler_even {c : ℕ} (hc : 1 ≤ c) :
    IP 1 c 2 * osum (fun n => X ^ (c * n) * QI 1 (2 * n)) =
      osum (fun p => X ^ (c * p + (2 * p).choose 2) * QI 1 (2 * p)) := by
  have h2 : (2 : ℕ) ≠ 0 := two_ne_zero
  set T : PowerSeries ℤ →ₐ[ℤ] PowerSeries ℤ := expand 2 h2
  have hA : LF (fun n => X ^ (c * n) * QI 1 (2 * n) : ℕ → PowerSeries ℤ) :=
    LF.of_nat fun n k hk => by rw [coeff_X_pow_mul', if_neg (by nlinarith)]
  have hB : LF (fun p => X ^ (c * p + (2 * p).choose 2) * QI 1 (2 * p) : ℕ → PowerSeries ℤ) :=
    LF.of_nat fun n k hk => by rw [coeff_X_pow_mul', if_neg (by nlinarith)]
  -- `q ↦ q²` images
  have TA : T (osum fun n => X ^ (c * n) * QI 1 (2 * n)) = osum fun n => X ^ (c * (2 * n)) * QI 2 (2 * n) := by
    rw [expand_osum 2 h2 hA]
    refine osum_ext fun n => ?_
    rw [map_mul, map_pow, expand_X, expand_QI 2 h2 1 _ le_rfl, ← pow_mul]; ring_nf
  have TB : T (osum fun p => X ^ (c * p + (2 * p).choose 2) * QI 1 (2 * p)) =
      osum fun p => X ^ (c * (2 * p) + 2 * (2 * p).choose 2) * QI 2 (2 * p) := by
    rw [expand_osum 2 h2 hB]
    refine osum_ext fun n => ?_
    rw [map_mul, map_pow, expand_X, expand_QI 2 h2 1 _ le_rfl, ← pow_mul]; ring_nf
  -- the two Euler expansions in base `q²`
  have hGsum : GI 1 c 2 + GI (-1) c 2 = 2 * T (osum fun n => X ^ (c * n) * QI 1 (2 * n)) := by
    rw [TA, GI, GI, ← osum_add (LF_gI 1 hc 2) (LF_gI (-1) hc 2)]
    have hu : LF (fun k => X ^ (c * k) * QI 2 k : ℕ → PowerSeries ℤ) :=
      LF.of_nat fun n k hk => by rw [coeff_X_pow_mul', if_neg (by nlinarith)]
    rw [← osum_even_part hu]
    refine osum_ext fun k => ?_
    simp only [gI]; push_cast; ring
  have hHsum : HP 1 c 2 + HP (-1) c 2 = 2 * T (osum fun p => X ^ (c * p + (2 * p).choose 2) * QI 1 (2 * p)) := by
    rw [TB, HP, HP, ← osum_add (LF_hP 1 hc 2) (LF_hP (-1) hc 2)]
    have hu : LF (fun k => X ^ (c * k + 2 * k.choose 2) * QI 2 k : ℕ → PowerSeries ℤ) :=
      LF.of_nat fun n k hk => by rw [coeff_X_pow_mul', if_neg (by nlinarith)]
    rw [← osum_even_part hu]
    refine osum_ext fun k => ?_
    simp only [hP]; push_cast; ring_nf
  -- combine
  have u1 := isUnit_IP 1 hc (show 1 ≤ 2 by norm_num)
  have u2 := isUnit_IP (-1) hc (show 1 ≤ 2 by norm_num)
  have hsq : IP 1 c 2 * IP (-1) c 2 = T (IP 1 c 2) := by
    rw [IP_sq 1 hc (show 1 ≤ 2 by norm_num), expand_IP 2 h2 1 hc (show 1 ≤ 2 by norm_num)]; norm_num
  have key : T (IP 1 c 2) * (2 * T (osum fun n => X ^ (c * n) * QI 1 (2 * n))) =
      2 * T (osum fun p => X ^ (c * p + (2 * p).choose 2) * QI 1 (2 * p)) := by
    rw [← hGsum, ← hHsum, ← euler_prod 1 hc (by norm_num), ← euler_prod (-1) hc (by norm_num),
      GI_eq 1 hc (by norm_num), GI_eq (-1) hc (by norm_num), ← hsq]
    have e1 := Ring.mul_inverse_cancel _ u1
    have e2 := Ring.mul_inverse_cancel _ u2
    linear_combination (IP (-1) c 2) * e1 + (IP 1 c 2) * e2
  apply expand_injective 2 h2
  rw [map_mul]
  have h2ne : (2 : PowerSeries ℤ) ≠ 0 := by
    intro h
    have := congrArg (coeff 0) h
    rw [show (2 : PowerSeries ℤ) = C 2 by simp, coeff_C, if_pos rfl, map_zero] at this
    norm_num at this
  apply mul_left_cancel₀ h2ne
  rw [← key]; ring

end Watson
