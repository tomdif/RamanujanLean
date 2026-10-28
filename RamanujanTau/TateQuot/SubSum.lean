/-
# Sums over the nonzero points of `⟨s⟩ ⊂ Tate(s^p)`

* `euler`: `θ^m(w/(1−w)²) = Σ_r r^{m+1} w^r`, i.e. `cpoly m (w) = (1−w)^{m+2} Σ_r r^{m+1} w^r` (`m = 0,2,4`).
* `coeff_tB`: `[s^M] θ^m x(s^k) = Σ_{d ∣ M} d^{m+1} ([M/d ≡ k] + [M/d ≡ −k]) − 2[m=0][p∣M] σ₁(M/p)`.
* `tB0_sym`: `x(s^{p−k}) = x(s^k)`.
* `SB_eq`: `Σ_{k=1}^{p−1} θ^m x(s^k) = 2σ_{m+1}(s) − 2σ_{m+1}(s^p) − 2(p−1)[m=0] σ₁(s^p)`.
-/
import RamanujanTau.TateQuot.SubSeries
import RamanujanTau.TateQuot.SubComb
import RamanujanTau.TateQuot.MuSum

set_option autoImplicit false

noncomputable section

namespace TateQuot

open PowerSeries Finset
open scoped ArithmeticFunction.sigma

local notation "aX" => (Polynomial.X : P)

variable {K : Type*} [Field K] [CharZero K]

/-- `Σ_r r^{m+1} w^r`. -/
def gm (K : Type*) [Field K] (m : ℕ) : PowerSeries K := mk fun r => (r : K) ^ (m + 1)

lemma coeff_rhs (m n : ℕ) : coeff n ((1 - X) ^ (m + 2) * gm K m) =
    ∑ i ∈ range (n + 1), (-1) ^ i * ((m + 2).choose i : K) * ((n - i : ℕ) : K) ^ (m + 1) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => coeff a ((1 - X : PowerSeries K) ^ (m + 2)) * coeff b (gm K m))]
  refine sum_congr rfl fun i _ => ?_
  rw [coeff_one_sub_X_pow, gm, coeff_mk]

lemma euler0 : φk K 1 (cpoly 0) = (1 - X) ^ (0 + 2) * gm K 0 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_rhs]
  simp only [cpoly, φk, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X, pow_one,
    coeff_X]
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> simp [sum_range_succ, Nat.choose]
  · rw [← sum_range_add_sum_Ico _ (by omega : 3 ≤ n + 1),
      sum_eq_zero (s := Ico 3 (n + 1)) fun i hi => by
        rw [mem_Ico] at hi; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp]
    simp only [sum_range_succ, sum_range_zero]
    rw [if_neg (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega]
    simp [Nat.choose]
    ring

lemma φ1_cpoly2 : φk K 1 (cpoly 2) = C 1 * X ^ 1 + C 4 * X ^ 2 + C 1 * X ^ 3 := by
  rw [show (C 4 : PowerSeries K) = 4 from map_ofNat _ 4, map_one]
  simp [φk, cpoly, map_ofNat]; ring

lemma euler2 : φk K 1 (cpoly 2) = (1 - X) ^ (2 + 2) * gm K 2 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_rhs, φ1_cpoly2]
  simp only [map_add, coeff_C_mul, coeff_X_pow]
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp [sum_range_succ, Nat.choose] <;> norm_num
  · rw [← sum_range_add_sum_Ico _ (by omega : 5 ≤ n + 1),
      sum_eq_zero (s := Ico 5 (n + 1)) fun i hi => by
        rw [mem_Ico] at hi; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp]
    simp only [sum_range_succ, sum_range_zero]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega]
    simp [Nat.choose]
    ring

lemma φ1_cpoly4 : φk K 1 (cpoly 4) =
    C 1 * X ^ 1 + C 26 * X ^ 2 + C 66 * X ^ 3 + C 26 * X ^ 4 + C 1 * X ^ 5 := by
  rw [show (C 26 : PowerSeries K) = 26 from map_ofNat _ 26,
    show (C 66 : PowerSeries K) = 66 from map_ofNat _ 66, map_one]
  simp [φk, cpoly, map_ofNat]; ring

lemma euler4 : φk K 1 (cpoly 4) = (1 - X) ^ (4 + 2) * gm K 4 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_rhs, φ1_cpoly4]
  simp only [map_add, coeff_C_mul, coeff_X_pow]
  rcases Nat.lt_or_ge n 7 with h | h
  · interval_cases n <;> simp [sum_range_succ, Nat.choose] <;> norm_num
  · rw [← sum_range_add_sum_Ico _ (by omega : 7 ≤ n + 1),
      sum_eq_zero (s := Ico 7 (n + 1)) fun i hi => by
        rw [mem_Ico] at hi; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp]
    simp only [sum_range_succ, sum_range_zero]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show 5 ≤ n by omega, show 6 ≤ n by omega]
    simp [Nat.choose]
    ring

lemma φk_eq_expand {k : ℕ} (hk : k ≠ 0) (c : P) :
    φk K k c = PowerSeries.expand k hk (φk K 1 c) := by
  have : φk K k = (PowerSeries.expand (R := K) k hk).toRingHom.comp (φk K 1) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [φk]
    · simp [φk]
  rw [this]; rfl

variable {p : ℕ} [hp : Fact p.Prime]

lemma evB_zB_split (k : ℕ) (m : ℕ) :
    evB K k (p - k) (zB m) = φk K k (cpoly m) + Us K k ^ (m + 2) * evB K k (p - k) (mk (Rm m)) := by
  rw [zB, map_add, map_mul, evB_C, evB_C]
  congr 2
  simp [φk, Us]

lemma tB_eq {m : ℕ} (hm : m = 0 ∨ m = 2 ∨ m = 4) {k : ℕ} (hk1 : 1 ≤ k) :
    tB K p m k = PowerSeries.expand k (by omega) (gm K m) + evB K k (p - k) (mk (Rm m)) := by
  have he : φk K 1 (cpoly m) = (1 - X) ^ (m + 2) * gm K m := by
    rcases hm with rfl | rfl | rfl
    · exact euler0
    · exact euler2
    · exact euler4
  have hev : Even (m + 2) := by rcases hm with rfl | rfl | rfl <;> decide
  have hφ : φk K k (cpoly m) = Us K k ^ (m + 2) * PowerSeries.expand k (by omega) (gm K m) := by
    rw [φk_eq_expand (by omega), he, map_mul, map_pow, map_sub, map_one, PowerSeries.expand_X, Us,
      ← hev.neg_pow, neg_sub]
  rw [tB, evB_zB_split, hφ, ← mul_add, mul_comm, ← mul_assoc,
    PowerSeries.inv_mul_cancel _ (cc_Us_pow hk1 _), one_mul]

lemma coeff_expand_gm {k : ℕ} (hk : k ≠ 0) (m M : ℕ) :
    coeff M (PowerSeries.expand k hk (gm K m)) = if k ∣ M then ((M / k : ℕ) : K) ^ (m + 1) else 0 := by
  rw [coeff_expand, gm]
  split_ifs <;> simp

lemma coeff_natpow_X (d j a M : ℕ) :
    coeff M ((d : PowerSeries K) ^ j * X ^ a) = (d : K) ^ j * if a = M then 1 else 0 := by
  rw [← map_natCast (C (R := K)), ← map_pow, coeff_C_mul, coeff_X_pow]
  split_ifs <;> simp_all

lemma coeff_natpow_two_X (d j a M : ℕ) :
    coeff M ((d : PowerSeries K) ^ j * (2 * X ^ a)) = 2 * ((d : K) ^ j * if a = M then 1 else 0) := by
  rw [mul_left_comm, show (2 : PowerSeries K) = C 2 from (map_ofNat C 2).symm, coeff_C_mul,
    coeff_natpow_X]

lemma coeff_evB_Rm {m : ℕ} (hm : Even m) {k : ℕ} (hk : k < p) (M : ℕ) :
    coeff M (evB K k (p - k) (mk (Rm m))) =
      ∑ N ∈ range (M + 1), ∑ d ∈ N.divisors, (d : K) ^ (m + 1) *
        ((if k * (N + d) + (p - k) * N = M then 1 else 0) +
          (if k * (N - d) + (p - k) * N = M then 1 else 0)) -
      (if m = 0 then 2 else 0) * ∑ N ∈ range (M + 1), ∑ d ∈ N.divisors, (d : K) ^ (m + 1) *
        (if p * N = M then 1 else 0) := by
  rw [coeff_evB k (p - k) (by omega), mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun N _ => ?_
  rw [coeff_mk, Rm, map_sum, sum_mul, map_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun d _ => ?_
  have hpN : k * N + (p - k) * N = p * N := by rw [← add_mul, Nat.add_sub_cancel' hk.le]
  by_cases h0 : m = 0
  · subst h0
    simp only [if_true, RingHom.map_mul (φk K k), RingHom.map_add (φk K k),
      RingHom.map_sub (φk K k), RingHom.map_pow (φk K k), φk_aX, map_natCast, pow_zero, one_mul,
      map_ofNat]
    simp only [← pow_mul, mul_add, mul_sub, add_mul, sub_mul, mul_assoc, ← pow_add, map_add,
      map_sub, coeff_natpow_X, coeff_natpow_two_X, hpN]
  · simp only [h0, if_false, zero_mul, sub_zero, RingHom.map_mul (φk K k),
      RingHom.map_add (φk K k), RingHom.map_pow (φk K k), φk_aX, map_natCast, hm.neg_one_pow,
      one_mul]
    simp only [← pow_mul, mul_add, add_mul, mul_assoc, ← pow_add, map_add, coeff_natpow_X]

lemma cpart (j M : ℕ) :
    ∑ N ∈ range (M + 1), ∑ d ∈ N.divisors, (d : K) ^ j * (if p * N = M then 1 else 0) =
      if p ∣ M then (σ j (M / p) : K) else 0 := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [sum_congr rfl fun N _ => (sum_ite_irrel ..)]
  simp_rw [sum_const_zero]
  split_ifs with h
  · obtain ⟨c, rfl⟩ := h
    simp only [mul_right_inj' hp.out.ne_zero]
    rw [sum_ite_eq', if_pos (by
      have := Nat.le_mul_of_pos_left c hp.out.pos; simp only [mem_range]; omega),
      Nat.mul_div_cancel_left _ hp.out.pos, sigma_cast]
  · refine sum_eq_zero fun N _ => ?_
    rw [if_neg]; rintro rfl; exact h (dvd_mul_right p N)

/-- **The coefficients of `θ^m x(s^k)`.** -/
theorem coeff_tB {m : ℕ} (hm : m = 0 ∨ m = 2 ∨ m = 4) {k : ℕ} (hk : k ∈ Ico 1 p) (M : ℕ) :
    coeff M (tB K p m k) = ∑ d ∈ M.divisors, (d : K) ^ (m + 1) * br p (M / d) k -
      (if m = 0 then 2 else 0) * (if p ∣ M then (σ (m + 1) (M / p) : K) else 0) := by
  have hk' := mem_Ico.mp hk
  have hev : Even m := by rcases hm with rfl | rfl | rfl <;> decide
  rw [tB_eq hm hk'.1, map_add, coeff_expand_gm, coeff_evB_Rm hev hk'.2, cpart, ← add_sub_assoc,
    comb_k hp.out.two_le (fun d => (d : K) ^ (m + 1)) (by simp) M hk]

/-- `x(s^{p−k}) = x(s^k)`. -/
theorem tB0_sym {k : ℕ} (hk : k ∈ Ico 1 p) : tB K p 0 (p - k) = tB K p 0 k := by
  have hk' : p - k ∈ Ico 1 p := by rw [mem_Ico] at hk ⊢; omega
  refine PowerSeries.ext fun M => ?_
  rw [coeff_tB (Or.inl rfl) hk', coeff_tB (Or.inl rfl) hk]
  simp only [br_sym hk]

omit hp in
lemma sum_dvd_div (g : ℕ → K) (M : ℕ) (q : ℕ) (hq : 0 < q) :
    ∑ e ∈ M.divisors, (if q ∣ e then g e else 0) =
      if q ∣ M then ∑ e ∈ (M / q).divisors, g (q * e) else 0 := by
  split_ifs with hM
  · obtain ⟨M', rfl⟩ := hM
    rw [Nat.mul_div_cancel_left _ hq, ← sum_filter]
    have hset : (q * M').divisors.filter (q ∣ ·) = M'.divisors.image (q * ·) := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, mem_image]
      constructor
      · rintro ⟨⟨h1, h2⟩, e, rfl⟩
        exact ⟨e, ⟨(Nat.mul_dvd_mul_iff_left hq).mp h1, by rintro rfl; simp at h2⟩, rfl⟩
      · rintro ⟨e, ⟨h1, h2⟩, rfl⟩
        exact ⟨⟨mul_dvd_mul_left q h1, mul_ne_zero (by omega) h2⟩, dvd_mul_right _ _⟩
    rw [hset, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hq h)]
  · refine sum_eq_zero fun e he => ?_
    rw [if_neg]
    intro hqe; exact hM (hqe.trans (Nat.dvd_of_mem_divisors he))

lemma divsum_compl (j M : ℕ) :
    ∑ d ∈ M.divisors, (d : K) ^ j * (if p ∣ M / d then 0 else 2) =
      2 * (σ j M : K) - 2 * (if p ∣ M then (σ j (M / p) : K) else 0) := by
  have h1 : ∑ d ∈ M.divisors, (d : K) ^ j * (if p ∣ M / d then 0 else 2) =
      2 * ∑ d ∈ M.divisors, (d : K) ^ j -
        2 * ∑ d ∈ M.divisors, (if p ∣ M / d then ((M / (M / d) : ℕ) : K) ^ j else 0) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun d hd => ?_
    have hdM := Nat.dvd_of_mem_divisors hd
    have hM0 : M ≠ 0 := (Nat.mem_divisors.mp hd).2
    rw [Nat.div_div_self hdM hM0]
    split_ifs <;> ring
  rw [h1, Nat.sum_div_divisors M (fun e => if p ∣ e then ((M / e : ℕ) : K) ^ j else 0),
    sum_dvd_div _ M p hp.out.pos, sigma_cast]
  congr 2
  split_ifs with h
  · rw [sigma_cast]
    conv_rhs => rw [← Nat.sum_div_divisors]
    refine sum_congr rfl fun e _ => ?_
    rw [Nat.div_div_eq_div_mul]
  · rfl

/-- `Σ_{k=1}^{p−1} θ^m x(s^k)`. -/
def SB (K : Type*) [Field K] (p m : ℕ) : PowerSeries K := ∑ k ∈ Ico 1 p, tB K p m k

/-- **`Σ_k θ^m x(s^k) = 2σ_{m+1}(s) − 2σ_{m+1}(s^p) − 2(p−1)[m=0]σ₁(s^p)`.** -/
theorem SB_eq {m : ℕ} (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    SB K p m = C 2 * sigK K (m + 1) -
      C (2 + (if m = 0 then 2 else 0) * ((p : K) - 1)) *
        PowerSeries.expand p hp.out.ne_zero (sigK K (m + 1)) := by
  refine PowerSeries.ext fun M => ?_
  rw [SB, map_sum, sum_congr rfl fun k hk => coeff_tB hm hk M, sum_sub_distrib, sum_comm,
    sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hp.out.one_le, Nat.cast_one]
  have hbr : ∀ d : ℕ, (d : K) ^ (m + 1) * ∑ i ∈ Ico 1 p, br p (M / d) i =
      (d : K) ^ (m + 1) * (if p ∣ M / d then 0 else 2) := fun d => by
    simp only [br]; rw [count_k hp.out.two_le]
  rw [sum_congr rfl fun d _ => by rw [← mul_sum, hbr], divsum_compl]
  rw [map_sub, coeff_C_mul, coeff_C_mul, coeff_sigK, coeff_expand]
  split_ifs with h1 h2
  · rw [coeff_sigK]; ring
  · rw [coeff_sigK]; ring
  · ring
  · ring

end TateQuot
