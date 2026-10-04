/-
# Jacobi's four-square theorem

  `r₄(N) = #{(a,b,c,d) ∈ ℤ⁴ : a²+b²+c²+d² = N} = 8 Σ_{d ∣ N, 4 ∤ d} d`   (`N ≥ 1`).

* `FourSquaresWZ`: a terminating specialization of Jackson's ₈φ₇ summation, proved by a WZ certificate.
* `FourSquaresLimit`: its limit `((−q;q)_∞/(q;q)_∞)⁴ (1 + 8 Σ_{k≥1} (−1)^k q^k/(1+q^k)²) = 1`.
* This file: `(q;q)_∞/(−q;q)_∞ = J_{2,1} = Σ_m (−1)^m q^{m²}` (Jacobi triple product `jtp_ab 2 1`), so
  `φ(−q)⁴ = 1 + 8 Σ (−1)^k q^k/(1+q^k)²`. Comparing coefficients gives `(−1)^N r₄(N)` on the left and a
  signed divisor sum on the right.
-/
import RamanujanTau.FourSquaresLimit
import RamanujanTau.RankTheta

set_option autoImplicit false

namespace FourSquares
open PowerSeries Finset MockTheta5.Bailey MockTheta5.JTP
open RankProof (Pinf Pfin Pfin_succ X_pow_dvd_Pinf_sub X_pow_dvd_Pfin_sub Pinf_ext Pinf_one_one thetaS jtp_ab thA thB
  thetaTr thetaTr_eq thetaS_dvd)

lemma π_Pinf {b a : ℕ} (hb : 1 ≤ b) (ha : 1 ≤ a) (N : ℕ) : π (N + 1) (Pinf b a) = π (N + 1) (Pfin b a N) :=
  π_eq_iff.mpr (X_pow_dvd_Pinf_sub b a hb ha N)

lemma Pfin_split2 : ∀ N, Pfin 1 1 (2 * N) = Pfin 1 2 N * Pfin 2 2 N
  | 0 => by simp [Pfin]
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Pfin_succ, Pfin_succ, Pfin_split2 N, Pfin_succ, Pfin_succ]
    ring_nf

lemma Pinf_split2 : Pinf 1 1 = Pinf 1 2 * Pinf 2 2 := by
  symm
  refine Pinf_ext le_rfl le_rfl fun N => ?_
  rw [← π_eq_iff, map_mul, π_Pinf (by norm_num) (by norm_num), π_Pinf (by norm_num) (by norm_num), ← map_mul,
    ← Pfin_split2, π_eq_iff]
  exact X_pow_dvd_Pfin_sub 1 1 N le_rfl le_rfl (2 * N) (by omega)

lemma mfac_qfac (N : ℕ) : mfac N * qfac N = Pfin 2 2 N := by
  induction N with
  | zero => simp [mfac, qfac, Pfin]
  | succ N ih =>
    rw [mfac_succ, qfac_succ', Pfin_succ, ← ih]; ring_nf

lemma mfacInf_qfacInf : mfacInf * qfacInf = Pinf 2 2 := by
  refine Pinf_ext (by norm_num) (by norm_num) fun N => ?_
  rw [← π_eq_iff, map_mul, ← π_mfac (show N + 1 ≤ N + 1 by omega), ← π_qfac (show N + 1 ≤ N + 1 by omega),
    ← map_mul, mfac_qfac, π_eq_iff]
  exact X_pow_dvd_Pfin_sub 2 2 N (by norm_num) (by norm_num) (N + 1) (by omega)

lemma isUnit_Pinf {b a : ℕ} (hb : 1 ≤ b) (ha : 1 ≤ a) : IsUnit (Pinf b a) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply,
    coeff_eq_of_dvd (X_pow_dvd_Pinf_sub b a hb ha 0) (Nat.zero_lt_one), Pfin]
  simp

/-- **Gauss**: `φ(−q) = Σ_m (−1)^m q^{m²} = (q;q)_∞/(−q;q)_∞`, i.e. `φ(−q)·(−q;q)_∞ = (q;q)_∞`. -/
lemma theta_mul_mfacInf : thetaS 2 1 * mfacInf = qfacInf := by
  have hj := jtp_ab 2 1 (by norm_num) (by norm_num)
  have hs := Pinf_split2
  rw [Pinf_one_one] at hs
  have hm := mfacInf_qfacInf
  rw [hs] at hm
  -- `(−q;q)_∞ (q;q²)_∞ = 1`
  have h1 : mfacInf * Pinf 1 2 = 1 := by
    have hu := isUnit_Pinf (b := 2) (a := 2) (by norm_num) (by norm_num)
    apply hu.mul_left_cancel
    linear_combination hm
  rw [← hj, hs]
  norm_num
  linear_combination (Pinf 1 2 * Pinf 2 2) * h1

/-- **`φ(−q)⁴ = 1 + 8 Σ_{k≥1} (−1)^k q^k/(1+q^k)²`**. -/
theorem theta_pow_four : thetaS 2 1 ^ 4 = 1 + 8 * Lser := by
  have hl := limit_identity
  have ht := theta_mul_mfacInf
  have hq : qfacInf ^ 4 * Ring.inverse (qfacInf ^ 4) = 1 := Ring.mul_inverse_cancel _ (isUnit_qfacInf.pow 4)
  calc thetaS 2 1 ^ 4 = thetaS 2 1 ^ 4 * (mfacInf ^ 4 * Ring.inverse (qfacInf ^ 4) * (1 + 8 * Lser)) := by
        rw [hl, mul_one]
    _ = (thetaS 2 1 * mfacInf) ^ 4 * Ring.inverse (qfacInf ^ 4) * (1 + 8 * Lser) := by ring
    _ = 1 + 8 * Lser := by rw [ht, hq, one_mul]


/-! ## coefficients of the Lambert series -/

/-- `1/(1+q^k)² = Σ_m (−1)^m (m+1) q^{km}`. -/
noncomputable def hser (k : ℕ) : PowerSeries ℤ :=
  mk fun j => if k ∣ j then (-1) ^ (j / k) * ((j / k : ℕ) + 1 : ℤ) else 0

lemma hser_eval {k : ℕ} (hk : 1 ≤ k) (m r : ℕ) (hr : r < k) :
    coeff (k * m + r) (hser k) = if r = 0 then (-1) ^ m * ((m : ℤ) + 1) else 0 := by
  rw [hser, coeff_mk]
  have hdiv : (k * m + r) / k = m := by
    rw [add_comm, Nat.add_mul_div_left r m (by omega), Nat.div_eq_of_lt hr, zero_add]
  have hdvd : k ∣ k * m + r ↔ r = 0 := by
    rw [Nat.dvd_add_right (dvd_mul_right k m)]
    exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hr, fun h => h ▸ dvd_zero k⟩
  by_cases h0 : r = 0
  · rw [if_pos (hdvd.mpr h0), if_pos h0, hdiv]
  · rw [if_neg (fun h => h0 (hdvd.mp h)), if_neg h0]

lemma sq_mul_hser {k : ℕ} (hk : 1 ≤ k) : (1 + X ^ k) ^ 2 * hser k = 1 := by
  ext j
  rw [show (1 + X ^ k : PowerSeries ℤ) ^ 2 * hser k = hser k + 2 * (X ^ k * hser k) + X ^ (k + k) * hser k by
    rw [pow_add]; ring]
  rw [map_add, map_add, show (2 : PowerSeries ℤ) = C 2 by simp, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul',
    coeff_one]
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < k ∧ j = k * m + r :=
    ⟨j / k, j % k, Nat.mod_lt _ (by omega), (Nat.div_add_mod j k).symm⟩
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · rw [if_neg (show ¬ k ≤ k * 0 + r by omega), if_neg (show ¬ k + k ≤ k * 0 + r by omega), hser_eval hk 0 r hr]
      by_cases h0 : r = 0 <;> simp [h0]
    · rw [if_pos (show k ≤ k * 1 + r by omega), if_neg (show ¬ k + k ≤ k * 1 + r by omega),
        show k * 1 + r - k = k * 0 + r by omega, hser_eval hk 0 r hr, hser_eval hk 1 r hr,
        if_neg (show k * 1 + r ≠ 0 by omega)]
      by_cases h0 : r = 0 <;> simp [h0]
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    have e1 : k * (m + 2) + r - k = k * (m + 1) + r := by rw [Nat.mul_add, Nat.mul_add]; omega
    have e2 : k * (m + 2) + r - (k + k) = k * m + r := by rw [Nat.mul_add]; omega
    rw [if_pos (show k ≤ k * (m + 2) + r by nlinarith), if_pos (show k + k ≤ k * (m + 2) + r by nlinarith),
      if_neg (show k * (m + 2) + r ≠ 0 by nlinarith), e1, e2, hser_eval hk (m + 2) r hr, hser_eval hk (m + 1) r hr,
      hser_eval hk m r hr]
    by_cases h0 : r = 0
    · simp only [h0, if_true]; push_cast; ring
    · simp [h0]


lemma inverse_eq_of_mul' {a b : PowerSeries ℤ} (h : a * b = 1) : Ring.inverse a = b := by
  have ha : IsUnit a := ⟨⟨a, b, h, by rw [mul_comm]; exact h⟩, rfl⟩
  calc Ring.inverse a = Ring.inverse a * (a * b) := by rw [h, mul_one]
    _ = b := by rw [← mul_assoc, Ring.inverse_mul_cancel a ha, one_mul]

lemma coeff_tk {k N : ℕ} (hk : 1 ≤ k) (hN : 1 ≤ N) :
    coeff N (tk k) = if k ∣ N then (-1) ^ k * ((-1) ^ (N / k - 1) * ((N / k : ℕ) : ℤ)) else 0 := by
  rw [tk, inverse_eq_of_mul' (sq_mul_hser hk), mul_assoc, show ((-1 : PowerSeries ℤ) ^ k) = C ((-1) ^ k) by simp,
    coeff_C_mul, coeff_X_pow_mul']
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < k ∧ N = k * m + r :=
    ⟨N / k, N % k, Nat.mod_lt _ (by omega), (Nat.div_add_mod N k).symm⟩
  have hdvd : k ∣ k * m + r ↔ r = 0 := by
    rw [Nat.dvd_add_right (dvd_mul_right k m)]
    exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hr, fun h => h ▸ dvd_zero k⟩
  have hdiv : (k * m + r) / k = m := by
    rw [add_comm, Nat.add_mul_div_left r m (by omega), Nat.div_eq_of_lt hr, zero_add]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [if_neg (show ¬ k ≤ k * 0 + r by omega), if_neg (fun h => by
      have := hdvd.mp h; omega), mul_zero]
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [if_pos (show k ≤ k * (m + 1) + r by nlinarith),
      show k * (m + 1) + r - k = k * m + r by rw [Nat.mul_succ]; omega, hser_eval hk m r hr, hdiv]
    by_cases h0 : r = 0
    · rw [if_pos h0, if_pos (hdvd.mpr h0), Nat.add_sub_cancel]; push_cast; ring
    · rw [if_neg h0, if_neg (fun h => h0 (hdvd.mp h)), mul_zero]

lemma sum_range_dvd (f : ℕ → ℤ) {k N : ℕ} (hk : 1 ≤ k) (hN : k ≤ N) :
    ∑ i ∈ range N, (if i + 1 ∣ k then f (i + 1) else 0) = ∑ d ∈ k.divisors, f d := by
  rw [Nat.divisors, sum_filter, sum_Ico_eq_sum_range, show k + 1 - 1 = k by omega]
  rw [show N = k + (N - k) by omega, sum_range_add]
  rw [sum_eq_zero (s := range (N - k)) (fun i _ => if_neg (fun h => by have := Nat.le_of_dvd hk h; omega)),
    add_zero]
  exact sum_congr rfl fun i _ => by rw [add_comm 1 i]

lemma coeff_Lser {N : ℕ} (hN : 1 ≤ N) :
    coeff N Lser = ∑ d ∈ N.divisors, (-1) ^ (N / d) * ((-1) ^ (d - 1) * (d : ℤ)) := by
  rw [Lser, coeff_mk, map_sum]
  rw [sum_congr rfl fun i _ => coeff_tk (k := i + 1) (by omega) hN]
  rw [sum_range_dvd (fun d => (-1) ^ d * ((-1) ^ (N / d - 1) * ((N / d : ℕ) : ℤ))) hN le_rfl]
  rw [← Nat.sum_div_divisors N (fun e => (-1) ^ (N / e) * ((-1) ^ (e - 1) * (e : ℤ)))]
  refine sum_congr rfl fun d hd => ?_
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) (by omega)]

/-! ## the divisor identity -/

lemma neg_one_pow_even {n : ℕ} (h : Even n) : (-1 : ℤ) ^ n = 1 := h.neg_one_pow
lemma neg_one_pow_odd {n : ℕ} (h : Odd n) : (-1 : ℤ) ^ n = -1 := h.neg_one_pow

/-- the divisors of `2M` are the odd divisors of `M` and the doubles of the divisors of `M`. -/
lemma sum_divisors_two_mul {M : ℕ} (hM : 1 ≤ M) (f : ℕ → ℤ) :
    ∑ d ∈ (2 * M).divisors, f d = ∑ d ∈ M.divisors.filter Odd, f d + ∑ e ∈ M.divisors, f (2 * e) := by
  rw [← sum_filter_add_sum_filter_not _ Odd]
  congr 1
  · congr 1
    ext d
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨⟨Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr h2) h1, by omega⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨⟨dvd_mul_of_dvd_right h1 2, by omega⟩, h2⟩
  · have : (2 * M).divisors.filter (fun d => ¬ Odd d) = M.divisors.image (2 * ·) := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, mem_image, Nat.not_odd_iff_even]
      constructor
      · rintro ⟨⟨h1, -⟩, ⟨e, rfl⟩⟩
        refine ⟨e, ⟨?_, by omega⟩, by ring⟩
        rw [← two_mul] at h1
        exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp h1
      · rintro ⟨e, ⟨h1, -⟩, rfl⟩
        exact ⟨⟨Nat.mul_dvd_mul_left 2 h1, by omega⟩, ⟨e, by ring⟩⟩
    rw [this, sum_image fun a _ b _ h => by simpa using h]

/-- the odd-divisor sum. -/
noncomputable def oddSigma (M : ℕ) : ℤ := ∑ d ∈ M.divisors.filter Odd, (d : ℤ)

lemma oddSigma_two_mul {M : ℕ} (hM : 1 ≤ M) : oddSigma (2 * M) = oddSigma M := by
  rw [oddSigma, sum_filter, sum_divisors_two_mul hM, oddSigma]
  rw [sum_eq_zero (s := M.divisors) fun e _ => if_neg (by simp [Nat.not_odd_iff_even]), add_zero,
    sum_filter, sum_filter]
  exact sum_congr rfl fun d _ => by split_ifs <;> rfl

/-- `Σ_{e ∣ M} (−1)^{M/e+1} e = Σ_{e ∣ M, e odd} e`. -/
lemma star (M : ℕ) (hM : 1 ≤ M) :
    ∑ e ∈ M.divisors, (-1 : ℤ) ^ (M / e + 1) * e = oddSigma M := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    rcases Nat.even_or_odd M with ⟨K, hK⟩ | hodd
    · have hK2 : M = 2 * K := by omega
      subst hK2
      have hK1 : 1 ≤ K := by omega
      rw [sum_divisors_two_mul hK1, oddSigma_two_mul hK1]
      have h1 : ∑ d ∈ K.divisors.filter Odd, (-1 : ℤ) ^ (2 * K / d + 1) * (d : ℤ) = -oddSigma K := by
        rw [oddSigma, ← sum_neg_distrib]
        refine sum_congr rfl fun d hd => ?_
        rw [mem_filter, Nat.mem_divisors] at hd
        rw [Nat.mul_div_assoc 2 hd.1.1, neg_one_pow_odd (by
          rw [Nat.odd_add_one, Nat.not_odd_iff_even]; exact even_two_mul _)]
        ring
      have h2 : ∑ e ∈ K.divisors, (-1 : ℤ) ^ (2 * K / (2 * e) + 1) * ((2 * e : ℕ) : ℤ) = 2 * oddSigma K := by
        rw [← ih K (by omega) hK1, mul_sum]
        refine sum_congr rfl fun e he => ?_
        rw [Nat.mul_div_mul_left _ _ (by norm_num)]; push_cast; ring
      rw [h1, h2]; ring
    · rw [oddSigma, filter_true_of_mem fun d hd => Odd.of_dvd_nat hodd (Nat.dvd_of_mem_divisors hd)]
      refine sum_congr rfl fun d hd => ?_
      have hdd := Nat.dvd_of_mem_divisors hd
      have hq : Odd (M / d) := Odd.of_dvd_nat hodd (Nat.div_dvd_of_dvd hdd)
      rw [neg_one_pow_even (by rw [Nat.even_add_one, Nat.not_even_iff_odd]; exact hq), one_mul]


lemma four_dvd_two_mul_iff (e : ℕ) : 4 ∣ 2 * e ↔ 2 ∣ e := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num]; exact Nat.mul_dvd_mul_iff_left (by norm_num)

/-- **the divisor identity**: `(−1)^N [q^N] Σ (−1)^k q^k/(1+q^k)² = Σ_{d ∣ N, 4 ∤ d} d`. -/
theorem coeff_Lser_eq {N : ℕ} (hN : 1 ≤ N) :
    (-1) ^ N * coeff N Lser = ∑ d ∈ N.divisors.filter (fun d => ¬ 4 ∣ d), (d : ℤ) := by
  rw [coeff_Lser hN]
  rcases Nat.even_or_odd N with ⟨M, hM⟩ | hodd
  · have hM2 : N = 2 * M := by omega
    subst hM2
    have hM1 : 1 ≤ M := by omega
    rw [neg_one_pow_even (even_two_mul M), one_mul, sum_filter (fun d => ¬ 4 ∣ d), sum_divisors_two_mul hM1,
      sum_divisors_two_mul hM1]
    have h1 : ∑ d ∈ M.divisors.filter Odd, (-1 : ℤ) ^ (2 * M / d) * ((-1) ^ (d - 1) * (d : ℤ)) = oddSigma M := by
      rw [oddSigma]
      refine sum_congr rfl fun d hd => ?_
      rw [mem_filter, Nat.mem_divisors] at hd
      obtain ⟨c, hc⟩ := hd.2
      rw [Nat.mul_div_assoc 2 hd.1.1, neg_one_pow_even (even_two_mul _),
        neg_one_pow_even (show Even (d - 1) from ⟨c, by omega⟩)]
      ring
    have h2 : ∑ e ∈ M.divisors, (-1 : ℤ) ^ (2 * M / (2 * e)) * ((-1) ^ (2 * e - 1) * ((2 * e : ℕ) : ℤ))
        = 2 * oddSigma M := by
      rw [← star M hM1, mul_sum]
      refine sum_congr rfl fun e he => ?_
      have he1 : 1 ≤ e := Nat.pos_of_mem_divisors he
      rw [Nat.mul_div_mul_left _ _ (by norm_num), neg_one_pow_odd (show Odd (2 * e - 1) from ⟨e - 1, by omega⟩),
        pow_succ]
      push_cast; ring
    have h3 : ∑ d ∈ M.divisors.filter Odd, (if ¬ 4 ∣ d then (d : ℤ) else 0) = oddSigma M := by
      rw [oddSigma]
      refine sum_congr rfl fun d hd => ?_
      rw [mem_filter] at hd
      rw [if_pos (fun h => by
        obtain ⟨c, hc⟩ := hd.2
        have := Nat.dvd_trans (show 2 ∣ 4 by norm_num) h; omega)]
    have h4 : ∑ e ∈ M.divisors, (if ¬ 4 ∣ 2 * e then ((2 * e : ℕ) : ℤ) else 0) = 2 * oddSigma M := by
      rw [oddSigma, sum_filter, mul_sum]
      refine sum_congr rfl fun e _ => ?_
      by_cases ho : Odd e
      · rw [if_pos ho, if_pos (fun h => by
          rw [four_dvd_two_mul_iff] at h
          exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h))]
        push_cast; ring
      · rw [if_neg ho, if_neg (fun h => h (by
          rw [four_dvd_two_mul_iff]; exact even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp ho)))]
        ring
    rw [h1, h2, h3, h4]
  · rw [neg_one_pow_odd hodd, mul_sum, sum_filter]
    refine sum_congr rfl fun d hd => ?_
    have hdd := Nat.dvd_of_mem_divisors hd
    have hd1 : Odd d := Odd.of_dvd_nat hodd hdd
    have hq : Odd (N / d) := Odd.of_dvd_nat hodd (Nat.div_dvd_of_dvd hdd)
    obtain ⟨c, hc⟩ := hd1
    rw [neg_one_pow_odd hq, neg_one_pow_even (show Even (d - 1) from ⟨c, by omega⟩),
      if_pos (fun h => by have := Nat.dvd_trans (show 2 ∣ 4 by norm_num) h; omega)]
    ring


/-! ## the coefficients of `φ(−q)⁴` count representations -/

/-- the monomial `(−1)^a q^{a²}`. -/
noncomputable def fz (a : ℤ) : PowerSeries ℤ := C ((-1 : ℤ) ^ a.natAbs) * X ^ (a.natAbs ^ 2)

/-- `Σ_{|a| ≤ N} (−1)^a q^{a²}`. -/
noncomputable def thN (N : ℕ) : PowerSeries ℤ := ∑ a ∈ Icc (-(N : ℤ)) N, fz a

lemma two_choose' (n : ℕ) : 2 * n.choose 2 + n = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.choose_succ_succ, Nat.choose_one_right]; nlinarith

lemma Icc_succ (N : ℕ) : Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ)
    = insert ((N + 1 : ℕ) : ℤ) (insert (-((N + 1 : ℕ) : ℤ)) (Icc (-(N : ℤ)) N)) := by
  ext a; simp only [mem_Icc, mem_insert]; push_cast; omega

lemma thN_eq (N : ℕ) : thN N = ∑ d ∈ range (N + 1), thA 2 1 d + ∑ d ∈ range N, thB 2 1 d := by
  induction N with
  | zero => simp [thN, fz, RankProof.thA]
  | succ N ih =>
    rw [thN, Icc_succ, sum_insert (by simp; omega), sum_insert (by simp), ← thN, ih,
      sum_range_succ (thA 2 1) (N + 1), sum_range_succ (thB 2 1) N]
    have e1 : fz ((N + 1 : ℕ) : ℤ) = thA 2 1 (N + 1) := by
      rw [fz, RankProof.thA, Int.natAbs_natCast, ← two_choose' (N + 1), one_mul]
    have e2 : fz (-((N + 1 : ℕ) : ℤ)) = thB 2 1 N := by
      rw [fz, RankProof.thB, Int.natAbs_neg, Int.natAbs_natCast, ← two_choose' (N + 1)]; try norm_num
    rw [e1, e2]; ring

lemma π_theta (N : ℕ) : π (N + 1) (thetaS 2 1) = π (N + 1) (thN N) := by
  rw [π_eq_iff]
  have h1 := thetaS_dvd 2 1 (by norm_num) (by norm_num) N
  rw [thetaTr_eq, sum_range_succ (thB 2 1) N] at h1
  rw [thN_eq]
  have h2 : (X : PowerSeries ℤ) ^ (N + 1) ∣ thB 2 1 N := by
    rw [RankProof.thB]
    exact dvd_mul_of_dvd_right (pow_dvd_pow X (by nlinarith [Nat.choose_le_pow (N + 1) 2])) _
  have := dvd_add h1 h2
  rwa [show thetaS 2 1 - (∑ d ∈ range (N + 1), thA 2 1 d + (∑ d ∈ range N, thB 2 1 d + thB 2 1 N)) + thB 2 1 N
    = thetaS 2 1 - (∑ d ∈ range (N + 1), thA 2 1 d + ∑ d ∈ range N, thB 2 1 d) by ring] at this

/-- the box `[-N, N]⁴`. -/
noncomputable def box4 (N : ℕ) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  Icc (-(N : ℤ)) N ×ˢ Icc (-(N : ℤ)) N ×ˢ Icc (-(N : ℤ)) N ×ˢ Icc (-(N : ℤ)) N

/-- `r₄(N)`: the representations of `N` as an ordered sum of four squares of integers. -/
noncomputable def r4 (N : ℕ) : ℕ :=
  ((box4 N).filter fun v => v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2 = (N : ℤ)).card

lemma mul_sum_prod {α β : Type*} (s : Finset α) (t : Finset β) (f : α → PowerSeries ℤ) (g : β → PowerSeries ℤ) :
    (∑ a ∈ s, f a) * (∑ y ∈ t, g y) = ∑ x ∈ s ×ˢ t, f x.1 * g x.2 := by
  rw [sum_product, sum_mul_sum]

lemma thN_pow_four (N : ℕ) :
    thN N ^ 4 = ∑ v ∈ box4 N, fz v.1 * (fz v.2.1 * (fz v.2.2.1 * fz v.2.2.2)) := by
  rw [show thN N ^ 4 = thN N * (thN N * (thN N * thN N)) by ring, thN, mul_sum_prod, mul_sum_prod, mul_sum_prod]
  rfl

lemma neg_one_pow_natAbs_sq (a : ℤ) : (-1 : ℤ) ^ a.natAbs = (-1) ^ (a.natAbs ^ 2) := by
  rcases Nat.even_or_odd a.natAbs with h | h
  · rw [sq, pow_mul, h.neg_one_pow, one_pow]
  · rw [sq, pow_mul, h.neg_one_pow, h.neg_one_pow]

lemma coeff_thN_pow_four (N : ℕ) : coeff N (thN N ^ 4) = (-1) ^ N * (r4 N : ℤ) := by
  rw [thN_pow_four, map_sum, r4, card_eq_sum_ones, Nat.cast_sum, mul_sum, sum_filter]
  refine sum_congr rfl fun v _ => ?_
  obtain ⟨a, b, c, d⟩ := v
  simp only [fz]
  rw [show C ((-1 : ℤ) ^ a.natAbs) * X ^ (a.natAbs ^ 2) * (C ((-1 : ℤ) ^ b.natAbs) * X ^ (b.natAbs ^ 2) *
      (C ((-1 : ℤ) ^ c.natAbs) * X ^ (c.natAbs ^ 2) * (C ((-1 : ℤ) ^ d.natAbs) * X ^ (d.natAbs ^ 2))))
      = C ((-1 : ℤ) ^ (a.natAbs ^ 2 + b.natAbs ^ 2 + c.natAbs ^ 2 + d.natAbs ^ 2)) *
        X ^ (a.natAbs ^ 2 + b.natAbs ^ 2 + c.natAbs ^ 2 + d.natAbs ^ 2) by
    rw [neg_one_pow_natAbs_sq a, neg_one_pow_natAbs_sq b, neg_one_pow_natAbs_sq c, neg_one_pow_natAbs_sq d]
    simp only [pow_add, map_mul]; ring,
    coeff_C_mul, coeff_X_pow]
  have hcast : (a.natAbs ^ 2 + b.natAbs ^ 2 + c.natAbs ^ 2 + d.natAbs ^ 2 = N)
      ↔ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = (N : ℤ) := by
    rw [← Int.natAbs_sq a, ← Int.natAbs_sq b, ← Int.natAbs_sq c, ← Int.natAbs_sq d]
    exact_mod_cast Iff.rfl
  by_cases h : a.natAbs ^ 2 + b.natAbs ^ 2 + c.natAbs ^ 2 + d.natAbs ^ 2 = N
  · rw [if_pos h.symm, if_pos (hcast.mp h), h]; simp
  · rw [if_neg (Ne.symm h), if_neg (fun h' => h (hcast.mpr h'))]; simp

/-- **Jacobi's four-square theorem**: for `N ≥ 1`, the number of `(a,b,c,d) ∈ ℤ⁴` with
`a² + b² + c² + d² = N` is `8 Σ_{d ∣ N, 4 ∤ d} d`. -/
theorem jacobi_four_squares {N : ℕ} (hN : 1 ≤ N) :
    r4 N = 8 * ∑ d ∈ N.divisors.filter (fun d => ¬ 4 ∣ d), d := by
  have h1 : coeff N (thetaS 2 1 ^ 4) = coeff N (thN N ^ 4) := by
    have := congrArg (· ^ 4) (π_theta N)
    simp only [← map_pow] at this
    exact coeff_eq_of_dvd (π_eq_iff.mp this) (Nat.lt_succ_self N)
  rw [theta_pow_four, coeff_thN_pow_four, map_add, coeff_one, if_neg (by omega), zero_add,
    show (8 : PowerSeries ℤ) = C 8 by simp, coeff_C_mul] at h1
  have h2 := coeff_Lser_eq hN
  have hsq : ((-1 : ℤ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; norm_num
  have : (r4 N : ℤ) = 8 * ∑ d ∈ N.divisors.filter (fun d => ¬ 4 ∣ d), (d : ℤ) := by
    rw [← h2]
    linear_combination (-(-1 : ℤ) ^ N) * h1 - (r4 N : ℤ) * hsq
  apply Nat.cast_injective (R := ℤ)
  push_cast
  exact this

/-- `r4` counts all integer solutions: every solution lies in the box `[-N, N]⁴`. -/
theorem r4_eq_ncard (N : ℕ) :
    {v : ℤ × ℤ × ℤ × ℤ | v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2 = (N : ℤ)}.ncard = r4 N := by
  rw [r4, ← Set.ncard_coe_finset]
  congr 1
  ext ⟨a, b, c, d⟩
  simp only [Set.mem_setOf_eq, coe_filter, box4, mem_product, mem_Icc]
  constructor
  · intro h
    have := Int.le_self_sq a; have := Int.le_self_sq (-a); have := Int.le_self_sq b; have := Int.le_self_sq (-b)
    have := Int.le_self_sq c; have := Int.le_self_sq (-c); have := Int.le_self_sq d; have := Int.le_self_sq (-d)
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, h⟩ <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c,
      sq_nonneg d]
  · exact fun h => h.2

end FourSquares
