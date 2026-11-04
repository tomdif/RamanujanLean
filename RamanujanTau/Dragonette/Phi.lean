/-
# A uniform bound for the third-order mock theta function `φ(s) = Σ s^{n²}/(−s²;s²)_n`

For `‖s‖ = r = e^{−t}`, `0 < t ≤ 1/32` (all arguments of `s`):

  `‖φ(s)‖ ≤ (−r;r²)_∞ · (1/t) · e^{−1/(2400 t)}`.

Note `(−r;r²)_∞ ~ e^{π²/(24t)}` is exactly the size of the main term of `b(−e^{−t})`, so this says `φ` is
exponentially smaller than `b` near every point of the circle. Proof:
* `‖1 + u‖ ≥ (1 − ‖u‖) e^{(‖u‖ + Re u)/8}`, so the `n`-th term is `≤ c_n e^{−G_n/8}`,
  `c_n = r^{n²}/(r²;r²)_n`, `G_n = Σ_{j≤n} (r^{2j} + Re s^{2j})`;
* pairing `j` with `2j`: `G_n ≥ (7/16) m r^{4m}` for `2m ≤ n`;
* small `n < N`: `c_n ≤ 2^N S(1/2) ≤ 2^N S(1) e^{−r/(4(1−r²))}` (`Euler.lean`); large `n`: `Σ c_n = S(1)`.
-/
import RamanujanTau.Dragonette.Euler

set_option autoImplicit false

namespace Dragonette
open Complex Finset Filter
open scoped Real Topology

/-- **one factor, from below**. -/
lemma factor_lower {u : ℂ} (hu : ‖u‖ < 1) : (1 - ‖u‖) * Real.exp ((‖u‖ + u.re) / 8) ≤ ‖1 + u‖ := by
  set a := ‖u‖
  set c := u.re
  have hc : |c| ≤ a := Complex.abs_re_le_norm u
  have ha0 : 0 ≤ a := norm_nonneg u
  have hy : 0 ≤ a + c := by linarith [neg_abs_le c]
  have hsq : ‖1 + u‖ ^ 2 = 1 + 2 * c + a ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, show a ^ 2 = ‖u‖ ^ 2 from rfl, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [add_re, one_re, add_im, one_im, zero_add]; ring
  have he : Real.exp ((a + c) / 4) ≤ 1 + (a + c) / 2 := by
    have hx : (a + c) / 4 < 1 := by linarith [le_abs_self c]
    have := Real.exp_bound_div_one_sub_of_interval (by positivity : 0 ≤ (a + c) / 4) hx
    refine this.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [le_abs_self c]
  have hL : 0 ≤ (1 - a) * Real.exp ((a + c) / 8) :=
    mul_nonneg (by linarith [show a < 1 from hu]) (Real.exp_pos _).le
  refine (pow_le_pow_iff_left₀ hL (norm_nonneg _) two_ne_zero).mp ?_
  rw [hsq, mul_pow, ← Real.exp_nat_mul]
  have he' : Real.exp (((2 : ℕ) : ℝ) * ((a + c) / 8)) = Real.exp ((a + c) / 4) := by congr 1; push_cast; ring
  rw [he']
  have h1a : (1 - a) ^ 2 ≤ 1 := by nlinarith [show a < 1 from hu]
  calc (1 - a) ^ 2 * Real.exp ((a + c) / 4) ≤ (1 - a) ^ 2 * (1 + (a + c) / 2) := by gcongr
    _ ≤ 1 + 2 * c + a ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right h1a hy]

/-- **the pair `j, 2j`**: `(y + Re u) + (y² + Re u²) ≥ (7/8) y²`, `y = ‖u‖ ≤ 1`. -/
lemma pair_bound {u : ℂ} (hu : ‖u‖ ≤ 1) : 7 / 8 * ‖u‖ ^ 2 ≤ (‖u‖ + u.re) + (‖u‖ ^ 2 + (u ^ 2).re) := by
  have hc : |u.re| ≤ ‖u‖ := Complex.abs_re_le_norm u
  have hn : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h2 : (u ^ 2).re = u.re ^ 2 - u.im ^ 2 := by rw [pow_two, mul_re]; ring
  rw [h2]
  have h1 : (‖u‖ + u.re) * (1 - ‖u‖) ≥ 0 := mul_nonneg (by linarith [neg_abs_le u.re]) (by linarith)
  nlinarith [sq_nonneg (u.re + ‖u‖ / 4)]

/-- `a_j = ‖w‖^j + Re w^j`. -/
noncomputable def aj (w : ℂ) (j : ℕ) : ℝ := ‖w‖ ^ j + (w ^ j).re

lemma aj_nonneg (w : ℂ) (j : ℕ) : 0 ≤ aj w j := by
  unfold aj
  have := Complex.abs_re_le_norm (w ^ j)
  rw [norm_pow] at this
  linarith [neg_abs_le (w ^ j).re]

/-- **`G_n ≥ (7/16) m ‖w‖^{2m}` for `2m ≤ n`**. -/
lemma G_lower {w : ℂ} (hw : ‖w‖ ≤ 1) {m n : ℕ} (hmn : 2 * m ≤ n) :
    7 / 16 * m * ‖w‖ ^ (2 * m) ≤ ∑ i ∈ range n, aj w (i + 1) := by
  have hA : ∑ k ∈ range m, aj w (k + 1) ≤ ∑ i ∈ range n, aj w (i + 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega)) fun i _ _ => aj_nonneg w _
  have hB : ∑ k ∈ range m, aj w (2 * (k + 1)) ≤ ∑ i ∈ range n, aj w (i + 1) := by
    have hinj : Set.InjOn (fun k : ℕ => 2 * k + 1) (range m : Set ℕ) := fun a _ b _ h => by simp at h; omega
    rw [show ∑ k ∈ range m, aj w (2 * (k + 1)) = ∑ i ∈ (range m).image (fun k => 2 * k + 1), aj w (i + 1) by
      rw [Finset.sum_image hinj]; exact Finset.sum_congr rfl fun k _ => by congr 1]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i _ _ => aj_nonneg w _
    simp only [Finset.mem_image, Finset.mem_range] at hi ⊢
    obtain ⟨k, hk, rfl⟩ := hi; omega
  have hP : ∀ k ∈ range m, 7 / 8 * ‖w‖ ^ (2 * m) ≤ aj w (k + 1) + aj w (2 * (k + 1)) := by
    intro k hk
    have hk' : k + 1 ≤ m := by simp at hk; omega
    have hu : ‖w ^ (k + 1)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
    have := pair_bound hu
    have e1 : aj w (k + 1) = ‖w ^ (k + 1)‖ + (w ^ (k + 1)).re := by unfold aj; rw [norm_pow]
    have e2 : aj w (2 * (k + 1)) = ‖w ^ (k + 1)‖ ^ 2 + ((w ^ (k + 1)) ^ 2).re := by
      unfold aj; rw [norm_pow, ← pow_mul, ← pow_mul, mul_comm 2 (k + 1)]
    have hmono : ‖w‖ ^ (2 * m) ≤ ‖w ^ (k + 1)‖ ^ 2 := by
      rw [norm_pow, ← pow_mul]; exact pow_le_pow_of_le_one (norm_nonneg _) hw (by omega)
    rw [e1, e2]
    linarith
  have hsum := Finset.sum_le_sum hP
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  linarith

/-- the `n`-th term of `φ`. -/
noncomputable def phiT (s : ℂ) (n : ℕ) : ℂ := s ^ (n ^ 2) / ∏ i ∈ range n, (1 + s ^ (2 + 2 * i))

lemma gA_neg_eq (s : ℂ) : MockTheta3.Radial.gA (-s) = ∑' n, phiT s n := by
  rw [MockTheta3.Radial.gA_eq]
  congr 1; funext n
  rw [phiT]
  have e1 : ∀ i : ℕ, (-s) ^ (2 + 2 * i) = s ^ (2 + 2 * i) := fun i => Even.neg_pow ⟨1 + i, by ring⟩ _
  simp only [e1]
  congr 1
  rw [neg_pow s, ← mul_assoc, ← pow_add, Even.neg_one_pow (by
    rw [show n + n ^ 2 = n * (n + 1) by ring]; exact Nat.even_mul_succ_self n), one_mul]

/-- **the term bound** `‖phiT s n‖ ≤ c_n e^{−G_n/8}`. -/
lemma phiT_le {s : ℂ} (hs : ‖s‖ < 1) (n : ℕ) :
    ‖phiT s n‖ ≤ cn ‖s‖ n * Real.exp (-(∑ i ∈ range n, aj (s ^ 2) (i + 1)) / 8) := by
  set r := ‖s‖
  have h0 : 0 ≤ r := norm_nonneg s
  have hfac : ∀ i : ℕ, (1 - r ^ (2 * (i + 1))) * Real.exp (aj (s ^ 2) (i + 1) / 8) ≤ ‖1 + s ^ (2 + 2 * i)‖ := by
    intro i
    have hu : ‖s ^ (2 + 2 * i)‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ h0 hs (by omega)
    have := factor_lower hu
    have e1 : ‖s ^ (2 + 2 * i)‖ = r ^ (2 * (i + 1)) := by
      rw [norm_pow, show 2 + 2 * i = 2 * (i + 1) by ring]
    have e2 : aj (s ^ 2) (i + 1) = ‖s ^ (2 + 2 * i)‖ + (s ^ (2 + 2 * i)).re := by
      unfold aj; rw [← pow_mul, norm_pow, norm_pow, ← pow_mul, show 2 * (i + 1) = 2 + 2 * i by ring]
    rw [e2, ← e1]; exact this
  have hprod : (∏ i ∈ range n, (1 - r ^ (2 * (i + 1)))) * Real.exp ((∑ i ∈ range n, aj (s ^ 2) (i + 1)) / 8)
      ≤ ‖∏ i ∈ range n, (1 + s ^ (2 + 2 * i))‖ := by
    rw [norm_prod, Finset.sum_div, Real.exp_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun i _ => ?_) fun i _ => hfac i
    have : r ^ (2 * (i + 1)) < 1 := pow_lt_one₀ h0 hs (by omega)
    have := Real.exp_pos (aj (s ^ 2) (i + 1) / 8)
    nlinarith
  have hq := qpoch_pos h0 hs n
  have hpos : 0 < (∏ i ∈ range n, (1 - r ^ (2 * (i + 1)))) * Real.exp ((∑ i ∈ range n, aj (s ^ 2) (i + 1)) / 8) :=
    mul_pos hq (Real.exp_pos _)
  rw [phiT, norm_div, norm_pow, cn, div_le_iff₀ (lt_of_lt_of_le hpos hprod)]
  set Q := ∏ i ∈ range n, (1 - r ^ (2 * (i + 1)))
  set G := ∑ i ∈ range n, aj (s ^ 2) (i + 1)
  have key : r ^ (n ^ 2) / Q * Real.exp (-G / 8) * (Q * Real.exp (G / 8)) = r ^ (n ^ 2) := by
    rw [neg_div, Real.exp_neg]; field_simp
  calc r ^ (n ^ 2) = r ^ (n ^ 2) / Q * Real.exp (-G / 8) * (Q * Real.exp (G / 8)) := key.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod
        (mul_nonneg (div_nonneg (pow_nonneg h0 _) hq.le) (Real.exp_pos _).le)

/-- the two-piece bound on all terms. -/
lemma phiT_le_split {s : ℂ} (hs : ‖s‖ < 1) (N : ℕ) (n : ℕ) :
    ‖phiT s n‖ ≤ (if n < N then 2 ^ N * Sx ‖s‖ (1 / 2) else 0) +
      cn ‖s‖ n * Real.exp (-(7 / 16 * (N / 2 : ℕ) * ‖s‖ ^ (4 * (N / 2 : ℕ))) / 8) := by
  set r := ‖s‖
  have h0 : 0 ≤ r := norm_nonneg s
  have hc := cn_nonneg h0 hs n
  have hT := phiT_le hs n
  have hG : ∀ n, 0 ≤ ∑ i ∈ range n, aj (s ^ 2) (i + 1) := fun n => Finset.sum_nonneg fun i _ => aj_nonneg _ _
  by_cases hn : n < N
  · rw [if_pos hn]
    have h1 : ‖phiT s n‖ ≤ cn r n := hT.trans (by
      have : Real.exp (-(∑ i ∈ range n, aj (s ^ 2) (i + 1)) / 8) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith [hG n])
      nlinarith)
    have h2 : cn r n ≤ 2 ^ N * Sx r (1 / 2) := by
      have hsum := summable_cn h0 hs (x := 1 / 2) (by norm_num) (by norm_num)
      have hle : cn r n * (1 / 2) ^ n ≤ Sx r (1 / 2) :=
        hsum.le_tsum n fun m _ => mul_nonneg (cn_nonneg h0 hs m) (by positivity)
      have hp : (2 : ℝ) ^ n ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hn.le
      have e : cn r n = 2 ^ n * (cn r n * (1 / 2) ^ n) := by
        rw [← mul_assoc, mul_comm ((2 : ℝ) ^ n), mul_assoc, ← mul_pow]; norm_num
      rw [e]
      have : 0 ≤ cn r n * (1 / 2) ^ n := by positivity
      calc 2 ^ n * (cn r n * (1 / 2) ^ n) ≤ 2 ^ N * (cn r n * (1 / 2) ^ n) := by gcongr
        _ ≤ _ := by gcongr
    have : 0 ≤ cn r n * Real.exp (-(7 / 16 * (N / 2 : ℕ) * r ^ (4 * (N / 2 : ℕ))) / 8) := by positivity
    linarith
  · rw [if_neg hn, zero_add]
    refine hT.trans ?_
    gcongr
    have hw : ‖s ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ h0 hs.le
    have := G_lower hw (m := N / 2) (n := n) (by omega)
    rw [norm_pow, ← pow_mul] at this
    rw [show 2 * (2 * (N / 2)) = 4 * (N / 2) by ring] at this
    exact this

/-- **the uniform bound on `φ`** in terms of `S`. -/
theorem norm_gA_le {s : ℂ} (hs : ‖s‖ < 1) (N : ℕ) :
    ‖MockTheta3.Radial.gA (-s)‖ ≤ N * 2 ^ N * Sx ‖s‖ (1 / 2) +
      Sx ‖s‖ 1 * Real.exp (-(7 / 16 * (N / 2 : ℕ) * ‖s‖ ^ (4 * (N / 2 : ℕ))) / 8) := by
  set r := ‖s‖
  have h0 : 0 ≤ r := norm_nonneg s
  set E := Real.exp (-(7 / 16 * (N / 2 : ℕ) * r ^ (4 * (N / 2 : ℕ))) / 8)
  have hs1 := summable_cn h0 hs (x := 1) zero_le_one le_rfl
  simp only [one_pow, mul_one] at hs1
  have hfin : Summable fun n : ℕ => (if n < N then 2 ^ N * Sx r (1 / 2) else (0 : ℝ)) :=
    summable_of_ne_finset_zero (s := range N) fun n hn => by
      rw [Finset.mem_range] at hn; rw [if_neg hn]
  have hB : Summable fun n : ℕ => (if n < N then 2 ^ N * Sx r (1 / 2) else (0 : ℝ)) + cn r n * E :=
    hfin.add (hs1.mul_right E)
  have hnorm : Summable fun n => ‖phiT s n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (phiT_le_split hs N) hB
  rw [gA_neg_eq]
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  refine (hnorm.tsum_le_tsum (phiT_le_split hs N) hB).trans (le_of_eq ?_)
  rw [hfin.tsum_add (hs1.mul_right E), hs1.tsum_mul_right, tsum_eq_sum (s := range N) (fun n hn => by
    rw [Finset.mem_range] at hn; rw [if_neg hn]), Finset.sum_ite_of_true (fun n hn => Finset.mem_range.mp hn),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : Sx r 1 = ∑' n, cn r n := by unfold Sx; simp
  rw [this]; ring

end Dragonette
