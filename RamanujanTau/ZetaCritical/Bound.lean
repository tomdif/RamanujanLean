/-
# Coefficient bounds for `cₙ = n^{−1/2}`

* `∑_{n≤N} cₙ² = H_N`, and `log N ≤ H_N`;
* `∑_{n≤N} cₙ ≤ 2√N`, hence `∫₀¹ |P|² ≤ 4N`;
* the off-diagonal weight of `avg_mv`: `∑_{m≠n} c_m c_n · 2/(log n − log m)² ≤ 20 N²`.

The last bound has no logarithm: `1/|log n − log m| ≤ 1 + min(m,n)/|n−m|` and
`c_m c_n min(m,n)² ≤ min(m,n) ≤ N`, with `∑_{n≠m} 1/(n−m)² ≤ 4`.
-/
import RamanujanTau.ZetaCritical.Poly

set_option autoImplicit false

namespace RamanujanTau.ZetaCritical

open Complex MeasureTheory Set Filter Topology Finset
open RamanujanTau.MeanSquare (dpoly ex H norm_ex inv_log_sub_le)

/-- `cₙ = n^{−1/2}`. -/
noncomputable def ch (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 / 2 : ℝ))

lemma ch_nonneg (n : ℕ) : 0 ≤ ch n := Real.rpow_nonneg (Nat.cast_nonneg n) _

lemma ch_eq {n : ℕ} (hn : 1 ≤ n) : ch n = 1 / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ch, Real.rpow_neg hn0.le, Real.sqrt_eq_rpow, one_div]; norm_num

lemma ch_sq {n : ℕ} (hn : 1 ≤ n) : ch n ^ 2 = 1 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ch_eq hn, div_pow, Real.sq_sqrt hn0.le, one_pow]

lemma sum_ch_sq (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, ch n ^ 2 = H N := by
  unfold H
  exact sum_congr rfl fun n hn => ch_sq (mem_Icc.1 hn).1

lemma ch_anti {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : ch n ≤ ch k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  exact Real.rpow_le_rpow_of_nonpos hk0 (by exact_mod_cast hkn) (by norm_num)

lemma log_le_H (N : ℕ) : Real.log N ≤ H N := by
  have h := log_add_one_le_harmonic N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have e : H N = ∑ i ∈ Finset.Icc 1 N, ((i : ℝ))⁻¹ := by simp [H, one_div]
  rw [e]
  refine le_trans ?_ h
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; simp
  · exact Real.log_le_log (by exact_mod_cast h0) (by linarith)

/-- `∑_{n≤N} n^{−1/2} ≤ 2√N`. -/
lemma sum_ch_le (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, ch n ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ch_eq (by omega)]
    set s := Real.sqrt N with hs
    set r := Real.sqrt ((N + 1 : ℕ) : ℝ) with hr
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = s ^ 2 + 1 := by
      rw [hr, hs, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; push_cast; ring
    have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
    have key : 1 / r ≤ 2 * r - 2 * s := by
      rw [div_le_iff₀ hr0]
      nlinarith [sq_nonneg (r - s)]
    linarith

/-- `|P(t)|² ≤ 4N` pointwise, hence `∫₀¹ |P|² ≤ 4N`. -/
lemma normSq_dpoly_ch_le (N : ℕ) (t : ℝ) :
    ‖dpoly (fun n => (ch n : ℂ)) N t‖ ^ 2 ≤ 4 * N := by
  have h1 : ‖dpoly (fun n => (ch n : ℂ)) N t‖ ≤ 2 * Real.sqrt N := by
    refine le_trans ?_ (sum_ch_le N)
    unfold dpoly
    refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ => ?_))
    rw [norm_mul, norm_ex, mul_one, Complex.norm_real, Real.norm_of_nonneg (ch_nonneg n)]
  have h0 := norm_nonneg (dpoly (fun n => (ch n : ℂ)) N t)
  have := pow_le_pow_left₀ h0 h1 2
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)] at this
  linarith

lemma primitive_one_le (N : ℕ) :
    ∫ t in (0 : ℝ)..1, ‖dpoly (fun n => (ch n : ℂ)) N t‖ ^ 2 ≤ 4 * N := by
  have := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (((RamanujanTau.MeanSquare.continuous_dpoly _ N).norm.pow 2).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable (μ := volume) _ _)
    (fun t _ => normSq_dpoly_ch_le N t)
  simpa using this

/-- `∑_{n ∈ [1,N], n ≠ m} 1/(n − m)² ≤ 4`. -/
lemma sum_inv_dist_sq_le (N m : ℕ) (hmN : m ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (if n = m then 0 else (1 : ℝ) / ((n : ℝ) - m) ^ 2) ≤ 4 := by
  have hsplit : ∀ n ∈ Finset.Icc 1 N, (if n = m then 0 else (1 : ℝ) / ((n : ℝ) - m) ^ 2) ≤
      (if n < m then (((m - n : ℕ) : ℝ) ^ 2)⁻¹ else 0) +
        (if m < n then (((n - m : ℕ) : ℝ) ^ 2)⁻¹ else 0) := by
    intro n _
    rcases lt_trichotomy n m with h | h | h
    · have : ¬ n = m := h.ne
      have h2 : ¬ m < n := by omega
      simp only [this, h, h2, if_false, if_true, add_zero]
      rw [Nat.cast_sub h.le, one_div, show ((n : ℝ) - m) ^ 2 = ((m : ℝ) - n) ^ 2 by ring]
    · simp [h]
    · have : ¬ n = m := h.ne'
      have h2 : ¬ n < m := by omega
      simp only [this, h, h2, if_false, if_true, zero_add]
      rw [Nat.cast_sub h.le, one_div]
  have hbound : ∀ (f : ℕ → ℕ) (p : ℕ → Prop) [DecidablePred p],
      Set.InjOn f ((Finset.Icc 1 N).filter p : Set ℕ) →
      (∀ n ∈ (Finset.Icc 1 N).filter p, f n ∈ Finset.Ioo 0 (N + 1)) →
      ∑ n ∈ (Finset.Icc 1 N).filter p, (((f n : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 := by
    intro f p _ hinj hmem
    rw [← sum_image (f := fun d : ℕ => (((d : ℕ) : ℝ) ^ 2)⁻¹) hinj]
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity)
      ((sum_Ioo_inv_sq_le 0 (N + 1)).trans (by norm_num))
    intro d hd
    obtain ⟨n, hn, rfl⟩ := mem_image.1 hd
    exact hmem n hn
  refine (sum_le_sum hsplit).trans ?_
  rw [sum_add_distrib, show (4 : ℝ) = 2 + 2 by norm_num]
  gcongr
  · rw [← sum_filter]
    refine hbound (fun n => m - n) (fun n => n < m) ?_ ?_
    · intro a ha b hb hab
      simp only [coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at ha hb
      simp only at hab; omega
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      simp only [Finset.mem_Ioo]; omega
  · rw [← sum_filter]
    refine hbound (fun n => n - m) (fun n => m < n) ?_ ?_
    · intro a ha b hb hab
      simp only [coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at ha hb
      simp only at hab; omega
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      simp only [Finset.mem_Ioo]; omega

/-- The pair bound: `c_m c_n · 2/(log n − log m)² ≤ 4 + 4N/(n−m)²`. -/
lemma pair_le {N m n : ℕ} (hm : m ∈ Finset.Icc 1 N) (hn : n ∈ Finset.Icc 1 N) (hmn : n ≠ m) :
    |ch m * ch n| * (2 / (Real.log n - Real.log m) ^ 2) ≤
      4 + 4 * N * ((1 : ℝ) / ((n : ℝ) - m) ^ 2) := by
  obtain ⟨hm1, hmN⟩ := mem_Icc.1 hm
  obtain ⟨hn1, hnN⟩ := mem_Icc.1 hn
  set k : ℝ := min (m : ℝ) (n : ℝ) with hk
  have hk1 : (1 : ℝ) ≤ k := le_min (by exact_mod_cast hm1) (by exact_mod_cast hn1)
  have hkN : k ≤ N := (min_le_left _ _).trans (by exact_mod_cast hmN)
  have hd : 0 < |(n : ℝ) - m| := abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast hmn))
  set x : ℝ := k / |(n : ℝ) - m| with hx
  have hx0 : 0 ≤ x := by positivity
  have hinv := inv_log_sub_le hm1 hn1 (Ne.symm hmn)
  rw [← hk, ← hx] at hinv
  have hl0 : 0 ≤ 1 / |Real.log n - Real.log m| := by positivity
  have hl2 : 2 / (Real.log n - Real.log m) ^ 2 = 2 * (1 / |Real.log n - Real.log m|) ^ 2 := by
    rw [div_pow, one_pow, sq_abs]; ring
  have hsq : (1 / |Real.log n - Real.log m|) ^ 2 ≤ 2 + 2 * x ^ 2 := by
    have := pow_le_pow_left₀ hl0 hinv 2
    nlinarith [sq_nonneg (1 - x)]
  -- `c_m c_n ≤ 1/k`
  have hcc : ch m * ch n ≤ 1 / k := by
    have hkey : ∀ a b : ℕ, 1 ≤ a → a ≤ b → ch a * ch b ≤ 1 / (a : ℝ) := by
      intro a b ha hab
      have h1 := ch_anti ha hab
      have h2 := ch_nonneg b
      have h3 : ch a * ch a = 1 / (a : ℝ) := by rw [← sq, ch_sq ha]
      nlinarith [ch_nonneg a]
    rcases le_total m n with h | h
    · rw [hk, min_eq_left (by exact_mod_cast h)]; exact hkey m n hm1 h
    · rw [hk, min_eq_right (by exact_mod_cast h), mul_comm]; exact hkey n m hn1 h
  have hcc0 : 0 ≤ ch m * ch n := mul_nonneg (ch_nonneg m) (ch_nonneg n)
  have hk0 : 0 < k := by linarith
  have hcc1 : ch m * ch n ≤ 1 := hcc.trans (by rw [div_le_one hk0]; exact hk1)
  have hx2 : x ^ 2 = k ^ 2 * ((1 : ℝ) / ((n : ℝ) - m) ^ 2) := by
    rw [hx, div_pow, sq_abs]; ring
  have hckk : ch m * ch n * k ^ 2 ≤ N := by
    calc ch m * ch n * k ^ 2 ≤ 1 / k * k ^ 2 := by gcongr
      _ = k := by field_simp
      _ ≤ N := hkN
  have hq0 : (0 : ℝ) ≤ (1 : ℝ) / ((n : ℝ) - m) ^ 2 := by positivity
  rw [abs_of_nonneg hcc0, hl2]
  calc ch m * ch n * (2 * (1 / |Real.log n - Real.log m|) ^ 2)
      ≤ ch m * ch n * (2 * (2 + 2 * x ^ 2)) := by gcongr
    _ = 4 * (ch m * ch n) + 4 * (ch m * ch n * k ^ 2) * ((1 : ℝ) / ((n : ℝ) - m) ^ 2) := by
        rw [hx2]; ring
    _ ≤ 4 * 1 + 4 * N * ((1 : ℝ) / ((n : ℝ) - m) ^ 2) := by gcongr
    _ = 4 + 4 * N * ((1 : ℝ) / ((n : ℝ) - m) ^ 2) := by ring

/-- **The off-diagonal weight** is at most `20 N²`. -/
theorem offdiag_ch_le (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if n = m then 0 else |ch m * ch n| * (2 / (Real.log n - Real.log m) ^ 2)) ≤
      20 * (N : ℝ) ^ 2 := by
  have h1 : ∀ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      (if n = m then 0 else |ch m * ch n| * (2 / (Real.log n - Real.log m) ^ 2)) ≤
      ∑ n ∈ Finset.Icc 1 N, (4 + 4 * N * (if n = m then 0 else (1 : ℝ) / ((n : ℝ) - m) ^ 2)) := by
    intro m hm
    refine sum_le_sum fun n hn => ?_
    by_cases h : n = m
    · simp [h]
    · simp only [h, if_false]; exact pair_le hm hn h
  refine (sum_le_sum h1).trans ?_
  have h2 : ∀ m ∈ Finset.Icc 1 N,
      ∑ n ∈ Finset.Icc 1 N, (4 + 4 * N * (if n = m then 0 else (1 : ℝ) / ((n : ℝ) - m) ^ 2)) ≤
        20 * N := by
    intro m hm
    rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc]
    have := sum_inv_dist_sq_le N m (mem_Icc.1 hm).2
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    simp only [nsmul_eq_mul, Nat.add_sub_cancel]
    nlinarith
  refine (sum_le_sum h2).trans (le_of_eq ?_)
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]; ring

end RamanujanTau.ZetaCritical
