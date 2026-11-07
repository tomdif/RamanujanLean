/-
# The mean value theorem for Dirichlet polynomials (weak Montgomery–Vaughan form)

For `b : ℕ → ℂ`, `N : ℕ` and `P(t) = ∑_{n=1}^{N} bₙ n^{-it}` (written `dpoly b N t`, with
`n^{-it} = e^{-it log n}`) and `T ≥ 0`:

    |∫₀ᵀ |P(t)|² dt − T ∑ |bₙ|²| ≤ 6 H_N ∑ n |bₙ|²,      H_N = ∑_{d=1}^{N} 1/d   (`mv_poly`).

Proof: expand `|P|² = ∑_{m,n} b_m b̄_n e^{it(log n − log m)}`; the diagonal integrates to
`T ∑ |bₙ|²`, an off-diagonal term is at most `2|b_m||b_n|/|log n − log m|`, and
`1/|log n − log m| ≤ 1 + min(m,n)/|n − m|` (from `log x ≥ 1 − 1/x`).  Then
`∑_{m≠n} |b_m||b_n| ≤ (∑|bₙ|)² ≤ H_N ∑ n|bₙ|²` (Cauchy–Schwarz) and
`|b_m||b_n| min(m,n) ≤ (m|b_m|² + n|b_n|²)/2` with `∑_{n≠m} 1/|n−m| ≤ 2H_N`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.MeanSquare

open Complex Finset MeasureTheory intervalIntegral

/-- `e(λ, t) = e^{iλt}`. -/
noncomputable def ex (l t : ℝ) : ℂ := cexp ((l * t : ℝ) * I)

/-- The Dirichlet polynomial `∑_{n=1}^{N} bₙ n^{-it}`. -/
noncomputable def dpoly (b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, b n * ex (-Real.log n) t

/-- The harmonic sum `H_N = ∑_{d=1}^{N} 1/d`. -/
noncomputable def H (N : ℕ) : ℝ := ∑ d ∈ Icc 1 N, (1 : ℝ) / d

lemma H_nonneg (N : ℕ) : 0 ≤ H N := sum_nonneg fun _ _ => by positivity

lemma H_le_one_add_log (N : ℕ) : H N ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [H, one_div] using h

lemma H_mono {M N : ℕ} (h : M ≤ N) : H M ≤ H N :=
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl h) fun _ _ _ => by positivity

lemma continuous_ex (l : ℝ) : Continuous (ex l) := by
  unfold ex; fun_prop

lemma norm_ex (l t : ℝ) : ‖ex l t‖ = 1 := by
  unfold ex; rw [Complex.norm_exp_ofReal_mul_I]

lemma conj_ex (l t : ℝ) : (starRingEnd ℂ) (ex l t) = ex (-l) t := by
  unfold ex; rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]

lemma ex_mul (l l' t : ℝ) : ex l t * ex l' t = ex (l + l') t := by
  unfold ex; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma ex_zero (t : ℝ) : ex 0 t = 1 := by simp [ex]

lemma continuous_dpoly (b : ℕ → ℂ) (N : ℕ) : Continuous (dpoly b N) := by
  unfold dpoly
  exact continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_ex _)

/-- `∫₀ᵀ e^{iλt} dt` for `λ ≠ 0` has norm `≤ 2/|λ|`. -/
lemma norm_integral_ex_le {l : ℝ} (hl : l ≠ 0) (T : ℝ) :
    ‖∫ t in (0 : ℝ)..T, ex l t‖ ≤ 2 / |l| := by
  have hc : ((l : ℂ) * I) ≠ 0 := mul_ne_zero (by exact_mod_cast hl) I_ne_zero
  have e : ∀ t : ℝ, ex l t = cexp (((l : ℂ) * I) * t) := fun t => by
    unfold ex; congr 1; push_cast; ring
  simp_rw [e]
  rw [integral_exp_mul_complex hc]
  rw [norm_div]
  have h1 : ‖cexp ((l : ℂ) * I * T) - cexp ((l : ℂ) * I * (0 : ℝ))‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have a1 : ‖cexp ((l : ℂ) * I * T)‖ = 1 := by
      rw [show (l : ℂ) * I * T = ((l * T : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have a2 : ‖cexp ((l : ℂ) * I * (0 : ℝ))‖ = 1 := by simp
    rw [a1, a2]; norm_num
  have h2 : ‖(l : ℂ) * I‖ = |l| := by simp
  rw [h2]
  exact div_le_div_of_nonneg_right h1 (abs_nonneg l)

lemma integral_ex_zero (T : ℝ) : ∫ t in (0 : ℝ)..T, ex 0 t = T := by
  simp [ex_zero]

/-- `1/|log n − log m| ≤ 1 + min(m,n)/|n − m|` for distinct positive integers. -/
lemma inv_log_sub_le {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    1 / |Real.log n - Real.log m| ≤ 1 + min (m : ℝ) (n : ℝ) / |(n : ℝ) - m| := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- the case `p < q`
  have key : ∀ p q : ℝ, 0 < p → p < q →
      1 / (Real.log q - Real.log p) ≤ 1 + p / (q - p) := by
    intro p q hp hpq
    have hq : 0 < q := hp.trans hpq
    have hl : 1 - (q / p)⁻¹ ≤ Real.log (q / p) := Real.one_sub_inv_le_log_of_pos (by positivity)
    rw [Real.log_div hq.ne' hp.ne', inv_div] at hl
    have hpos : 0 < 1 - p / q := by
      rw [sub_pos, div_lt_one hq]; exact hpq
    have hlog : 0 < Real.log q - Real.log p := lt_of_lt_of_le hpos hl
    rw [div_le_iff₀ hlog]
    have e : (1 + p / (q - p)) * (1 - p / q) = 1 := by
      field_simp [(sub_pos.2 hpq).ne']; ring
    calc (1 : ℝ) = (1 + p / (q - p)) * (1 - p / q) := e.symm
      _ ≤ (1 + p / (q - p)) * (Real.log q - Real.log p) := by
          gcongr
          have : 0 < q - p := sub_pos.2 hpq
          positivity
  rcases lt_or_gt_of_ne hmn with h | h
  · have h' : (m : ℝ) < n := by exact_mod_cast h
    have hlog : 0 < Real.log n - Real.log m := sub_pos.2 (Real.log_lt_log hm0 h')
    rw [abs_of_pos hlog, abs_of_pos (sub_pos.2 h'), min_eq_left (by exact_mod_cast h.le)]
    exact key m n hm0 h'
  · have h' : (n : ℝ) < m := by exact_mod_cast h
    have hlog : Real.log n - Real.log m < 0 := sub_neg.2 (Real.log_lt_log hn0 h')
    rw [abs_of_neg hlog, abs_of_neg (sub_neg.2 h'), min_eq_right (by exact_mod_cast h.le)]
    have := key n m hn0 h'
    simpa [neg_sub] using this

/-- `∑_{n ∈ [1,N], n ≠ m} 1/|n − m| ≤ 2 H_N`. -/
lemma sum_inv_dist_le (N m : ℕ) (hmN : m ≤ N) :
    ∑ n ∈ Icc 1 N, (if n = m then 0 else (1 : ℝ) / |(n : ℝ) - m|) ≤ 2 * H N := by
  -- split into `n < m` and `n > m`
  have hsplit : ∀ n ∈ Icc 1 N, (if n = m then 0 else (1 : ℝ) / |(n : ℝ) - m|) ≤
      (if n < m then (1 : ℝ) / ((m - n : ℕ) : ℝ) else 0) +
        (if m < n then (1 : ℝ) / ((n - m : ℕ) : ℝ) else 0) := by
    intro n _
    rcases lt_trichotomy n m with h | h | h
    · have : ¬ n = m := h.ne
      have h2 : ¬ m < n := by omega
      simp only [this, h, h2, if_false, if_true, add_zero]
      have h' : (n : ℝ) < m := by exact_mod_cast h
      rw [Nat.cast_sub h.le, abs_of_neg (by linarith : (n : ℝ) - m < 0), neg_sub]
    · simp [h]
    · have : ¬ n = m := h.ne'
      have h2 : ¬ n < m := by omega
      simp only [this, h, h2, if_false, if_true, zero_add]
      have h' : (m : ℝ) < n := by exact_mod_cast h
      rw [Nat.cast_sub h.le, abs_of_pos (by linarith : (0 : ℝ) < n - m)]
  refine (sum_le_sum hsplit).trans ?_
  rw [sum_add_distrib, two_mul]
  gcongr
  · -- `∑_{n<m} 1/(m−n) ≤ H_N`
    rw [← sum_filter]
    have hinj : Set.InjOn (fun n => m - n) ((Icc 1 N).filter fun n => n < m) := by
      intro a ha b hb hab
      simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at ha hb
      simp only at hab; omega
    rw [← sum_image (f := fun d : ℕ => (1 : ℝ) / (d : ℝ)) hinj]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
    intro d hd
    simp only [mem_image, mem_filter, mem_Icc] at hd
    obtain ⟨n, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := hd
    simp only [mem_Icc]; omega
  · rw [← sum_filter]
    have hinj : Set.InjOn (fun n => n - m) ((Icc 1 N).filter fun n => m < n) := by
      intro a ha b hb hab
      simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at ha hb
      simp only at hab; omega
    rw [← sum_image (f := fun d : ℕ => (1 : ℝ) / (d : ℝ)) hinj]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
    intro d hd
    simp only [mem_image, mem_filter, mem_Icc] at hd
    obtain ⟨n, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := hd
    simp only [mem_Icc]; omega

/-- Cauchy–Schwarz: `(∑ |bₙ|)² ≤ H_N ∑ n |bₙ|²`. -/
lemma sq_sum_le (b : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖b n‖) ^ 2 ≤ H N * ∑ n ∈ Icc 1 N, (n : ℝ) * ‖b n‖ ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq (Icc 1 N) (fun n => Real.sqrt n * ‖b n‖)
    (fun n => 1 / Real.sqrt n)
  have e1 : ∀ n ∈ Icc 1 N, Real.sqrt n * ‖b n‖ * (1 / Real.sqrt n) = ‖b n‖ := by
    intro n hn
    have : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by
      have := (mem_Icc.1 hn).1; exact_mod_cast this)
    field_simp
  have e2 : ∀ n ∈ Icc 1 N, (Real.sqrt n * ‖b n‖) ^ 2 = (n : ℝ) * ‖b n‖ ^ 2 := by
    intro n _; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have e3 : ∀ n ∈ Icc 1 N, (1 / Real.sqrt n) ^ 2 = (1 : ℝ) / n := by
    intro n _; rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3] at h
  unfold H; linarith

/-- The squared modulus as a double sum. -/
lemma normSq_dpoly (b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    ((‖dpoly b N t‖ ^ 2 : ℝ) : ℂ) = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      b m * (starRingEnd ℂ) (b n) * ex (Real.log n - Real.log m) t := by
  push_cast
  rw [← Complex.mul_conj', dpoly, map_sum, sum_mul_sum]
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
  rw [map_mul, conj_ex]
  have : ex (-Real.log m) t * ex (- -Real.log n) t = ex (Real.log n - Real.log m) t := by
    rw [ex_mul]; congr 1; ring
  rw [← this]; ring

/-- **Mean value theorem for Dirichlet polynomials** (weak Montgomery–Vaughan):
`|∫₀ᵀ |P|² − T ∑ |bₙ|²| ≤ 6 H_N ∑ n |bₙ|²`. -/
theorem mv_poly (b : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖dpoly b N t‖ ^ 2) - T * ∑ n ∈ Icc 1 N, ‖b n‖ ^ 2| ≤
      6 * H N * ∑ n ∈ Icc 1 N, (n : ℝ) * ‖b n‖ ^ 2 := by
  set S := Icc 1 N with hS
  set W := ∑ n ∈ S, (n : ℝ) * ‖b n‖ ^ 2 with hW
  have hW0 : 0 ≤ W := sum_nonneg fun _ _ => by positivity
  -- the complex integral
  have hint : ∀ l : ℝ, IntervalIntegrable (ex l) volume 0 T :=
    fun l => (continuous_ex l).intervalIntegrable _ _
  have hI : ((∫ t in (0 : ℝ)..T, ‖dpoly b N t‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ S, ∑ n ∈ S, b m * (starRingEnd ℂ) (b n) *
        ∫ t in (0 : ℝ)..T, ex (Real.log n - Real.log m) t := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [normSq_dpoly]
    rw [intervalIntegral.integral_finsetSum (fun m _ => ?_)]
    · refine sum_congr rfl fun m _ => ?_
      rw [intervalIntegral.integral_finsetSum (fun n _ => (hint _).const_mul _)]
      refine sum_congr rfl fun n _ => ?_
      rw [intervalIntegral.integral_const_mul]
    · exact (continuous_finsetSum _ fun n _ => continuous_const.mul
        (continuous_ex _)).intervalIntegrable _ _
  -- off-diagonal terms
  set F : ℕ → ℕ → ℂ := fun m n => b m * (starRingEnd ℂ) (b n) *
    ∫ t in (0 : ℝ)..T, ex (Real.log n - Real.log m) t with hF
  have hdiag : ∀ m ∈ S, F m m = (‖b m‖ ^ 2 : ℝ) * T := by
    intro m _
    simp only [hF, sub_self, integral_ex_zero]
    rw [Complex.mul_conj']; push_cast; ring
  have hsplit : ∀ m ∈ S, ∑ n ∈ S, F m n =
      F m m + ∑ n ∈ S, (if n = m then 0 else F m n) := by
    intro m hm
    rw [← sum_erase_add S _ hm, add_comm]
    congr 1
    rw [← sum_erase_add S _ hm]
    simp only [if_true, add_zero]
    refine sum_congr rfl fun n hn => ?_
    rw [if_neg (ne_of_mem_erase hn)]
  have hdiff : ((∫ t in (0 : ℝ)..T, ‖dpoly b N t‖ ^ 2 : ℝ) : ℂ) -
      ((T * ∑ n ∈ S, ‖b n‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ S, ∑ n ∈ S, (if n = m then 0 else F m n) := by
    rw [hI]
    rw [sum_congr rfl hsplit, sum_add_distrib, sum_congr rfl hdiag]
    push_cast
    rw [mul_sum]
    have : ∑ i ∈ S, ((‖b i‖ : ℂ) ^ 2 * (T : ℂ)) = ∑ i ∈ S, (T : ℂ) * (‖b i‖ : ℂ) ^ 2 :=
      sum_congr rfl fun _ _ => by ring
    rw [this]; ring
  -- pointwise bound on off-diagonal terms
  have hterm : ∀ m ∈ S, ∀ n ∈ S, ‖(if n = m then 0 else F m n)‖ ≤
      2 * (‖b m‖ * ‖b n‖) +
        (if n = m then 0 else ((m : ℝ) * ‖b m‖ ^ 2 + (n : ℝ) * ‖b n‖ ^ 2) / |(n : ℝ) - m|) := by
    intro m hm n hn
    by_cases hnm : n = m
    · simp only [hnm, if_true, norm_zero, add_zero]; positivity
    · simp only [hnm, if_false]
      have hm1 := (mem_Icc.1 hm).1
      have hn1 := (mem_Icc.1 hn).1
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hl : Real.log n - Real.log m ≠ 0 := by
        intro h
        have : Real.log n = Real.log m := by linarith
        have := Real.log_injOn_pos (Set.mem_Ioi.2 hn0) (Set.mem_Ioi.2 hm0) this
        exact hnm (by exact_mod_cast this)
      have hlpos : 0 < |Real.log n - Real.log m| := abs_pos.2 hl
      have hb := norm_integral_ex_le hl T
      have hinv := inv_log_sub_le hm1 hn1 (Ne.symm hnm)
      have hd : 0 < |(n : ℝ) - m| := abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast hnm))
      simp only [hF, norm_mul, Complex.norm_conj]
      have hmin : min (m : ℝ) (n : ℝ) * (‖b m‖ * ‖b n‖) ≤
          ((m : ℝ) * ‖b m‖ ^ 2 + (n : ℝ) * ‖b n‖ ^ 2) / 2 := by
        have h1 : min (m : ℝ) (n : ℝ) ≤ m := min_le_left _ _
        have h2 : min (m : ℝ) (n : ℝ) ≤ n := min_le_right _ _
        have h0 : (0 : ℝ) ≤ min (m : ℝ) (n : ℝ) := le_min hm0.le hn0.le
        nlinarith [sq_nonneg (‖b m‖ - ‖b n‖), norm_nonneg (b m), norm_nonneg (b n),
          mul_nonneg h0 (sq_nonneg (‖b m‖ - ‖b n‖)),
          mul_nonneg (sub_nonneg.2 h1) (sq_nonneg ‖b m‖),
          mul_nonneg (sub_nonneg.2 h2) (sq_nonneg ‖b n‖)]
      calc ‖b m‖ * ‖b n‖ * ‖∫ t in (0 : ℝ)..T, ex (Real.log n - Real.log m) t‖
          ≤ ‖b m‖ * ‖b n‖ * (2 / |Real.log n - Real.log m|) := by gcongr
        _ = 2 * (‖b m‖ * ‖b n‖) * (1 / |Real.log n - Real.log m|) := by ring
        _ ≤ 2 * (‖b m‖ * ‖b n‖) * (1 + min (m : ℝ) (n : ℝ) / |(n : ℝ) - m|) := by gcongr
        _ = 2 * (‖b m‖ * ‖b n‖) + 2 * (min (m : ℝ) (n : ℝ) * (‖b m‖ * ‖b n‖)) / |(n : ℝ) - m| := by
            ring
        _ ≤ 2 * (‖b m‖ * ‖b n‖) +
              ((m : ℝ) * ‖b m‖ ^ 2 + (n : ℝ) * ‖b n‖ ^ 2) / |(n : ℝ) - m| := by
            gcongr; linarith
  -- summing the bounds
  have hA : ∑ m ∈ S, ∑ n ∈ S, 2 * (‖b m‖ * ‖b n‖) ≤ 2 * (H N * W) := by
    have : ∑ m ∈ S, ∑ n ∈ S, 2 * (‖b m‖ * ‖b n‖) = 2 * (∑ n ∈ S, ‖b n‖) ^ 2 := by
      rw [sq, sum_mul_sum, mul_sum]
      refine sum_congr rfl fun m _ => ?_
      rw [mul_sum]
    rw [this]
    have := sq_sum_le b N
    linarith
  have hsym : ∀ m ∈ S, ∀ n ∈ S,
      (if n = m then 0 else ((m : ℝ) * ‖b m‖ ^ 2 + (n : ℝ) * ‖b n‖ ^ 2) / |(n : ℝ) - m|) =
        (m : ℝ) * ‖b m‖ ^ 2 * (if n = m then 0 else 1 / |(n : ℝ) - m|) +
          (n : ℝ) * ‖b n‖ ^ 2 * (if m = n then 0 else 1 / |(m : ℝ) - n|) := by
    intro m _ n _
    by_cases h : n = m
    · simp [h]
    · have h' : ¬ m = n := Ne.symm h
      simp only [h, h', if_false]
      rw [abs_sub_comm (m : ℝ) n]; ring
  have hB : ∑ m ∈ S, ∑ n ∈ S,
      (if n = m then 0 else ((m : ℝ) * ‖b m‖ ^ 2 + (n : ℝ) * ‖b n‖ ^ 2) / |(n : ℝ) - m|) ≤
        4 * (H N * W) := by
    rw [sum_congr rfl fun m hm => sum_congr rfl fun n hn => hsym m hm n hn]
    simp_rw [sum_add_distrib]
    have h1 : ∑ m ∈ S, ∑ n ∈ S, (m : ℝ) * ‖b m‖ ^ 2 * (if n = m then 0 else 1 / |(n : ℝ) - m|)
        ≤ 2 * (H N * W) := by
      have : ∀ m ∈ S, ∑ n ∈ S, (m : ℝ) * ‖b m‖ ^ 2 * (if n = m then 0 else 1 / |(n : ℝ) - m|)
          ≤ (m : ℝ) * ‖b m‖ ^ 2 * (2 * H N) := by
        intro m hm
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_inv_dist_le N m (mem_Icc.1 hm).2) (by positivity)
      refine (sum_le_sum this).trans (le_of_eq ?_)
      rw [← sum_mul, hW]; ring
    have h2 : ∑ m ∈ S, ∑ n ∈ S, (n : ℝ) * ‖b n‖ ^ 2 * (if m = n then 0 else 1 / |(m : ℝ) - n|)
        ≤ 2 * (H N * W) := by
      rw [sum_comm]
      have : ∀ n ∈ S, ∑ m ∈ S, (n : ℝ) * ‖b n‖ ^ 2 * (if m = n then 0 else 1 / |(m : ℝ) - n|)
          ≤ (n : ℝ) * ‖b n‖ ^ 2 * (2 * H N) := by
        intro n hn
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_inv_dist_le N n (mem_Icc.1 hn).2) (by positivity)
      refine (sum_le_sum this).trans (le_of_eq ?_)
      rw [← sum_mul, hW]; ring
    linarith
  -- conclude
  have hnorm : ‖∑ m ∈ S, ∑ n ∈ S, (if n = m then 0 else F m n)‖ ≤ 6 * H N * W := by
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum fun m _ => norm_sum_le _ _).trans ?_
    refine (sum_le_sum fun m hm => sum_le_sum fun n hn => hterm m hm n hn).trans ?_
    simp_rw [sum_add_distrib]
    linarith
  rw [← Complex.ofReal_sub] at hdiff
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hdiff]
  exact hnorm

end RamanujanTau.MeanSquare
