import RamanujanTau.ColoredPartitions
import RamanujanTau.HardyRamanujan.Entropy

/-!
# Leading entropy of colored partitions

The actual finite count of `k`-colored partitions has logarithmic growth
`π √(2/3) √k √n`. The proof uses the ordinary Hardy–Ramanujan theorem, a
balanced-tuple lower bound, and a Cauchy–Schwarz upper bound on the finite
convolution. In particular the coefficients of `1/Δ` have leading entropy
`4π√n`. The physical state identification and finer corrections are separate.
-/

set_option autoImplicit false
noncomputable section

namespace ColoredPartitions

open Filter Finset
open scoped Real Topology

lemma sizes_sqrt_le {k n : ℕ} (v : Sizes k n) :
    ∑ i : Fin k, √(v.1 i : ℝ) ≤ √((k : ℝ) * n) := by
  have h := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin k))
    (fun _ => (1 : ℝ)) (fun i => √(v.1 i : ℝ))
  have hs : ∑ i : Fin k, (√(v.1 i : ℝ)) ^ 2 = (n : ℝ) := by
    simp_rw [Real.sq_sqrt (Nat.cast_nonneg _)]
    exact_mod_cast sizes_sum v
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, hs] at h
  have hp : 0 ≤ (k : ℝ) * n := by positivity
  have hsum : 0 ≤ ∑ i : Fin k, √(v.1 i : ℝ) := sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg ((k : ℝ) * n)]

/-- A uniform exponential majorant for ordinary partitions, with any slope above its limit. -/
lemma ordinary_log_upper {A : ℝ} (hA : π * √(2 / 3 : ℝ) < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      Real.log (HardyRamanujan.p n : ℝ) ≤ A * √n + B := by
  have hA0 : 0 ≤ A := le_of_lt (lt_trans (by positivity) hA)
  have he : ∀ᶠ n : ℕ in atTop, Real.log (HardyRamanujan.p n : ℝ) ≤ A * √n := by
    filter_upwards [HardyRamanujan.entropy_sqrt_limit.eventually (eventually_lt_nhds hA),
      eventually_ge_atTop 1] with n h hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    exact ((div_lt_iff₀ (Real.sqrt_pos.mpr hn0)).mp h).le
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  let B : ℝ := ∑ j ∈ range N, |Real.log (HardyRamanujan.p j : ℝ)|
  have hB : 0 ≤ B := sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨B, hB, fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_add_of_nonneg_right hB)
  · have hb : Real.log (HardyRamanujan.p n : ℝ) ≤ B :=
      (le_abs_self _).trans (single_le_sum (s := range N)
        (f := fun j => |Real.log (HardyRamanujan.p j : ℝ)|)
        (fun _ _ => abs_nonneg _) (mem_range.mpr (Nat.lt_of_not_ge hn)))
    exact hb.trans (le_add_of_nonneg_left (mul_nonneg hA0 (Real.sqrt_nonneg _)))

/-- A finite convolution estimate; its prefactor is polynomial, so it does not alter leading entropy. -/
theorem log_count_upper {k : ℕ} (hk : 0 < k) (n : ℕ) {A B : ℝ} (hA : 0 ≤ A)
    (h : ∀ j : ℕ, Real.log (HardyRamanujan.p j : ℝ) ≤ A * √j + B) :
    Real.log (count k n : ℝ) ≤
      (k : ℝ) * Real.log ((n : ℝ) + 1) + A * √((k : ℝ) * n) + k * B := by
  have hterm (v : Sizes k n) :
      (∏ i : Fin k, (HardyRamanujan.p (v.1 i) : ℝ)) ≤
        Real.exp (A * √((k : ℝ) * n) + k * B) := by
    apply (Real.log_le_iff_le_exp (prod_pos (fun i _ => HardyRamanujan.partition_count_pos _))).mp
    rw [Real.log_prod (fun i _ => (HardyRamanujan.partition_count_pos _).ne')]
    calc
      ∑ i : Fin k, Real.log (HardyRamanujan.p (v.1 i) : ℝ) ≤
          ∑ i : Fin k, (A * √(v.1 i : ℝ) + B) := sum_le_sum (fun i _ => h _)
      _ = A * (∑ i : Fin k, √(v.1 i : ℝ)) + k * B := by
        rw [sum_add_distrib, ← mul_sum]
        simp
      _ ≤ A * √((k : ℝ) * n) + k * B :=
        add_le_add (mul_le_mul_of_nonneg_left (sizes_sqrt_le v) hA) le_rfl
  have hc : (count k n : ℝ) ≤ ((n : ℝ) + 1) ^ k *
      Real.exp (A * √((k : ℝ) * n) + k * B) := by
    calc
      (count k n : ℝ) = ∑ v : Sizes k n, ∏ i : Fin k,
          (HardyRamanujan.p (v.1 i) : ℝ) := by
        simp only [count_eq_sum, Nat.cast_sum, Nat.cast_prod, HardyRamanujan.p]
        exact (sum_coe_sort _ (fun v : Fin k →₀ ℕ =>
          ∏ i : Fin k, (Fintype.card (Nat.Partition (v i)) : ℝ))).symm
      _ ≤ ∑ _v : Sizes k n, Real.exp (A * √((k : ℝ) * n) + k * B) :=
        sum_le_sum (fun v _ => hterm v)
      _ = (Fintype.card (Sizes k n) : ℝ) *
          Real.exp (A * √((k : ℝ) * n) + k * B) := by simp
      _ ≤ ((n : ℝ) + 1) ^ k * Real.exp (A * √((k : ℝ) * n) + k * B) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact_mod_cast sizes_card_le k n
  have hc0 : (0 : ℝ) < count k n := by exact_mod_cast count_pos hk n
  have hlog := Real.log_le_log hc0 hc
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at hlog
  linarith

/-- Lower entropy bound from actual balanced colored partitions. -/
theorem log_count_lower {k : ℕ} (hk : 0 < k) (n : ℕ) :
    (k : ℝ) * Real.log (HardyRamanujan.p (n / k) : ℝ) ≤ Real.log (count k n : ℝ) := by
  have h : (HardyRamanujan.p (n / k) : ℝ) ^ k ≤ (count k n : ℝ) := by
    exact_mod_cast balanced_lower hk n
  have hlog := Real.log_le_log (pow_pos (HardyRamanujan.partition_count_pos _) _) h
  rwa [Real.log_pow] at hlog

lemma nat_div_tendsto {k : ℕ} (hk : 0 < k) : Tendsto (fun n : ℕ => n / k) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b * k)] with n hn
  exact (Nat.le_div_iff_mul_le hk).mpr hn

lemma nat_div_ratio {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => ((n / k : ℕ) : ℝ) / n) atTop (𝓝 (1 / (k : ℝ))) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_mod_div_atTop_nhds_zero_nat hk)).div_const (k : ℝ)
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have heq : (k : ℝ) * (n / k : ℕ) + (n % k : ℕ) = n := by
    exact_mod_cast Nat.div_add_mod n k
  field_simp
  nlinarith

lemma balanced_entropy_limit {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => (k : ℝ) * Real.log (HardyRamanujan.p (n / k) : ℝ) / √n)
      atTop (𝓝 (π * √(2 / 3 : ℝ) * √k)) := by
  have h := ((HardyRamanujan.entropy_sqrt_limit.comp (nat_div_tendsto hk)).mul
    (nat_div_ratio hk).sqrt).const_mul (k : ℝ)
  have hlim : (k : ℝ) * (π * √(2 / 3 : ℝ) * √(1 / (k : ℝ))) =
      π * √(2 / 3 : ℝ) * √k := by
    rw [Real.sqrt_div (show (0 : ℝ) ≤ 1 by norm_num), Real.sqrt_one]
    have hs : √(k : ℝ) ≠ 0 := by positivity
    have hsq := Real.sq_sqrt (Nat.cast_nonneg k)
    field_simp
    nlinarith
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop k] with n hn
  have hq : 0 < n / k := Nat.div_pos hn hk
  have hs : √((n / k : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Real.sqrt_div (Nat.cast_nonneg _)]
  simp only [Function.comp_def]
  field_simp

lemma log_succ_div_sqrt_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / √n) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / √n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ← Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (Real.tendsto_log_nat_add_one_sub_log.mul hinv).add hlog
  simp only [mul_zero, zero_add] at h
  refine h.congr fun n => ?_
  simp only [div_eq_mul_inv]
  ring

/-- Leading entropy of the actual finite count of colored partitions, for any fixed positive color count. -/
theorem entropy_sqrt_limit {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => Real.log (count k n : ℝ) / √n)
      atTop (𝓝 (π * √(2 / 3 : ℝ) * √k)) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : 0 < √(k : ℝ) := Real.sqrt_pos.mpr hkreal
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro b hb
    filter_upwards [(balanced_entropy_limit hk).eventually (eventually_gt_nhds hb)] with n hn
    exact hn.trans_le (div_le_div_of_nonneg_right (log_count_lower hk n) (Real.sqrt_nonneg _))
  · intro b hb
    obtain ⟨A, hA, hAb⟩ := exists_between ((lt_div_iff₀ hs).mpr hb)
    obtain ⟨B, _, hB⟩ := ordinary_log_upper hA
    have hA0 : 0 ≤ A := le_of_lt (lt_trans (by positivity) hA)
    have hab : A * √(k : ℝ) < b := (lt_div_iff₀ hs).mp hAb
    have hinv : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hu : Tendsto (fun n : ℕ => (k : ℝ) * (Real.log ((n : ℝ) + 1) / √n) +
        A * √(k : ℝ) + (k * B) * (√(n : ℝ))⁻¹) atTop (𝓝 (A * √(k : ℝ))) := by
      simpa using ((log_succ_div_sqrt_tendsto_zero.const_mul (k : ℝ)).add_const
        (A * √(k : ℝ))).add (hinv.const_mul ((k : ℝ) * B))
    filter_upwards [hu.eventually (eventually_lt_nhds hab), eventually_ge_atTop 1] with n hn hn1
    apply lt_of_le_of_lt _ hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hnreal
    have hbound := div_le_div_of_nonneg_right (log_count_upper hk n hA0 hB) hsn.le
    convert hbound using 1
    rw [Real.sqrt_mul (Nat.cast_nonneg k)]
    field_simp

/-- The 24-color constant is exactly `4π`. -/
theorem entropy_twentyfour :
    Tendsto (fun n : ℕ => Real.log (count 24 n : ℝ) / √n) atTop (𝓝 (4 * π)) := by
  have h := entropy_sqrt_limit (k := 24) (by decide)
  have heq : π * √(2 / 3 : ℝ) * √(24 : ℝ) = 4 * π := by
    rw [mul_assoc, ← Real.sqrt_mul (by norm_num)]
    norm_num
    ring
  simpa only [Nat.cast_ofNat, heq] using h

/-- The nonnegative-charge coefficients of `1/Δ`, including its one-unit index shift. -/
theorem degeneracy_entropy :
    Tendsto (fun n : ℕ => Real.log (degeneracy n : ℝ) / √n) atTop (𝓝 (4 * π)) := by
  have hr := ((tendsto_natCast_div_add_atTop (1 : ℝ)).inv₀ (by norm_num)).sqrt
  have hr' : Tendsto (fun n : ℕ => √((n : ℝ) + 1) / √n) atTop (𝓝 1) := by
    simp only [inv_div, inv_one, Real.sqrt_one] at hr
    exact hr.congr fun n => Real.sqrt_div (show 0 ≤ (n : ℝ) + 1 by positivity) (n : ℝ)
  have h := (entropy_twentyfour.comp (tendsto_add_atTop_nat 1)).mul hr'
  simp only [mul_one] at h
  refine h.congr fun n => ?_
  dsimp [degeneracy]
  push_cast
  have hs : √((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- The 24-color exponent in unifiedtheory's normalization `C_eff = 2`. -/
theorem cardy_leading_twentyfour (n : ℕ) :
    Cardy.leadingEntropy 2 n = 4 * π * √n := by
  unfold Cardy.leadingEntropy
  rw [show 2 * (2 : ℝ) * n = 2 ^ 2 * n by ring,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  ring

/-- Actual reciprocal-discriminant coefficients have the Cardy leading entropy. -/
theorem degeneracy_cardy_ratio :
    Tendsto (fun n : ℕ => Real.log (degeneracy n : ℝ) / Cardy.leadingEntropy 2 n)
      atTop (𝓝 1) := by
  have h := degeneracy_entropy.div_const (4 * π)
  rw [div_self (by positivity : (4 * π : ℝ) ≠ 0)] at h
  refine h.congr fun n => ?_
  rw [cardy_leading_twentyfour, div_div]
  congr 1
  ring

end ColoredPartitions
