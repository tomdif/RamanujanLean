/-
# The sharp shifted-convolution bound `SCS(1/22, 1/2)`

`shiftSum_bound'`: `|Σ_{n≤N} λ(n)λ(n+h)| ≤ C (N+h)^{1−1/22} √h`.

Abel summation as in `SCSProof.shiftSum_bound`, but the range `t < h` (where the weight
`t^{−11/2}(t+h)^{−11/2}` is not `≍ t^{−11}`) is handled by the Cauchy–Schwarz bound
`|Σ_{n≤m} τ(n)τ(n+h)| ≤ A m⁶(m+h)⁶` instead of the `h`-power bound; this removes the
`(1+h)^{13/2}` loss and gives `B = 1/2` (the `√h` of the Weil step) instead of `B = 8`.
-/
import RamanujanTau.SCSSharp.Asum

set_option autoImplicit false

namespace RamanujanTau.SCSSharp

open Finset MeasureTheory Set
open RamanujanTau.SubconvexityCond RamanujanTau.RankinError RamanujanTau.SCSProof
open scoped Real

/-- **Cauchy–Schwarz bound** `|Σ_{n≤m} τ(n)τ(n+h)| ≤ A m⁶ (m+h)⁶`. -/
theorem Asum_cs : ∃ A : ℝ, 0 ≤ A ∧ ∀ h m : ℕ,
    |Asum h m| ≤ A * (m : ℝ) ^ 6 * ((m : ℝ) + h) ^ 6 := by
  obtain ⟨A, hA0, hA⟩ := exists_sum_lam_sq_le
  refine ⟨A, hA0, fun h m => ?_⟩
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmh : (m : ℝ) ≤ m + h := by have := Nat.cast_nonneg (α := ℝ) h; linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (range (m + 1)) (fun n => (tau n : ℝ))
    (fun n => (tau (n + h) : ℝ))
  have h1 : ∑ n ∈ range (m + 1), (tau n : ℝ) ^ 2 ≤ A * (m : ℝ) ^ 12 := by
    calc ∑ n ∈ range (m + 1), (tau n : ℝ) ^ 2
        = ∑ n ∈ range (m + 1), lam n ^ 2 * (n : ℝ) ^ 11 := by simp_rw [lam_sq_eq]
      _ ≤ ∑ n ∈ range (m + 1), lam n ^ 2 * (m : ℝ) ^ 11 := by
          refine sum_le_sum fun n hn => ?_
          have : (n : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hn)
          gcongr
      _ = Slam m * (m : ℝ) ^ 11 := by rw [← sum_mul, sum_range_eq_Slam]
      _ ≤ (A * m) * (m : ℝ) ^ 11 := by gcongr; exact hA m
      _ = A * (m : ℝ) ^ 12 := by ring
  have h2 : ∑ n ∈ range (m + 1), (tau (n + h) : ℝ) ^ 2 ≤ A * ((m : ℝ) + h) ^ 12 := by
    calc ∑ n ∈ range (m + 1), (tau (n + h) : ℝ) ^ 2
        = ∑ n ∈ range (m + 1), lam (n + h) ^ 2 * ((n + h : ℕ) : ℝ) ^ 11 := by
          simp_rw [lam_sq_eq]
      _ ≤ ∑ n ∈ range (m + 1), lam (n + h) ^ 2 * ((m : ℝ) + h) ^ 11 := by
          refine sum_le_sum fun n hn => ?_
          have : (n : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hn)
          push_cast
          gcongr
      _ = (∑ n ∈ range (m + 1), lam (n + h) ^ 2) * ((m : ℝ) + h) ^ 11 := by rw [← sum_mul]
      _ ≤ Slam (m + h) * ((m : ℝ) + h) ^ 11 := by gcongr; exact sum_lam_shift h m
      _ ≤ (A * ((m : ℝ) + h)) * ((m : ℝ) + h) ^ 11 := by
          gcongr; have := hA (m + h); push_cast at this; exact this
      _ = A * ((m : ℝ) + h) ^ 12 := by ring
  have hsq : (Asum h m) ^ 2 ≤ (A * (m : ℝ) ^ 6 * ((m : ℝ) + h) ^ 6) ^ 2 := by
    have e : Asum h m = ∑ n ∈ range (m + 1), (tau n : ℝ) * (tau (n + h) : ℝ) := by
      unfold Asum aR; push_cast; rfl
    rw [e]
    refine hcs.trans ?_
    calc (∑ n ∈ range (m + 1), (tau n : ℝ) ^ 2) * ∑ n ∈ range (m + 1), (tau (n + h) : ℝ) ^ 2
        ≤ (A * (m : ℝ) ^ 12) * (A * ((m : ℝ) + h) ^ 12) :=
          mul_le_mul h1 h2 (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = _ := by ring
  have := sq_le_sq.1 hsq
  rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ A * (m : ℝ) ^ 6 * ((m : ℝ) + h) ^ 6)] at this

/-- `∫_{(1,N]} t^{−a} ≤ 2 N^{1−a}` for `0 ≤ a ≤ 1/2`. -/
lemma integral_rpow_neg_le (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (N : ℕ) (hN : 1 ≤ N) :
    ∫ t in Set.Ioc (1 : ℝ) N, t ^ (-a) ≤ 2 * (N : ℝ) ^ (1 - a) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [← intervalIntegral.integral_of_le hNR, integral_rpow (Or.inl (by linarith))]
  have e : -a + 1 = 1 - a := by ring
  rw [e, Real.one_rpow]
  have hp : 0 ≤ (N : ℝ) ^ (1 - a) := Real.rpow_nonneg (by linarith) _
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma sqrt_two_mul_le (h : ℝ) (hh : 0 ≤ h) : Real.sqrt (2 * h) ≤ 2 * Real.sqrt h := by
  rw [Real.sqrt_mul (by norm_num)]
  have : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have := Real.sqrt_nonneg h
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **The sharp shifted-convolution bound** `|Σ_{n≤N} λ(n)λ(n+h)| ≤ C (N+h)^{1−1/22} √h`. -/
theorem shiftSum_bound' : ∃ C : ℝ, 0 ≤ C ∧ ∀ h N : ℕ, 1 ≤ h →
    |shiftSum h N| ≤ C * ((N : ℝ) + h) ^ (1 - ηs) * Real.sqrt h := by
  obtain ⟨C, hC0, hL⟩ := Asum_bound_large'
  obtain ⟨A, hA0, hcs⟩ := Asum_cs
  set K2 : ℝ := 11 * 2 ^ 7 * C + 22 * A
  have hK2 : 0 ≤ K2 := by positivity
  refine ⟨2 ^ 6 * C + A + 4 * K2, by positivity, fun h N hh => ?_⟩
  have hη := ηs_pos; have hη2 := ηs_le
  have hηh : ηs ≤ 1 / 2 := by unfold ηs; norm_num
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hsh : (1 : ℝ) ≤ Real.sqrt h := by rw [Real.one_le_sqrt]; exact hhR
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [shiftSum]; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set M := (N : ℝ) + h
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  -- Abel summation
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) N, DifferentiableAt ℝ (wf h) t := fun t ht =>
    (hasDerivAt_wf h (by linarith [ht.1])).differentiableAt
  have hint : IntegrableOn (deriv (wf h)) (Set.Icc (1 : ℝ) N) := by
    refine ((continuousOn_wf' h).mono fun t ht => (show (0 : ℝ) < t by linarith [ht.1])).integrableOn_Icc
      |>.congr_fun (fun t ht => (deriv_wf h (by linarith [ht.1])).symm) measurableSet_Icc
  have hAbel := sum_mul_eq_sub_integral_mul₀' (aR h) (by simp [aR, RamanujanTau.tau_zero]) N hdiff
    hint
  rw [← shiftSum_eq_abel] at hAbel
  have hAs : ∀ m : ℕ, ∑ k ∈ Finset.Icc 0 m, aR h k = Asum h m := fun m => by
    rw [Icc_zero_eq_range]; rfl
  simp_rw [hAs] at hAbel
  rw [hAbel]
  have hMη : 0 ≤ M ^ (1 - ηs) := Real.rpow_nonneg hM0.le _
  -- boundary term
  have hb : |wf h N * Asum h N| ≤ (2 ^ 6 * C + A) * Real.sqrt h * M ^ (1 - ηs) := by
    rw [abs_mul]
    have hw : |wf h N| = (N : ℝ) ^ (-(11 / 2 : ℝ)) * M ^ (-(11 / 2 : ℝ)) := by
      unfold wf; rw [abs_of_pos (by positivity)]
    rw [hw]
    have hNp : 0 < (N : ℝ) ^ (11 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hMp : 0 < M ^ (11 / 2 : ℝ) := Real.rpow_pos_of_pos hM0 _
    have i1 : (N : ℝ) ^ (-(11 / 2 : ℝ)) = 1 / (N : ℝ) ^ (11 / 2 : ℝ) := by
      rw [Real.rpow_neg (by linarith), one_div]
    have i2 : M ^ (-(11 / 2 : ℝ)) = 1 / M ^ (11 / 2 : ℝ) := by
      rw [Real.rpow_neg hM0.le, one_div]
    rw [i1, i2]
    rcases le_or_gt h N with hhN | hNh
    · have hMN : M ≤ 2 * N := by
        have : (h : ℝ) ≤ N := by exact_mod_cast hhN
        show (N : ℝ) + h ≤ 2 * N; linarith
      have hpowM : M ^ (11 / 2 : ℝ) ≤ 2 ^ 6 * (N : ℝ) ^ (11 / 2 : ℝ) := by
        calc M ^ (11 / 2 : ℝ) ≤ (2 * N) ^ (11 / 2 : ℝ) := Real.rpow_le_rpow hM0.le hMN (by norm_num)
          _ = 2 ^ (11 / 2 : ℝ) * (N : ℝ) ^ (11 / 2 : ℝ) := Real.mul_rpow (by norm_num) (by linarith)
          _ ≤ 2 ^ 6 * (N : ℝ) ^ (11 / 2 : ℝ) := by
              gcongr
              calc (2 : ℝ) ^ (11 / 2 : ℝ) ≤ 2 ^ (6 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 2 ^ 6 := by norm_num
      have e : M ^ (12 - ηs) = M ^ (1 - ηs) * M ^ (11 / 2 : ℝ) * M ^ (11 / 2 : ℝ) := by
        rw [← Real.rpow_add hM0, ← Real.rpow_add hM0]; norm_num; ring_nf
      calc 1 / (N : ℝ) ^ (11 / 2 : ℝ) * (1 / M ^ (11 / 2 : ℝ)) * |Asum h N|
          ≤ 1 / (N : ℝ) ^ (11 / 2 : ℝ) * (1 / M ^ (11 / 2 : ℝ)) * (C * Real.sqrt h * M ^ (12 - ηs)) := by
            gcongr; exact hL h hh N hhN
        _ = C * Real.sqrt h * M ^ (1 - ηs) * (M ^ (11 / 2 : ℝ) / (N : ℝ) ^ (11 / 2 : ℝ)) := by
            rw [e]; field_simp
        _ ≤ C * Real.sqrt h * M ^ (1 - ηs) * 2 ^ 6 := by
            gcongr
            rw [div_le_iff₀ hNp]; linarith
        _ ≤ (2 ^ 6 * C + A) * Real.sqrt h * M ^ (1 - ηs) := by
            have : 0 ≤ A * Real.sqrt h * M ^ (1 - ηs) := by positivity
            nlinarith
    · have hNh' : (N : ℝ) < h := by exact_mod_cast hNh
      have hc := hcs h N
      have e6 : (N : ℝ) ^ 6 = (N : ℝ) ^ (11 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add (by linarith), ← Real.rpow_natCast]; norm_num
      have e6' : M ^ 6 = M ^ (11 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hM0, ← Real.rpow_natCast]; norm_num
      have hNs : (N : ℝ) ^ (1 / 2 : ℝ) ≤ Real.sqrt h := by
        rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt hNh'.le
      have hMs : M ^ (1 / 2 : ℝ) ≤ M ^ (1 - ηs) :=
        Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
      calc 1 / (N : ℝ) ^ (11 / 2 : ℝ) * (1 / M ^ (11 / 2 : ℝ)) * |Asum h N|
          ≤ 1 / (N : ℝ) ^ (11 / 2 : ℝ) * (1 / M ^ (11 / 2 : ℝ)) * (A * (N : ℝ) ^ 6 * M ^ 6) := by
            gcongr
        _ = A * (N : ℝ) ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by rw [e6, e6']; field_simp
        _ ≤ A * Real.sqrt h * M ^ (1 - ηs) := by gcongr
        _ ≤ (2 ^ 6 * C + A) * Real.sqrt h * M ^ (1 - ηs) := by
            have : 0 ≤ 2 ^ 6 * C * Real.sqrt h * M ^ (1 - ηs) := by positivity
            nlinarith
  -- integral term
  have hB : ∀ t ∈ Set.Ioc (1 : ℝ) N, ‖deriv (wf h) t * Asum h ⌊t⌋₊‖ ≤
      K2 * Real.sqrt h * (t ^ (-ηs) + t ^ (-(1 / 2 : ℝ))) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : 1 ≤ t := ht.1.le
    rw [deriv_wf h ht0, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
    have hfl2 : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
    have hth0 : 0 < t + h := by linarith
    have hw := abs_wf'_le h ht0
    have hp1 : 0 ≤ t ^ (-ηs) := Real.rpow_nonneg ht0.le _
    have hp2 : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht0.le _
    rcases le_or_gt h ⌊t⌋₊ with hhm | hmh
    · have hhm' : (h : ℝ) ≤ t := le_trans (by exact_mod_cast hhm) hfl
      have hAt : |Asum h ⌊t⌋₊| ≤ C * Real.sqrt h * (t + h) ^ (12 - ηs) := by
        refine (hL h hh _ hhm).trans ?_
        gcongr
        linarith
      have hth : t + h ≤ 2 * t := by linarith
      have hpow : (t + h) ^ (13 / 2 - ηs) ≤ 2 ^ 7 * t ^ (13 / 2 - ηs) := by
        calc (t + h) ^ (13 / 2 - ηs) ≤ (2 * t) ^ (13 / 2 - ηs) :=
              Real.rpow_le_rpow hth0.le hth (by linarith)
          _ = 2 ^ (13 / 2 - ηs) * t ^ (13 / 2 - ηs) := Real.mul_rpow (by norm_num) ht0.le
          _ ≤ 2 ^ 7 * t ^ (13 / 2 - ηs) := by
              gcongr
              calc (2 : ℝ) ^ (13 / 2 - ηs) ≤ 2 ^ (7 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                _ = 2 ^ 7 := by norm_num
      have e1 : (t + h) ^ (-(11 / 2 : ℝ)) * (t + h) ^ (12 - ηs) = (t + h) ^ (13 / 2 - ηs) := by
        rw [← Real.rpow_add hth0]; ring_nf
      have e2 : t ^ (-(13 / 2 : ℝ)) * t ^ (13 / 2 - ηs) = t ^ (-ηs) := by
        rw [← Real.rpow_add ht0]; ring_nf
      calc |wf' h t| * |Asum h ⌊t⌋₊|
          ≤ (11 * t ^ (-(13 / 2 : ℝ)) * (t + h) ^ (-(11 / 2 : ℝ))) *
              (C * Real.sqrt h * (t + h) ^ (12 - ηs)) := by gcongr
        _ = 11 * C * Real.sqrt h * (t ^ (-(13 / 2 : ℝ)) *
              ((t + h) ^ (-(11 / 2 : ℝ)) * (t + h) ^ (12 - ηs))) := by ring
        _ = 11 * C * Real.sqrt h * (t ^ (-(13 / 2 : ℝ)) * (t + h) ^ (13 / 2 - ηs)) := by rw [e1]
        _ ≤ 11 * C * Real.sqrt h * (t ^ (-(13 / 2 : ℝ)) * (2 ^ 7 * t ^ (13 / 2 - ηs))) := by
            gcongr
        _ = 11 * 2 ^ 7 * C * Real.sqrt h * (t ^ (-(13 / 2 : ℝ)) * t ^ (13 / 2 - ηs)) := by ring
        _ = 11 * 2 ^ 7 * C * Real.sqrt h * t ^ (-ηs) := by rw [e2]
        _ ≤ K2 * Real.sqrt h * (t ^ (-ηs) + t ^ (-(1 / 2 : ℝ))) := by
            have h0 : 0 ≤ Real.sqrt h := Real.sqrt_nonneg _
            have : 11 * 2 ^ 7 * C ≤ K2 := by simp only [K2]; linarith
            calc 11 * 2 ^ 7 * C * Real.sqrt h * t ^ (-ηs)
                ≤ K2 * Real.sqrt h * t ^ (-ηs) := by gcongr
              _ ≤ _ := by
                  have : 0 ≤ K2 * Real.sqrt h * t ^ (-(1 / 2 : ℝ)) := by positivity
                  nlinarith
    · have hmh' : t < h := by
        have : ((⌊t⌋₊ : ℕ) : ℝ) + 1 ≤ h := by exact_mod_cast hmh
        linarith
      have hAt : |Asum h ⌊t⌋₊| ≤ A * t ^ 6 * (t + h) ^ 6 := by
        refine (hcs h _).trans ?_
        have : (0 : ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
        gcongr
      have e1 : t ^ (-(13 / 2 : ℝ)) * t ^ 6 = t ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add ht0]; norm_num
      have e2 : (t + h) ^ (-(11 / 2 : ℝ)) * (t + h) ^ 6 = Real.sqrt (t + h) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hth0, Real.sqrt_eq_rpow]; norm_num
      have hs2 : Real.sqrt (t + h) ≤ 2 * Real.sqrt h :=
        (Real.sqrt_le_sqrt (by linarith : t + h ≤ 2 * h)).trans
          (sqrt_two_mul_le h (Nat.cast_nonneg _))
      calc |wf' h t| * |Asum h ⌊t⌋₊|
          ≤ (11 * t ^ (-(13 / 2 : ℝ)) * (t + h) ^ (-(11 / 2 : ℝ))) * (A * t ^ 6 * (t + h) ^ 6) := by
            gcongr
        _ = 11 * A * (t ^ (-(13 / 2 : ℝ)) * t ^ 6) * ((t + h) ^ (-(11 / 2 : ℝ)) * (t + h) ^ 6) := by
            ring
        _ = 11 * A * t ^ (-(1 / 2 : ℝ)) * Real.sqrt (t + h) := by rw [e1, e2]
        _ ≤ 11 * A * t ^ (-(1 / 2 : ℝ)) * (2 * Real.sqrt h) := by gcongr
        _ = 22 * A * Real.sqrt h * t ^ (-(1 / 2 : ℝ)) := by ring
        _ ≤ K2 * Real.sqrt h * (t ^ (-ηs) + t ^ (-(1 / 2 : ℝ))) := by
            have h0 : 0 ≤ Real.sqrt h := Real.sqrt_nonneg _
            have hC' : 0 ≤ 11 * 2 ^ 7 * C := by positivity
            have : 22 * A ≤ K2 := by simp only [K2]; linarith
            calc 22 * A * Real.sqrt h * t ^ (-(1 / 2 : ℝ))
                ≤ K2 * Real.sqrt h * t ^ (-(1 / 2 : ℝ)) := by gcongr
              _ ≤ _ := by
                  have : 0 ≤ K2 * Real.sqrt h * t ^ (-ηs) := by positivity
                  nlinarith
  have hint1 : IntegrableOn (fun t : ℝ => t ^ (-ηs)) (Set.Ioc (1 : ℝ) N) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (by
      have := ht.1; show (t : ℝ) ≠ 0; linarith)
  have hint2 : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Set.Ioc (1 : ℝ) N) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (by
      have := ht.1; show (t : ℝ) ≠ 0; linarith)
  have hBint : IntegrableOn (fun t : ℝ => K2 * Real.sqrt h * (t ^ (-ηs) + t ^ (-(1 / 2 : ℝ))))
      (Set.Ioc (1 : ℝ) N) := (hint1.add hint2).const_mul _
  have hI : ‖∫ t in Set.Ioc (1 : ℝ) N, deriv (wf h) t * Asum h ⌊t⌋₊‖ ≤
      K2 * Real.sqrt h * (2 * (N : ℝ) ^ (1 - ηs) + 2 * (N : ℝ) ^ (1 - 1 / 2 : ℝ)) := by
    refine (norm_integral_le_of_norm_le hBint ((ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall hB))).trans ?_
    rw [integral_const_mul, integral_add hint1 hint2]
    gcongr
    · exact integral_rpow_neg_le ηs hη.le hηh N hN
    · exact integral_rpow_neg_le (1 / 2) (by norm_num) le_rfl N hN
  -- combine
  have hNM : (N : ℝ) ^ (1 - ηs) ≤ M ^ (1 - ηs) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  have hNM2 : (N : ℝ) ^ (1 - 1 / 2 : ℝ) ≤ M ^ (1 - ηs) :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans hNM
  calc |wf h N * Asum h N - ∫ t in Set.Ioc (1 : ℝ) N, deriv (wf h) t * Asum h ⌊t⌋₊|
      ≤ |wf h N * Asum h N| + ‖∫ t in Set.Ioc (1 : ℝ) N, deriv (wf h) t * Asum h ⌊t⌋₊‖ := by
        rw [Real.norm_eq_abs]; exact abs_sub _ _
    _ ≤ (2 ^ 6 * C + A) * Real.sqrt h * M ^ (1 - ηs) +
          K2 * Real.sqrt h * (2 * (N : ℝ) ^ (1 - ηs) + 2 * (N : ℝ) ^ (1 - 1 / 2 : ℝ)) :=
        add_le_add hb hI
    _ ≤ (2 ^ 6 * C + A) * Real.sqrt h * M ^ (1 - ηs) +
          K2 * Real.sqrt h * (2 * M ^ (1 - ηs) + 2 * M ^ (1 - ηs)) := by gcongr
    _ = (2 ^ 6 * C + A + 4 * K2) * M ^ (1 - ηs) * Real.sqrt h := by ring

end RamanujanTau.SCSSharp
