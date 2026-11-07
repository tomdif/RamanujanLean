/-
# Final step 2: partial summation and the shifted-convolution bound
-/
import RamanujanTau.SCSProof.Final1

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open Finset MeasureTheory Set
open RamanujanTau.SubconvexityCond RamanujanTau.RankinError
open scoped Real

lemma Icc_zero_eq_range (m : ℕ) : Finset.Icc 0 m = Finset.range (m + 1) := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_range]; omega

lemma lam_mul_eq (h k : ℕ) (hk : 1 ≤ k) : lam k * lam (k + h) = wf h k * aR h k := by
  unfold lam wf aR
  push_cast
  ring

lemma shiftSum_eq_abel (h N : ℕ) :
    shiftSum h N = ∑ k ∈ Finset.Icc 0 N, wf h k * aR h k := by
  unfold shiftSum
  have ha0 : aR h 0 = 0 := by simp [aR, RamanujanTau.tau_zero]
  rw [show Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
    Finset.sum_insert (by simp), ha0, mul_zero, zero_add]
  exact Finset.sum_congr rfl fun k hk => lam_mul_eq h k (Finset.mem_Icc.1 hk).1

/-- `∫_{(1,N]} t^{−ρ} ≤ 2 N^{1−ρ}`. -/
lemma integral_rpow_neg_rho (N : ℕ) (hN : 1 ≤ N) :
    ∫ t in Set.Ioc (1 : ℝ) N, t ^ (-ρ) ≤ 2 * (N : ℝ) ^ (1 - ρ) := by
  have hρ := ρ_pos; have hρ8 := ρ_le
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [← intervalIntegral.integral_of_le hNR, integral_rpow (Or.inl (by linarith))]
  have e : -ρ + 1 = 1 - ρ := by ring
  rw [e, Real.one_rpow]
  have hp : 0 ≤ (N : ℝ) ^ (1 - ρ) := Real.rpow_nonneg (by linarith) _
  rw [div_le_iff₀ (by linarith)]
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **The shifted-convolution bound** `|Σ_{n≤N} λ(n)λ(n+h)| ≤ C (N+h)^{1−ρ} h⁸`. -/
theorem shiftSum_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ h N : ℕ, 1 ≤ h →
    |shiftSum h N| ≤ C * ((N : ℝ) + h) ^ (1 - ρ) * (h : ℝ) ^ (8 : ℝ) := by
  obtain ⟨C, hC0, hA⟩ := Asum_bound
  refine ⟨23 * 2 ^ 7 * C, by positivity, fun h N hh => ?_⟩
  have hρ := ρ_pos; have hρ8 := ρ_le
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
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
  -- boundary term
  have hb : |wf h N * Asum h N| ≤ C * h * (1 + h) ^ (11 / 2 : ℝ) * M ^ (1 - ρ) := by
    rw [abs_mul]
    have hw : |wf h N| = (N : ℝ) ^ (-(11 / 2 : ℝ)) * M ^ (-(11 / 2 : ℝ)) := by
      unfold wf; rw [abs_of_pos (by positivity)]
    rw [hw]
    have hMN : M ≤ N * (1 + h) := by nlinarith
    have hpowM : M ^ (11 / 2 : ℝ) ≤ (N : ℝ) ^ (11 / 2 : ℝ) * (1 + h) ^ (11 / 2 : ℝ) := by
      rw [← Real.mul_rpow (by linarith) (by linarith)]
      exact Real.rpow_le_rpow hM0.le hMN (by norm_num)
    have e : M ^ (12 - ρ) = M ^ (1 - ρ) * M ^ (11 / 2 : ℝ) * M ^ (11 / 2 : ℝ) := by
      rw [← Real.rpow_add hM0, ← Real.rpow_add hM0]; norm_num; ring_nf
    have hNp : 0 < (N : ℝ) ^ (11 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hMp : 0 < M ^ (11 / 2 : ℝ) := Real.rpow_pos_of_pos hM0 _
    have i1 : (N : ℝ) ^ (-(11 / 2 : ℝ)) = 1 / (N : ℝ) ^ (11 / 2 : ℝ) := by
      rw [Real.rpow_neg (by linarith), one_div]
    have i2 : M ^ (-(11 / 2 : ℝ)) = 1 / M ^ (11 / 2 : ℝ) := by
      rw [Real.rpow_neg hM0.le, one_div]
    rw [i1, i2]
    calc 1 / (N : ℝ) ^ (11 / 2 : ℝ) * (1 / M ^ (11 / 2 : ℝ)) * |Asum h N|
        ≤ 1 / (N : ℝ) ^ (11 / 2 : ℝ) * (1 / M ^ (11 / 2 : ℝ)) * (C * h * M ^ (12 - ρ)) := by
          gcongr; exact hA h hh N
      _ = C * h * M ^ (1 - ρ) * (M ^ (11 / 2 : ℝ) / (N : ℝ) ^ (11 / 2 : ℝ)) := by
          rw [e]; field_simp
      _ ≤ C * h * M ^ (1 - ρ) * (1 + h) ^ (11 / 2 : ℝ) := by
          gcongr
          rw [div_le_iff₀ hNp]; linarith
      _ = _ := by ring
  -- integral term
  have hB : ∀ t ∈ Set.Ioc (1 : ℝ) N, ‖deriv (wf h) t * Asum h ⌊t⌋₊‖ ≤
      11 * C * h * (1 + h) ^ (13 / 2 : ℝ) * t ^ (-ρ) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : 1 ≤ t := ht.1.le
    rw [deriv_wf h ht0, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
    have hAt := hA h hh ⌊t⌋₊
    have hAt' : |Asum h ⌊t⌋₊| ≤ C * h * (t + h) ^ (12 - ρ) := by
      refine hAt.trans ?_
      gcongr
      linarith
    have hth0 : 0 < t + h := by linarith
    have hth : t + h ≤ t * (1 + h) := by nlinarith
    have hpow : (t + h) ^ (13 / 2 - ρ) ≤ t ^ (13 / 2 - ρ) * (1 + h) ^ (13 / 2 : ℝ) := by
      calc (t + h) ^ (13 / 2 - ρ) ≤ (t * (1 + h)) ^ (13 / 2 - ρ) :=
            Real.rpow_le_rpow hth0.le hth (by linarith)
        _ = t ^ (13 / 2 - ρ) * (1 + h) ^ (13 / 2 - ρ) := Real.mul_rpow ht0.le (by linarith)
        _ ≤ t ^ (13 / 2 - ρ) * (1 + h) ^ (13 / 2 : ℝ) := by
            gcongr
            · linarith
            · linarith
    have e1 : (t + h) ^ (-(11 / 2 : ℝ)) * (t + h) ^ (12 - ρ) = (t + h) ^ (13 / 2 - ρ) := by
      rw [← Real.rpow_add hth0]; ring_nf
    have e2 : t ^ (-(13 / 2 : ℝ)) * t ^ (13 / 2 - ρ) = t ^ (-ρ) := by
      rw [← Real.rpow_add ht0]; ring_nf
    calc |wf' h t| * |Asum h ⌊t⌋₊|
        ≤ (11 * t ^ (-(13 / 2 : ℝ)) * (t + h) ^ (-(11 / 2 : ℝ))) * (C * h * (t + h) ^ (12 - ρ)) := by
          gcongr
          · exact abs_wf'_le h ht0
      _ = 11 * C * h * (t ^ (-(13 / 2 : ℝ)) * ((t + h) ^ (-(11 / 2 : ℝ)) * (t + h) ^ (12 - ρ))) := by
          ring
      _ = 11 * C * h * (t ^ (-(13 / 2 : ℝ)) * (t + h) ^ (13 / 2 - ρ)) := by rw [e1]
      _ ≤ 11 * C * h * (t ^ (-(13 / 2 : ℝ)) * (t ^ (13 / 2 - ρ) * (1 + h) ^ (13 / 2 : ℝ))) := by
          gcongr
      _ = 11 * C * h * (1 + h) ^ (13 / 2 : ℝ) * (t ^ (-(13 / 2 : ℝ)) * t ^ (13 / 2 - ρ)) := by ring
      _ = 11 * C * h * (1 + h) ^ (13 / 2 : ℝ) * t ^ (-ρ) := by rw [e2]
  have hBint : IntegrableOn (fun t : ℝ => 11 * C * h * (1 + h) ^ (13 / 2 : ℝ) * t ^ (-ρ))
      (Set.Ioc (1 : ℝ) N) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    refine continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl ?_)
    have := ht.1; show (t : ℝ) ≠ 0; linarith
  have hI : ‖∫ t in Set.Ioc (1 : ℝ) N, deriv (wf h) t * Asum h ⌊t⌋₊‖ ≤
      11 * C * h * (1 + h) ^ (13 / 2 : ℝ) * (2 * (N : ℝ) ^ (1 - ρ)) := by
    refine (norm_integral_le_of_norm_le hBint ((ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall hB))).trans ?_
    rw [integral_const_mul]
    gcongr
    exact integral_rpow_neg_rho N hN
  -- combine
  have hNM : (N : ℝ) ^ (1 - ρ) ≤ M ^ (1 - ρ) := Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  have h1h : (1 : ℝ) + h ≤ 2 * h := by linarith
  have hp1 : (1 + (h : ℝ)) ^ (11 / 2 : ℝ) ≤ (1 + (h : ℝ)) ^ (13 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hp2 : (1 + (h : ℝ)) ^ (13 / 2 : ℝ) ≤ 2 ^ 7 * (h : ℝ) ^ (7 : ℝ) := by
    calc (1 + (h : ℝ)) ^ (13 / 2 : ℝ) ≤ (2 * h) ^ (13 / 2 : ℝ) := Real.rpow_le_rpow (by linarith) h1h
          (by norm_num)
      _ ≤ (2 * h) ^ (7 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = 2 ^ 7 * (h : ℝ) ^ (7 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) (by linarith)]; norm_num
  have hh8 : (h : ℝ) * (h : ℝ) ^ (7 : ℝ) = (h : ℝ) ^ (8 : ℝ) := by
    rw [show (8 : ℝ) = 1 + 7 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  have hMp : 0 ≤ M ^ (1 - ρ) := Real.rpow_nonneg hM0.le _
  calc |wf h N * Asum h N - ∫ t in Set.Ioc (1 : ℝ) N, deriv (wf h) t * Asum h ⌊t⌋₊|
      ≤ |wf h N * Asum h N| + ‖∫ t in Set.Ioc (1 : ℝ) N, deriv (wf h) t * Asum h ⌊t⌋₊‖ := by
        rw [Real.norm_eq_abs]; exact abs_sub _ _
    _ ≤ C * h * (1 + h) ^ (11 / 2 : ℝ) * M ^ (1 - ρ) +
          11 * C * h * (1 + h) ^ (13 / 2 : ℝ) * (2 * (N : ℝ) ^ (1 - ρ)) := add_le_add hb hI
    _ ≤ C * h * (1 + h) ^ (13 / 2 : ℝ) * M ^ (1 - ρ) +
          11 * C * h * (1 + h) ^ (13 / 2 : ℝ) * (2 * M ^ (1 - ρ)) := by gcongr
    _ = 23 * C * (h * (1 + h) ^ (13 / 2 : ℝ)) * M ^ (1 - ρ) := by ring
    _ ≤ 23 * C * (h * (2 ^ 7 * (h : ℝ) ^ (7 : ℝ))) * M ^ (1 - ρ) := by gcongr
    _ = 23 * 2 ^ 7 * C * M ^ (1 - ρ) * (h * (h : ℝ) ^ (7 : ℝ)) := by ring
    _ = 23 * 2 ^ 7 * C * M ^ (1 - ρ) * (h : ℝ) ^ (8 : ℝ) := by rw [hh8]

end RamanujanTau.SCSProof
