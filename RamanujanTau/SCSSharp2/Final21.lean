/-
# `SCS(1/21, 1/21)`

Copy of `shiftSum_boundG` for the `η = 1/21` chain.
-/
import RamanujanTau.SCSSharp2.Final
import RamanujanTau.SCSSharp2.Asum21

set_option autoImplicit false

namespace RamanujanTau.SCSSharp2

open Finset MeasureTheory Set
open RamanujanTau.SubconvexityCond RamanujanTau.RankinError RamanujanTau.SCSProof RamanujanTau.SCSSharp
open scoped Real

set_option maxHeartbeats 4000000 in
/-- **Shifted-convolution bound** `|Σ_{n≤N} λ(n)λ(n+h)| ≤ C (N+h)^{1−1/21} h^{1/21}`. -/
theorem shiftSum_bound21 : ∃ C : ℝ, 0 ≤ C ∧ ∀ h N : ℕ, 1 ≤ h →
    |shiftSum h N| ≤ C * ((N : ℝ) + h) ^ (1 - ηt) * (h : ℝ) ^ (1 / 21 : ℝ) := by
  obtain ⟨C, hC0, hL⟩ := Asum_bound_large21
  obtain ⟨A, hA0, hcs⟩ := Asum_cs
  set K2 : ℝ := 11 * 2 ^ 7 * C + 22 * A
  have hK2 : 0 ≤ K2 := by positivity
  refine ⟨2 ^ 6 * C + A + 4 * K2, by positivity, fun h N hh => ?_⟩
  have hη := ηt_pos; have hη2 := ηt_le
  have hηh : ηt ≤ 1 / 2 := by unfold ηt; norm_num
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hsh : (1 : ℝ) ≤ (h : ℝ) ^ (1 / 21 : ℝ) := Real.one_le_rpow hhR (by norm_num)
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
  have hMη : 0 ≤ M ^ (1 - ηt) := Real.rpow_nonneg hM0.le _
  -- boundary term
  have hb : |wf h N * Asum h N| ≤ (2 ^ 6 * C + A) * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) := by
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
      have e : M ^ (12 - ηt) = M ^ (1 - ηt) * M ^ (11 / 2 : ℝ) * M ^ (11 / 2 : ℝ) := by
        rw [← Real.rpow_add hM0, ← Real.rpow_add hM0]; norm_num; ring_nf
      calc 1 / (N : ℝ) ^ (11 / 2 : ℝ) * (1 / M ^ (11 / 2 : ℝ)) * |Asum h N|
          ≤ 1 / (N : ℝ) ^ (11 / 2 : ℝ) * (1 / M ^ (11 / 2 : ℝ)) * (C * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (12 - ηt)) := by
            gcongr; exact hL h hh N hhN
        _ = C * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) * (M ^ (11 / 2 : ℝ) / (N : ℝ) ^ (11 / 2 : ℝ)) := by
            rw [e]; field_simp
        _ ≤ C * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) * 2 ^ 6 := by
            gcongr
            rw [div_le_iff₀ hNp]; linarith
        _ ≤ (2 ^ 6 * C + A) * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) := by
            have : 0 ≤ A * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) := by positivity
            nlinarith
    · have hNh' : (N : ℝ) < h := by exact_mod_cast hNh
      have hc := hcs h N
      have e6 : (N : ℝ) ^ 6 = (N : ℝ) ^ (11 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add (by linarith), ← Real.rpow_natCast]; norm_num
      have e6' : M ^ 6 = M ^ (11 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hM0, ← Real.rpow_natCast]; norm_num
      have hNs : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 / 2 - ηt) := by
        have h1 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (h : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by linarith) hNh'.le (by norm_num)
        have h2 : (h : ℝ) ^ (1 / 2 : ℝ) = (h : ℝ) ^ (1 / 21 : ℝ) * (h : ℝ) ^ (1 / 2 - ηt) := by
          rw [← Real.rpow_add (by linarith)]; unfold ηt; norm_num
        have h3 : (h : ℝ) ^ (1 / 2 - ηt) ≤ M ^ (1 / 2 - ηt) :=
          Real.rpow_le_rpow (by linarith) (by show (h : ℝ) ≤ N + h; linarith) (by linarith)
        rw [h2] at h1
        exact h1.trans (by gcongr)
      have hMs : M ^ (1 / 2 - ηt) * M ^ (1 / 2 : ℝ) = M ^ (1 - ηt) := by
        rw [← Real.rpow_add hM0]; ring_nf
      calc 1 / (N : ℝ) ^ (11 / 2 : ℝ) * (1 / M ^ (11 / 2 : ℝ)) * |Asum h N|
          ≤ 1 / (N : ℝ) ^ (11 / 2 : ℝ) * (1 / M ^ (11 / 2 : ℝ)) * (A * (N : ℝ) ^ 6 * M ^ 6) := by
            gcongr
        _ = A * (N : ℝ) ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by rw [e6, e6']; field_simp
        _ ≤ A * ((h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 / 2 - ηt)) * M ^ (1 / 2 : ℝ) := by gcongr
        _ = A * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) := by rw [← hMs]; ring
        _ ≤ (2 ^ 6 * C + A) * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) := by
            have : 0 ≤ 2 ^ 6 * C * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) := by positivity
            nlinarith
  -- integral term
  have hB : ∀ t ∈ Set.Ioc (1 : ℝ) N, ‖deriv (wf h) t * Asum h ⌊t⌋₊‖ ≤
      K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-ηt) + M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ))) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : 1 ≤ t := ht.1.le
    rw [deriv_wf h ht0, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
    have hfl2 : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
    have hth0 : 0 < t + h := by linarith
    have hw := abs_wf'_le h ht0
    have hp1 : 0 ≤ t ^ (-ηt) := Real.rpow_nonneg ht0.le _
    have hp2 : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht0.le _
    rcases le_or_gt h ⌊t⌋₊ with hhm | hmh
    · have hhm' : (h : ℝ) ≤ t := le_trans (by exact_mod_cast hhm) hfl
      have hAt : |Asum h ⌊t⌋₊| ≤ C * (h : ℝ) ^ (1 / 21 : ℝ) * (t + h) ^ (12 - ηt) := by
        refine (hL h hh _ hhm).trans ?_
        gcongr
        linarith
      have hth : t + h ≤ 2 * t := by linarith
      have hpow : (t + h) ^ (13 / 2 - ηt) ≤ 2 ^ 7 * t ^ (13 / 2 - ηt) := by
        calc (t + h) ^ (13 / 2 - ηt) ≤ (2 * t) ^ (13 / 2 - ηt) :=
              Real.rpow_le_rpow hth0.le hth (by linarith)
          _ = 2 ^ (13 / 2 - ηt) * t ^ (13 / 2 - ηt) := Real.mul_rpow (by norm_num) ht0.le
          _ ≤ 2 ^ 7 * t ^ (13 / 2 - ηt) := by
              gcongr
              calc (2 : ℝ) ^ (13 / 2 - ηt) ≤ 2 ^ (7 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                _ = 2 ^ 7 := by norm_num
      have e1 : (t + h) ^ (-(11 / 2 : ℝ)) * (t + h) ^ (12 - ηt) = (t + h) ^ (13 / 2 - ηt) := by
        rw [← Real.rpow_add hth0]; ring_nf
      have e2 : t ^ (-(13 / 2 : ℝ)) * t ^ (13 / 2 - ηt) = t ^ (-ηt) := by
        rw [← Real.rpow_add ht0]; ring_nf
      calc |wf' h t| * |Asum h ⌊t⌋₊|
          ≤ (11 * t ^ (-(13 / 2 : ℝ)) * (t + h) ^ (-(11 / 2 : ℝ))) *
              (C * (h : ℝ) ^ (1 / 21 : ℝ) * (t + h) ^ (12 - ηt)) := by gcongr
        _ = 11 * C * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-(13 / 2 : ℝ)) *
              ((t + h) ^ (-(11 / 2 : ℝ)) * (t + h) ^ (12 - ηt))) := by ring
        _ = 11 * C * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-(13 / 2 : ℝ)) * (t + h) ^ (13 / 2 - ηt)) := by rw [e1]
        _ ≤ 11 * C * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-(13 / 2 : ℝ)) * (2 ^ 7 * t ^ (13 / 2 - ηt))) := by
            gcongr
        _ = 11 * 2 ^ 7 * C * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-(13 / 2 : ℝ)) * t ^ (13 / 2 - ηt)) := by ring
        _ = 11 * 2 ^ 7 * C * (h : ℝ) ^ (1 / 21 : ℝ) * t ^ (-ηt) := by rw [e2]
        _ ≤ K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-ηt) + M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ))) := by
            have h0 : 0 ≤ (h : ℝ) ^ (1 / 21 : ℝ) := by positivity
            have : 11 * 2 ^ 7 * C ≤ K2 := by simp only [K2]; linarith
            calc 11 * 2 ^ 7 * C * (h : ℝ) ^ (1 / 21 : ℝ) * t ^ (-ηt)
                ≤ K2 * (h : ℝ) ^ (1 / 21 : ℝ) * t ^ (-ηt) := by gcongr
              _ ≤ _ := by
                  have : 0 ≤ K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ))) := by
                    positivity
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
      have hs2 : Real.sqrt (t + h) ≤ 2 * ((h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 / 2 - ηt)) := by
        have htN : t ≤ N := ht.2
        rw [Real.sqrt_eq_rpow]
        have h1 : (t + h) ^ (1 / 2 : ℝ) = (t + h) ^ (1 / 21 : ℝ) * (t + h) ^ (1 / 2 - ηt) := by
          rw [← Real.rpow_add hth0]; unfold ηt; norm_num
        have h2 : (t + h) ^ (1 / 21 : ℝ) ≤ 2 * (h : ℝ) ^ (1 / 21 : ℝ) := by
          calc (t + h) ^ (1 / 21 : ℝ) ≤ (2 * h) ^ (1 / 21 : ℝ) :=
                Real.rpow_le_rpow hth0.le (by linarith) (by norm_num)
            _ = 2 ^ (1 / 21 : ℝ) * (h : ℝ) ^ (1 / 21 : ℝ) := Real.mul_rpow (by norm_num) (by linarith)
            _ ≤ 2 * (h : ℝ) ^ (1 / 21 : ℝ) := by
                gcongr
                calc (2 : ℝ) ^ (1 / 21 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                  _ = 2 := by norm_num
        have h3 : (t + h) ^ (1 / 2 - ηt) ≤ M ^ (1 / 2 - ηt) :=
          Real.rpow_le_rpow hth0.le (by show t + h ≤ N + h; linarith) (by linarith)
        rw [h1]
        calc (t + h) ^ (1 / 21 : ℝ) * (t + h) ^ (1 / 2 - ηt)
            ≤ (2 * (h : ℝ) ^ (1 / 21 : ℝ)) * M ^ (1 / 2 - ηt) := by gcongr
          _ = _ := by ring
      calc |wf' h t| * |Asum h ⌊t⌋₊|
          ≤ (11 * t ^ (-(13 / 2 : ℝ)) * (t + h) ^ (-(11 / 2 : ℝ))) * (A * t ^ 6 * (t + h) ^ 6) := by
            gcongr
        _ = 11 * A * (t ^ (-(13 / 2 : ℝ)) * t ^ 6) * ((t + h) ^ (-(11 / 2 : ℝ)) * (t + h) ^ 6) := by
            ring
        _ = 11 * A * t ^ (-(1 / 2 : ℝ)) * Real.sqrt (t + h) := by rw [e1, e2]
        _ ≤ 11 * A * t ^ (-(1 / 2 : ℝ)) * (2 * ((h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 / 2 - ηt))) := by
            gcongr
        _ = 22 * A * (h : ℝ) ^ (1 / 21 : ℝ) * (M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-ηt) + M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ))) := by
            have h0 : 0 ≤ (h : ℝ) ^ (1 / 21 : ℝ) := by positivity
            have hC' : 0 ≤ 11 * 2 ^ 7 * C := by positivity
            have : 22 * A ≤ K2 := by simp only [K2]; linarith
            calc 22 * A * (h : ℝ) ^ (1 / 21 : ℝ) * (M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ)))
                ≤ K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ))) := by
                  gcongr
              _ ≤ _ := by
                  have : 0 ≤ K2 * (h : ℝ) ^ (1 / 21 : ℝ) * t ^ (-ηt) := by positivity
                  nlinarith
  have hint1 : IntegrableOn (fun t : ℝ => t ^ (-ηt)) (Set.Ioc (1 : ℝ) N) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (by
      have := ht.1; show (t : ℝ) ≠ 0; linarith)
  have hint2 : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Set.Ioc (1 : ℝ) N) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (by
      have := ht.1; show (t : ℝ) ≠ 0; linarith)
  have hint2' : IntegrableOn (fun t : ℝ => M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ)))
      (Set.Ioc (1 : ℝ) N) := hint2.const_mul _
  have hBint : IntegrableOn (fun t : ℝ => K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-ηt) + M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ))))
      (Set.Ioc (1 : ℝ) N) := (hint1.add hint2').const_mul _
  have hI : ‖∫ t in Set.Ioc (1 : ℝ) N, deriv (wf h) t * Asum h ⌊t⌋₊‖ ≤
      K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (2 * (N : ℝ) ^ (1 - ηt) +
        M ^ (1 / 2 - ηt) * (2 * (N : ℝ) ^ (1 - 1 / 2 : ℝ))) := by
    refine (norm_integral_le_of_norm_le hBint ((ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall hB))).trans ?_
    rw [integral_const_mul, integral_add hint1 hint2', integral_const_mul]
    gcongr
    · exact integral_rpow_neg_le ηt hη.le hηh N hN
    · exact integral_rpow_neg_le (1 / 2) (by norm_num) le_rfl N hN
  -- combine
  have hNM : (N : ℝ) ^ (1 - ηt) ≤ M ^ (1 - ηt) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  have hMhalf : M ^ (1 / 2 - ηt) * M ^ (1 / 2 : ℝ) = M ^ (1 - ηt) := by
    rw [← Real.rpow_add hM0]; ring_nf
  calc |wf h N * Asum h N - ∫ t in Set.Ioc (1 : ℝ) N, deriv (wf h) t * Asum h ⌊t⌋₊|
      ≤ |wf h N * Asum h N| + ‖∫ t in Set.Ioc (1 : ℝ) N, deriv (wf h) t * Asum h ⌊t⌋₊‖ := by
        rw [Real.norm_eq_abs]; exact abs_sub _ _
    _ ≤ (2 ^ 6 * C + A) * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) +
          K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (2 * (N : ℝ) ^ (1 - ηt) +
            M ^ (1 / 2 - ηt) * (2 * (N : ℝ) ^ (1 - 1 / 2 : ℝ))) :=
        add_le_add hb hI
    _ ≤ (2 ^ 6 * C + A) * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) +
          K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (2 * M ^ (1 - ηt) + 2 * M ^ (1 - ηt)) := by
        have hNh : (N : ℝ) ^ (1 - 1 / 2 : ℝ) ≤ M ^ (1 / 2 : ℝ) := by
          rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
          exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        have hk : 2 * (N : ℝ) ^ (1 - ηt) + M ^ (1 / 2 - ηt) * (2 * (N : ℝ) ^ (1 - 1 / 2 : ℝ)) ≤
            2 * M ^ (1 - ηt) + 2 * M ^ (1 - ηt) := by
          have hp : 0 ≤ M ^ (1 / 2 - ηt) := by positivity
          have := mul_le_mul_of_nonneg_left hNh hp
          rw [hMhalf] at this
          nlinarith
        have hc : 0 ≤ K2 * (h : ℝ) ^ (1 / 21 : ℝ) := by positivity
        have := mul_le_mul_of_nonneg_left hk hc
        linarith
    _ = (2 ^ 6 * C + A + 4 * K2) * M ^ (1 - ηt) * (h : ℝ) ^ (1 / 21 : ℝ) := by ring

end RamanujanTau.SCSSharp2
