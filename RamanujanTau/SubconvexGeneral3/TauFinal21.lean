/-
# Abel summation with `B = η` (weight-`k` copy of `SCSSharp2.Final21`)

`scsf_of_pointwise21`: the weight-`k` pointwise bound with `h^{1/21}` and saving `99/1000`
implies `SCS_f(1/21, 1/21)`.  For `t < h` the Cauchy–Schwarz range uses
`(t+h)^{1/2} ≤ (2h)^{η}(N+h)^{1/2−η}` instead of `≤ √(2h)`, which turns `B = 1/2` into `B = η`.
-/
import RamanujanTau.SubconvexGeneral2.TauFinal
import RamanujanTau.SubconvexGeneral3.TauAsum21

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral3

open MeasureTheory Set Complex
open RamanujanTau.HeckeConvexGeneral RamanujanTau.SubconvexGeneral RamanujanTau.SubconvexGeneral2
open RamanujanTau.EigenformEdge
open RamanujanTau.RankinError RamanujanTau.SCSProof RamanujanTau.SCSSharp RamanujanTau.SCSSharp2
open scoped MatrixGroups Real

variable {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ))

set_option maxHeartbeats 4000000 in
/-- **The sharp shifted-convolution bound, weight `k`**, from the pointwise bound for `G^f_h`. -/
theorem shS_bound21 (hk : 1 ≤ k) (hreal : ∀ n, (coef f n).im = 0)
    (hpw : ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 → (h : ℝ) * σ ≤ 1 →
      ‖GhF f h ((σ : ℂ) + v * I)‖ ≤
        K * (h : ℝ) ^ (1 / 21 : ℝ) * (|2 * v / σ| + 3) * σ ^ (-(k : ℝ) + 99 / 1000)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h N : ℕ, 1 ≤ h →
      |shS (nlam f) h N| ≤ C * ((N : ℝ) + h) ^ (1 - ηt) * (h : ℝ) ^ (1 / 21 : ℝ) := by
  obtain ⟨C, hC0, hL⟩ := AsumT_bound_large21 f hk hreal hpw
  obtain ⟨A, hA0, hcs⟩ := AsumT_cs f hk
  have ha0 := aw_nonneg hk
  have hka := k_eq_aw k
  set a := aw k with hadef
  set K2 : ℝ := 2 * a * 2 ^ (a + 1) * C + 4 * a * A
  have hK2 : 0 ≤ K2 := by positivity
  refine ⟨2 ^ a * C + A + 4 * K2, by positivity, fun h N hh => ?_⟩
  have hη := ηt_pos; have hη2 := ηt_le
  have hηh : ηt ≤ 1 / 2 := by unfold ηt; norm_num
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hsh : (1 : ℝ) ≤ (h : ℝ) ^ (1 / 21 : ℝ) := Real.one_le_rpow hhR (by norm_num)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [shS]; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set M := (N : ℝ) + h
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  -- Abel summation
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) N, DifferentiableAt ℝ (wT k h) t := fun t ht =>
    (hasDerivAt_wT k h (by linarith [ht.1])).differentiableAt
  have hint : IntegrableOn (deriv (wT k h)) (Set.Icc (1 : ℝ) N) := by
    refine ((continuousOn_wT' k h).mono fun t ht =>
      (show (0 : ℝ) < t by linarith [ht.1])).integrableOn_Icc
      |>.congr_fun (fun t ht => (deriv_wT k h (by linarith [ht.1])).symm) measurableSet_Icc
  have hAbel := sum_mul_eq_sub_integral_mul₀' (aT f h) (aT_zero f h) N hdiff hint
  rw [← shS_eq_abelT f hk] at hAbel
  have hAs : ∀ m : ℕ, ∑ j ∈ Finset.Icc 0 m, aT f h j = AsumT f h m := fun m => by
    rw [Icc_zero_eq_range]; rfl
  simp_rw [hAs] at hAbel
  rw [hAbel]
  have hMη : 0 ≤ M ^ (1 - ηt) := Real.rpow_nonneg hM0.le _
  -- boundary term
  have hb : |wT k h N * AsumT f h N| ≤ (2 ^ a * C + A) * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) := by
    rw [abs_mul]
    have hw : |wT k h N| = (N : ℝ) ^ (-a) * M ^ (-a) := by
      unfold wT; rw [abs_of_pos (by positivity)]
    rw [hw]
    have hNp : 0 < (N : ℝ) ^ a := Real.rpow_pos_of_pos (by linarith) _
    have hMp : 0 < M ^ a := Real.rpow_pos_of_pos hM0 _
    have i1 : (N : ℝ) ^ (-a) = 1 / (N : ℝ) ^ a := by
      rw [Real.rpow_neg (by linarith), one_div]
    have i2 : M ^ (-a) = 1 / M ^ a := by
      rw [Real.rpow_neg hM0.le, one_div]
    rw [i1, i2]
    rcases le_or_gt h N with hhN | hNh
    · have hMN : M ≤ 2 * N := by
        have : (h : ℝ) ≤ N := by exact_mod_cast hhN
        show (N : ℝ) + h ≤ 2 * N; linarith
      have hpowM : M ^ a ≤ 2 ^ a * (N : ℝ) ^ a := by
        calc M ^ a ≤ (2 * N) ^ a := Real.rpow_le_rpow hM0.le hMN ha0
          _ = 2 ^ a * (N : ℝ) ^ a := Real.mul_rpow (by norm_num) (by linarith)
      have e : M ^ ((k : ℝ) - ηt) = M ^ (1 - ηt) * M ^ a * M ^ a := by
        rw [← Real.rpow_add hM0, ← Real.rpow_add hM0]; congr 1; rw [hka]; ring
      calc 1 / (N : ℝ) ^ a * (1 / M ^ a) * |AsumT f h N|
          ≤ 1 / (N : ℝ) ^ a * (1 / M ^ a) * (C * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ ((k : ℝ) - ηt)) := by
            gcongr; exact hL h hh N hhN
        _ = C * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) * (M ^ a / (N : ℝ) ^ a) := by
            rw [e]; field_simp
        _ ≤ C * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) * 2 ^ a := by
            gcongr
            rw [div_le_iff₀ hNp]; linarith
        _ ≤ (2 ^ a * C + A) * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) := by
            have : 0 ≤ A * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) := by positivity
            nlinarith
    · have hNh' : (N : ℝ) < h := by exact_mod_cast hNh
      have hc := hcs h N
      have e6 : (N : ℝ) ^ ((k : ℝ) / 2) = (N : ℝ) ^ a * (N : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add (by linarith)]; congr 1; rw [hka]; ring
      have e6' : M ^ ((k : ℝ) / 2) = M ^ a * M ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hM0]; congr 1; rw [hka]; ring
      have hNs : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 / 2 - ηt) := by
        have h1 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (h : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by linarith) hNh'.le (by norm_num)
        have h2 : (h : ℝ) ^ (1 / 2 : ℝ) = (h : ℝ) ^ (1 / 21 : ℝ) * (h : ℝ) ^ (1 / 2 - ηt) := by
          rw [← Real.rpow_add (by linarith)]; unfold ηt; norm_num
        have h3 : (h : ℝ) ^ (1 / 2 - ηt) ≤ M ^ (1 / 2 - ηt) :=
          Real.rpow_le_rpow (by linarith) (by show (h : ℝ) ≤ (N : ℝ) + h; linarith)
            (by unfold ηt; norm_num)
        rw [h2] at h1
        calc (N : ℝ) ^ (1 / 2 : ℝ) ≤ (h : ℝ) ^ (1 / 21 : ℝ) * (h : ℝ) ^ (1 / 2 - ηt) := h1
          _ ≤ (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 / 2 - ηt) := by gcongr
      have hMs : M ^ (1 / 2 - ηt) * M ^ (1 / 2 : ℝ) = M ^ (1 - ηt) := by
        rw [← Real.rpow_add hM0]; ring_nf
      calc 1 / (N : ℝ) ^ a * (1 / M ^ a) * |AsumT f h N|
          ≤ 1 / (N : ℝ) ^ a * (1 / M ^ a) *
              (A * (N : ℝ) ^ ((k : ℝ) / 2) * M ^ ((k : ℝ) / 2)) := by
            gcongr
        _ = A * (N : ℝ) ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by rw [e6, e6']; field_simp
        _ ≤ A * ((h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 / 2 - ηt)) * M ^ (1 / 2 : ℝ) := by gcongr
        _ = A * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) := by rw [← hMs]; ring
        _ ≤ (2 ^ a * C + A) * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) := by
            have : 0 ≤ 2 ^ a * C * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) := by positivity
            nlinarith
  -- integral term
  have hB : ∀ t ∈ Set.Ioc (1 : ℝ) N, ‖deriv (wT k h) t * AsumT f h ⌊t⌋₊‖ ≤
      K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-ηt) + M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ))) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : 1 ≤ t := ht.1.le
    rw [deriv_wT k h ht0, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
    have hfl2 : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
    have hth0 : 0 < t + h := by linarith
    have hw := abs_wT'_le hk h ht0
    have hp1 : 0 ≤ t ^ (-ηt) := Real.rpow_nonneg ht0.le _
    have hp2 : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht0.le _
    rcases le_or_gt h ⌊t⌋₊ with hhm | hmh
    · have hhm' : (h : ℝ) ≤ t := le_trans (by exact_mod_cast hhm) hfl
      have hAt : |AsumT f h ⌊t⌋₊| ≤ C * (h : ℝ) ^ (1 / 21 : ℝ) * (t + h) ^ ((k : ℝ) - ηt) := by
        refine (hL h hh _ hhm).trans ?_
        have : (0 : ℝ) ≤ (k : ℝ) - ηt := by rw [hka]; linarith
        gcongr
      have hth : t + h ≤ 2 * t := by linarith
      have hpow : (t + h) ^ (a + 1 - ηt) ≤ 2 ^ (a + 1) * t ^ (a + 1 - ηt) := by
        calc (t + h) ^ (a + 1 - ηt) ≤ (2 * t) ^ (a + 1 - ηt) :=
              Real.rpow_le_rpow hth0.le hth (by linarith)
          _ = 2 ^ (a + 1 - ηt) * t ^ (a + 1 - ηt) := Real.mul_rpow (by norm_num) ht0.le
          _ ≤ 2 ^ (a + 1) * t ^ (a + 1 - ηt) :=
              mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
                (Real.rpow_nonneg ht0.le _)
      have e1 : (t + h) ^ (-a) * (t + h) ^ ((k : ℝ) - ηt) = (t + h) ^ (a + 1 - ηt) := by
        rw [← Real.rpow_add hth0]; congr 1; rw [hka]; ring
      have e2 : t ^ (-a - 1) * t ^ (a + 1 - ηt) = t ^ (-ηt) := by
        rw [← Real.rpow_add ht0]; congr 1; ring
      calc |wT' k h t| * |AsumT f h ⌊t⌋₊|
          ≤ (2 * a * t ^ (-a - 1) * (t + h) ^ (-a)) *
              (C * (h : ℝ) ^ (1 / 21 : ℝ) * (t + h) ^ ((k : ℝ) - ηt)) := by gcongr
        _ = 2 * a * C * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-a - 1) *
              ((t + h) ^ (-a) * (t + h) ^ ((k : ℝ) - ηt))) := by ring
        _ = 2 * a * C * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-a - 1) * (t + h) ^ (a + 1 - ηt)) := by rw [e1]
        _ ≤ 2 * a * C * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-a - 1) * (2 ^ (a + 1) * t ^ (a + 1 - ηt))) := by
            gcongr
        _ = 2 * a * 2 ^ (a + 1) * C * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-a - 1) * t ^ (a + 1 - ηt)) := by ring
        _ = 2 * a * 2 ^ (a + 1) * C * (h : ℝ) ^ (1 / 21 : ℝ) * t ^ (-ηt) := by rw [e2]
        _ ≤ K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-ηt) + M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ))) := by
            have h0 : 0 ≤ (h : ℝ) ^ (1 / 21 : ℝ) := by positivity
            have : 2 * a * 2 ^ (a + 1) * C ≤ K2 := by
              simp only [K2]; have : 0 ≤ 4 * a * A := by positivity
              linarith
            calc 2 * a * 2 ^ (a + 1) * C * (h : ℝ) ^ (1 / 21 : ℝ) * t ^ (-ηt)
                ≤ K2 * (h : ℝ) ^ (1 / 21 : ℝ) * t ^ (-ηt) := by gcongr
              _ ≤ _ := by
                  have : 0 ≤ K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ))) := by positivity
                  nlinarith
    · have hmh' : t < h := by
        have : ((⌊t⌋₊ : ℕ) : ℝ) + 1 ≤ h := by exact_mod_cast hmh
        linarith
      have hAt : |AsumT f h ⌊t⌋₊| ≤ A * t ^ ((k : ℝ) / 2) * (t + h) ^ ((k : ℝ) / 2) := by
        refine (hcs h _).trans ?_
        have : (0 : ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
        have : (0 : ℝ) ≤ (k : ℝ) / 2 := by rw [hka]; linarith
        gcongr
      have e1 : t ^ (-a - 1) * t ^ ((k : ℝ) / 2) = t ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add ht0]; congr 1; rw [hka]; ring
      have e2 : (t + h) ^ (-a) * (t + h) ^ ((k : ℝ) / 2) = Real.sqrt (t + h) := by
        rw [← Real.rpow_add hth0, Real.sqrt_eq_rpow]; congr 1; rw [hka]; ring
      have hs2 : Real.sqrt (t + h) ≤ 2 * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 / 2 - ηt) := by
        have htM : t + h ≤ M := by show t + h ≤ (N : ℝ) + h; linarith [ht.2]
        have hsplit : Real.sqrt (t + h) = (t + h) ^ ηt * (t + h) ^ (1 / 2 - ηt) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hth0]; ring_nf
        have hq1 : (t + h) ^ ηt ≤ (2 * (h : ℝ)) ^ ηt :=
          Real.rpow_le_rpow hth0.le (by linarith) hη.le
        have hq2 : (2 * (h : ℝ)) ^ ηt ≤ 2 * (h : ℝ) ^ (1 / 21 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) (by linarith)]
          have h2 : (2 : ℝ) ^ ηt ≤ 2 := by
            calc (2 : ℝ) ^ ηt ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 2 := Real.rpow_one 2
          have e : (h : ℝ) ^ ηt = (h : ℝ) ^ (1 / 21 : ℝ) := by unfold ηt; norm_num
          rw [e]
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
        have hq3 : (t + h) ^ (1 / 2 - ηt) ≤ M ^ (1 / 2 - ηt) :=
          Real.rpow_le_rpow hth0.le htM (by unfold ηt; norm_num)
        rw [hsplit]
        calc (t + h) ^ ηt * (t + h) ^ (1 / 2 - ηt) ≤ (2 * (h : ℝ)) ^ ηt * M ^ (1 / 2 - ηt) := by
              gcongr
          _ ≤ 2 * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 / 2 - ηt) := by gcongr
      calc |wT' k h t| * |AsumT f h ⌊t⌋₊|
          ≤ (2 * a * t ^ (-a - 1) * (t + h) ^ (-a)) *
              (A * t ^ ((k : ℝ) / 2) * (t + h) ^ ((k : ℝ) / 2)) := by
            gcongr
        _ = 2 * a * A * (t ^ (-a - 1) * t ^ ((k : ℝ) / 2)) *
              ((t + h) ^ (-a) * (t + h) ^ ((k : ℝ) / 2)) := by ring
        _ = 2 * a * A * t ^ (-(1 / 2 : ℝ)) * Real.sqrt (t + h) := by rw [e1, e2]
        _ ≤ 2 * a * A * t ^ (-(1 / 2 : ℝ)) * (2 * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 / 2 - ηt)) := by gcongr
        _ = 4 * a * A * (h : ℝ) ^ (1 / 21 : ℝ) * (M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-ηt) + M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ))) := by
            have h0 : 0 ≤ (h : ℝ) ^ (1 / 21 : ℝ) := by positivity
            have hC' : 0 ≤ 2 * a * 2 ^ (a + 1) * C := by positivity
            have : 4 * a * A ≤ K2 := by simp only [K2]; linarith
            calc 4 * a * A * (h : ℝ) ^ (1 / 21 : ℝ) * (M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ)))
                ≤ K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ))) := by gcongr
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
  have hBint : IntegrableOn
      (fun t : ℝ => K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (t ^ (-ηt) + M ^ (1 / 2 - ηt) * t ^ (-(1 / 2 : ℝ))))
      (Set.Ioc (1 : ℝ) N) := (hint1.add hint2').const_mul _
  have hI : ‖∫ t in Set.Ioc (1 : ℝ) N, deriv (wT k h) t * AsumT f h ⌊t⌋₊‖ ≤
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
  have hNM2 : M ^ (1 / 2 - ηt) * (N : ℝ) ^ (1 - 1 / 2 : ℝ) ≤ M ^ (1 - ηt) := by
    have h1 : (N : ℝ) ^ (1 - 1 / 2 : ℝ) ≤ M ^ (1 - 1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    calc M ^ (1 / 2 - ηt) * (N : ℝ) ^ (1 - 1 / 2 : ℝ) ≤ M ^ (1 / 2 - ηt) * M ^ (1 - 1 / 2 : ℝ) := by
          gcongr
      _ = M ^ (1 - ηt) := by rw [← Real.rpow_add hM0]; ring_nf
  calc |wT k h N * AsumT f h N - ∫ t in Set.Ioc (1 : ℝ) N, deriv (wT k h) t * AsumT f h ⌊t⌋₊|
      ≤ |wT k h N * AsumT f h N| +
          ‖∫ t in Set.Ioc (1 : ℝ) N, deriv (wT k h) t * AsumT f h ⌊t⌋₊‖ := by
        rw [Real.norm_eq_abs]; exact abs_sub _ _
    _ ≤ (2 ^ a * C + A) * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) +
          K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (2 * (N : ℝ) ^ (1 - ηt) +
            M ^ (1 / 2 - ηt) * (2 * (N : ℝ) ^ (1 - 1 / 2 : ℝ))) :=
        add_le_add hb hI
    _ ≤ (2 ^ a * C + A) * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ (1 - ηt) +
          K2 * (h : ℝ) ^ (1 / 21 : ℝ) * (2 * M ^ (1 - ηt) + 2 * M ^ (1 - ηt)) := by
        have hp : 0 ≤ K2 * (h : ℝ) ^ (1 / 21 : ℝ) := by positivity
        have hsum : 2 * (N : ℝ) ^ (1 - ηt) + M ^ (1 / 2 - ηt) * (2 * (N : ℝ) ^ (1 - 1 / 2 : ℝ)) ≤
            2 * M ^ (1 - ηt) + 2 * M ^ (1 - ηt) := by nlinarith [hNM, hNM2]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hp)
    _ = (2 ^ a * C + A + 4 * K2) * M ^ (1 - ηt) * (h : ℝ) ^ (1 / 21 : ℝ) := by ring


/-- **`SCS_f(1/21, 1/21)` from the weight-`k` pointwise bound** (`k ≥ 12`, real coefficients). -/
theorem scsf_of_pointwise21 {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k)
    (hreal : ∀ n, (coef f n).im = 0)
    (hpw : ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 → (h : ℝ) * σ ≤ 1 →
      ‖GhF f h ((σ : ℂ) + v * I)‖ ≤
        K * (h : ℝ) ^ (1 / 21 : ℝ) * (|2 * v / σ| + 3) * σ ^ (-(k : ℝ) + 99 / 1000)) :
    SCSf f (1 / 21) (1 / 21) := by
  obtain ⟨C, hC0, hC⟩ := shS_bound21 f (by omega) hreal hpw
  refine ⟨⟨C, hC0, fun h N hh => ?_⟩⟩
  have := hC h N hh
  unfold ηt at this
  exact this

end RamanujanTau.SubconvexGeneral3
