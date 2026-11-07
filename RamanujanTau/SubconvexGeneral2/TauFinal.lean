/-
# Weight-`k` Tauberian chain, part 4: Abel summation and `SCS_f(1/22, 1/2)` from the pointwise bound

Weight-`k` copy of `SCSSharp.Asum_cs`, `SCSProof.wf`/`abs_wf'_le`/`shiftSum_eq_abel` and
`SCSSharp.shiftSum_bound'`.  Abel weight `w(t) = t^{−a}(t+h)^{−a}`, `a = (k−1)/2`,
`|w'(t)| ≤ 2a t^{−a−1}(t+h)^{−a}`.

* `scsf_of_pointwise`: for every level-one cusp form `f` of weight `k ≥ 12` with real coefficients,
  the weight-`k` pointwise bound for `G^f_h` (the analogue of `SCSSharp.pointwise_G'`, an explicit
  hypothesis here) implies `SCS_f(1/22, 1/2)`.
-/
import RamanujanTau.SubconvexGeneral2.TauAsum

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral2

open Finset MeasureTheory Set Complex
open RamanujanTau.HeckeConvexGeneral RamanujanTau.SubconvexGeneral RamanujanTau.EigenformEdge
open RamanujanTau.RankinError RamanujanTau.SCSProof RamanujanTau.SCSSharp
open scoped MatrixGroups Real

/-- The Abel exponent `a = (k−1)/2`. -/
noncomputable def aw (k : ℕ) : ℝ := ((k : ℝ) - 1) / 2

lemma aw_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ aw k := by
  unfold aw; have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

lemma k_eq_aw (k : ℕ) : (k : ℝ) = 2 * aw k + 1 := by unfold aw; ring

/-- The weight `w(t) = t^{−a}(t+h)^{−a}`. -/
noncomputable def wT (k h : ℕ) (t : ℝ) : ℝ := t ^ (-aw k) * (t + h) ^ (-aw k)

/-- Its derivative for `t > 0`. -/
noncomputable def wT' (k h : ℕ) (t : ℝ) : ℝ :=
  (-aw k) * t ^ (-aw k - 1) * (t + h) ^ (-aw k) +
    t ^ (-aw k) * ((-aw k) * (t + h) ^ (-aw k - 1))

lemma hasDerivAt_wT (k h : ℕ) {t : ℝ} (ht : 0 < t) : HasDerivAt (wT k h) (wT' k h t) t := by
  have h1 := Real.hasDerivAt_rpow_const (x := t) (p := -aw k) (Or.inl ht.ne')
  have h2 : HasDerivAt (fun t : ℝ => (t + h) ^ (-aw k))
      ((-aw k) * (t + h) ^ (-aw k - 1)) t := by
    have := (Real.hasDerivAt_rpow_const (x := t + h) (p := -aw k)
      (Or.inl (by have := Nat.cast_nonneg (α := ℝ) h; linarith))).comp t
      ((hasDerivAt_id t).add_const (h : ℝ))
    simpa using this
  exact h1.mul h2

lemma deriv_wT (k h : ℕ) {t : ℝ} (ht : 0 < t) : deriv (wT k h) t = wT' k h t :=
  (hasDerivAt_wT k h ht).deriv

lemma continuousOn_wT' (k h : ℕ) : ContinuousOn (wT' k h) (Ioi 0) := by
  intro t ht
  have ht0 : 0 < t := ht
  have hth : 0 < t + h := by have := Nat.cast_nonneg (α := ℝ) h; linarith
  unfold wT'
  refine ContinuousAt.continuousWithinAt ?_
  have c1 : ContinuousAt (fun t : ℝ => t ^ (-aw k - 1)) t :=
    Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')
  have c2 : ContinuousAt (fun t : ℝ => t ^ (-aw k)) t :=
    Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')
  have c3 : ContinuousAt (fun t : ℝ => (t + h) ^ (-aw k)) t :=
    (Real.continuousAt_rpow_const (t + h) _ (Or.inl hth.ne')).comp
      (f := fun t : ℝ => t + (h : ℝ)) (continuous_add_const _).continuousAt
  have c4 : ContinuousAt (fun t : ℝ => (t + h) ^ (-aw k - 1)) t :=
    (Real.continuousAt_rpow_const (t + h) _ (Or.inl hth.ne')).comp
      (f := fun t : ℝ => t + (h : ℝ)) (continuous_add_const _).continuousAt
  exact ((continuousAt_const.mul c1).mul c3).add (c2.mul (continuousAt_const.mul c4))

/-- `|w'(t)| ≤ 2a t^{−a−1}(t+h)^{−a}`. -/
lemma abs_wT'_le {k : ℕ} (hk : 1 ≤ k) (h : ℕ) {t : ℝ} (ht : 0 < t) :
    |wT' k h t| ≤ 2 * aw k * t ^ (-aw k - 1) * (t + h) ^ (-aw k) := by
  have hth : t ≤ t + h := by have := Nat.cast_nonneg (α := ℝ) h; linarith
  have hth0 : 0 < t + h := by linarith
  have ha0 := aw_nonneg hk
  set a := aw k
  have p1 : 0 < t ^ (-a - 1) := Real.rpow_pos_of_pos ht _
  have p2 : 0 < (t + h) ^ (-a) := Real.rpow_pos_of_pos hth0 _
  have p3 : 0 < t ^ (-a) := Real.rpow_pos_of_pos ht _
  have p4 : 0 < (t + h) ^ (-a - 1) := Real.rpow_pos_of_pos hth0 _
  have key : t ^ (-a) * (t + h) ^ (-a - 1) ≤ t ^ (-a - 1) * (t + h) ^ (-a) := by
    have a1 : t ^ (-a) = t ^ (-a - 1) * t := by
      rw [← Real.rpow_add_one ht.ne']; congr 1; ring
    have a2 : (t + h) ^ (-a) = (t + h) ^ (-a - 1) * (t + h) := by
      rw [← Real.rpow_add_one hth0.ne']; congr 1; ring
    rw [a1, a2]
    have : t ^ (-a - 1) * (t + h) ^ (-a - 1) * t ≤
        t ^ (-a - 1) * (t + h) ^ (-a - 1) * (t + h) := by gcongr
    nlinarith
  have e : wT' k h t = -(a * (t ^ (-a - 1) * (t + h) ^ (-a)) +
      a * (t ^ (-a) * (t + h) ^ (-a - 1))) := by unfold wT'; ring
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key ha0]

variable {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ))

lemma nrm_eq_rpow (hk : 1 ≤ k) (n : ℕ) : nrm k n = (n : ℝ) ^ aw k := by
  unfold nrm aw
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1; push_cast [Nat.cast_sub hk]; ring

lemma nlam_eq_rpow (hk : 1 ≤ k) (n : ℕ) : nlam f n = (coef f n).re * (n : ℝ) ^ (-aw k) := by
  rw [nlam, nrm_eq_rpow hk, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

lemma shS_eq_abelT (hk : 1 ≤ k) (h N : ℕ) :
    shS (nlam f) h N = ∑ n ∈ Finset.Icc 0 N, wT k h n * aT f h n := by
  unfold shS
  rw [show Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
    Finset.sum_insert (by simp), aT_zero, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [nlam_eq_rpow f hk, nlam_eq_rpow f hk]
  unfold wT aT
  push_cast
  ring

lemma sq_rpow_half {x : ℝ} (hx : 0 ≤ x) : (x ^ ((k : ℝ) / 2)) ^ 2 = x ^ k := by
  rw [← Real.rpow_natCast (x ^ _) 2, ← Real.rpow_mul hx, ← Real.rpow_natCast]
  congr 1; push_cast; ring

/-- **Cauchy–Schwarz bound** `|Σ_{n≤m} a_n| ≤ A m^{k/2} (m+h)^{k/2}`. -/
theorem AsumT_cs (hk : 1 ≤ k) : ∃ A : ℝ, 0 ≤ A ∧ ∀ h m : ℕ,
    |AsumT f h m| ≤ A * (m : ℝ) ^ ((k : ℝ) / 2) * ((m : ℝ) + h) ^ ((k : ℝ) / 2) := by
  obtain ⟨A, hA0, hA⟩ := exists_SlamT_le f hk
  refine ⟨A, hA0, fun h m => ?_⟩
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmh0 : (0 : ℝ) ≤ m + h := by positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (range (m + 1)) (fun n => (coef f n).re)
    (fun n => (coef f (n + h)).re)
  have hpk : ∀ y : ℝ, 0 ≤ y → y * y ^ (k - 1) = y ^ k := fun y _ => by
    rw [← pow_succ']; congr 1; omega
  have h1 : ∑ n ∈ range (m + 1), (coef f n).re ^ 2 ≤ A * (m : ℝ) ^ k := by
    calc ∑ n ∈ range (m + 1), (coef f n).re ^ 2
        ≤ ∑ n ∈ range (m + 1), ‖coef f n‖ ^ 2 := sum_le_sum fun n _ => re_sq_le f n
      _ = ∑ n ∈ range (m + 1), lsqT f n * (n : ℝ) ^ (k - 1) := by simp_rw [coef_sq_eq]
      _ ≤ ∑ n ∈ range (m + 1), lsqT f n * (m : ℝ) ^ (k - 1) := by
          refine sum_le_sum fun n hn => ?_
          have : (n : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hn)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) this _)
            (lsqT_nonneg f n)
      _ = SlamT f m * (m : ℝ) ^ (k - 1) := by rw [← sum_mul, sum_range_eq_SlamT]
      _ ≤ (A * m) * (m : ℝ) ^ (k - 1) := by gcongr; exact hA m
      _ = A * (m : ℝ) ^ k := by rw [mul_assoc, hpk _ hm0]
  have h2 : ∑ n ∈ range (m + 1), (coef f (n + h)).re ^ 2 ≤ A * ((m : ℝ) + h) ^ k := by
    calc ∑ n ∈ range (m + 1), (coef f (n + h)).re ^ 2
        ≤ ∑ n ∈ range (m + 1), ‖coef f (n + h)‖ ^ 2 := sum_le_sum fun n _ => re_sq_le f _
      _ = ∑ n ∈ range (m + 1), lsqT f (n + h) * ((n + h : ℕ) : ℝ) ^ (k - 1) := by
          simp_rw [coef_sq_eq]
      _ ≤ ∑ n ∈ range (m + 1), lsqT f (n + h) * ((m : ℝ) + h) ^ (k - 1) := by
          refine sum_le_sum fun n hn => ?_
          have : (n : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hn)
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _)
            (lsqT_nonneg f _)
          push_cast; linarith
      _ = (∑ n ∈ range (m + 1), lsqT f (n + h)) * ((m : ℝ) + h) ^ (k - 1) := by rw [← sum_mul]
      _ ≤ SlamT f (m + h) * ((m : ℝ) + h) ^ (k - 1) := by
          gcongr; exact sum_lsqT_shift f h m
      _ ≤ (A * ((m : ℝ) + h)) * ((m : ℝ) + h) ^ (k - 1) := by
          gcongr; have := hA (m + h); push_cast at this; exact this
      _ = A * ((m : ℝ) + h) ^ k := by rw [mul_assoc, hpk _ hmh0]
  have hsq : (AsumT f h m) ^ 2 ≤
      (A * (m : ℝ) ^ ((k : ℝ) / 2) * ((m : ℝ) + h) ^ ((k : ℝ) / 2)) ^ 2 := by
    have e : AsumT f h m = ∑ n ∈ range (m + 1), (coef f n).re * (coef f (n + h)).re := rfl
    rw [e]
    refine hcs.trans ?_
    calc (∑ n ∈ range (m + 1), (coef f n).re ^ 2) * ∑ n ∈ range (m + 1), (coef f (n + h)).re ^ 2
        ≤ (A * (m : ℝ) ^ k) * (A * ((m : ℝ) + h) ^ k) :=
          mul_le_mul h1 h2 (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = _ := by rw [mul_pow, mul_pow, sq_rpow_half hm0, sq_rpow_half hmh0]; ring
  have := sq_le_sq.1 hsq
  rwa [abs_of_nonneg (by positivity :
    (0:ℝ) ≤ A * (m : ℝ) ^ ((k : ℝ) / 2) * ((m : ℝ) + h) ^ ((k : ℝ) / 2))] at this

set_option maxHeartbeats 4000000 in
/-- **The sharp shifted-convolution bound, weight `k`**, from the pointwise bound for `G^f_h`. -/
theorem shS_bound_of_pointwise (hk : 1 ≤ k) (hreal : ∀ n, (coef f n).im = 0)
    (hpw : ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 → (h : ℝ) * σ ≤ 1 →
      ‖GhF f h ((σ : ℂ) + v * I)‖ ≤
        K * Real.sqrt h * (|2 * v / σ| + 3) * σ ^ (-(k : ℝ) + 12 / 125)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h N : ℕ, 1 ≤ h →
      |shS (nlam f) h N| ≤ C * ((N : ℝ) + h) ^ (1 - ηs) * Real.sqrt h := by
  obtain ⟨C, hC0, hL⟩ := AsumT_bound_large f hk hreal hpw
  obtain ⟨A, hA0, hcs⟩ := AsumT_cs f hk
  have ha0 := aw_nonneg hk
  have hka := k_eq_aw k
  set a := aw k with hadef
  set K2 : ℝ := 2 * a * 2 ^ (a + 1) * C + 4 * a * A
  have hK2 : 0 ≤ K2 := by positivity
  refine ⟨2 ^ a * C + A + 4 * K2, by positivity, fun h N hh => ?_⟩
  have hη := ηs_pos; have hη2 := ηs_le
  have hηh : ηs ≤ 1 / 2 := by unfold ηs; norm_num
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hsh : (1 : ℝ) ≤ Real.sqrt h := by rw [Real.one_le_sqrt]; exact hhR
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
  have hMη : 0 ≤ M ^ (1 - ηs) := Real.rpow_nonneg hM0.le _
  -- boundary term
  have hb : |wT k h N * AsumT f h N| ≤ (2 ^ a * C + A) * Real.sqrt h * M ^ (1 - ηs) := by
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
      have e : M ^ ((k : ℝ) - ηs) = M ^ (1 - ηs) * M ^ a * M ^ a := by
        rw [← Real.rpow_add hM0, ← Real.rpow_add hM0]; congr 1; rw [hka]; ring
      calc 1 / (N : ℝ) ^ a * (1 / M ^ a) * |AsumT f h N|
          ≤ 1 / (N : ℝ) ^ a * (1 / M ^ a) * (C * Real.sqrt h * M ^ ((k : ℝ) - ηs)) := by
            gcongr; exact hL h hh N hhN
        _ = C * Real.sqrt h * M ^ (1 - ηs) * (M ^ a / (N : ℝ) ^ a) := by
            rw [e]; field_simp
        _ ≤ C * Real.sqrt h * M ^ (1 - ηs) * 2 ^ a := by
            gcongr
            rw [div_le_iff₀ hNp]; linarith
        _ ≤ (2 ^ a * C + A) * Real.sqrt h * M ^ (1 - ηs) := by
            have : 0 ≤ A * Real.sqrt h * M ^ (1 - ηs) := by positivity
            nlinarith
    · have hNh' : (N : ℝ) < h := by exact_mod_cast hNh
      have hc := hcs h N
      have e6 : (N : ℝ) ^ ((k : ℝ) / 2) = (N : ℝ) ^ a * (N : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add (by linarith)]; congr 1; rw [hka]; ring
      have e6' : M ^ ((k : ℝ) / 2) = M ^ a * M ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hM0]; congr 1; rw [hka]; ring
      have hNs : (N : ℝ) ^ (1 / 2 : ℝ) ≤ Real.sqrt h := by
        rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt hNh'.le
      have hMs : M ^ (1 / 2 : ℝ) ≤ M ^ (1 - ηs) :=
        Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
      calc 1 / (N : ℝ) ^ a * (1 / M ^ a) * |AsumT f h N|
          ≤ 1 / (N : ℝ) ^ a * (1 / M ^ a) *
              (A * (N : ℝ) ^ ((k : ℝ) / 2) * M ^ ((k : ℝ) / 2)) := by
            gcongr
        _ = A * (N : ℝ) ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by rw [e6, e6']; field_simp
        _ ≤ A * Real.sqrt h * M ^ (1 - ηs) := by gcongr
        _ ≤ (2 ^ a * C + A) * Real.sqrt h * M ^ (1 - ηs) := by
            have : 0 ≤ 2 ^ a * C * Real.sqrt h * M ^ (1 - ηs) := by positivity
            nlinarith
  -- integral term
  have hB : ∀ t ∈ Set.Ioc (1 : ℝ) N, ‖deriv (wT k h) t * AsumT f h ⌊t⌋₊‖ ≤
      K2 * Real.sqrt h * (t ^ (-ηs) + t ^ (-(1 / 2 : ℝ))) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : 1 ≤ t := ht.1.le
    rw [deriv_wT k h ht0, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
    have hfl2 : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
    have hth0 : 0 < t + h := by linarith
    have hw := abs_wT'_le hk h ht0
    have hp1 : 0 ≤ t ^ (-ηs) := Real.rpow_nonneg ht0.le _
    have hp2 : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht0.le _
    rcases le_or_gt h ⌊t⌋₊ with hhm | hmh
    · have hhm' : (h : ℝ) ≤ t := le_trans (by exact_mod_cast hhm) hfl
      have hAt : |AsumT f h ⌊t⌋₊| ≤ C * Real.sqrt h * (t + h) ^ ((k : ℝ) - ηs) := by
        refine (hL h hh _ hhm).trans ?_
        have : (0 : ℝ) ≤ (k : ℝ) - ηs := by rw [hka]; linarith
        gcongr
      have hth : t + h ≤ 2 * t := by linarith
      have hpow : (t + h) ^ (a + 1 - ηs) ≤ 2 ^ (a + 1) * t ^ (a + 1 - ηs) := by
        calc (t + h) ^ (a + 1 - ηs) ≤ (2 * t) ^ (a + 1 - ηs) :=
              Real.rpow_le_rpow hth0.le hth (by linarith)
          _ = 2 ^ (a + 1 - ηs) * t ^ (a + 1 - ηs) := Real.mul_rpow (by norm_num) ht0.le
          _ ≤ 2 ^ (a + 1) * t ^ (a + 1 - ηs) :=
              mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
                (Real.rpow_nonneg ht0.le _)
      have e1 : (t + h) ^ (-a) * (t + h) ^ ((k : ℝ) - ηs) = (t + h) ^ (a + 1 - ηs) := by
        rw [← Real.rpow_add hth0]; congr 1; rw [hka]; ring
      have e2 : t ^ (-a - 1) * t ^ (a + 1 - ηs) = t ^ (-ηs) := by
        rw [← Real.rpow_add ht0]; congr 1; ring
      calc |wT' k h t| * |AsumT f h ⌊t⌋₊|
          ≤ (2 * a * t ^ (-a - 1) * (t + h) ^ (-a)) *
              (C * Real.sqrt h * (t + h) ^ ((k : ℝ) - ηs)) := by gcongr
        _ = 2 * a * C * Real.sqrt h * (t ^ (-a - 1) *
              ((t + h) ^ (-a) * (t + h) ^ ((k : ℝ) - ηs))) := by ring
        _ = 2 * a * C * Real.sqrt h * (t ^ (-a - 1) * (t + h) ^ (a + 1 - ηs)) := by rw [e1]
        _ ≤ 2 * a * C * Real.sqrt h * (t ^ (-a - 1) * (2 ^ (a + 1) * t ^ (a + 1 - ηs))) := by
            gcongr
        _ = 2 * a * 2 ^ (a + 1) * C * Real.sqrt h * (t ^ (-a - 1) * t ^ (a + 1 - ηs)) := by ring
        _ = 2 * a * 2 ^ (a + 1) * C * Real.sqrt h * t ^ (-ηs) := by rw [e2]
        _ ≤ K2 * Real.sqrt h * (t ^ (-ηs) + t ^ (-(1 / 2 : ℝ))) := by
            have h0 : 0 ≤ Real.sqrt h := Real.sqrt_nonneg _
            have : 2 * a * 2 ^ (a + 1) * C ≤ K2 := by
              simp only [K2]; have : 0 ≤ 4 * a * A := by positivity
              linarith
            calc 2 * a * 2 ^ (a + 1) * C * Real.sqrt h * t ^ (-ηs)
                ≤ K2 * Real.sqrt h * t ^ (-ηs) := by gcongr
              _ ≤ _ := by
                  have : 0 ≤ K2 * Real.sqrt h * t ^ (-(1 / 2 : ℝ)) := by positivity
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
      have hs2 : Real.sqrt (t + h) ≤ 2 * Real.sqrt h :=
        (Real.sqrt_le_sqrt (by linarith : t + h ≤ 2 * h)).trans
          (sqrt_two_mul_le h (Nat.cast_nonneg _))
      calc |wT' k h t| * |AsumT f h ⌊t⌋₊|
          ≤ (2 * a * t ^ (-a - 1) * (t + h) ^ (-a)) *
              (A * t ^ ((k : ℝ) / 2) * (t + h) ^ ((k : ℝ) / 2)) := by
            gcongr
        _ = 2 * a * A * (t ^ (-a - 1) * t ^ ((k : ℝ) / 2)) *
              ((t + h) ^ (-a) * (t + h) ^ ((k : ℝ) / 2)) := by ring
        _ = 2 * a * A * t ^ (-(1 / 2 : ℝ)) * Real.sqrt (t + h) := by rw [e1, e2]
        _ ≤ 2 * a * A * t ^ (-(1 / 2 : ℝ)) * (2 * Real.sqrt h) := by gcongr
        _ = 4 * a * A * Real.sqrt h * t ^ (-(1 / 2 : ℝ)) := by ring
        _ ≤ K2 * Real.sqrt h * (t ^ (-ηs) + t ^ (-(1 / 2 : ℝ))) := by
            have h0 : 0 ≤ Real.sqrt h := Real.sqrt_nonneg _
            have hC' : 0 ≤ 2 * a * 2 ^ (a + 1) * C := by positivity
            have : 4 * a * A ≤ K2 := by simp only [K2]; linarith
            calc 4 * a * A * Real.sqrt h * t ^ (-(1 / 2 : ℝ))
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
  have hI : ‖∫ t in Set.Ioc (1 : ℝ) N, deriv (wT k h) t * AsumT f h ⌊t⌋₊‖ ≤
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
  calc |wT k h N * AsumT f h N - ∫ t in Set.Ioc (1 : ℝ) N, deriv (wT k h) t * AsumT f h ⌊t⌋₊|
      ≤ |wT k h N * AsumT f h N| +
          ‖∫ t in Set.Ioc (1 : ℝ) N, deriv (wT k h) t * AsumT f h ⌊t⌋₊‖ := by
        rw [Real.norm_eq_abs]; exact abs_sub _ _
    _ ≤ (2 ^ a * C + A) * Real.sqrt h * M ^ (1 - ηs) +
          K2 * Real.sqrt h * (2 * (N : ℝ) ^ (1 - ηs) + 2 * (N : ℝ) ^ (1 - 1 / 2 : ℝ)) :=
        add_le_add hb hI
    _ ≤ (2 ^ a * C + A) * Real.sqrt h * M ^ (1 - ηs) +
          K2 * Real.sqrt h * (2 * M ^ (1 - ηs) + 2 * M ^ (1 - ηs)) := by gcongr
    _ = (2 ^ a * C + A + 4 * K2) * M ^ (1 - ηs) * Real.sqrt h := by ring

/-- **`SCS_f(1/22, 1/2)` from the weight-`k` pointwise bound** (`k ≥ 12`, real coefficients). -/
theorem scsf_of_pointwise {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k)
    (hreal : ∀ n, (RamanujanTau.HeckeConvexGeneral.coef f n).im = 0)
    (hpw : ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 → (h : ℝ) * σ ≤ 1 →
      ‖RamanujanTau.SubconvexGeneral.GhF f h ((σ : ℂ) + v * I)‖ ≤
        K * Real.sqrt h * (|2 * v / σ| + 3) * σ ^ (-(k : ℝ) + 12 / 125)) :
    RamanujanTau.SubconvexGeneral.SCSf f (1 / 22) (1 / 2) := by
  obtain ⟨C, hC0, hC⟩ := shS_bound_of_pointwise f (by omega) hreal hpw
  refine ⟨⟨C, hC0, fun h N hh => ?_⟩⟩
  have := hC h N hh
  rw [Real.sqrt_eq_rpow] at this
  unfold ηs at this
  exact this

end RamanujanTau.SubconvexGeneral2
