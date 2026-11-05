/-
# Hardy–Littlewood-type count for `L(Δ,s)`: `N₀(T) ≫ T / log log T`

See `docs/HARDY_COUNT_LINEAR.md`.

For `T` large put `L = log T`, `κ = √(2 log L)` (so `e^{κ²} = L²`), `h = H κ`, `r = κ h`
(`≍ log log T`), `α = π/2 − 1/T`, and `Iw(t₀) = ∫ Z(t) e^{αt} tri_{2r}(t − t₀) dt`.

* upper (`Windows.mean_sq_Iw`): `∫_T^{2T} Iw² ≤ 4 S² (2r)³`, `S = 2πM/cos⁶α ≪ T⁶`;
* lower (`Windows.Iw_lower` + `Kernel.kernel_lower`): if `Z` has no zero within `2r` of `t₀`
  then `|Iw(t₀)| ≥ A = r e^{−3} c_Z (T/2)^{11/2} · h e^{−3}`;
* `A² T/2 ≥ 4 S² (2r)³` as soon as `h ≥ D κ` (exponents of `T` balance exactly: this is where
  the averaging over `t₀` gains the factor lost by the sup bound in `HardyCount`);
* Chebyshev + covering (`Count.many_zeros_of_mean_sq`): `≥ T/(8r) ≍ T/log log T` zeros in
  `[T/2, 3T]`.
-/
import RamanujanTau.HardyCountLinear.Windows
import RamanujanTau.HardyCountLinear.Kernel
import RamanujanTau.HardyCountLinear.Count
import RamanujanTau.HardyCount.Main

set_option autoImplicit false

namespace RamanujanTau.HardyCountLinear

open Complex MeasureTheory Set Filter
open RamanujanTau.HeckeL RamanujanTau.HardyZeros RamanujanTau.HardyCount
open scoped Real

/-- `1/cos⁶(π/2 − 1/T) ≤ (πT/2)⁶`. -/
lemma inv_cos_pow_le {T : ℝ} (hT : 1 ≤ T) :
    1 / Real.cos (π / 2 - 1 / T) ^ 6 ≤ (π * T / 2) ^ 6 := by
  have hTpos : 0 < T := by linarith
  have hinv : 1 / T ≤ 1 := by rw [div_le_one hTpos]; exact hT
  have hinvpos : 0 < 1 / T := by positivity
  have hcos : 2 / π * (1 / T) ≤ Real.cos (π / 2 - 1 / T) := by
    rw [Real.cos_pi_div_two_sub]
    exact Real.mul_le_sin hinvpos.le (by linarith [Real.pi_gt_three])
  have hcpos : 0 < 2 / π * (1 / T) := by positivity
  have hc6 : (2 / π * (1 / T)) ^ 6 ≤ Real.cos (π / 2 - 1 / T) ^ 6 :=
    pow_le_pow_left₀ hcpos.le hcos 6
  rw [div_le_iff₀ (pow_pos (hcpos.trans_le hcos) 6)]
  have e : (π * T / 2) ^ 6 * (2 / π * (1 / T)) ^ 6 = 1 := by
    rw [← mul_pow]; field_simp
  calc (1 : ℝ) = (π * T / 2) ^ 6 * (2 / π * (1 / T)) ^ 6 := e.symm
    _ ≤ _ := by gcongr

set_option maxHeartbeats 1000000 in
/-- **Core count**: `≥ T / (16 H log log T)` zeros of `Z` in `(0, 3T]`. -/
theorem core_count : ∃ H T₀ : ℝ, 1 ≤ H ∧ 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
    (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ Zr γ = 0) ∧
      T / (16 * H * Real.log (Real.log T)) ≤ S.card := by
  obtain ⟨M, hM0, hmean⟩ := mean_sq_Iw
  obtain ⟨β, C, hβ0, hC0, hker⟩ := kernel_lower
  have hcZ := cZ_pos
  set D : ℝ := 128 * π ^ 14 * M ^ 2 * Real.exp 12 / cZ ^ 2 with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  set H : ℝ := D + 2 * β + 1 with hH
  have hH1 : 1 ≤ H := by rw [hH]; linarith
  set T₀ : ℝ := max (max (Real.exp 8) (4 * Real.exp 3 * (4 * C + 1) * β)) (256 * H ^ 2)
    with hT₀
  have hT₀8 : Real.exp 8 ≤ T₀ := (le_max_left _ _).trans (le_max_left _ _)
  have he8 : 1 ≤ Real.exp 8 := Real.one_le_exp (by norm_num)
  refine ⟨H, T₀, hH1, he8.trans hT₀8, fun T hT => ?_⟩
  have hT8 : Real.exp 8 ≤ T := hT₀8.trans hT
  have hTC : 4 * Real.exp 3 * (4 * C + 1) * β ≤ T :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hT
  have hTH : 256 * H ^ 2 ≤ T := (le_max_right _ _).trans hT
  have hT1 : 1 ≤ T := he8.trans hT8
  have hTpos : 0 < T := by linarith
  set L : ℝ := Real.log T with hLdef
  have hL8 : 8 ≤ L := by
    rw [hLdef, ← Real.log_exp 8]; exact Real.log_le_log (Real.exp_pos 8) hT8
  have hLpos : 0 < L := by linarith
  have hlogL : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set κ : ℝ := Real.sqrt (2 * Real.log L) with hκdef
  have hκ2 : κ ^ 2 = 2 * Real.log L := Real.sq_sqrt (by linarith)
  have hκ1 : 1 ≤ κ := by
    rw [hκdef, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hexpκ : Real.exp (κ ^ 2) = L ^ 2 := by
    rw [hκ2, show 2 * Real.log L = Real.log (L ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  set h : ℝ := H * κ with hhdef
  have hh1 : 1 ≤ h := by rw [hhdef]; nlinarith
  set r : ℝ := κ * h with hrdef
  have hr_eq : r = 2 * H * Real.log L := by
    rw [hrdef, hhdef]
    calc κ * (H * κ) = H * κ ^ 2 := by ring
      _ = _ := by rw [hκ2]; ring
  have hrpos : 0 < r := by rw [hr_eq]; positivity
  -- `r ≤ T/4`
  have hrT : r ≤ T / 4 := by
    have h1 : Real.log L ≤ L := Real.log_le_self hLpos.le
    have h2 : L ≤ T ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div hTpos.le (by norm_num)
    have hsq : T ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) = T := by
      rw [← Real.rpow_add hTpos]; norm_num
    have h3 : 16 * H ≤ T ^ (1 / 2 : ℝ) := by
      have : (16 * H) ^ 2 ≤ (T ^ (1 / 2 : ℝ)) ^ 2 := by rw [sq, sq, hsq]; nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp this
    have hp : 0 ≤ T ^ (1 / 2 : ℝ) := by positivity
    rw [hr_eq]
    nlinarith
  -- the kernel smallness condition
  have hsmall : (4 * C + 1) * β * T * Real.exp (-(Real.exp (κ ^ 2) / 4)) ≤ Real.exp (-3) / 4 := by
    rw [hexpκ]
    have h1 : Real.exp (-(L ^ 2 / 4)) ≤ Real.exp (-(2 * L)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp (-(2 * L)) = 1 / T ^ 2 := by
      rw [Real.exp_neg, show 2 * L = Real.log (T ^ 2) by rw [Real.log_pow]; push_cast; ring,
        Real.exp_log (by positivity), one_div]
    have hB0 : 0 ≤ (4 * C + 1) * β * T := by positivity
    calc (4 * C + 1) * β * T * Real.exp (-(L ^ 2 / 4))
        ≤ (4 * C + 1) * β * T * (1 / T ^ 2) := by rw [← h2]; gcongr
      _ = (4 * C + 1) * β / T := by field_simp
      _ ≤ Real.exp (-3) / 4 := by
        rw [div_le_iff₀ hTpos]
        have hE : Real.exp (-3) * Real.exp 3 = 1 := by rw [← Real.exp_add]; simp
        have := mul_le_mul_of_nonneg_left hTC (Real.exp_pos (-3)).le
        nlinarith
  -- the moments
  set α : ℝ := π / 2 - 1 / T with hα
  have hinv : 1 / T ≤ 1 := by rw [div_le_one hTpos]; exact hT1
  have hα0 : 0 ≤ α := by rw [hα]; linarith [Real.pi_gt_three, (by positivity : (0 : ℝ) < 1 / T)]
  have hinvpos : 0 < 1 / T := by positivity
  have hαπ : α < π / 2 := by rw [hα]; linarith
  obtain ⟨hIc, hIm⟩ := hmean α hα0 hαπ (2 * r) (by positivity)
  set P : ℝ := (T / 2) ^ (11 / 2 : ℝ) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos (by linarith) _
  set A : ℝ := r * Real.exp (-3) * cZ * P * (h * Real.exp (-3)) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have hlow : ∀ t₀ ∈ Icc T (2 * T), (∀ t ∈ Icc (t₀ - 2 * r) (t₀ + 2 * r), Zr t ≠ 0) →
      A ≤ |Iw α (2 * r) t₀| := by
    intro t₀ ht₀ hno
    have hk := hker T t₀ h κ hT1 ht₀.1 ht₀.2 hh1 hκ1 (by rw [hhdef, hH]; nlinarith)
      (by rw [← hrdef]; linarith) hsmall
    have hl := Iw_lower hT1 ht₀.1 ht₀.2 hrpos (by linarith) hno
    have hc : 0 ≤ r * Real.exp (-3) * cZ * P := by positivity
    calc A = r * Real.exp (-3) * cZ * P * (h * Real.exp (-3)) := rfl
      _ ≤ r * Real.exp (-3) * cZ * P * ∫ t in (t₀ - κ * h)..(t₀ + κ * h), ‖tauL (6 + t * I)‖ :=
        mul_le_mul_of_nonneg_left hk hc
      _ ≤ |Iw α (2 * r) t₀| := hl
  -- the mean-square comparison
  have hm : ∫ t₀ in Icc T (2 * T), Iw α (2 * r) t₀ ^ 2 ≤ A ^ 2 * T / 2 := by
    refine (hIm T hTpos).trans ?_
    have hS : 2 * π * M / Real.cos α ^ 6 ≤ 2 * π * M * (π * T / 2) ^ 6 := by
      have := inv_cos_pow_le hT1
      rw [← hα] at this
      calc 2 * π * M / Real.cos α ^ 6 = 2 * π * M * (1 / Real.cos α ^ 6) := by ring
        _ ≤ _ := by gcongr
    have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαπ⟩
    have hS0 : 0 ≤ 2 * π * M / Real.cos α ^ 6 := by positivity
    have hP2 : P ^ 2 = (T / 2) ^ 11 := by
      rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    have hhD : D * κ ≤ h := by rw [hhdef, hH]; nlinarith
    have hDe : D * Real.exp (-12) * cZ ^ 2 = 128 * π ^ 14 * M ^ 2 := by
      rw [hD]
      have hE : Real.exp 12 * Real.exp (-12) = 1 := by rw [← Real.exp_add]; simp
      field_simp
      rw [mul_assoc, hE]; ring
    have hkey : 128 * π ^ 14 * M ^ 2 * r ≤ h ^ 2 * Real.exp (-12) * cZ ^ 2 := by
      have hE0 : 0 ≤ Real.exp (-12) * cZ ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_right hhD hE0
      have hh0 : 0 ≤ h := by linarith
      calc 128 * π ^ 14 * M ^ 2 * r = h * (D * κ * (Real.exp (-12) * cZ ^ 2)) := by
            rw [hrdef, ← hDe]; ring
        _ ≤ h * (h * (Real.exp (-12) * cZ ^ 2)) := mul_le_mul_of_nonneg_left this hh0
        _ = _ := by ring
    have hAeq : A ^ 2 * T / 2 = (h ^ 2 * Real.exp (-12) * cZ ^ 2) * (r ^ 2 * (T / 2) ^ 12) := by
      have hE : Real.exp (-3) ^ 2 * Real.exp (-3) ^ 2 = Real.exp (-12) := by
        rw [← pow_add, ← Real.exp_nat_mul]; norm_num
      have h12 : (T / 2) ^ 12 = P ^ 2 * (T / 2) := by rw [hP2]; ring
      clear_value A P r h
      rw [h12, ← hE, hA]; ring
    have hT2 : 0 ≤ (T / 2) ^ 12 := by positivity
    have hr3 : 0 ≤ r ^ 2 := sq_nonneg r
    calc 4 * (2 * π * M / Real.cos α ^ 6) ^ 2 * (2 * r) ^ 3
        ≤ 4 * (2 * π * M * (π * T / 2) ^ 6) ^ 2 * (2 * r) ^ 3 := by gcongr
      _ = (128 * π ^ 14 * M ^ 2 * r) * (r ^ 2 * (T / 2) ^ 12) := by ring
      _ ≤ (h ^ 2 * Real.exp (-12) * cZ ^ 2) * (r ^ 2 * (T / 2) ^ 12) := by gcongr
      _ = A ^ 2 * T / 2 := hAeq.symm
  obtain ⟨S, hS, hcard⟩ := many_zeros_of_mean_sq hIc hTpos (by positivity : 0 < 2 * r) hlow hm
    hApos
  refine ⟨S, fun γ hγ => ?_, ?_⟩
  · obtain ⟨hγI, hz⟩ := hS γ hγ
    exact ⟨by linarith [hγI.1], by linarith [hγI.2], hz⟩
  · calc T / (16 * H * Real.log (Real.log T)) = T / (4 * (2 * r)) := by
          rw [hr_eq, ← hLdef]; ring_nf
      _ ≤ S.card := hcard

/-- **Headline: `N₀(T) ≫ T / log log T`** for the critical zeros of `L(Δ,s)`. -/
theorem tauL_critical_zeros_loglog : ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
    (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ tauL (6 + t * I) = 0) ∧
      c * T / Real.log (Real.log T) ≤ S.card := by
  obtain ⟨H, T₀, hH1, hT₀1, hcore⟩ := core_count
  refine ⟨1 / (48 * H), 3 * max T₀ (Real.exp 3), by positivity, fun T hT => ?_⟩
  have he3 : 1 ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  set T' : ℝ := T / 3 with hT'
  have hT'0 : T₀ ≤ T' := by rw [hT']; linarith [le_max_left T₀ (Real.exp 3)]
  have hT'e : Real.exp 3 ≤ T' := by rw [hT']; linarith [le_max_right T₀ (Real.exp 3)]
  have hT'pos : 0 < T' := by linarith
  obtain ⟨S, hS, hcard⟩ := hcore T' hT'0
  refine ⟨S, fun t ht => ?_, ?_⟩
  · obtain ⟨h0, h1, hz⟩ := hS t ht
    exact ⟨h0, by rw [hT'] at h1; linarith, tauL_zero_of_Zr_zero hz⟩
  · -- `log log T' ≤ log log T` and both are positive
    have hTT : T' ≤ T := by rw [hT']; linarith
    have hl1 : 3 ≤ Real.log T' := by
      rw [← Real.log_exp 3]; exact Real.log_le_log (Real.exp_pos 3) hT'e
    have hl2 : Real.log T' ≤ Real.log T := Real.log_le_log hT'pos hTT
    have hll1 : 0 < Real.log (Real.log T') := Real.log_pos (by linarith)
    have hll2 : Real.log (Real.log T') ≤ Real.log (Real.log T) :=
      Real.log_le_log (by linarith) hl2
    have hHpos : 0 < H := by linarith
    calc 1 / (48 * H) * T / Real.log (Real.log T)
        = T' / (16 * H * Real.log (Real.log T)) := by rw [hT']; field_simp; ring
      _ ≤ T' / (16 * H * Real.log (Real.log T')) := by
          apply div_le_div_of_nonneg_left hT'pos.le (by positivity)
          gcongr
      _ ≤ S.card := hcard

/-- The same count for `Λ(Δ, 6+it)`. -/
theorem heckeLambda_critical_zeros_loglog : ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T →
    ∃ S : Finset ℝ, (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ heckeLambda (6 + t * I) = 0) ∧
      c * T / Real.log (Real.log T) ≤ S.card := by
  obtain ⟨c, T₀, hc, h⟩ := tauL_critical_zeros_loglog
  refine ⟨c, T₀, hc, fun T hT => ?_⟩
  obtain ⟨S, hS, hcard⟩ := h T hT
  refine ⟨S, fun t ht => ?_, hcard⟩
  obtain ⟨h0, h1, hz⟩ := hS t ht
  refine ⟨h0, h1, ?_⟩
  have hs : ∀ n : ℕ, (6 + t * I : ℂ) ≠ -n :=
    RamanujanTau.HeckeZeros.ne_neg_nat_of_re_pos (by simp)
  rw [heckeLambda_eq_tauL hs, hz, mul_zero]

/-- **Corollary: `N₀(T) ≫_ε T^{1−ε}`** for every `ε > 0`. -/
theorem tauL_critical_zeros_one_sub_eps {ε : ℝ} (hε : 0 < ε) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ tauL (6 + t * I) = 0) ∧ c * T ^ (1 - ε) ≤ S.card := by
  obtain ⟨c, T₀, hc, h⟩ := tauL_critical_zeros_loglog
  refine ⟨c * ε, max T₀ (Real.exp (Real.exp 1)), by positivity, fun T hT => ?_⟩
  obtain ⟨S, hS, hcard⟩ := h T ((le_max_left _ _).trans hT)
  refine ⟨S, hS, ?_⟩
  have hee : Real.exp (Real.exp 1) ≤ T := (le_max_right _ _).trans hT
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hee
  have hl : Real.exp 1 ≤ Real.log T := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hee
  have hlpos : 0 < Real.log T := (Real.exp_pos 1).trans_le hl
  have hll : 1 ≤ Real.log (Real.log T) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hl
  have hll' : Real.log (Real.log T) ≤ T ^ ε / ε :=
    (Real.log_le_self hlpos.le).trans (Real.log_le_rpow_div hTpos.le hε)
  have hsplit : T = T ^ (1 - ε) * T ^ ε := by
    rw [← Real.rpow_add hTpos]; simp
  have hTe : 0 < T ^ ε := Real.rpow_pos_of_pos hTpos ε
  have hT1e : 0 < T ^ (1 - ε) := Real.rpow_pos_of_pos hTpos _
  refine le_trans ?_ hcard
  rw [le_div_iff₀ (by linarith)]
  calc c * ε * T ^ (1 - ε) * Real.log (Real.log T)
      ≤ c * ε * T ^ (1 - ε) * (T ^ ε / ε) := by gcongr
    _ = c * (T ^ (1 - ε) * T ^ ε) := by field_simp
    _ = c * T := by rw [← hsplit]

end RamanujanTau.HardyCountLinear

#print axioms RamanujanTau.HardyCountLinear.tauL_critical_zeros_loglog
#print axioms RamanujanTau.HardyCountLinear.heckeLambda_critical_zeros_loglog
#print axioms RamanujanTau.HardyCountLinear.tauL_critical_zeros_one_sub_eps
#print axioms RamanujanTau.HardyCountLinear.core_count
#print axioms RamanujanTau.HardyCountLinear.kernel_lower
#print axioms RamanujanTau.HardyCountLinear.mean_sq_Iw
#print axioms RamanujanTau.HardyCountLinear.Iw_lower
#print axioms RamanujanTau.HardyCountLinear.integral_tri_norm_fI_sq_le
#print axioms RamanujanTau.HardyCountLinear.many_zeros_of_mean_sq
