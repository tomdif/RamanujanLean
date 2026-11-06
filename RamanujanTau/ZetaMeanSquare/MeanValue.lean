/-
# The mean-value theorem for `ζ` off the critical line (Hardy–Littlewood / Landau)

For `1/2 < σ₀ ≤ σ ≤ 1` and `T ≥ 1`,

    |∫_1^T |ζ(σ+it)|² dt − ζ(2σ) T| ≤ C(σ₀) (T^{3/2−σ} + T^{2−2σ} (1 + log T)²).

Proof: `N = ⌈T⌉`, `P(s) = ∑_{n≤N} n^{−s}`.
* `∫_1^T |ζ − P|² ≪ T^{2−2σ}` (`err_L2`, Plancherel for the Euler–Maclaurin tail);
* `∫_1^T |P|² = (T−1) ∑_{n≤N} n^{−2σ} + O(H_N ∑ n^{1−2σ})` (`MeanSquare.mv_poly`) with
  `H_N ∑ n^{1−2σ} ≤ H_N² N^{2−2σ} ≪ (1+log T)² T^{2−2σ}`;
* `∑_{n≤N} n^{−2σ} = ζ(2σ) + O(T^{1−2σ})` (`zeta_formula_large` on the real axis);
* the cross term by AM–GM with weight `η = T^{1/2−σ}`: `| |ζ|² − |P|² | ≤ η|P|² + (1+1/η)|ζ−P|²`.
-/
import RamanujanTau.ZetaMeanSquare.Error
import RamanujanTau.ZetaMeanSquare.Conj
import RamanujanTau.RankinOmega.ZetaMean

set_option autoImplicit false

namespace RamanujanTau.ZetaMeanSquare

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.RankinOmega
open RamanujanTau.MeanSquare (dpoly H H_le_one_add_log mv_poly continuous_dpoly H_nonneg)

/-- The coefficients `n^{−σ}`. -/
noncomputable def bσ (σ : ℝ) (n : ℕ) : ℂ := ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)

lemma norm_bσ_sq (σ : ℝ) (n : ℕ) : ‖bσ σ n‖ ^ 2 = (n : ℝ) ^ (-(2 * σ)) := by
  simp only [bσ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1; push_cast; ring

lemma norm_Pz_eq (N : ℕ) (σ t : ℝ) : ‖Pz N ((σ : ℂ) - t * I)‖ = ‖dpoly (bσ σ) N t‖ :=
  norm_sum_cpow_eq N σ t

lemma sum_cpow_real (N : ℕ) (σ : ℝ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-(2 * (σ : ℂ))) =
      (((∑ n ∈ Finset.Icc 1 N, ‖bσ σ n‖ ^ 2 : ℝ)) : ℂ) := by
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [norm_bσ_sq, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast; ring_nf

/-- **The diagonal sum against `ζ(2σ)`.** -/
lemma diag_close (N : ℕ) (hN : 1 ≤ N) {σ : ℝ} (hσ : 1 / 2 < σ) :
    ‖riemannZeta (2 * (σ : ℂ)) - (((∑ n ∈ Finset.Icc 1 N, ‖bσ σ n‖ ^ 2 : ℝ)) : ℂ)‖ ≤
      (N : ℝ) ^ (1 - 2 * σ) / (2 * σ - 1) + (N : ℝ) ^ (-(2 * σ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hre : (2 * (σ : ℂ)).re = 2 * σ := by simp
  rw [← sum_cpow_real, zeta_formula_large N hN (by rw [hre]; linarith)]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_mul]
  have e1 : ‖(N : ℂ) ^ (1 - 2 * (σ : ℂ))‖ = (N : ℝ) ^ (1 - 2 * σ) := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_eq_rpow_re_of_pos hN0]
    simp
  have e2 : ‖2 * (σ : ℂ) - 1‖ = 2 * σ - 1 := by
    rw [show 2 * (σ : ℂ) - 1 = ((2 * σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have e3 : ‖2 * (σ : ℂ)‖ = 2 * σ := by
    rw [show 2 * (σ : ℂ) = ((2 * σ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [e1, e2, e3]
  have h := norm_IN_le N hN (s := 2 * (σ : ℂ)) (by rw [hre]; linarith)
  rw [hre] at h
  have : 2 * σ * ‖IN N (2 * (σ : ℂ))‖ ≤ (N : ℝ) ^ (-(2 * σ)) := by
    calc 2 * σ * ‖IN N (2 * (σ : ℂ))‖ ≤ 2 * σ * ((N : ℝ) ^ (-(2 * σ)) / (2 * σ)) := by gcongr
      _ = (N : ℝ) ^ (-(2 * σ)) := by field_simp
  linarith

/-- The off-diagonal weight: `∑ n |bₙ|² ≤ N^{2−2σ} H_N`. -/
lemma offdiag_le (N : ℕ) {σ : ℝ} (hσ : σ ≤ 1) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖bσ σ n‖ ^ 2 ≤ (N : ℝ) ^ (2 - 2 * σ) * H N := by
  unfold H
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  simp only [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.2
  rw [norm_bσ_sq]
  have e : (n : ℝ) * (n : ℝ) ^ (-(2 * σ)) = (n : ℝ) ^ (2 - 2 * σ) * (1 / n) := by
    have : (n : ℝ) ^ (2 - 2 * σ) = (n : ℝ) ^ (-(2 * σ)) * (n : ℝ) * n := by
      rw [show 2 - 2 * σ = -(2 * σ) + 1 + 1 by ring, Real.rpow_add hn0, Real.rpow_add hn0,
        Real.rpow_one]
    rw [this]; field_simp
  rw [e]
  have : (n : ℝ) ^ (2 - 2 * σ) ≤ (N : ℝ) ^ (2 - 2 * σ) :=
    Real.rpow_le_rpow hn0.le hnN (by linarith)
  gcongr

/-- The polynomial mean value on `[1, T]`. -/
lemma poly_L2 (b : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    |(∫ t in (1 : ℝ)..T, ‖dpoly b N t‖ ^ 2) - (T - 1) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2| ≤
      12 * H N * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖b n‖ ^ 2 := by
  have h1 := mv_poly b N T
  have h0 := mv_poly b N 1
  have hc : Continuous fun t => ‖dpoly b N t‖ ^ 2 := (continuous_dpoly b N).norm.pow 2
  rw [← intervalIntegral.integral_interval_sub_left (a := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  rw [abs_le] at h1 h0 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h0.1, h0.2]

/-- Pointwise comparison of `|ζ|²` and `|P|²`. -/
lemma sq_compare {z p e η : ℝ} (hz : 0 ≤ z) (hp : 0 ≤ p) (he : 0 ≤ e) (hη : 0 < η)
    (h1 : z ≤ p + e) (h2 : p ≤ z + e) :
    z ^ 2 ≤ (1 + η) * p ^ 2 + (1 + 1 / η) * e ^ 2 ∧
      p ^ 2 ≤ z ^ 2 + η * p ^ 2 + (1 + 1 / η) * e ^ 2 := by
  have amgm : 2 * p * e ≤ η * p ^ 2 + e ^ 2 / η := by
    have key : η * (η * p ^ 2 + e ^ 2 / η) = η ^ 2 * p ^ 2 + e ^ 2 := by field_simp
    have : η * (2 * p * e) ≤ η * (η * p ^ 2 + e ^ 2 / η) := by
      rw [key]; nlinarith [sq_nonneg (η * p - e)]
    exact le_of_mul_le_mul_left this hη
  have hee : 0 ≤ e ^ 2 / η := by positivity
  have hfe : (1 + 1 / η) * e ^ 2 = e ^ 2 + e ^ 2 / η := by ring
  constructor
  · have := pow_le_pow_left₀ hz h1 2
    nlinarith
  · rcases le_or_gt p z with h | h
    · nlinarith
    · have : p ^ 2 - z ^ 2 ≤ 2 * p * e := by nlinarith
      nlinarith

/-- `H_N ≤ 2(1 + log T)` for `N = ⌈T⌉`. -/
lemma H_ceil_le {T : ℝ} (hT : 1 ≤ T) : H ⌈T⌉₊ ≤ 2 * (1 + Real.log T) := by
  obtain ⟨hN1, -, hNT⟩ := ceil_bounds hT
  have hN0 : (0 : ℝ) < ⌈T⌉₊ := by exact_mod_cast hN1
  have h1 := H_le_one_add_log ⌈T⌉₊
  have h2 : Real.log ⌈T⌉₊ ≤ Real.log (2 * T) := Real.log_le_log hN0 hNT
  rw [Real.log_mul (by norm_num) (by linarith)] at h2
  have h3 := Real.log_two_lt_d9
  have h4 : 0 ≤ Real.log T := Real.log_nonneg hT
  linarith

set_option maxHeartbeats 1600000 in
/-- **The mean-value theorem below the real axis**, uniform on `[σ₀, 1]`. -/
theorem mean_value_minus {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 1 → ∀ T : ℝ, 1 ≤ T →
      |(∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) - t * I)‖ ^ 2) -
          (riemannZeta (2 * (σ : ℂ))).re * T| ≤
        C * (T ^ ((3 : ℝ) / 2 - σ) + T ^ (2 - 2 * σ) * (1 + Real.log T) ^ 2) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 * σ₀))) :=
    Real.summable_nat_rpow.2 (by linarith)
  set Z0 : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(2 * σ₀)) with hZ0
  have hZ00 : 0 ≤ Z0 := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  set CE : ℝ := 4 + 16 * Real.pi with hCE
  have hCE0 : 0 ≤ CE := by rw [hCE]; positivity
  set K3 : ℝ := 1 / (2 * σ₀ - 1) + 1 with hK3
  have hK30 : 0 ≤ K3 := by
    rw [hK3]; have : 0 < 2 * σ₀ - 1 := by linarith
    positivity
  refine ⟨2 * Z0 + 2 * CE + 192 + K3, by positivity, fun σ hσ1 hσ2 T hT => ?_⟩
  have hσh : 1 / 2 < σ := by linarith
  have hσ0 : 0 < σ := by linarith
  have hT0 : 0 < T := by linarith
  obtain ⟨hN1, hTN, hNT⟩ := ceil_bounds hT
  set N : ℕ := ⌈T⌉₊ with hN
  have hN0 : (0 : ℝ) < N := by linarith
  set b := bσ σ with hb
  set Sd : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 with hSd
  set W : ℝ := ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖b n‖ ^ 2 with hW
  set L : ℝ := Real.log T with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hT
  set ζR : ℝ := (riemannZeta (2 * (σ : ℂ))).re with hζR
  set G : ℝ := T ^ (2 - 2 * σ) with hG
  set Q : ℝ := T ^ ((3 : ℝ) / 2 - σ) with hQ
  have hG0 : 0 ≤ G := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hT (by linarith)
  -- (F4) Sd ≤ Z0
  have hSd0 : 0 ≤ Sd := Finset.sum_nonneg fun _ _ => by positivity
  have hSdZ : Sd ≤ Z0 := by
    calc Sd = ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ)) := by
          rw [hSd]; exact Finset.sum_congr rfl fun n _ => norm_bσ_sq σ n
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ₀)) := by
          refine Finset.sum_le_sum fun n hn => ?_
          simp only [Finset.mem_Icc] at hn
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
          exact Real.rpow_le_rpow_of_exponent_le this (by linarith)
      _ ≤ Z0 := hsum.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  -- (F3) the diagonal against ζ(2σ)
  have hF3 : T * |ζR - Sd| ≤ K3 * G := by
    have hd := diag_close N hN1 hσh
    have hre : |ζR - Sd| ≤ ‖riemannZeta (2 * (σ : ℂ)) - ((Sd : ℝ) : ℂ)‖ := by
      have := Complex.abs_re_le_norm (riemannZeta (2 * (σ : ℂ)) - ((Sd : ℝ) : ℂ))
      simpa [hζR] using this
    have h1 : (N : ℝ) ^ (1 - 2 * σ) ≤ T ^ (1 - 2 * σ) :=
      Real.rpow_le_rpow_of_nonpos hT0 hTN (by linarith)
    have h2 : (N : ℝ) ^ (-(2 * σ)) ≤ T ^ (1 - 2 * σ) :=
      le_trans (Real.rpow_le_rpow_of_nonpos hT0 hTN (by linarith))
        (Real.rpow_le_rpow_of_exponent_le hT (by linarith))
    have h3 : 1 / (2 * σ - 1) ≤ 1 / (2 * σ₀ - 1) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have hp : 0 ≤ T ^ (1 - 2 * σ) := by positivity
    have h4 : (N : ℝ) ^ (1 - 2 * σ) / (2 * σ - 1) ≤ T ^ (1 - 2 * σ) * (1 / (2 * σ₀ - 1)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul h1 h3 (by have : 0 < 2 * σ - 1 := by linarith
                                 positivity) hp
    have hTG : T * T ^ (1 - 2 * σ) = G := by
      rw [hG, show 2 - 2 * σ = 1 + (1 - 2 * σ) by ring, Real.rpow_add hT0, Real.rpow_one]
    calc T * |ζR - Sd| ≤ T * (T ^ (1 - 2 * σ) * (1 / (2 * σ₀ - 1)) + T ^ (1 - 2 * σ)) := by
          gcongr; linarith
      _ = (T * T ^ (1 - 2 * σ)) * K3 := by rw [hK3]; ring
      _ = K3 * G := by rw [hTG]; ring
  -- (F2) polynomial mean value
  have hH : H N ≤ 2 * (1 + L) := H_ceil_le hT
  have hH0 : 0 ≤ H N := H_nonneg N
  have hNG : (N : ℝ) ^ (2 - 2 * σ) ≤ 2 * G := by
    calc (N : ℝ) ^ (2 - 2 * σ) ≤ (2 * T) ^ (2 - 2 * σ) := Real.rpow_le_rpow hN0.le hNT (by linarith)
      _ = 2 ^ (2 - 2 * σ) * G := Real.mul_rpow (by norm_num) hT0.le
      _ ≤ 2 ^ (1 : ℝ) * G := by
          gcongr
          · norm_num
          · linarith
      _ = 2 * G := by rw [Real.rpow_one]
  have hWle : W ≤ 2 * G * H N := by
    have := offdiag_le N hσ2 (σ := σ)
    calc W ≤ (N : ℝ) ^ (2 - 2 * σ) * H N := this
      _ ≤ 2 * G * H N := by gcongr
  have hHW : 12 * H N * W ≤ 96 * (1 + L) ^ 2 * G := by
    have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => by positivity
    calc 12 * H N * W ≤ 12 * H N * (2 * G * H N) := by gcongr
      _ = 24 * G * (H N) ^ 2 := by ring
      _ ≤ 24 * G * (2 * (1 + L)) ^ 2 := by gcongr
      _ = 96 * (1 + L) ^ 2 * G := by ring
  have hF2 := poly_L2 b N T
  rw [← hSd, ← hW] at hF2
  -- the three integrands and their continuity
  set fz : ℝ → ℝ := fun t => ‖riemannZeta ((σ : ℂ) - t * I)‖ ^ 2 with hfz
  set fp : ℝ → ℝ := fun t => ‖dpoly b N t‖ ^ 2 with hfp
  set fe : ℝ → ℝ := fun t => ‖riemannZeta ((σ : ℂ) - t * I) - Pz N ((σ : ℂ) - t * I)‖ ^ 2 with hfe
  have hcz : ContinuousOn fz (uIcc 1 T) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact ((continuousAt_zeta_line σ (by linarith [ht.1] : t ≠ 0)).norm.pow 2).continuousWithinAt
  have hcp : Continuous fp := (continuous_dpoly b N).norm.pow 2
  have hce : ContinuousOn fe (uIcc 1 T) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact (((continuousAt_zeta_line σ (by linarith [ht.1] : t ≠ 0)).sub
      (continuous_Pz_line N σ).continuousAt).norm.pow 2).continuousWithinAt
  have hiz := hcz.intervalIntegrable (μ := volume)
  have hip : IntervalIntegrable fp volume 1 T := hcp.intervalIntegrable _ _
  have hie := hce.intervalIntegrable (μ := volume)
  set Iz := ∫ t in (1 : ℝ)..T, fz t with hIz
  set IP := ∫ t in (1 : ℝ)..T, fp t with hIP
  set IE := ∫ t in (1 : ℝ)..T, fe t with hIE
  have hF1 : IE ≤ CE * G := err_L2 (by linarith) hσ2 hT
  have hIE0 : 0 ≤ IE := intervalIntegral.integral_nonneg hT fun t _ => by positivity
  -- (F5) comparison with weight η
  set η : ℝ := T ^ ((1 : ℝ) / 2 - σ) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT (by linarith)
  have hpt := fun t (ht : t ∈ Icc (1 : ℝ) T) => by
    have ht0 : 0 < t := by linarith [ht.1]
    have hPz := norm_Pz_eq N σ t
    have h1 := norm_le_norm_add_norm_sub' (riemannZeta ((σ : ℂ) - t * I)) (Pz N ((σ : ℂ) - t * I))
    have h2 := norm_le_norm_add_norm_sub' (Pz N ((σ : ℂ) - t * I)) (riemannZeta ((σ : ℂ) - t * I))
    rw [norm_sub_rev] at h2
    rw [hPz] at h1 h2
    exact sq_compare (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hη0 h1 h2
  have hup : Iz ≤ (1 + η) * IP + (1 + 1 / η) * IE := by
    have := intervalIntegral.integral_mono_on hT hiz
      ((hip.const_mul (1 + η)).add (hie.const_mul (1 + 1 / η))) (fun t ht => (hpt t ht).1)
    rw [intervalIntegral.integral_add (hip.const_mul _) (hie.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at this
    exact this
  have hlo : IP ≤ Iz + η * IP + (1 + 1 / η) * IE := by
    have := intervalIntegral.integral_mono_on hT hip
      ((hiz.add (hip.const_mul η)).add (hie.const_mul (1 + 1 / η))) (fun t ht => (hpt t ht).2)
    rw [intervalIntegral.integral_add (hiz.add (hip.const_mul _)) (hie.const_mul _),
      intervalIntegral.integral_add hiz (hip.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at this
    exact this
  have hIP0 : 0 ≤ IP := intervalIntegral.integral_nonneg hT fun t _ => by positivity
  clear_value Iz IP IE fz fp fe η Q G L ζR Sd W
  -- exponent bookkeeping
  have hηT : η * T = Q := by
    rw [hη, hQ, show (3 : ℝ) / 2 - σ = (1 / 2 - σ) + 1 by ring, Real.rpow_add hT0, Real.rpow_one]
  have hiη : 1 / η = T ^ (σ - 1 / 2) := by
    rw [hη, one_div, ← Real.rpow_neg hT0.le]; congr 1; ring
  have hiηG : 1 / η * G = Q := by
    rw [hiη, hG, hQ, ← Real.rpow_add hT0]; congr 1; ring
  have hiη1 : 1 ≤ 1 / η := by rw [le_div_iff₀ hη0]; linarith
  have hIPu : IP ≤ T * Sd + 96 * (1 + L) ^ 2 * G := by
    have := (abs_le.1 hF2).2; nlinarith
  have hcross : η * IP + (1 + 1 / η) * IE ≤ Sd * Q + 96 * (1 + L) ^ 2 * G + 2 * CE * Q := by
    have e1 : η * IP ≤ Sd * Q + 96 * (1 + L) ^ 2 * G := by
      have h96 : 0 ≤ 96 * (1 + L) ^ 2 * G := by positivity
      calc η * IP ≤ η * (T * Sd + 96 * (1 + L) ^ 2 * G) := by gcongr
        _ = (η * T) * Sd + η * (96 * (1 + L) ^ 2 * G) := by ring
        _ ≤ Q * Sd + 1 * (96 * (1 + L) ^ 2 * G) := by rw [hηT]; gcongr
        _ = Sd * Q + 96 * (1 + L) ^ 2 * G := by ring
    have e2 : (1 + 1 / η) * IE ≤ 2 * CE * Q := by
      calc (1 + 1 / η) * IE ≤ (2 * (1 / η)) * (CE * G) := by
            gcongr; linarith
        _ = 2 * CE * (1 / η * G) := by ring
        _ = 2 * CE * Q := by rw [hiηG]
    linarith
  -- final assembly
  have hL1 : 1 ≤ (1 + L) ^ 2 := by nlinarith
  have hfin : |Iz - ζR * T| ≤ (Sd + 2 * CE) * Q + Sd + (192 * (1 + L) ^ 2 + K3) * G := by
    have hA : |Iz - IP| ≤ η * IP + (1 + 1 / η) * IE := by
      rw [abs_le]; constructor <;> linarith
    have hB := hF2
    have hC : |(T - 1) * Sd - ζR * T| ≤ K3 * G + Sd := by
      have : (T - 1) * Sd - ζR * T = T * (Sd - ζR) - Sd := by ring
      rw [this]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_pos hT0, abs_sub_comm, abs_of_nonneg hSd0]
      linarith
    have e : Iz - ζR * T = (Iz - IP) + (IP - (T - 1) * Sd) + ((T - 1) * Sd - ζR * T) := by ring
    rw [e]
    refine (abs_add_three _ _ _).trans ?_
    linarith [hA, hB, hC, hcross, hHW]
  have hGL : G ≤ G * (1 + L) ^ 2 := le_mul_of_one_le_right hG0 hL1
  calc |Iz - ζR * T| ≤ (Sd + 2 * CE) * Q + Sd + (192 * (1 + L) ^ 2 + K3) * G := hfin
    _ ≤ (Z0 + 2 * CE) * Q + Z0 * Q + (192 + K3) * (G * (1 + L) ^ 2) := by
        have h1 : (Sd + 2 * CE) * Q ≤ (Z0 + 2 * CE) * Q := by gcongr
        have h2 : Sd ≤ Z0 * Q := by nlinarith
        have h3 : (192 * (1 + L) ^ 2 + K3) * G ≤ (192 + K3) * (G * (1 + L) ^ 2) := by
          have := mul_le_mul_of_nonneg_left hGL hK30
          linarith
        linarith
    _ ≤ (2 * Z0 + 2 * CE + 192 + K3) * (Q + G * (1 + L) ^ 2) := by
        have h0 : 0 ≤ G * (1 + L) ^ 2 := by positivity
        have h1 := mul_nonneg (show (0 : ℝ) ≤ 192 + K3 by positivity) hQ0
        have h2 := mul_nonneg (show (0 : ℝ) ≤ 2 * Z0 + 2 * CE by positivity) h0
        linarith

end RamanujanTau.ZetaMeanSquare
