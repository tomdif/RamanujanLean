/-
# The Appell–Lerch form of `f(q)` on the unit disc

`f_AL`: for `|q| < 1`,

  `f(q) (q;q)_∞ = 1 + 4 Σ_{n≥1} (−1)ⁿ q^{n(3n+1)/2} / (1 + qⁿ)`.

This is `RankProof.rank_AL` at `z = −1` (the formal identity in `ℂ⟦q⟧`), transferred to holomorphic functions
on the disc with the Taylor-series machinery of `Taylor` / `MockTheta3Analytic` (`Taylor.eq_of_T`).
-/
import RamanujanTau.RankAL
import RamanujanTau.MockTheta3Radial
import RamanujanTau.HardyRamanujan.GenFun

set_option autoImplicit false

namespace MockCusp
open Complex Filter Metric Function Set PowerSeries Taylor
open scoped Topology Nat

noncomputable section

/-- `e(n) = (n+1)(3n+4)/2`, the exponent `m(3m+1)/2` at `m = n+1`. -/
def eN (n : ℕ) : ℕ := (n + 1) * (3 * n + 4) / 2

lemma two_mul_eN (n : ℕ) : 2 * eN n = (n + 1) * (3 * n + 4) := by
  unfold eN
  have : 2 ∣ (n + 1) * (3 * n + 4) := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Dvd.dvd.mul_left ⟨3 * k + 2, by omega⟩ _
    · exact Dvd.dvd.mul_right ⟨k + 1, by omega⟩ _
  exact Nat.mul_div_cancel' this

lemma eN_ge (n : ℕ) : n + 1 ≤ eN n := by
  have := two_mul_eN n; nlinarith

lemma eN_eq (n : ℕ) : eN n = (n + 1) ^ 2 + (n + 1 + 1).choose 2 := by
  have h1 := two_mul_eN n
  have h2 : 2 * (n + 1 + 1).choose 2 = (n + 2) * (n + 1) := by
    rw [Nat.choose_two_right]
    have : 2 ∣ (n + 1 + 1) * (n + 1 + 1 - 1) := by
      rw [show n + 1 + 1 - 1 = n + 1 by omega]
      exact (Nat.even_mul_succ_self (n + 1)).two_dvd |>.trans (by rw [mul_comm])
    rw [Nat.mul_div_cancel' this]; rw [show n + 1 + 1 - 1 = n + 1 by omega]
  nlinarith

/-- the `n`-th term (index shifted, `m = n + 1`). -/
def fGt (n : ℕ) (q : ℂ) : ℂ := (-1 : ℂ) ^ (n + 1) * q ^ eN n * (1 + q ^ (n + 1))⁻¹

/-- `G(q) = 1 + 4 Σ_{m≥1} (−1)^m q^{m(3m+1)/2}/(1+q^m)`. -/
def fG (q : ℂ) : ℂ := 1 + 4 * ∑' n, fGt n q

lemma one_add_pow_ne {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) (k : ℕ) (hk : 1 ≤ k) : 1 + q ^ k ≠ 0 := by
  intro h
  have : ‖q ^ k‖ = 1 := by rw [show q ^ k = -1 by linear_combination h]; simp
  rw [norm_pow] at this
  have h1 : ‖q‖ < 1 := by simpa using hq
  have : ‖q‖ ^ k < 1 := pow_lt_one₀ (norm_nonneg _) h1 (by omega)
  linarith

lemma fGt_hol (n : ℕ) : Hol (fGt n) := by
  unfold fGt Hol
  refine ((differentiableOn_const _).mul (differentiableOn_id.pow _)).mul ?_
  exact ((differentiableOn_const _).add (differentiableOn_id.pow _)).inv fun q hq => one_add_pow_ne hq _ (by omega)

lemma T_fGt (n : ℕ) : T (fGt n) = PowerSeries.C ((-1 : ℂ) ^ (n + 1)) * X ^ eN n * (1 + X ^ (n + 1))⁻¹ := by
  have hA : Hol (fun q : ℂ => (-1 : ℂ) ^ (n + 1) * q ^ eN n) :=
    (differentiableOn_const _).mul (differentiableOn_id.pow _)
  have hh : Hol (fun q : ℂ => 1 + q ^ (n + 1)) := (differentiableOn_const _).add (differentiableOn_id.pow _)
  have hB : Hol (fun q : ℂ => (1 + q ^ (n + 1))⁻¹) := hh.inv fun q hq => one_add_pow_ne hq _ (by omega)
  show T (fun q => (fun q : ℂ => (-1 : ℂ) ^ (n + 1) * q ^ eN n) q * (fun q : ℂ => (1 + q ^ (n + 1))⁻¹) q) = _
  rw [T_mul hA hB, T_mul (f := fun _ => (-1 : ℂ) ^ (n + 1)) (g := fun q : ℂ => q ^ eN n)
    (differentiableOn_const _) (differentiableOn_id.pow _), T_const,
    T_pow (f := fun q : ℂ => q) differentiableOn_id, T_id,
    T_inv hh fun q hq => one_add_pow_ne hq _ (by omega),
    T_add (f := fun _ => (1 : ℂ)) (g := fun q : ℂ => q ^ (n + 1)) (differentiableOn_const _)
      (differentiableOn_id.pow _), T_const, T_pow (f := fun q : ℂ => q) differentiableOn_id, T_id, map_one]

lemma tlu_fG : TendstoLocallyUniformlyOn (fun N q => ∑ n ∈ Finset.range N, fGt n q) (fun q => ∑' n, fGt n q)
    atTop (ball 0 1) := by
  refine tlu_tsum_nat fun r h0 h1 => ⟨fun n => r ^ n / (1 - r), ?_, fun n q hq => ?_⟩
  · exact (summable_geometric_of_lt_one h0 h1).div_const _
  · unfold fGt
    rw [norm_mul, norm_mul, norm_inv, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    have hq1 : ‖q‖ ^ (n + 1) ≤ r := by
      calc ‖q‖ ^ (n + 1) ≤ ‖q‖ := pow_le_of_le_one (norm_nonneg _) (hq.trans h1.le) (by omega)
        _ ≤ r := hq
    have hden : 1 - r ≤ ‖1 + q ^ (n + 1)‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-(q ^ (n + 1)))
      rw [norm_one, norm_neg, norm_pow, sub_neg_eq_add] at this
      linarith
    have hr : 0 < 1 - r := by linarith
    have he : ‖q‖ ^ eN n ≤ r ^ n := by
      calc ‖q‖ ^ eN n ≤ ‖q‖ ^ n := pow_le_pow_of_le_one (norm_nonneg _) (hq.trans h1.le)
            (by have := eN_ge n; omega)
        _ ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg _) hq n
    show _ ≤ r ^ n / (1 - r)
    rw [div_eq_mul_inv]
    gcongr

lemma αser_neg_one {r : ℕ} (hr : r ≠ 0) :
    RankProof.αser (-1) r = C (4 * (-1 : ℂ) ^ r) * X ^ ((r + 1).choose 2) * (1 + X ^ r)⁻¹ := by
  unfold RankProof.αser
  rw [if_neg hr]
  have hu : (1 + X ^ r : PowerSeries ℂ) ≠ 0 := fun h => by
    have := congrArg (PowerSeries.constantCoeff) h; simp [zero_pow hr] at this
  have hc : PowerSeries.constantCoeff (1 + X ^ r : PowerSeries ℂ) ≠ 0 := by simp [zero_pow hr]
  have e1 : ((1 - C (-1 : ℂ) * X ^ r) * (1 - C (-1 : ℂ)⁻¹ * X ^ r) : PowerSeries ℂ) = (1 + X ^ r) * (1 + X ^ r) := by
    simp only [inv_neg, inv_one, map_neg, map_one]; ring
  rw [e1, inverse_eq_inv _ (by simp [zero_pow hr]), PowerSeries.mul_inv_rev]
  have hinv : (1 + X ^ r : PowerSeries ℂ) * (1 + X ^ r)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hc
  rw [show C ((-1 : ℂ) ^ r * ((1 - -1) * (1 - (-1)⁻¹))) = C (4 * (-1 : ℂ) ^ r) by congr 1; norm_num; ring]
  calc C (4 * (-1 : ℂ) ^ r) * X ^ ((r + 1).choose 2) * (1 + X ^ r) * ((1 + X ^ r)⁻¹ * (1 + X ^ r)⁻¹)
      = C (4 * (-1 : ℂ) ^ r) * X ^ ((r + 1).choose 2) * ((1 + X ^ r) * (1 + X ^ r)⁻¹) * (1 + X ^ r)⁻¹ := by ring
    _ = _ := by rw [hinv, mul_one]

theorem fG_T : Hol fG ∧ T fG = RankProof.ALser (-1) := by
  have hT := tlu_fG
  have hFh : ∀ N, Hol (fun q => ∑ n ∈ Finset.range N, fGt n q) := fun N =>
    DifferentiableOn.fun_sum fun n _ => fGt_hol n
  have hS : Hol (fun q => ∑' n, fGt n q) := Hol.of_tlu hT hFh
  have hG : Hol fG := (differentiableOn_const _).add ((differentiableOn_const _).mul hS)
  refine ⟨hG, ?_⟩
  have hTS : T (fun q => ∑' n, fGt n q) = PowerSeries.mk fun c =>
      coeff c (∑ n ∈ Finset.range c, T (fGt n)) := by
    refine T_of_tlu hT hFh fun c => ?_
    filter_upwards [eventually_ge_atTop c] with N hN
    rw [T_sum _ _ fun n => fGt_hol n, coeff_mk]
    rw [← Finset.sum_range_add_sum_Ico _ hN, map_add, add_eq_left, map_sum]
    refine Finset.sum_eq_zero fun n hn => ?_
    have : c < eN n := by have := (Finset.mem_Ico.mp hn).1; have := eN_ge n; omega
    rw [T_fGt, mul_comm (C _), mul_assoc, coeff_X_pow_mul', if_neg (by omega)]
  unfold fG
  rw [T_add (f := fun _ => (1 : ℂ)) (g := fun q => 4 * ∑' n, fGt n q) (differentiableOn_const _)
      ((differentiableOn_const _).mul hS),
    T_mul (f := fun _ => (4 : ℂ)) (g := fun q => ∑' n, fGt n q) (differentiableOn_const _) hS, T_const, T_const, hTS]
  ext c
  rw [RankProof.ALser, coeff_mk, map_add, coeff_C_mul, coeff_mk, Finset.sum_range_succ', map_add, map_sum,
    map_sum, Finset.mul_sum]
  simp only [show RankProof.αser (-1) 0 = 1 by simp [RankProof.αser], ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [αser_neg_one (by omega), T_fGt, eN_eq, pow_add]
  rw [← coeff_C_mul]
  congr 1
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

lemma qfacInf_eq : MockTheta5.JTP.qfacInf = RankProof.Pinf 1 1 := by
  ext k
  simp [MockTheta5.JTP.qfacInf, RankProof.Pinf, RankProof.Pfin, MockTheta5.Bailey.qfac, add_comm]

lemma Pq_T : T HardyRamanujan.Pq = MockTheta5.JTP.ψC (RankProof.Pinf 1 1) := by
  ext n
  rw [coeff_T, (Realize.realizes_Pinf 1 1 le_rfl le_rfl).iteratedDeriv_zero n]
  have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [show MockTheta5.JTP.ψC = PowerSeries.map (Int.castRingHom ℂ) from rfl, PowerSeries.coeff_map]
  field_simp; simp

/-- `T fA = Dser(−1)(−1)`. -/
lemma fA_T_D : T MockTheta3.Radial.fA = CrankProof.Dser (-1) (-1) := by
  rw [MockTheta3.Radial.fA_T.2]
  ext n
  rw [CrankProof.Dser, coeff_mk, show MockTheta5.JTP.ψC = PowerSeries.map (Int.castRingHom ℂ) from rfl,
    PowerSeries.coeff_map, coeff_mk, ← PowerSeries.coeff_map, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hU : IsUnit ((MockTheta3.Radial.P1 k : Polynomial ℤ) : PowerSeries ℤ) := by
    rw [MockTheta3.Radial.coe_P1]; exact MockTheta3.Watson3.isUnit_NP le_rfl 1 k
  simp only [map_mul, map_pow]
  rw [CrankProof.map_inverse _ hU, MockTheta3.Radial.coe_P1]
  have hN : PowerSeries.map (Int.castRingHom ℂ) (MockTheta3.Watson3.NP 1 1 k) = CrankProof.poch (-1) 1 k := by
    simp [MockTheta3.Watson3.NP, Watson.FP, CrankProof.poch, map_prod, sub_eq_add_neg, add_comm]
  rw [hN]
  simp; ring

/-- **the Appell–Lerch form of `f` on the disc**: `f(q)(q;q)_∞ = 1 + 4Σ_{m≥1}(−1)^m q^{m(3m+1)/2}/(1+q^m)`. -/
theorem f_AL {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) : MockTheta3.Radial.fA q * HardyRamanujan.Pq q = fG q := by
  have hP : Hol HardyRamanujan.Pq := (Realize.realizes_Pinf 1 1 le_rfl le_rfl).diff
  have hf := MockTheta3.Radial.fA_T.1
  refine eq_of_T (f := fun q => MockTheta3.Radial.fA q * HardyRamanujan.Pq q) (hf.mul hP) fG_T.1 ?_ hq
  have hr := RankProof.rank_AL (z := -1) (by norm_num)
  rw [inv_neg, inv_one] at hr
  rw [T_mul hf hP, fA_T_D, Pq_T, fG_T.2, hr, ← qfacInf_eq]
  have hu : IsUnit MockTheta5.JTP.qfacInf := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp [MockTheta5.JTP.qfacInf, MockTheta5.Bailey.qfac]
  rw [CrankProof.map_inverse _ hu, mul_comm, ← mul_assoc, Ring.mul_inverse_cancel _ (hu.map _), one_mul]

end

end MockCusp
