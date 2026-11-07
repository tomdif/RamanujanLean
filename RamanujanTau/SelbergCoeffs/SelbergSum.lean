/-
# Selberg's lemma `Σ_{n≤N} α(n)²/n ≪ (log N)^{1/4}` (under Deligne)

The Rankin trick with `σ = 1 + 1/log N` and finite Euler products:

    Σ_{n≤N} α(n)²/n ≤ e · Σ_{n≤N} α(n)² n^{−σ} ≤ e · ∏_{p≤N} A_p(σ),
    A_p(σ) = Σ_k α(p^k)² p^{−kσ} ≤ (1 + u_p/4)(1 + 2/p²),   u_p = λ(p)² p^{−σ} ≤ 4/p,
    (1 + u/4)⁴ ≤ (1 + u)(1 + 3u²/8),   1 + u_p ≤ R_p(σ) = Σ_k λ(p^k)² p^{−kσ},
    ∏_{p≤N} R_p(σ) ≤ R(σ) = Σ_n λ(n)² n^{−σ} ≤ Kσ/(σ−1)        (Rankin: Σ_{n≤x} λ(n)² ≤ Kx),

so `(∏ A_p)⁴ ≤ e^{14} R(σ) ≤ e^{14}K(log N + 1)`.  Inputs: `DeligneBound` (`|α(p^k)| ≤ 1`,
`λ(p)² ≤ 4`) and Rankin's unconditional linear bound `EdgeNonvanishing.rs_partial_le`.
The exponent `1/4 = |α(p)|²`-average `λ(p)²/4` is Selberg's.
-/
import RamanujanTau.SelbergCoeffs.Global

set_option autoImplicit false

namespace RamanujanTau.SelbergCoeffs

open Finset Filter Topology Asymptotics MeasureTheory
open RamanujanTau.EdgeNonvanishing (rsb rsB RS rs_partial_le rs_summable rsb_nonneg rsb_mul_coprime
  rsb_pow lam)

noncomputable section

/-! ## The real Rankin–Selberg series -/

lemma term_rsB_real (σ : ℝ) (n : ℕ) :
    LSeries.term rsB σ n = ((rsb n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [EdgeNonvanishing.rsb_zero]
  · rw [LSeries.term_of_ne_zero hn, rsB, Real.rpow_neg (Nat.cast_nonneg _), ← div_eq_mul_inv]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast; rfl

lemma summable_rs_real {σ : ℝ} (hσ : 1 < σ) : Summable fun n : ℕ => rsb n * (n : ℝ) ^ (-σ) := by
  have h := rs_summable (s := (σ : ℂ)) (by simpa using hσ)
  rw [LSeriesSummable, funext (term_rsB_real σ)] at h
  exact Complex.summable_ofReal.mp h

/-- **`R(σ) ≪ σ/(σ−1)`** for real `σ > 1` (Abel summation of Rankin's `Σ_{n≤x} λ(n)² ≤ Kx`). -/
lemma rs_real_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, 1 < σ →
    ∑' n : ℕ, rsb n * (n : ℝ) ^ (-σ) ≤ K * σ / (σ - 1) := by
  obtain ⟨C, hC0, hC⟩ := rs_partial_le
  refine ⟨C, hC0, fun σ hσ => ?_⟩
  have hS : LSeriesSummable rsB σ := rs_summable (by simpa using hσ)
  have hpart : ∀ N : ℕ, ‖∑ k ∈ Icc 1 N, rsB k‖ ≤ C * (N : ℝ) ^ (1 : ℝ) := by
    intro N
    have : ∑ k ∈ Icc 1 N, rsB k = ((∑ n ∈ Icc 1 N, rsb n : ℝ) : ℂ) := by simp [rsB]
    rw [this, Complex.norm_real, Real.norm_of_nonneg (sum_nonneg fun n _ => rsb_nonneg n),
      Real.rpow_one]
    exact hC N
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, rsB k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpart n
  have hval : LSeries rsB σ = ((∑' n : ℕ, rsb n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    exact tsum_congr fun n => term_rsB_real σ n
  have hσre : (1 : ℝ) < (σ : ℂ).re := by simpa using hσ
  have key := LSeries_eq_mul_integral rsB zero_le_one hσre hS hO
  set a : ℝ := 1 - σ - 1
  have ha : a < -1 := by simp only [a]; linarith
  have hint : IntegrableOn (fun t : ℝ => C * t ^ a) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt ha zero_lt_one).const_mul C
  have hbound : ‖∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, rsB k) * (t : ℂ) ^ (-((σ : ℂ) + 1))‖ ≤
      ∫ t in Set.Ioi (1 : ℝ), C * t ^ a := by
    refine norm_integral_le_of_norm_le hint ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t (ht : 1 < t) => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
    have h1 : ‖∑ k ∈ Icc 1 ⌊t⌋₊, rsB k‖ ≤ C * t ^ (1 : ℝ) :=
      (hpart _).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hfl (by norm_num)) hC0)
    have h2 : t ^ a = t ^ (1 : ℝ) * t ^ (-((σ : ℂ) + 1)).re := by
      rw [← Real.rpow_add ht0]; congr 1; simp [a]
    rw [h2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hval2 : ∫ t in Set.Ioi (1 : ℝ), C * t ^ a = C / (σ - 1) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt ha zero_lt_one, Real.one_rpow]
    have : a + 1 = -(σ - 1) := by simp only [a]; ring
    rw [this, neg_div_neg_eq, one_div, div_eq_mul_inv]
  rw [hval2] at hbound
  have hnorm : ‖LSeries rsB σ‖ ≤ σ * (C / (σ - 1)) := by
    rw [key, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left hbound (by linarith)
  rw [hval, Complex.norm_real, Real.norm_eq_abs] at hnorm
  calc ∑' n : ℕ, rsb n * (n : ℝ) ^ (-σ) ≤ |∑' n : ℕ, rsb n * (n : ℝ) ^ (-σ)| := le_abs_self _
    _ ≤ σ * (C / (σ - 1)) := hnorm
    _ = C * σ / (σ - 1) := by ring

/-! ## Finite Euler products -/

lemma rpow_neg_mul_coprime (σ : ℝ) (m n : ℕ) :
    ((m * n : ℕ) : ℝ) ^ (-σ) = (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) := by
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

/-- `f(n) = λ(n)² n^{−σ}`. -/
def fR (σ : ℝ) (n : ℕ) : ℝ := rsb n * (n : ℝ) ^ (-σ)
/-- `g(n) = α(n)² n^{−σ}`. -/
def gA (σ : ℝ) (n : ℕ) : ℝ := alpha n ^ 2 * (n : ℝ) ^ (-σ)

lemma rsb_one : rsb 1 = 1 := by simp [rsb, tau_one]

lemma fR_one (σ : ℝ) : fR σ 1 = 1 := by simp [fR, rsb_one]
lemma gA_one (σ : ℝ) : gA σ 1 = 1 := by simp [gA, alpha_one]

lemma fR_mul (σ : ℝ) {m n : ℕ} (h : m.Coprime n) : fR σ (m * n) = fR σ m * fR σ n := by
  simp only [fR, rsb_mul_coprime h, rpow_neg_mul_coprime]; ring

lemma gA_mul (σ : ℝ) {m n : ℕ} (h : m.Coprime n) : gA σ (m * n) = gA σ m * gA σ n := by
  simp only [gA, alpha_mult.map_mul_of_coprime h, rpow_neg_mul_coprime]; ring

lemma fR_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ fR σ n := mul_nonneg (rsb_nonneg n) (by positivity)
lemma gA_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ gA σ n := mul_nonneg (sq_nonneg _) (by positivity)

lemma summable_gA [DeligneBound] {σ : ℝ} (hσ : 1 < σ) : Summable (gA σ) := by
  refine Summable.of_nonneg_of_le (gA_nonneg σ) (fun n => ?_)
    (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))
  have h1 : alpha n ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (abs_alpha_le_one n)
  unfold gA
  exact mul_le_of_le_one_left (by positivity) h1

lemma prod_fR_le {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    ∏ p ∈ N.primesBelow, ∑' k : ℕ, fR σ (p ^ k) ≤ ∑' n : ℕ, fR σ n := by
  have hs : Summable (fR σ) := summable_rs_real hσ
  rw [EulerProduct.prod_primesBelow_tsum_eq_tsum_smoothNumbers (fR_one σ) (fun h => fR_mul σ h)
    (by simpa [Real.norm_of_nonneg (fR_nonneg σ _)] using hs)]
  exact tsum_comp_le_tsum_of_inj hs (fR_nonneg σ) Subtype.val_injective

lemma sum_gA_le_prod [DeligneBound] {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, gA σ n ≤ ∏ p ∈ (N + 1).primesBelow, ∑' k : ℕ, gA σ (p ^ k) := by
  have hs : Summable (gA σ) := summable_gA hσ
  rw [EulerProduct.prod_primesBelow_tsum_eq_tsum_smoothNumbers (gA_one σ) (fun h => gA_mul σ h)
    (by simpa [Real.norm_of_nonneg (gA_nonneg σ _)] using hs)]
  have hmem : ∀ n ∈ Icc 1 N, n ∈ (N + 1).smoothNumbers := fun n hn => by
    rw [mem_Icc] at hn
    exact Nat.mem_smoothNumbers_of_lt (by omega) (by omega)
  rw [← Finset.sum_subtype_of_mem (gA σ) hmem]
  exact (hs.subtype _).sum_le_tsum _ (fun _ _ => gA_nonneg σ _)

/-! ## Local estimates -/

lemma ppow_rpow_le {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 1 ≤ σ) (k : ℕ) :
    ((p ^ k : ℕ) : ℝ) ^ (-σ) ≤ (1 / (p : ℝ)) ^ k := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hpk : (1 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ hp.pos
  calc ((p ^ k : ℕ) : ℝ) ^ (-σ) ≤ ((p ^ k : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hpk (by linarith)
    _ = (1 / (p : ℝ)) ^ k := by rw [Real.rpow_neg_one]; push_cast; rw [one_div_pow, one_div]

/-- `u_p = λ(p)² p^{−σ}`. -/
def uP (σ : ℝ) (p : ℕ) : ℝ := lam p ^ 2 * (p : ℝ) ^ (-σ)

lemma uP_nonneg (σ : ℝ) (p : ℕ) : 0 ≤ uP σ p := mul_nonneg (sq_nonneg _) (by positivity)

lemma uP_le [DeligneBound] {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 1 ≤ σ) : uP σ p ≤ 4 / p := by
  have h1 := ppow_rpow_le hp hσ 1
  rw [pow_one, pow_one] at h1
  have hl := lam_sq_le_four hp
  unfold uP
  calc lam p ^ 2 * (p : ℝ) ^ (-σ) ≤ 4 * (1 / (p : ℝ)) :=
        mul_le_mul hl h1 (by positivity) (by norm_num)
    _ = 4 / p := by ring

lemma one_add_uP_le {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 1 < σ) :
    1 + uP σ p ≤ ∑' k : ℕ, fR σ (p ^ k) := by
  have hs : Summable fun k : ℕ => fR σ (p ^ k) :=
    (summable_rs_real hσ).comp_injective (Nat.pow_right_injective hp.two_le)
  have h := hs.sum_le_tsum (range 2) (fun k _ => fR_nonneg σ _)
  have e : ∑ k ∈ range 2, fR σ (p ^ k) = 1 + uP σ p := by
    simp only [sum_range_succ, range_zero, sum_empty, zero_add, pow_zero, fR_one, pow_one]
    have hr := rsb_pow hp 1
    rw [pow_one] at hr
    simp only [fR, uP, hr]
    rfl
  linarith

lemma gA_ppow_le [DeligneBound] {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 1 ≤ σ) (k : ℕ) :
    gA σ (p ^ k) ≤ (1 / (p : ℝ)) ^ k := by
  have h1 : alpha (p ^ k) ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (abs_alpha_le_one _)
  unfold gA
  calc alpha (p ^ k) ^ 2 * ((p ^ k : ℕ) : ℝ) ^ (-σ) ≤ 1 * (1 / (p : ℝ)) ^ k :=
        mul_le_mul h1 (ppow_rpow_le hp hσ k) (by positivity) zero_le_one
    _ = _ := one_mul _

lemma tsum_gA_le [DeligneBound] {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 1 < σ) :
    ∑' k : ℕ, gA σ (p ^ k) ≤ 1 + uP σ p / 4 + 2 / (p : ℝ) ^ 2 := by
  have hs : Summable fun k : ℕ => gA σ (p ^ k) :=
    (summable_gA hσ).comp_injective (Nat.pow_right_injective hp.two_le)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hq1 : 1 / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hgeo : Summable fun k : ℕ => (1 / (p : ℝ)) ^ (k + 2) :=
    (summable_nat_add_iff 2).mpr (summable_geometric_of_lt_one hq0 (by linarith))
  rw [← hs.sum_add_tsum_nat_add 2]
  have e : ∑ k ∈ range 2, gA σ (p ^ k) = 1 + uP σ p / 4 := by
    simp only [sum_range_succ, range_zero, sum_empty, zero_add, pow_zero, gA_one, pow_one]
    simp only [gA, uP, alpha_prime hp]
    ring
  rw [e]
  have htail : ∑' k : ℕ, gA σ (p ^ (k + 2)) ≤ ∑' k : ℕ, (1 / (p : ℝ)) ^ (k + 2) :=
    ((summable_nat_add_iff 2).mpr hs).tsum_le_tsum (fun k => gA_ppow_le hp hσ.le _) hgeo
  have hgv : ∑' k : ℕ, (1 / (p : ℝ)) ^ (k + 2) = (1 / (p : ℝ)) ^ 2 * (1 - 1 / (p : ℝ))⁻¹ := by
    simp_rw [pow_add, mul_comm _ ((1 / (p : ℝ)) ^ 2)]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 (by linarith)]
  have hb : (1 / (p : ℝ)) ^ 2 * (1 - 1 / (p : ℝ))⁻¹ ≤ 2 / (p : ℝ) ^ 2 := by
    have h12 : (1 - 1 / (p : ℝ))⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc (1 / (p : ℝ)) ^ 2 * (1 - 1 / (p : ℝ))⁻¹ ≤ (1 / (p : ℝ)) ^ 2 * 2 :=
          mul_le_mul_of_nonneg_left h12 (by positivity)
      _ = 2 / (p : ℝ) ^ 2 := by ring
  linarith

/-- `(1 + u/4)⁴ ≤ (1 + u)(1 + 3u²/8)` for `0 ≤ u ≤ 80`. -/
lemma quartic_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 80) :
    (1 + u / 4) ^ 4 ≤ (1 + u) * (1 + 3 / 8 * u ^ 2) := by
  nlinarith [mul_nonneg (mul_nonneg h0 h0) (mul_nonneg h0 (sub_nonneg.mpr h1)),
    mul_nonneg (mul_nonneg h0 h0) h0]

lemma local_quartic [DeligneBound] {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 1 < σ) :
    (∑' k : ℕ, gA σ (p ^ k)) ^ 4 ≤ (∑' k : ℕ, fR σ (p ^ k)) * Real.exp (14 / (p : ℝ) ^ 2) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hu0 := uP_nonneg σ p
  have hu1 := uP_le hp hσ.le
  have hu80 : uP σ p ≤ 80 := hu1.trans (by rw [div_le_iff₀ (by linarith)]; linarith)
  have hA0 : 0 ≤ ∑' k : ℕ, gA σ (p ^ k) := tsum_nonneg fun _ => gA_nonneg σ _
  have hA := tsum_gA_le hp hσ
  have hR := one_add_uP_le hp hσ
  set u := uP σ p
  set q : ℝ := 1 / (p : ℝ) ^ 2
  have hq : 0 ≤ q := by positivity
  have hA' : ∑' k : ℕ, gA σ (p ^ k) ≤ (1 + u / 4) * (1 + 2 * q) := by
    have h2q : 2 / (p : ℝ) ^ 2 = 2 * q := by simp only [q]; ring
    have : 1 + u / 4 + 2 / (p : ℝ) ^ 2 ≤ (1 + u / 4) * (1 + 2 * q) := by
      rw [h2q]; nlinarith [mul_nonneg hu0 hq]
    linarith
  have hu2 : u ^ 2 ≤ 16 * q := by
    have : u ^ 2 ≤ (4 / p) ^ 2 := pow_le_pow_left₀ hu0 hu1 2
    calc u ^ 2 ≤ (4 / p) ^ 2 := this
      _ = 16 * q := by simp only [q]; ring
  have e1 : 1 + 3 / 8 * u ^ 2 ≤ Real.exp (6 * q) := by
    have := Real.add_one_le_exp (6 * q); nlinarith
  have e2 : (1 + 2 * q) ^ 4 ≤ Real.exp (8 * q) := by
    have h := Real.add_one_le_exp (2 * q)
    have h' : (1 + 2 * q) ^ 4 ≤ Real.exp (2 * q) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    rw [← Real.exp_nat_mul] at h'; convert h' using 2; push_cast; ring
  have hexp : Real.exp (6 * q) * Real.exp (8 * q) = Real.exp (14 / (p : ℝ) ^ 2) := by
    rw [← Real.exp_add]; congr 1; simp only [q]; ring
  calc (∑' k : ℕ, gA σ (p ^ k)) ^ 4 ≤ ((1 + u / 4) * (1 + 2 * q)) ^ 4 :=
        pow_le_pow_left₀ hA0 hA' 4
    _ = (1 + u / 4) ^ 4 * (1 + 2 * q) ^ 4 := by ring
    _ ≤ ((1 + u) * (1 + 3 / 8 * u ^ 2)) * Real.exp (8 * q) :=
        mul_le_mul (quartic_le hu0 hu80) e2 (by positivity) (by positivity)
    _ ≤ ((∑' k : ℕ, fR σ (p ^ k)) * Real.exp (6 * q)) * Real.exp (8 * q) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hR e1 (by positivity)
          (tsum_nonneg fun _ => fR_nonneg σ _)) (by positivity)
    _ = (∑' k : ℕ, fR σ (p ^ k)) * Real.exp (14 / (p : ℝ) ^ 2) := by rw [mul_assoc, hexp]

lemma sum_primesBelow_inv_sq_le (N : ℕ) : ∑ p ∈ N.primesBelow, 1 / (p : ℝ) ^ 2 ≤ 1 := by
  have hsub : N.primesBelow ⊆ Ioo 1 N := fun p hp => by
    rw [Nat.mem_primesBelow] at hp
    exact mem_Ioo.mpr ⟨hp.2.one_lt, hp.1⟩
  calc ∑ p ∈ N.primesBelow, 1 / (p : ℝ) ^ 2 ≤ ∑ i ∈ Ioo 1 N, ((i : ℝ) ^ 2)⁻¹ := by
        simp_rw [one_div]
        exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ 2 / ((1 : ℕ) + 1 : ℝ) := sum_Ioo_inv_sq_le 1 N
    _ = 1 := by norm_num

/-- `(∏_{p<N} A_p(σ))⁴ ≤ e^{14} R(σ)`. -/
lemma prod_quartic [DeligneBound] {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    (∏ p ∈ N.primesBelow, ∑' k : ℕ, gA σ (p ^ k)) ^ 4 ≤
      Real.exp 14 * ∑' n : ℕ, fR σ n := by
  rw [← Finset.prod_pow]
  have hloc : ∀ p ∈ N.primesBelow, (∑' k : ℕ, gA σ (p ^ k)) ^ 4 ≤
      (∑' k : ℕ, fR σ (p ^ k)) * Real.exp (14 / (p : ℝ) ^ 2) := fun p hp =>
    local_quartic (Nat.prime_of_mem_primesBelow hp) hσ
  calc ∏ p ∈ N.primesBelow, (∑' k : ℕ, gA σ (p ^ k)) ^ 4
      ≤ ∏ p ∈ N.primesBelow, ((∑' k : ℕ, fR σ (p ^ k)) * Real.exp (14 / (p : ℝ) ^ 2)) :=
        prod_le_prod (fun _ _ => by positivity) hloc
    _ = (∏ p ∈ N.primesBelow, ∑' k : ℕ, fR σ (p ^ k)) *
          Real.exp (∑ p ∈ N.primesBelow, 14 / (p : ℝ) ^ 2) := by
        rw [prod_mul_distrib, Real.exp_sum]
    _ ≤ (∑' n : ℕ, fR σ n) * Real.exp 14 := by
        apply mul_le_mul (prod_fR_le hσ N) _ (by positivity)
          (tsum_nonneg fun n => fR_nonneg σ n)
        apply Real.exp_le_exp.mpr
        have := sum_primesBelow_inv_sq_le N
        calc ∑ p ∈ N.primesBelow, 14 / (p : ℝ) ^ 2 = 14 * ∑ p ∈ N.primesBelow, 1 / (p : ℝ) ^ 2 := by
              rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
          _ ≤ 14 := by linarith
    _ = Real.exp 14 * ∑' n : ℕ, fR σ n := mul_comm _ _

/-- **Selberg's lemma for `L(Δ,s)^{−1/2}`** (under Deligne):
`Σ_{n≤N} α(n)²/n ≤ C (log N + 1)^{1/4}` for all `N ≥ 2`. -/
theorem sum_alpha_sq_div_le [DeligneBound] : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    ∑ n ∈ Icc 1 N, alpha n ^ 2 / n ≤ C * (Real.log N + 1) ^ (1 / 4 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := rs_real_le
  refine ⟨Real.exp 1 * (Real.exp 14 * K) ^ (1 / 4 : ℝ), by positivity, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < Real.log N := Real.log_pos hN1
  set σ : ℝ := 1 + 1 / Real.log N with hσdef
  have hσ : 1 < σ := by simp only [σ]; linarith [one_div_pos.mpr hL]
  -- Rankin trick
  have hterm : ∀ n ∈ Icc 1 N, alpha n ^ 2 / n ≤ Real.exp 1 * gA σ n := by
    intro n hn
    rw [mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.2
    have hn0 : (0 : ℝ) < n := by linarith
    have hpow : (n : ℝ) ^ (1 / Real.log N) ≤ Real.exp 1 := by
      calc (n : ℝ) ^ (1 / Real.log N) ≤ (N : ℝ) ^ (1 / Real.log N) :=
            Real.rpow_le_rpow hn0.le hnN (by positivity)
        _ = Real.exp 1 := by
            rw [Real.rpow_def_of_pos (by linarith), mul_one_div, div_self hL.ne']
    have hsplit : alpha n ^ 2 / n = gA σ n * (n : ℝ) ^ (1 / Real.log N) := by
      unfold gA
      rw [mul_assoc, ← Real.rpow_add hn0, hσdef]
      rw [show -(1 + 1 / Real.log N) + 1 / Real.log N = (-1 : ℝ) by ring, Real.rpow_neg_one,
        div_eq_mul_inv]
    rw [hsplit, mul_comm (Real.exp 1)]
    exact mul_le_mul_of_nonneg_left hpow (gA_nonneg σ n)
  have h1 : ∑ n ∈ Icc 1 N, alpha n ^ 2 / n ≤ Real.exp 1 * ∑ n ∈ Icc 1 N, gA σ n := by
    rw [mul_sum]; exact sum_le_sum hterm
  have h2 := sum_gA_le_prod hσ N
  set P := ∏ p ∈ (N + 1).primesBelow, ∑' k : ℕ, gA σ (p ^ k)
  have hP0 : 0 ≤ P := prod_nonneg fun _ _ => tsum_nonneg fun _ => gA_nonneg σ _
  have h3 := prod_quartic hσ (N + 1)
  have hR := hK σ hσ
  have hσ' : K * σ / (σ - 1) = K * (Real.log N + 1) := by
    simp only [σ]; field_simp; ring
  rw [hσ'] at hR
  have h4 : P ^ 4 ≤ Real.exp 14 * K * (Real.log N + 1) := by
    calc P ^ 4 ≤ Real.exp 14 * ∑' n : ℕ, fR σ n := h3
      _ ≤ Real.exp 14 * (K * (Real.log N + 1)) :=
          mul_le_mul_of_nonneg_left hR (by positivity)
      _ = _ := by ring
  have h5 : P ≤ (Real.exp 14 * K * (Real.log N + 1)) ^ (1 / 4 : ℝ) := by
    have := Real.rpow_le_rpow (by positivity) h4 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hP0, show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num,
      Real.rpow_one] at this
  rw [Real.mul_rpow (by positivity) (by positivity)] at h5
  calc ∑ n ∈ Icc 1 N, alpha n ^ 2 / n ≤ Real.exp 1 * ∑ n ∈ Icc 1 N, gA σ n := h1
    _ ≤ Real.exp 1 * P := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ Real.exp 1 * ((Real.exp 14 * K) ^ (1 / 4 : ℝ) * (Real.log N + 1) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = _ := by ring

end

end RamanujanTau.SelbergCoeffs
