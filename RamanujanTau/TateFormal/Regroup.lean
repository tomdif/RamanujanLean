import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.Complex.Basic

/-!
# Regrouping `Σ_{k ≥ 1} Σ_{d ≥ 1} d^j wᵈ q^{kd}` by `N = kd`
-/

set_option autoImplicit false

noncomputable section

namespace TateFormal

open Complex

variable (j : ℕ) {w q : ℂ} {r : ℝ}

lemma pow_bound (hq : ‖q‖ ≤ r) (hwq : ‖w‖ * ‖q‖ ≤ r) {d k : ℕ} (hk : 1 ≤ k) :
    ‖w‖ ^ d * ‖q‖ ^ (k * d) ≤ r ^ (k * d) := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hq
  rcases le_or_gt ‖w‖ 1 with hw | hw
  · calc ‖w‖ ^ d * ‖q‖ ^ (k * d) ≤ 1 * r ^ (k * d) := by
          gcongr
          · exact pow_le_one₀ (norm_nonneg _) hw
    _ = r ^ (k * d) := one_mul _
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    calc ‖w‖ ^ d * ‖q‖ ^ ((k' + 1) * d) = (‖w‖ * ‖q‖) ^ d * ‖q‖ ^ (k' * d) := by ring
      _ ≤ r ^ d * r ^ (k' * d) := by gcongr
      _ = r ^ ((k' + 1) * d) := by ring

/-- the doubly indexed family `F(k, d) = d^j (w q^k)^d`. -/
def F2 (w q : ℂ) (c : ℕ+ × ℕ+) : ℂ := (c.2 : ℂ) ^ j * (w * q ^ (c.1 : ℕ)) ^ (c.2 : ℕ)

lemma summable_norm_F2 (hr : r < 1) (hq : ‖q‖ ≤ r) (hwq : ‖w‖ * ‖q‖ ≤ r) :
    Summable fun c => ‖F2 j w q c‖ := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hq
  have h := summable_prod_mul_pow (𝕜 := ℝ) j (r := r) (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun c => ?_) h
  simp only [F2, norm_mul, norm_pow, Complex.norm_natCast, mul_pow, ← pow_mul]
  gcongr
  convert pow_bound hq hwq (d := (c.2 : ℕ)) c.1.pos using 2

lemma tsum_pnat_eq (hj : 1 ≤ j) {v : ℂ} (hv : ‖v‖ < 1) :
    ∑' d : ℕ+, (d : ℂ) ^ j * v ^ (d : ℕ) = ∑' d : ℕ, (d : ℂ) ^ j * v ^ d := by
  rw [← tsum_zero_pnat_eq_tsum_nat (summable_pow_mul_geometric_of_norm_lt_one j hv)]
  simp [zero_pow (by omega : j ≠ 0)]

lemma hasSum_k (hj : 1 ≤ j) (hr : r < 1) (hq : ‖q‖ ≤ r) (hwq : ‖w‖ * ‖q‖ ≤ r) :
    HasSum (fun k : ℕ => ∑' d : ℕ, (d : ℂ) ^ j * (w * q ^ (k + 1)) ^ d)
      (∑' k : ℕ, ∑' d : ℕ, (d : ℂ) ^ j * (w * q ^ (k + 1)) ^ d) := by
  have hF := (summable_norm_F2 j hr hq hwq).of_norm
  have hk : HasSum (fun k : ℕ+ => ∑' d : ℕ+, F2 j w q (k, d)) (∑' c, F2 j w q c) :=
    hF.hasSum.prod_fiberwise fun k => (hF.prod_factor k).hasSum
  have h2 := (Equiv.pnatEquivNat.symm.hasSum_iff).mpr hk
  refine (h2.congr_fun fun k => ?_).summable.hasSum
  have h1 : ‖w * q ^ (k + 1)‖ < 1 := by
    have := pow_bound hq hwq (d := 1) (k := k + 1) (by omega)
    rw [norm_mul, norm_pow]
    calc ‖w‖ * ‖q‖ ^ (k + 1) = ‖w‖ ^ 1 * ‖q‖ ^ ((k + 1) * 1) := by ring
      _ ≤ r ^ ((k + 1) * 1) := this
      _ < 1 := pow_lt_one₀ ((norm_nonneg _).trans hq) hr (by simp)
  rw [← tsum_pnat_eq j hj h1]
  simp [F2]

/-- **regrouping**: `Σ_{N ≥ 0} (Σ_{d ∣ N} d^j wᵈ) qᴺ = Σ_{k ≥ 0} S_j(w q^{k+1})`. -/
theorem regroup (hj : 1 ≤ j) (hr : r < 1) (hq : ‖q‖ ≤ r) (hwq : ‖w‖ * ‖q‖ ≤ r) :
    HasSum (fun N : ℕ => (∑ d ∈ N.divisors, (d : ℂ) ^ j * w ^ d) * q ^ N)
      (∑' k : ℕ, ∑' d : ℕ, (d : ℂ) ^ j * (w * q ^ (k + 1)) ^ d) := by
  have hF := (summable_norm_F2 j hr hq hwq).of_norm
  -- the `k`-fibers
  have hk : HasSum (fun k : ℕ+ => ∑' d : ℕ+, F2 j w q (k, d)) (∑' c, F2 j w q c) :=
    hF.hasSum.prod_fiberwise fun k => (hF.prod_factor k).hasSum
  have hk' : ∀ k : ℕ+, ∑' d : ℕ+, F2 j w q (k, d) = ∑' d : ℕ, (d : ℂ) ^ j * (w * q ^ (k : ℕ)) ^ d := by
    intro k
    have h1 : ‖w * q ^ (k : ℕ)‖ < 1 := by
      have := pow_bound hq hwq (d := 1) k.pos
      rw [norm_mul, norm_pow]
      calc ‖w‖ * ‖q‖ ^ (k : ℕ) = ‖w‖ ^ 1 * ‖q‖ ^ ((k : ℕ) * 1) := by ring
        _ ≤ r ^ ((k : ℕ) * 1) := this
        _ < 1 := pow_lt_one₀ ((norm_nonneg _).trans hq) hr (by simp)
    rw [← tsum_pnat_eq j hj h1]
    rfl
  have hT : ∑' k : ℕ, ∑' d : ℕ, (d : ℂ) ^ j * (w * q ^ (k + 1)) ^ d = ∑' c, F2 j w q c := by
    rw [← hk.tsum_eq, ← Equiv.pnatEquivNat.symm.tsum_eq]
    congr 1; funext k
    rw [hk']; simp
  rw [hT]
  have hS := (sigmaAntidiagonalEquivProd.hasSum_iff (f := F2 j w q)).mpr hF.hasSum
  have hN := hS.sigma (fun N => hasSum_fintype _)
  have key : ∀ N : ℕ+, ∑ c, (F2 j w q ∘ sigmaAntidiagonalEquivProd) ⟨N, c⟩ =
      (∑ d ∈ (N : ℕ).divisors, (d : ℂ) ^ j * w ^ d) * q ^ (N : ℕ) := by
    intro N
    simp only [Function.comp_apply, sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk,
      divisorsAntidiagonalFactors, F2, PNat.mk_coe]
    rw [Finset.sum_coe_sort (N : ℕ).divisorsAntidiagonal
      (fun x : ℕ × ℕ => (x.2 : ℂ) ^ j * (w * q ^ x.1) ^ x.2),
      Nat.sum_divisorsAntidiagonal' (fun a b => (b : ℂ) ^ j * (w * q ^ a) ^ b), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hd := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hi)
    rw [mul_pow, ← pow_mul, hd]; ring
  simp only [key] at hN
  have h2 := (Equiv.pnatEquivNat.symm.hasSum_iff).mpr hN
  rw [← hasSum_nat_add_iff' 1]
  simpa using h2

lemma summable_coeff_norm (hr : r < 1) (hq : ‖q‖ ≤ r) (hwq : ‖w‖ * ‖q‖ ≤ r) :
    Summable (fun N : ℕ => ‖(∑ d ∈ N.divisors, (d : ℂ) ^ j * w ^ d) * q ^ N‖) := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hq
  have hs := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (j + 1)
    (r := r) (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun N => ?_) hs
  rw [norm_mul, norm_pow]
  calc ‖∑ d ∈ N.divisors, (d : ℂ) ^ j * w ^ d‖ * ‖q‖ ^ N
      ≤ (∑ d ∈ N.divisors, ‖(d : ℂ) ^ j * w ^ d‖) * ‖q‖ ^ N := by
        gcongr; exact norm_sum_le _ _
    _ = ∑ d ∈ N.divisors, (d : ℝ) ^ j * (‖w‖ ^ d * ‖q‖ ^ N) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast]; ring
    _ ≤ ∑ d ∈ N.divisors, (N : ℝ) ^ j * r ^ N := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hdN := Nat.divisor_le hd
        have hdv := Nat.dvd_of_mem_divisors hd
        have hk : 1 ≤ N / d := Nat.div_pos hdN (Nat.pos_of_mem_divisors hd)
        have hb := pow_bound hq hwq (d := d) hk
        rw [Nat.div_mul_cancel hdv] at hb
        gcongr
    _ ≤ (N : ℝ) ^ (j + 1) * r ^ N := by
        rw [Finset.sum_const, nsmul_eq_mul, pow_succ]
        have := Nat.card_divisors_le_self N
        have h1 : ((N.divisors.card : ℕ) : ℝ) ≤ N := by exact_mod_cast this
        nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) N) j, pow_nonneg hr0 N,
          mul_nonneg (pow_nonneg (Nat.cast_nonneg (α := ℝ) N) j) (pow_nonneg hr0 N)]

end TateFormal
