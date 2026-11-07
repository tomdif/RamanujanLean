/-
# The mean-square theorem in the half-plane of absolute convergence `σ > 13/2`

`mean_square_abs`: for `σ > 13/2`,

    (1/T) ∫₀ᵀ |L(Δ, σ+it)|² dt → ∑ τ(n)² n^{-2σ}.

Instance of `mean_sq_of_approx` with the partial sums `P_T = ∑_{n ≤ ⌊T⌋} τ(n) n^{-σ-it}`:
the approximation error is the tail `∑_{n > ⌊T⌋} |τ(n)| n^{-σ} → 0` (Rankin's absolute
convergence), and `H_N ∑ n·τ(n)² n^{-2σ} ≤ (1 + log T) RS(2σ−1) = o(T)`.
-/
import RamanujanTau.MeanSquare.Assembly
import RamanujanTau.MeanSquare.Sums

set_option autoImplicit false

namespace RamanujanTau.MeanSquare

open Complex Finset Filter Topology LSeries
open RamanujanTau.HeckeL

/-- `n^{-(σ+it)} = n^{-σ} e^{-it log n}`. -/
lemma natCast_cpow_inv {n : ℕ} (hn : n ≠ 0) (σ t : ℝ) :
    ((n : ℂ) ^ ((σ : ℂ) + t * I))⁻¹ = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * ex (-Real.log n) t := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [cpow_def_of_ne_zero hn0, ← Complex.natCast_log, Real.rpow_def_of_pos hnr, ex,
    ← Complex.exp_neg, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- The `n`-th term of `L(Δ, σ+it)`. -/
noncomputable def cterm (σ t : ℝ) (n : ℕ) : ℂ :=
  (tau n : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * ex (-Real.log n) t

lemma cterm_zero (σ t : ℝ) : cterm σ t 0 = 0 := by simp [cterm, tau_zero]

lemma norm_cterm (σ t : ℝ) (n : ℕ) : ‖cterm σ t n‖ = |(tau n : ℝ)| * (n : ℝ) ^ (-σ) := by
  rw [cterm, norm_mul, norm_mul, norm_ex, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  simp [Complex.norm_intCast]

lemma tauL_eq_tsum_cterm {σ : ℝ} (hσ : 13 / 2 < σ) (t : ℝ) :
    tauL ((σ : ℂ) + t * I) = ∑' n, cterm σ t n := by
  rw [RamanujanTau.HeckeConvex.tauL_eq_LSeries_of_gt (by simpa using hσ), LSeries]
  congr 1; funext n
  rw [LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [cterm_zero]
  · rw [if_neg hn, div_eq_mul_inv, natCast_cpow_inv hn, cterm, RamanujanTau.tauC]
    ring

/-- The coefficients `bₙ = τ(n) n^{-σ}`. -/
noncomputable def babs (σ : ℝ) (n : ℕ) : ℂ := (tau n : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)

lemma dpoly_babs (σ t : ℝ) (N : ℕ) :
    dpoly (babs σ) N t = ∑ n ∈ range (N + 1), cterm σ t n := by
  rw [dpoly, ← sum_Icc_eq_sum_range (cterm_zero σ t)]
  rfl

lemma norm_babs_sq (σ : ℝ) (n : ℕ) :
    ‖babs σ n‖ ^ 2 = ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) := by
  rw [babs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), mul_pow]
  have e : ((n : ℝ) ^ (-σ)) ^ 2 = (n : ℝ) ^ (-(2 * σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]; congr 1; push_cast; ring
  rw [e]
  simp only [Complex.norm_intCast, sq_abs]

/-- **Mean square of `L(Δ,s)` on `Re s = σ > 13/2`.** -/
theorem mean_square_abs {σ : ℝ} (hσ : 13 / 2 < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2) / T) atTop
      (𝓝 (RS (2 * σ))) := by
  have hcont : Continuous fun t : ℝ => tauL ((σ : ℂ) + t * I) :=
    tauLSeries_entire.continuous.comp (by fun_prop)
  set a : ℕ → ℝ := fun n => |(tau n : ℝ)| * (n : ℝ) ^ (-σ) with ha
  have hasum : Summable a := RamanujanTau.HeckeConvex.summable_abs_tau_div_rpow hσ |>.congr
    fun n => by
      rw [ha]; simp only
      rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  set N : ℝ → ℕ := fun T => ⌊T⌋₊ with hN
  have hNt : Tendsto N atTop atTop := tendsto_nat_floor_atTop
  set ρ : ℝ → ℝ := fun T => ∑' k, a (k + (N T + 1)) with hρ
  refine mean_sq_of_approx hcont (fun _ => babs σ) N ρ ?_ ?_ ?_ ?_
  · -- approximation by partial sums
    refine Eventually.of_forall fun T t _ => ?_
    have hcs : Summable (cterm σ t) :=
      Summable.of_norm (hasum.congr fun n => (norm_cterm σ t n).symm)
    have hsplit := hcs.sum_add_tsum_nat_add (N T + 1)
    have e : tauL ((σ : ℂ) + t * I) - dpoly (babs σ) (N T) t =
        ∑' i, cterm σ t (i + (N T + 1)) := by
      rw [tauL_eq_tsum_cterm hσ, dpoly_babs, ← hsplit]; ring
    rw [e]
    have h1 : Summable fun i => ‖cterm σ t (i + (N T + 1))‖ :=
      (summable_nat_add_iff (f := fun n => ‖cterm σ t n‖) (N T + 1)).2 hcs.norm
    have h2 : Summable fun i => a (i + (N T + 1)) :=
      (summable_nat_add_iff (f := a) (N T + 1)).2 hasum
    refine (norm_tsum_le_tsum_norm h1).trans (h1.tsum_le_tsum (fun k => ?_) h2)
    rw [norm_cterm]
  · -- tail → 0
    exact (tendsto_sum_nat_add a).comp ((tendsto_add_atTop_nat 1).comp hNt)
  · -- diagonal
    have hs := summable_tau_sq (β := 2 * σ) (by linarith)
    have h := (hs.hasSum.tendsto_sum_nat).comp ((tendsto_add_atTop_nat 1).comp hNt)
    refine h.congr fun T => ?_
    simp only [Function.comp]
    rw [← sum_Icc_eq_sum_range (g := fun n => ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)))
      (tau_sq_rpow_zero _)]
    exact sum_congr rfl fun n _ => (norm_babs_sq σ n).symm
  · -- off-diagonal error
    have hlim := (tendsto_log_rpow_div (p := 0) le_rfl one_pos).const_mul (RS (2 * σ - 1))
    rw [mul_zero] at hlim
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have := H_nonneg (N T)
      have : 0 ≤ ∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖babs σ n‖ ^ 2 := sum_nonneg fun _ _ => by positivity
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hT0 : 0 < T := by linarith
      have hW : ∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖babs σ n‖ ^ 2 ≤ RS (2 * σ - 1) := by
        have e : ∀ n ∈ Icc 1 (N T), (n : ℝ) * ‖babs σ n‖ ^ 2 =
            ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ - 1)) := by
          intro n hn
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.1 hn).1
          rw [norm_babs_sq]
          have : (n : ℝ) ^ (-(2 * σ - 1)) = (n : ℝ) * (n : ℝ) ^ (-(2 * σ)) := by
            rw [show -(2 * σ - 1) = 1 + -(2 * σ) by ring, Real.rpow_add hn0, Real.rpow_one]
          rw [this]; ring
        rw [sum_congr rfl e]
        have := sum_tau_sq_rpow_le (β := 2 * σ - 1) (γ := 2 * σ - 1) (by linarith) le_rfl (N T)
        simpa using this
      have hH : H (N T) ≤ 1 + Real.log T := by
        refine (H_le_one_add_log (N T)).trans ?_
        rcases Nat.eq_zero_or_pos (N T) with h0 | hpos
        · rw [h0]; simp; exact Real.log_nonneg hT
        · gcongr
          exact Nat.floor_le hT0.le
      have hlog : 0 ≤ 1 + Real.log T := by have := Real.log_nonneg hT; linarith
      rw [Real.rpow_zero, mul_one]
      have hW0 : 0 ≤ ∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖babs σ n‖ ^ 2 :=
        sum_nonneg fun _ _ => by positivity
      calc H (N T) * (∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖babs σ n‖ ^ 2) / T
          ≤ (1 + Real.log T) * RS (2 * σ - 1) / T := by
            gcongr
        _ = RS (2 * σ - 1) * ((1 + Real.log T) / T) := by ring

end RamanujanTau.MeanSquare
