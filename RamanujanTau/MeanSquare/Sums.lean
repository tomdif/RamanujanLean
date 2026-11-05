/-
# Rankin–Selberg sums `∑ τ(n)² n^{-β}`

From `∑_{n ≤ N} τ(n)² ≪ N¹²` (`HeckeConvex.sum_sq_le`, i.e. Rankin–Selberg / Zagier):

* `summable_tau_sq`: `∑ τ(n)² n^{-β}` converges for `β > 12`;
* `sum_tau_sq_rpow_le`: `∑_{n ≤ N} τ(n)² n^{-γ} ≤ N^{β−γ} RS(β)` for `γ ≤ β`, `β > 12`;
* elementary limit helpers used by the assembly.
-/
import RamanujanTau.HeckeConvex.Main
import RamanujanTau.MeanSquare.Poly

set_option autoImplicit false

namespace RamanujanTau.MeanSquare

open Complex Finset Filter Topology Asymptotics LSeries

/-- `RS β = ∑ τ(n)² n^{-β}`. -/
noncomputable def RS (β : ℝ) : ℝ := ∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-β)

lemma tau_sq_rpow_zero (β : ℝ) : ((tau 0 : ℝ)) ^ 2 * ((0 : ℕ) : ℝ) ^ (-β) = 0 := by
  simp [tau_zero]

/-- `∑ τ(n)² n^{-β} < ∞` for `β > 12`. -/
theorem summable_tau_sq {β : ℝ} (hβ : 12 < β) :
    Summable fun n : ℕ => ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-β) := by
  obtain ⟨B, hB0, hB⟩ := RamanujanTau.HeckeConvex.exists_sum_sq_div_le
  set f : ℕ → ℂ := fun n => (((tau n : ℝ)) ^ 2 : ℝ)
  have hf : ∀ n, ‖f n‖ = ((tau n : ℝ)) ^ 2 := fun n => by
    simp only [f, Complex.norm_real, Real.norm_eq_abs]; exact abs_of_nonneg (sq_nonneg _)
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n => (n : ℝ) ^ (12 : ℝ) := by
    refine IsBigO.of_bound B (Eventually.of_forall fun N => ?_)
    simp_rw [hf]
    rw [Real.norm_of_nonneg (sum_nonneg fun _ _ => sq_nonneg _),
      Real.norm_of_nonneg (by positivity)]
    rw [show (N : ℝ) ^ (12 : ℝ) = (N : ℝ) ^ (12 : ℕ) by norm_cast]
    exact RamanujanTau.HeckeConvex.sum_sq_le hB N
  have hL : LSeriesSummable f (β : ℂ) :=
    LSeriesSummable_of_sum_norm_bigO hO (by norm_num) (by simpa using hβ)
  refine hL.norm.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tau_zero]
  · rw [LSeries.norm_term_eq, if_neg hn.ne', hf, Complex.ofReal_re,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

lemma RS_nonneg (β : ℝ) : 0 ≤ RS β :=
  tsum_nonneg fun n => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- `∑_{n ≤ N} τ(n)² n^{-γ} ≤ N^{β−γ} RS(β)` for `γ ≤ β`, `β > 12`. -/
theorem sum_tau_sq_rpow_le {β γ : ℝ} (hβ : 12 < β) (hγβ : γ ≤ β) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-γ) ≤ (N : ℝ) ^ (β - γ) * RS β := by
  have hs := summable_tau_sq hβ
  have h1 : ∀ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-γ) ≤
      (N : ℝ) ^ (β - γ) * (((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-β)) := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Icc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast h2
    have e : (n : ℝ) ^ (-γ) = (n : ℝ) ^ (β - γ) * (n : ℝ) ^ (-β) := by
      rw [← Real.rpow_add hn0]; congr 1; ring
    rw [e]
    have : (n : ℝ) ^ (β - γ) ≤ (N : ℝ) ^ (β - γ) :=
      Real.rpow_le_rpow hn0.le hnN (by linarith)
    have h0 : 0 ≤ ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-β) := by positivity
    nlinarith
  refine (sum_le_sum h1).trans ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact hs.sum_le_tsum _ fun n _ => by positivity

/-- Sums over `Icc 1 N` of a sequence vanishing at `0` are sums over `range (N+1)`. -/
lemma sum_Icc_eq_sum_range {M : Type*} [AddCommMonoid M] {g : ℕ → M} (h0 : g 0 = 0) (N : ℕ) :
    ∑ n ∈ Icc 1 N, g n = ∑ n ∈ range (N + 1), g n := by
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_range_succ _ (N + 1)]

/-- `(1 + log T) T^p / T → 0` for `0 ≤ p < 1`. -/
lemma tendsto_log_rpow_div {p : ℝ} (_hp0 : 0 ≤ p) (hp : p < 1) :
    Tendsto (fun T : ℝ => (1 + Real.log T) * T ^ p / T) atTop (𝓝 0) := by
  set q : ℝ := (1 - p) / 2 with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have h1 : Tendsto (fun T : ℝ => T ^ (-(1 - p))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have h2 : Tendsto (fun T : ℝ => T ^ (-(1 - p - q)) / q) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := 1 - p - q) (by rw [hq]; linarith)).div_const q
    simpa using this
  have h3 := h1.add h2
  rw [zero_add] at h3
  refine squeeze_zero' ?_ ?_ h3
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have := Real.log_nonneg hT
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT0 : 0 < T := by linarith
    have hlog : Real.log T ≤ T ^ q / q := Real.log_le_rpow_div hT0.le hq0
    have e1 : T ^ p / T = T ^ (-(1 - p)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hT0]
      congr 1; ring
    have e2 : T ^ q / q * T ^ p / T = T ^ (-(1 - p - q)) / q := by
      have : T ^ q * T ^ p / T = T ^ (-(1 - p - q)) := by
        rw [← Real.rpow_add hT0, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hT0]
        congr 1; ring
      rw [← this]; field_simp
    have hTp : 0 ≤ T ^ p / T := by positivity
    calc (1 + Real.log T) * T ^ p / T = T ^ p / T + Real.log T * (T ^ p / T) := by ring
      _ ≤ T ^ p / T + T ^ q / q * (T ^ p / T) := by gcongr
      _ = T ^ (-(1 - p)) + T ^ (-(1 - p - q)) / q := by
          rw [e1, ← e2, ← e1]; ring

end RamanujanTau.MeanSquare
