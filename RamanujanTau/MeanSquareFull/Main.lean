/-
# Carlson–Potter mean square of `L(Δ,s)` on the full classical range `σ > 6`

    (1/T) ∫₀ᵀ |L(Δ, σ+it)|² dt  →  ∑_{n ≥ 1} τ(n)² n^{-2σ}     (T → ∞),   every σ > 6.

`mean_square_tauL` (MeanSquare/) gave `σ > 37/6`.  Here a functional-equation bootstrap extends
it: with thresholds `y_n = 1/(6+4n)` (`y_0 = 1/6`, `y_{n+1} = y_n/(1+4y_n)`),

* `mean_square_tauL_range n`: the theorem for `σ > 6 + y_n`, by induction on `n`;
* step `n → n+1` (`step_core`): for `6 + y_{n+1} < σ ≤ 37/6` pick `y ∈ (y_n, 1/4]` with
  `y < x(1+4y)` (`x = σ − 6`); the induction hypothesis on `Re s = 6+y` gives
  `∫₀ᵁ|L|² ≪ 1+U` (`bound_of_tendsto`); the functional equation moves it to
  `∫_{−U}^{U} |L(6−y+iu)|² ≪ (1+U)^{1+4y}` (`left_line_mean_bound`); this bounds the
  shifted-contour remainder in `L²` (`L2_remainder`), and `mean_sq_of_L2approx` concludes.
* `y_n → 0`, so every `σ > 6` is reached: `mean_square_tauL_full`.
-/
import RamanujanTau.MeanSquareFull.Step

set_option autoImplicit false

namespace RamanujanTau.MeanSquareFull

open Complex Real Filter Topology
open RamanujanTau.HeckeL RamanujanTau.MeanSquare

/-- The bootstrap thresholds `y_n = 1/(6+4n)`. -/
noncomputable def yth (n : ℕ) : ℝ := 1 / (6 + 4 * n)

lemma yth_pos (n : ℕ) : 0 < yth n := by unfold yth; positivity

lemma yth_le (n : ℕ) : yth n ≤ 1 / 6 := by
  unfold yth
  exact one_div_le_one_div_of_le (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)

lemma yth_succ (n : ℕ) : yth (n + 1) * (1 + 4 * yth n) = yth n := by
  unfold yth; push_cast; field_simp; ring

/-- **The theorem on `σ > 6 + 1/(6+4n)`**, by induction on `n`. -/
theorem mean_square_tauL_range (n : ℕ) {σ : ℝ} (hσ : 6 + yth n < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2) / T) atTop
      (𝓝 (∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)))) := by
  induction n generalizing σ with
  | zero =>
    refine mean_square_tauL ?_
    have : yth 0 = 1 / 6 := by unfold yth; norm_num
    rw [this] at hσ; linarith
  | succ n ih =>
    rcases lt_or_ge (37 / 6) σ with h | h
    · exact mean_square_tauL h
    set x : ℝ := σ - 6 with hxdef
    set y0 : ℝ := yth n with hy0def
    have hy0 : 0 < y0 := yth_pos n
    have hy0le : y0 ≤ 1 / 6 := yth_le n
    have hx1 : x ≤ 1 / 6 := by rw [hxdef]; linarith
    have hxt : yth (n + 1) < x := by rw [hxdef]; linarith
    have hx0 : 0 < x := (yth_pos (n + 1)).trans hxt
    have hm : 0 < x * (1 + 4 * y0) - y0 := by
      have h1 := yth_succ n
      rw [← hy0def] at h1
      have : yth (n + 1) * (1 + 4 * y0) < x * (1 + 4 * y0) :=
        mul_lt_mul_of_pos_right hxt (by linarith)
      linarith
    set m : ℝ := x * (1 + 4 * y0) - y0 with hmdef
    set d : ℝ := min (m / 2) (1 / 12) with hd
    have hd0 : 0 < d := lt_min (by linarith) (by norm_num)
    have hdm : d ≤ m / 2 := min_le_left _ _
    have hd12 : d ≤ 1 / 12 := min_le_right _ _
    set y : ℝ := y0 + d with hydef
    have hy : 0 < y := by rw [hydef]; linarith
    have hy4 : y ≤ 1 / 4 := by rw [hydef]; linarith
    have hxy : y < x * (1 + 4 * y) := by
      rw [hydef]
      have : 0 ≤ x * d := by positivity
      nlinarith
    have hR := bound_of_tendsto (h := fun u : ℝ => ‖tauL (((6 + y : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2)
      ((tauLSeries_entire.continuous.comp (by fun_prop)).norm.pow 2) (fun u => by positivity)
      (ih (σ := 6 + y) (by rw [hydef]; linarith))
    obtain ⟨C, hC⟩ := hR
    obtain ⟨α, η, hα, hη, hdg, hrem⟩ := exists_params hx0 hx1 hy hxy
    have hmain := step_core hx0 hx1 hy hy4 hα hη hdg hrem hC
    have e : (6 + x : ℝ) = σ := by rw [hxdef]; ring
    rw [e] at hmain
    exact hmain

/-- **Carlson–Potter mean-square theorem for `L(Δ,s)`, full range `σ > 6`.** -/
theorem mean_square_tauL_full {σ : ℝ} (hσ : 6 < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2) / T) atTop
      (𝓝 (∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)))) := by
  have hx : 0 < σ - 6 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (σ - 6))
  refine mean_square_tauL_range n ?_
  have hlt : yth n < σ - 6 := by
    unfold yth
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hx] at hn
    have := Nat.cast_nonneg (α := ℝ) n
    nlinarith
  linarith

/-- The limit is finite: `∑ τ(n)² n^{-2σ}` converges for `σ > 6`. -/
theorem summable_mean_square_limit_full {σ : ℝ} (hσ : 6 < σ) :
    Summable fun n : ℕ => ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) :=
  summable_tau_sq (by linarith)

end RamanujanTau.MeanSquareFull

#print axioms RamanujanTau.MeanSquareFull.mean_square_tauL_full
#print axioms RamanujanTau.MeanSquareFull.mean_square_tauL_range
#print axioms RamanujanTau.MeanSquareFull.step_core
#print axioms RamanujanTau.MeanSquareFull.exists_params
#print axioms RamanujanTau.MeanSquareFull.mean_sq_of_L2approx
#print axioms RamanujanTau.MeanSquareFull.L2_remainder
#print axioms RamanujanTau.MeanSquareFull.left_line_mean_bound
#print axioms RamanujanTau.MeanSquareFull.norm_tauL_left_le
#print axioms RamanujanTau.MeanSquareFull.tauL_identity
#print axioms RamanujanTau.MeanSquareFull.tendsto_lam
#print axioms RamanujanTau.MeanSquareFull.summable_mean_square_limit_full
