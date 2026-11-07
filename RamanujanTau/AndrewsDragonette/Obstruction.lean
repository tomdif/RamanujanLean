/-
# Why the inequality-only circle method cannot give the exact formula

`Andrews66.Hb C D` (a pointwise bound `‖f − ε_K b‖ ≤ C‖z‖^{−D}` near every cusp) is **false for every `D < 0`**
(`not_Hb_of_neg`): at the cusp `0/1` (`ε_1 = 0`), along the real radius `q = e^{−2πs} → 1⁻`, every term of
`f(q) = Σ q^{n²}/(−q;q)_n²` is nonnegative, so `f(q) ≥ 1` (`one_le_fA_real`), while `C s^{−D} → 0`.

Consequence (see `docs/ANDREWS_DRAGONETTE_EXACT.md`): in the Farey dissection of order `N` on `Im τ = 1/N²`,
the absolute-value bound for the non-principal part summed over all arcs is `≍ Σ_{K≤N} φ(K)·N^{2D}K^{−D}/(KN)
≍ N^{D}` (`0 ≤ D < 1`), which never tends to `0` for any admissible `D ≥ 0`. Rademacher's exactness
argument for `p(n)` works because there the non-principal part is `O(|z|^{1/2})`, i.e. effectively `D = −1/2`.
-/
import RamanujanTau.Andrews66.BNear

set_option autoImplicit false

namespace AndrewsDragonette
open Complex Filter Topology Finset
open scoped Real

lemma one_le_fA_real {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : 1 ≤ ‖MockTheta3.Radial.fA (t : ℂ)‖ := by
  set u : ℕ → ℝ := fun n => t ^ (n ^ 2) / (∏ i ∈ range n, (1 + t ^ (i + 1))) ^ 2 with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => by simp only [hu]; positivity
  have hule : ∀ n, u n ≤ t ^ n := fun n => by
    simp only [hu]
    have hP : 1 ≤ ∏ i ∈ range n, (1 + t ^ (i + 1)) := by
      induction n with
      | zero => simp
      | succ m ih =>
        rw [prod_range_succ]
        exact one_le_mul_of_one_le_of_one_le ih (by have := pow_nonneg h0 (m + 1); linarith)
    have hP2 : 1 ≤ (∏ i ∈ range n, (1 + t ^ (i + 1))) ^ 2 := one_le_pow₀ hP
    calc t ^ (n ^ 2) / (∏ i ∈ range n, (1 + t ^ (i + 1))) ^ 2 ≤ t ^ (n ^ 2) :=
          div_le_self (by positivity) hP2
      _ ≤ t ^ n := pow_le_pow_of_le_one h0 h1.le (by nlinarith)
  have hs : Summable u :=
    Summable.of_nonneg_of_le hu0 hule (summable_geometric_of_lt_one h0 h1)
  have hf : MockTheta3.Radial.fA (t : ℂ) = ((∑' n, u n : ℝ) : ℂ) := by
    rw [MockTheta3.Radial.fA_eq, Complex.ofReal_tsum]
    congr 1; funext n; simp only [hu]; push_cast; rfl
  have h1le : 1 ≤ ∑' n, u n := by
    have := hs.le_tsum 0 (fun j _ => hu0 j)
    simpa [hu] using this
  rw [hf, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg hu0)]
  exact h1le

lemma qp_zero_one_real (s : ℝ) : Rademacher.qp 0 1 (s : ℂ) = ((Real.exp (-2 * π * s) : ℝ) : ℂ) := by
  rw [Rademacher.qp, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]; ring

/-- **No pointwise bound with `D < 0`.** The non-principal part of `f` at the cusps does not tend to `0`. -/
theorem not_Hb_of_neg {C D : ℝ} (hD : D < 0) : ¬ Andrews66.Hb C D := by
  intro hHb
  have hp : 0 < -D := by linarith
  -- s^{-D} → 0 as s → 0
  have hc := Real.continuousAt_rpow_const 0 (-D) (Or.inr hp.le)
  rw [ContinuousAt, Real.zero_rpow hp.ne'] at hc
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), C * s ^ (-D) < 1 := by
    have := (hc.const_mul C)
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds one_pos)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set s : ℝ := min (ε / 2) 1 with hsdef
  have hs0 : 0 < s := lt_min (by linarith) one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hsε : dist s 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hlt := hball hsε
  have hz : 0 < ((s : ℂ)).re := by simpa using hs0
  have hR : ((1 : ℕ) : ℝ) / 2 ≤ (1 / (s : ℂ)).re := by
    rw [show (1 / (s : ℂ)) = ((1 / s : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
    rw [le_div_iff₀ hs0]; push_cast; linarith
  have hb := hHb 1 one_pos 0 (Nat.coprime_zero_left 1 |>.mpr rfl) (s : ℂ) hz hR
  have heps : Andrews66.epsK 1 = 0 := by
    unfold Andrews66.epsK; simp
  rw [heps, zero_mul, sub_zero] at hb
  have hq : Rademacher.qp ((0 : ℕ) : ℤ) 1 (s : ℂ) = ((Real.exp (-2 * π * s) : ℝ) : ℂ) := by
    simpa using qp_zero_one_real s
  rw [hq] at hb
  have hexp0 : 0 ≤ Real.exp (-2 * π * s) := (Real.exp_pos _).le
  have hexp1 : Real.exp (-2 * π * s) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have h1 := one_le_fA_real hexp0 hexp1
  have hzs : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
  rw [hzs] at hb
  linarith

end AndrewsDragonette
