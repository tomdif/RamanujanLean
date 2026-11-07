/-
# The Selberg-smoothed sum for `R^{−1/2}`

**Theorem** (`selberg_sum_fR`, unconditional).  With the same `C₁` as in `logmean_fR`:

  `Σ_{n≤x} (fR(n)/n) log(x/n) = 2C₁ (log x − c₀)^{1/2} + O((1+log(1+log x)) (log x)^{−1/2})`,

equivalently `Σ_{n≤y} (fR(n)/n)(1 − log n/log y) = 2C₁ (log y − c₀)^{1/2}/log y + O(log log y/(log y)^{3/2})`
— Selberg's mollifier weight `(1 − log n/log y)` applied to the `R^{−1/2}` coefficients.

Proof: `key_identity` with `κ = −1/2`: `I = 2(t − c₀)S − 2R`; `S` from `logmean_LSD`, `R` from
`Rsum_bound` + `weight_bound`.
-/
import RamanujanTau.SelbergDelange3.Shift

set_option autoImplicit false

namespace RamanujanTau.SelbergDelange3

open Finset Set Filter Topology ArithmeticFunction
open RamanujanTau.SelbergDelange2

theorem selberg_sum_fR : ∃ C₁ K₃ X₂ c₀ : ℝ, ∀ x : ℝ, X₂ ≤ x →
    |Ssum fR x - C₁ * (Real.log x - c₀) ^ (-(1 / 2 : ℝ))| ≤
        K₃ * (1 + Real.log (1 + Real.log x)) * Real.log x ^ (-(1 / 2 : ℝ) - 1) ∧
    |Isum fR x - 2 * C₁ * (Real.log x - c₀) ^ (1 / 2 : ℝ)| ≤
        K₃ * (1 + Real.log (1 + Real.log x)) * Real.log x ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨c, B, hB, hM⟩ := mertens_LamR_err
  obtain ⟨K, hK, hC⟩ := density_fR
  set c₀ : ℝ := -(c / 2) with hc₀
  have hM' : ∀ y : ℝ, 1 ≤ y → |Err (toA gR gR_zero) (-(1 / 2)) c₀ y| ≤
      (B / 2) / (1 + Real.log y) := by
    intro y hy
    have h := hM y hy
    have e : Err (toA gR gR_zero) (-(1 / 2)) c₀ y =
        -(1 / 2) * (Msum SelbergCoeffs2.LamR y - Real.log y - c) := by
      unfold Err Msum
      rw [mul_sub, mul_sub, mul_sum]
      have : ∑ m ∈ Finset.Ioc 0 ⌊y⌋₊, (toA gR gR_zero) m / m =
          ∑ m ∈ Finset.Ioc 0 ⌊y⌋₊, -(1 / 2) * (SelbergCoeffs2.LamR m / m) :=
        sum_congr rfl fun m _ => by simp only [toA, coe_mk, gR]; ring
      rw [this, hc₀]; ring
    rw [e, abs_mul]
    have : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num
    rw [this]
    calc 1 / 2 * |Msum SelbergCoeffs2.LamR y - Real.log y - c| ≤ 1 / 2 * (B / (1 + Real.log y)) := by
          gcongr
      _ = B / 2 / (1 + Real.log y) := by ring
  obtain ⟨C₁, K₁, X₀, h⟩ := logmean_LSD (recFA gR) (toA gR gR_zero) (κ := -(1 / 2)) (c₀ := c₀)
    (σ := 1 / 2) (B := B / 2) (K := K) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) hK fR_log hM' (fun y hy => hC y hy)
  set W : ℝ := (B / 2) * (Real.exp 1 * K) * 6 with hW
  refine ⟨C₁, |K₁| * 3 + 2 * W, max X₀ (Real.exp (2 * |c₀| + 2)), c₀, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) (le_trans (le_max_right _ _) hx)
  set t := Real.log x with ht
  have hta : 2 * |c₀| + 2 ≤ t := by
    rw [ht, Real.le_log_iff_exp_le hx0]; exact le_trans (le_max_right _ _) hx
  have ht2 : 2 ≤ t := by linarith [abs_nonneg c₀]
  have ht0 : 0 < t := by linarith
  have hx1 : 1 ≤ x := by rw [← Real.exp_log hx0]; exact Real.one_le_exp ht0.le
  have hcc := le_abs_self c₀
  have hcc' := neg_abs_le c₀
  have hpos : 0 < t - c₀ := by linarith
  have hup : t - c₀ ≤ 3 / 2 * t := by linarith
  have hL : 1 ≤ 1 + Real.log (1 + t) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + t by linarith); linarith
  have hlog1 : 1 ≤ Real.log (1 + t) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; have := Real.exp_one_lt_d9; linarith
  have hS := h x (le_trans (le_max_left _ _) hx)
  -- the `R` bound
  have hR1 := Rsum_bound (recFA gR) (toA gR gR_zero) hM' hx1
  have hR2 := weight_bound (recFA gR) (σ := 1 / 2) (by norm_num) (by norm_num) hK
    (fun y hy => hC y hy) hx1
  have h2t : (2 + t) ^ ((1 / 2 : ℝ) - 1) ≤ t ^ (-(1 / 2 : ℝ)) := by
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
    exact Real.rpow_le_rpow_of_nonpos ht0 (by linarith) (by norm_num)
  have hR : |Rsum (recFA gR) (toA gR gR_zero) (-(1 / 2)) c₀ x| ≤
      W * ((1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ))) := by
    refine hR1.trans ?_
    have hq : 0 ≤ (2 + t) ^ ((1 / 2 : ℝ) - 1) := by positivity
    have h6 : 2 * (1 + Real.log (1 + t)) + 2 / (1 / 2) ≤ 6 * (1 + Real.log (1 + t)) := by
      norm_num; linarith
    have hEK : 0 ≤ Real.exp 1 * K := by positivity
    calc B / 2 * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, |(recFA gR) n| / n / (1 + Real.log (x / n))
        ≤ B / 2 * (Real.exp 1 * K * ((2 * (1 + Real.log (1 + t)) + 2 / (1 / 2)) *
          (2 + t) ^ ((1 / 2 : ℝ) - 1))) := by gcongr
      _ ≤ B / 2 * (Real.exp 1 * K * ((6 * (1 + Real.log (1 + t))) * t ^ (-(1 / 2 : ℝ)))) := by
          gcongr
      _ = W * ((1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ))) := by rw [hW]; ring
  have hid := key_identity (recFA gR) (toA gR gR_zero) fR_log (-(1 / 2)) c₀ hx1
  rw [← ht] at hid
  -- `S` part
  have hSS : |Ssum fR x - C₁ * (t - c₀) ^ (-(1 / 2 : ℝ))| ≤
      K₁ * (1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ) - 1) := hS
  have hW0 : 0 ≤ W := by positivity
  have hp32 : 0 ≤ t ^ (-(1 / 2 : ℝ) - 1) := by positivity
  have hp12 : 0 ≤ t ^ (-(1 / 2 : ℝ)) := by positivity
  have hrel : t * t ^ (-(1 / 2 : ℝ) - 1) = t ^ (-(1 / 2 : ℝ)) := by
    rw [show -(1 / 2 : ℝ) = (-(1 / 2) - 1) + 1 by ring, Real.rpow_add_one ht0.ne']
    ring_nf
  constructor
  · refine hSS.trans ?_
    have : K₁ ≤ |K₁| * 3 + 2 * W := by linarith [le_abs_self K₁, abs_nonneg K₁]
    have hLp : 0 ≤ (1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ) - 1) := by positivity
    calc K₁ * (1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ) - 1)
        = K₁ * ((1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ) - 1)) := by ring
      _ ≤ (|K₁| * 3 + 2 * W) * ((1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right this hLp
      _ = _ := by ring
  · -- `I = 2(t − c₀)S − 2R`
    have hI : Isum fR x = 2 * ((t - c₀) * Ssum fR x) - 2 * Rsum (recFA gR) (toA gR gR_zero) (-(1 / 2)) c₀ x := by
      have : Isum (recFA gR) x = Isum fR x := rfl
      have hs : Ssum (recFA gR) x = Ssum fR x := rfl
      rw [hs, this] at hid
      linarith
    have hpow : (t - c₀) * (t - c₀) ^ (-(1 / 2 : ℝ)) = (t - c₀) ^ (1 / 2 : ℝ) := by
      rw [show (1 / 2 : ℝ) = -(1 / 2) + 1 by norm_num, Real.rpow_add_one hpos.ne']; ring
    have e : Isum fR x - 2 * C₁ * (t - c₀) ^ (1 / 2 : ℝ) =
        2 * (t - c₀) * (Ssum fR x - C₁ * (t - c₀) ^ (-(1 / 2 : ℝ))) -
          2 * Rsum (recFA gR) (toA gR gR_zero) (-(1 / 2)) c₀ x := by
      rw [hI, ← hpow]; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hpos, abs_two]
    have hA : 2 * (t - c₀) * |Ssum fR x - C₁ * (t - c₀) ^ (-(1 / 2 : ℝ))| ≤
        |K₁| * 3 * ((1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ))) := by
      have hk : K₁ * (1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ) - 1) ≤
          |K₁| * (1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ) - 1) := by
        gcongr; exact le_abs_self K₁
      have h1 := hSS.trans hk
      have h2 : 2 * (t - c₀) ≤ 3 * t := by linarith
      have hX : 0 ≤ |K₁| * (1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ) - 1) := by positivity
      calc 2 * (t - c₀) * |Ssum fR x - C₁ * (t - c₀) ^ (-(1 / 2 : ℝ))|
          ≤ 3 * t * (|K₁| * (1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ) - 1)) :=
            mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
        _ = |K₁| * 3 * ((1 + Real.log (1 + t)) * (t * t ^ (-(1 / 2 : ℝ) - 1))) := by ring
        _ = _ := by rw [hrel]
    have hB2 := mul_le_mul_of_nonneg_left hR (show (0 : ℝ) ≤ 2 by norm_num)
    calc 2 * (t - c₀) * |Ssum fR x - C₁ * (t - c₀) ^ (-(1 / 2 : ℝ))| +
          2 * |Rsum (recFA gR) (toA gR gR_zero) (-(1 / 2)) c₀ x|
        ≤ |K₁| * 3 * ((1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ))) +
          2 * (W * ((1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ)))) := add_le_add hA hB2
      _ = _ := by ring

end RamanujanTau.SelbergDelange3
