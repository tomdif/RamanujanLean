/-
# M3 done: `DiagApproxHyp θ` for small `θ`, and the diagonal clause from `SKQFHyp` alone

* `diagApproxHyp_small`: `∃ θ₀ > 0, ∀ θ ∈ [0, θ₀], DiagApproxHyp θ` (level 1);
* `diagHypT_of_SKQF'`: `0 ≤ θ ≤ θ₀ → SKQFHyp θ → SelbergKey5.DiagHypT θ` (level 2 on `SKQFHyp`);
* `sk_of_SKQF'`, `tauL_positive_proportion_of_SKQF'`: with `QuadOffHyp` (and `QFHyp`).
-/
import RamanujanTau.SelbergKeyDiag2.Final4
import RamanujanTau.SelbergKeyDiag.Assemble

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex Set RamanujanTau.SelbergKey RamanujanTau.HeckeL
open scoped Real

/-- **M3: the diagonal evaluation holds for every small `θ`** (level 1). -/
theorem diagApproxHyp_small : ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 ≤ θ → θ ≤ θ₀ →
    SelbergKeyDiag.DiagApproxHyp θ := by
  obtain ⟨C, N, hC0, hpt⟩ := diag_pointwise
  refine ⟨1 / (20 * (N + 1)), by positivity, fun θ hθ0 hθ => ?_⟩
  refine ⟨2 * C, 1 / 20, 2000, by positivity, by norm_num, fun T hT u hu v hv0 hv => ?_⟩
  have hT1 : (1:ℝ) ≤ T := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  set y := ⌊T ^ θ⌋₊ with hydef
  have hTθ1 : 1 ≤ T ^ θ := Real.one_le_rpow hT1 hθ0
  have hy1 : 1 ≤ y := Nat.one_le_floor_iff _ |>.2 hTθ1
  have hyT : (y : ℝ) ≤ T ^ θ := Nat.floor_le (by positivity)
  have hθ20 : θ ≤ 1 / 20 := hθ.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
  have hθN : θ * N ≤ 1 / 20 := by
    have : θ * (N + 1) ≤ 1 / 20 := by
      calc θ * (N + 1) ≤ 1 / (20 * (N + 1)) * (N + 1) := by gcongr
        _ = 1 / 20 := by field_simp
    nlinarith
  have hu40 : 40 ≤ u := by linarith [hu.1]
  have hu0 : 0 < u := by linarith
  -- `16π²y⁴ ≤ u²`
  have hy4 : (y : ℝ) ^ 4 ≤ T := by
    calc (y : ℝ) ^ 4 ≤ (T ^ θ) ^ 4 := by gcongr
      _ = T ^ (θ * 4) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
      _ ≤ T ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      _ = T := Real.rpow_one T
  have hyu : 16 * π ^ 2 * (y : ℝ) ^ 4 ≤ u ^ 2 := by
    have hπ : π ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
    have h1 : 16 * π ^ 2 * (y : ℝ) ^ 4 ≤ 256 * T := by nlinarith [hy4, sq_nonneg π]
    have h2 : T / 2 ≤ u := hu.1
    have h3 : (T / 2) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    have h4 : 256 * T ≤ (T / 2) ^ 2 := by nlinarith
    linarith
  have h := hpt y u v hy1 hu40 hv0 hv hyu
  refine h.trans ?_
  -- `y^N u^{−1/10} ≤ 2 T^{−1/20}`
  have hW : (y : ℝ) ^ N * u ^ (-(1 / 10 : ℝ)) ≤ 2 * T ^ (-(1 / 20 : ℝ)) := by
    have h1 : (y : ℝ) ^ N ≤ T ^ (θ * N) := by
      calc (y : ℝ) ^ N ≤ (T ^ θ) ^ N := by gcongr
        _ = T ^ (θ * N) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    have h2 : u ^ (-(1 / 10 : ℝ)) ≤ (T / 2) ^ (-(1 / 10 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hu.1 (by norm_num)
    have h3 : (T / 2) ^ (-(1 / 10 : ℝ)) ≤ 2 * T ^ (-(1 / 10 : ℝ)) := by
      rw [Real.div_rpow hT0.le (by norm_num), div_eq_mul_inv, mul_comm, ← Real.rpow_neg (by norm_num), neg_neg]
      gcongr
      calc (2:ℝ) ^ (1 / 10 : ℝ) ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have h4 : T ^ (θ * N) * T ^ (-(1 / 10 : ℝ)) ≤ T ^ (-(1 / 20 : ℝ)) := by
      rw [← Real.rpow_add hT0]
      exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    calc (y : ℝ) ^ N * u ^ (-(1 / 10 : ℝ)) ≤ T ^ (θ * N) * (2 * T ^ (-(1 / 10 : ℝ))) :=
          mul_le_mul h1 (h2.trans h3) (by positivity) (by positivity)
      _ = 2 * (T ^ (θ * N) * T ^ (-(1 / 10 : ℝ))) := by ring
      _ ≤ 2 * T ^ (-(1 / 20 : ℝ)) := by gcongr
  have hvS : 0 ≤ |v| * ‖Sv y v‖ := by positivity
  calc C * (|v| * ‖Sv y v‖ + (y : ℝ) ^ N * u ^ (-(1 / 10 : ℝ)))
      ≤ C * (|v| * ‖Sv y v‖ + 2 * T ^ (-(1 / 20 : ℝ))) := by gcongr
    _ ≤ 2 * C * (|v| * ‖Sv y v‖ + T ^ (-(1 / 20 : ℝ))) := by
        have : 0 ≤ T ^ (-(1 / 20 : ℝ)) := by positivity
        nlinarith [mul_nonneg hC0 hvS, mul_nonneg hC0 this]

/-- **The diagonal clause `DiagHypT θ` from `SKQFHyp θ` alone**, for `0 ≤ θ ≤ θ₀`
(level 2 on `SKQFHyp θ`; M3 and M4 are unconditional). -/
theorem diagHypT_of_SKQF' : ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 ≤ θ → θ ≤ θ₀ →
    SKQFHyp θ → SelbergKey5.DiagHypT θ := by
  obtain ⟨θ₀, hθ₀, h⟩ := diagApproxHyp_small
  exact ⟨θ₀, hθ₀, fun θ hθ0 hθ hS => SelbergKeyDiag.diagHypT_of_SKQF hS (h θ hθ0 hθ)⟩

/-- **`SKSplitHyp' θ` from `SKQFHyp θ` and the off-diagonal `QuadOffHyp`.** -/
theorem sk_of_SKQF' : ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ η B : ℝ, 0 ≤ θ → θ ≤ θ₀ → 0 ≤ B → 4 * θ * (1 + B) < η →
    SKQFHyp θ → SelbergKey5.QuadOffHyp η B → SelbergKey2.SKSplitHyp' θ := by
  obtain ⟨θ₀, hθ₀, h⟩ := diagApproxHyp_small
  exact ⟨θ₀, hθ₀, fun θ η B hθ0 hθ hB hηθ hS hO =>
    SelbergKeyDiag.sk_of_SKQF hB hθ0 hηθ hS (h θ hθ0 hθ) hO⟩

/-- **Positive proportion for `L(Δ,s)`** on `QFHyp ∧ SKQFHyp θ ∧ QuadOffHyp η B`, `θ` small. -/
theorem tauL_positive_proportion_of_SKQF' : ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ η B : ℝ, 0 < θ → θ ≤ θ₀ →
    θ ≤ 1 / 81600 → 0 ≤ B → 4 * θ * (1 + B) < η →
    HafnerBridge.QFHyp → SKQFHyp θ → SelbergKey5.QuadOffHyp η B →
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ tauL (6 + γ * I) = 0) ∧
        c * (ZeroCount.zeroCount (3 * T) : ℝ) ≤ S.card := by
  obtain ⟨θ₀, hθ₀, h⟩ := diagApproxHyp_small
  exact ⟨θ₀, hθ₀, fun θ η B hθ0 hθ hθ' hB hηθ hQ hS hO =>
    SelbergKeyDiag.tauL_positive_proportion_of_SKQF hθ0 hθ' hB hηθ hQ hS (h θ hθ0.le hθ) hO⟩

end RamanujanTau.SelbergKeyDiag2
