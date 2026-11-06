/-
# M1(c): all `u`-derivatives of the lag weight `u ↦ W̃_{u,u+v}(ξ)`, uniformly in `|v| ≤ 1`

On a line `Re z = x` (`x ≥ −1`, `x ≠ 0`) write the lag weight as

    Wl x v ξ u = ∫ R(u, y) R(−(u+v), y) K(y) dy,   R(t,y) = Γ(6+it+z)/Γ(6+it)  (`HeckeAFE3.Rf`),

`K = HeckeAFE3.Kf`.  Then (`Wsh_eq_Wl`) `W̃_{u,u+v}(ξ) = Wl x v ξ u` for `x > 0` and
`W̃_{u,u+v}(ξ) = 1 + Wl (−1) v ξ u`.  Leibniz plus `HeckeAFE3.norm_Rd_le` at `u` and at `−(u+v)`:

* `iteratedDeriv_Pf`: `∂_u^m [R(u)R(−(u+v))] = Σ C(m,i) R_i(u) (−1)^{m−i} R_{m−i}(−(u+v))`;
* `norm_Pd_le`: `≤ B (1+|y|)^{3m} (1+|u|)^{−m} |R(u)||R(−(u+v))|` for `|v| ≤ 1`;
* `iteratedDeriv_Wl`: differentiation under the integral, all orders;
* `norm_intPd_le`: `|∂_u^j Wl x v ξ u| ≤ K (T(u)T(u+v)/ξ)^x (1+|u|)^{−j}`;
* **`Wlag_iteratedDeriv_bound`**: for `j ≥ 1`, `A ≥ 0`:
  `|∂_u^j W̃_{u,u+v}(ξ)| ≤ C (1+|u|)^{−j} (1 + ξ/(T(u)T(u+v)))^{−A}`, uniformly in `u ∈ ℝ`,
  `|v| ≤ 1`, `ξ > 0`; and `u ↦ W̃_{u,u+v}(ξ)` is `C^∞`.
Level 1.
-/
import RamanujanTau.SelbergKey2.Main
import RamanujanTau.HeckeAFE3.Main

set_option autoImplicit false

namespace RamanujanTau.SelbergKey3

open Complex MeasureTheory Set Metric Filter Topology RamanujanTau.HeckeAFE RamanujanTau.HeckeAFE2
  RamanujanTau.HeckeAFE3 RamanujanTau.HeckeL RamanujanTau.SelbergKey RamanujanTau.SelbergKey2
open scoped Real

/-- The product symbol `R(u) R(−(u+v))`. -/
noncomputable def Pf (x v u y : ℝ) : ℂ := Rf x u y * Rf x (-(u + v)) y

/-- Its `m`-th `u`-derivative (Leibniz). -/
noncomputable def Pd (x v : ℝ) (m : ℕ) (u y : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (m + 1), (m.choose i : ℂ) * Rd x i u y *
    ((-1 : ℂ) ^ (m - i) * Rd x (m - i) (-(u + v)) y)

lemma contDiff_Rf_neg {x : ℝ} (hx : -1 ≤ x) (v y : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun u => Rf x (-(u + v)) y) :=
  (contDiff_Rf hx y n).comp (by fun_prop)

lemma iteratedDeriv_Rf_neg {x : ℝ} (hx : -1 ≤ x) (v y : ℝ) (k : ℕ) (u : ℝ) :
    iteratedDeriv k (fun u => Rf x (-(u + v)) y) u = (-1 : ℂ) ^ k * Rd x k (-(u + v)) y := by
  have e : (fun u => Rf x (-(u + v)) y) = fun u => (fun w => Rf x (w - v) y) (-u) := by
    funext u; congr 1; ring
  rw [e]
  refine (iteratedDeriv_comp_neg k (fun w => Rf x (w - v) y) u).trans ?_
  have h2 := congrFun (iteratedDeriv_comp_sub_const (n := k) (f := fun w => Rf x w y) (s := v)) (-u)
  simp only at h2
  rw [h2, iteratedDeriv_Rf hx y k, show -u - v = -(u + v) by ring]
  simp [Complex.real_smul]

theorem iteratedDeriv_Pf {x : ℝ} (hx : -1 ≤ x) (v y : ℝ) (m : ℕ) (u : ℝ) :
    iteratedDeriv m (fun u => Pf x v u y) u = Pd x v m u y := by
  unfold Pf Pd
  rw [iteratedDeriv_fun_mul ((contDiff_Rf hx y m).contDiffAt) ((contDiff_Rf_neg hx v y m).contDiffAt)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_Rf hx y i u, iteratedDeriv_Rf_neg hx v y (m - i) u]

lemma one_add_abs_shift {u v : ℝ} (hv : |v| ≤ 1) : (1 + |u|) / 2 ≤ 1 + |u + v| := by
  have := abs_sub_abs_le_abs_sub u (-v)
  rw [sub_neg_eq_add, abs_neg] at this
  have : |u| ≤ |u + v| + 1 := by linarith
  have h0 := abs_nonneg (u + v)
  linarith

theorem norm_Pd_le {x : ℝ} (hx : -1 ≤ x) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v u y : ℝ, |v| ≤ 1 →
      ‖Pd x v m u y‖ ≤ B * (1 + |y|) ^ (3 * m) / (1 + |u|) ^ m *
        (‖Rf x u y‖ * ‖Rf x (-(u + v)) y‖) := by
  choose B hB0 hB using fun i : ℕ => norm_Rd_le hx i
  refine ⟨∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B i * (B (m - i) * 2 ^ (m - i)),
    Finset.sum_nonneg fun i _ => by have := hB0 i; have := hB0 (m - i); positivity,
    fun v u y hv => ?_⟩
  have hy1 := one_le_one_add_abs y
  have hu1 : 0 < 1 + |u| := by positivity
  have huv := one_add_abs_shift (u := u) hv
  have huv0 : 0 < 1 + |-(u + v)| := by positivity
  unfold Pd
  rw [Finset.sum_mul, Finset.sum_div, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hc : ‖((m.choose i : ℕ) : ℂ)‖ = (m.choose i : ℝ) := by simp
  rw [hc]
  have h1 := hB i u y
  have h2 := hB (m - i) (-(u + v)) y
  rw [abs_neg] at h2
  have hR1 := norm_nonneg (Rf x u y)
  have hR2 := norm_nonneg (Rf x (-(u + v)) y)
  have hBi := hB0 i
  have hBm := hB0 (m - i)
  -- (1+|u+v|)^{−k} ≤ 2^k (1+|u|)^{−k}
  have hshift : 1 / (1 + |u + v|) ^ (m - i) ≤ 2 ^ (m - i) / (1 + |u|) ^ (m - i) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ hu1.le (by linarith) _
  have hpowy : (1 + |y|) ^ (3 * i) * (1 + |y|) ^ (3 * (m - i)) = (1 + |y|) ^ (3 * m) := by
    rw [← pow_add]; congr 1; omega
  have hpowu : (1 + |u|) ^ i * (1 + |u|) ^ (m - i) = (1 + |u|) ^ m := by
    rw [← pow_add]; congr 1; omega
  calc (m.choose i : ℝ) * ‖Rd x i u y‖ * ‖Rd x (m - i) (-(u + v)) y‖
      ≤ (m.choose i : ℝ) * (B i * (1 + |y|) ^ (3 * i) / (1 + |u|) ^ i * ‖Rf x u y‖) *
        (B (m - i) * (1 + |y|) ^ (3 * (m - i)) * (1 / (1 + |u + v|) ^ (m - i)) *
          ‖Rf x (-(u + v)) y‖) := by
        gcongr
        rw [mul_one_div]; exact h2
    _ ≤ (m.choose i : ℝ) * (B i * (1 + |y|) ^ (3 * i) / (1 + |u|) ^ i * ‖Rf x u y‖) *
        (B (m - i) * (1 + |y|) ^ (3 * (m - i)) * (2 ^ (m - i) / (1 + |u|) ^ (m - i)) *
          ‖Rf x (-(u + v)) y‖) := by gcongr
    _ = (m.choose i : ℝ) * B i * (B (m - i) * 2 ^ (m - i)) *
        ((1 + |y|) ^ (3 * i) * (1 + |y|) ^ (3 * (m - i))) /
          ((1 + |u|) ^ i * (1 + |u|) ^ (m - i)) * (‖Rf x u y‖ * ‖Rf x (-(u + v)) y‖) := by
        field_simp
    _ = _ := by rw [hpowy, hpowu]

/-! ## The line integral and its derivatives -/

/-- The lag weight on the line `Re z = x`. -/
noncomputable def Wl (x v ξ u : ℝ) : ℂ := ∫ y : ℝ, Pf x v u y * Kf x ξ y

lemma continuous_Pd_y {x : ℝ} (hx : -1 ≤ x) (v : ℝ) (m : ℕ) (u : ℝ) :
    Continuous (fun y => Pd x v m u y) := by
  unfold Pd
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_const.mul (continuous_Rd_y hx i u)).mul
    (continuous_const.mul (continuous_Rd_y hx (m - i) (-(u + v))))

lemma hasDerivAt_Pd {x : ℝ} (hx : -1 ≤ x) (v : ℝ) (j : ℕ) (y u : ℝ) :
    HasDerivAt (fun u => Pd x v j u y) (Pd x v (j + 1) u y) u := by
  have e : (fun u => Pd x v j u y) = iteratedDeriv j (fun u => Pf x v u y) := by
    funext w; exact (iteratedDeriv_Pf hx v y j w).symm
  rw [e, ← iteratedDeriv_Pf hx v y (j + 1) u, iteratedDeriv_succ]
  have hc : ContDiff ℝ (j + 1 : ℕ) (fun u => Pf x v u y) :=
    (contDiff_Rf hx y (j + 1 : ℕ)).mul (contDiff_Rf_neg hx v y (j + 1 : ℕ))
  exact ((hc.differentiable_iteratedDeriv' j) u).hasDerivAt

lemma Pd_zero (x v u y : ℝ) : Pd x v 0 u y = Pf x v u y := by
  simp [Pd, Pf, Rd_zero]

lemma norm_PdK_le_local {x ξ : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (j : ℕ) {v : ℝ}
    (hv : |v| ≤ 1) (u₀ : ℝ) :
    ∃ M : ℝ, ∀ u ∈ ball u₀ 1, ∀ y : ℝ,
      ‖Pd x v j u y * Kf x ξ y‖ ≤ M * Real.exp (-(1 / 2) * y ^ 2) := by
  obtain ⟨B, hB0, hB⟩ := norm_Pd_le hx j
  obtain ⟨G₁, hG₁0, hG₁⟩ := norm_Rf_le_local hx u₀
  obtain ⟨G₂, hG₂0, hG₂⟩ := norm_Rf_le_local hx (-(u₀ + v))
  set Q : ℝ := (2 * π)⁻¹ * (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹)
  have hQ : 0 ≤ Q := by positivity
  set E : ℝ := Real.exp (((3 * j : ℕ) + π / 2) ^ 2 / 2)
  refine ⟨B * (G₁ * G₂) * Q * E, fun u hu y => ?_⟩
  rw [norm_mul]
  have hu' : -(u + v) ∈ ball (-(u₀ + v)) 1 := by
    rw [mem_ball, Real.dist_eq] at hu ⊢
    rw [show -(u + v) - -(u₀ + v) = -(u - u₀) by ring, abs_neg]; exact hu
  have h1 := hB v u y hv
  have h3 := norm_Kf_le hx0 hξ y
  have hu1 : 1 ≤ (1 + |u|) ^ j := one_le_pow₀ (one_le_one_add_abs u)
  have hpg := poly_gauss (N := 3 * j) y
  have hPd : ‖Pd x v j u y‖ ≤ B * (1 + |y|) ^ (3 * j) * (G₁ * G₂) := by
    refine h1.trans ?_
    have hRR : ‖Rf x u y‖ * ‖Rf x (-(u + v)) y‖ ≤ G₁ * G₂ :=
      mul_le_mul (hG₁ u hu y) (hG₂ _ hu' y) (norm_nonneg _) hG₁0
    calc B * (1 + |y|) ^ (3 * j) / (1 + |u|) ^ j * (‖Rf x u y‖ * ‖Rf x (-(u + v)) y‖)
        ≤ B * (1 + |y|) ^ (3 * j) / 1 * (G₁ * G₂) := by gcongr
      _ = _ := by ring
  calc ‖Pd x v j u y‖ * ‖Kf x ξ y‖ ≤ (B * (1 + |y|) ^ (3 * j) * (G₁ * G₂)) * (Q * Real.exp (-1 * y ^ 2)) :=
        mul_le_mul hPd (by simpa [Q, mul_assoc] using h3) (norm_nonneg _) (by positivity)
    _ = B * (G₁ * G₂) * Q * ((1 + |y|) ^ (3 * j) * Real.exp (-1 * y ^ 2)) := by ring
    _ ≤ B * (G₁ * G₂) * Q * (E * Real.exp (-(1 / 2) * y ^ 2)) := by gcongr
    _ = _ := by ring

lemma integrable_PdK {x ξ : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (j : ℕ) {v : ℝ}
    (hv : |v| ≤ 1) (u : ℝ) : Integrable (fun y => Pd x v j u y * Kf x ξ y) := by
  obtain ⟨M, hM⟩ := norm_PdK_le_local hx hx0 hξ j hv u
  exact Integrable.mono' ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul M)
    ((continuous_Pd_y hx v j u).mul (continuous_Kf hx0 hξ)).aestronglyMeasurable
    (Eventually.of_forall fun y => hM u (mem_ball_self one_pos) y)

theorem hasDerivAt_intPd {x ξ : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (j : ℕ) {v : ℝ}
    (hv : |v| ≤ 1) (u₀ : ℝ) :
    HasDerivAt (fun u => ∫ y : ℝ, Pd x v j u y * Kf x ξ y)
      (∫ y : ℝ, Pd x v (j + 1) u₀ y * Kf x ξ y) u₀ := by
  obtain ⟨M, hM⟩ := norm_PdK_le_local hx hx0 hξ (j + 1) hv u₀
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := u₀)
    (F := fun u y => Pd x v j u y * Kf x ξ y) (F' := fun u y => Pd x v (j + 1) u y * Kf x ξ y)
    (bound := fun y => M * Real.exp (-(1 / 2) * y ^ 2)) (ball_mem_nhds u₀ one_pos)
    (Eventually.of_forall fun u =>
      ((continuous_Pd_y hx v j u).mul (continuous_Kf hx0 hξ)).aestronglyMeasurable)
    (integrable_PdK hx hx0 hξ j hv u₀)
    ((continuous_Pd_y hx v (j + 1) u₀).mul (continuous_Kf hx0 hξ)).aestronglyMeasurable
    (Eventually.of_forall fun y u hu => hM u hu y)
    ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul M)
    (Eventually.of_forall fun y u _ => (hasDerivAt_Pd hx v j y u).mul_const (Kf x ξ y))
  exact h.2

theorem iteratedDeriv_Wl {x ξ : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) {v : ℝ}
    (hv : |v| ≤ 1) (j : ℕ) :
    iteratedDeriv j (Wl x v ξ) = fun u => ∫ y : ℝ, Pd x v j u y * Kf x ξ y := by
  induction j with
  | zero => funext u; simp [Wl, Pd_zero]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext u; exact (hasDerivAt_intPd hx hx0 hξ j hv u).deriv

theorem norm_intPd_le {x : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v u ξ : ℝ, |v| ≤ 1 → 0 < ξ →
      ‖∫ y : ℝ, Pd x v j u y * Kf x ξ y‖ ≤
        K * (Tq u * Tq (u + v) / ξ) ^ x / (1 + |u|) ^ j := by
  obtain ⟨B, hB0, hB⟩ := norm_Pd_le hx j
  obtain ⟨C, hC0, hC⟩ := norm_Gamma_ratio_line (x := x) (by linarith)
  have hp0 : 0 ≤ 2 * (11 / 2 + x) + 3 * j := by
    have := (Nat.cast_nonneg j : (0:ℝ) ≤ j); linarith
  set E : ℝ := Real.exp ((2 * (11 / 2 + x) + 3 * j + π) ^ 2 / 2)
  set J : ℝ := ∫ y : ℝ, Real.exp (-(1 / 2) * y ^ 2)
  have hJ : 0 ≤ J := integral_nonneg fun _ => (Real.exp_pos _).le
  set K : ℝ := B * (C * C) * E * ((2 * π)⁻¹ * (Real.exp (x ^ 2) * |x|⁻¹)) * J
  refine ⟨K, by positivity, fun v u ξ hv hξ => ?_⟩
  have hu1 : 0 < (1 + |u|) ^ j := by positivity
  have hTT : 0 ≤ (Tq u * Tq (u + v)) ^ x :=
    Real.rpow_nonneg (mul_nonneg (Tq_pos u).le (Tq_pos (u + v)).le) _
  set P : ℝ := B / (1 + |u|) ^ j * (C * C) * (Tq u * Tq (u + v)) ^ x *
    ((2 * π)⁻¹ * (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹)) * E
  have hpt : ∀ y : ℝ, ‖Pd x v j u y * Kf x ξ y‖ ≤ P * Real.exp (-(1 / 2) * y ^ 2) := by
    intro y
    rw [norm_mul]
    have hy1 : 0 < 1 + |y| := by positivity
    have hGp : ∀ t : ℝ, 0 < ‖Gamma (6 + t * I)‖ := fun t => norm_pos_iff.2 (Gamma_line_ne t)
    have hR : ∀ t : ℝ, ‖Rf x t y‖ ≤
        C * Tq t ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) := by
      intro t; unfold Rf; rw [norm_div, div_le_iff₀ (hGp t)]; exact hC t y
    have h1 := hB v u y hv
    have h3 := norm_Kf_le hx0 hξ y
    have hpe := RamanujanTau.SelbergKey2.poly_exp_bound2 hp0 y
    have hR2 := hR (-(u + v))
    rw [Tq_neg] at hR2
    have hTm : (Tq u * Tq (u + v)) ^ x = Tq u ^ x * Tq (u + v) ^ x :=
      Real.mul_rpow (Tq_pos u).le (Tq_pos (u + v)).le
    have hpow : (1 + |y|) ^ (3 * j) * ((1 + |y|) ^ (11 / 2 + x) * (1 + |y|) ^ (11 / 2 + x)) =
        (1 + |y|) ^ (2 * (11 / 2 + x) + 3 * j) := by
      rw [← Real.rpow_add hy1, show (2 * (11 / 2 + x) + 3 * j : ℝ) =
        ((3 * j : ℕ) : ℝ) + ((11 / 2 + x) + (11 / 2 + x)) by push_cast; ring,
        Real.rpow_add hy1 ((3 * j : ℕ) : ℝ), Real.rpow_natCast]
    have hexp : Real.exp (π * |y| / 2) * Real.exp (π * |y| / 2) = Real.exp (π * |y|) := by
      rw [← Real.exp_add]; ring_nf
    have hTu := (Real.rpow_pos_of_pos (Tq_pos u) x).le
    have hTv := (Real.rpow_pos_of_pos (Tq_pos (u + v)) x).le
    calc ‖Pd x v j u y‖ * ‖Kf x ξ y‖
        ≤ (B * (1 + |y|) ^ (3 * j) / (1 + |u|) ^ j *
            ((C * Tq u ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2))) *
              (C * Tq (u + v) ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2))))) *
          ((2 * π)⁻¹ * (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹) * Real.exp (-1 * y ^ 2)) := by
          refine mul_le_mul (h1.trans ?_) h3 (norm_nonneg _) (by positivity)
          gcongr
          · exact hR u
      _ = B / (1 + |u|) ^ j * (C * C) * (Tq u ^ x * Tq (u + v) ^ x) *
          ((2 * π)⁻¹ * (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹)) *
          (((1 + |y|) ^ (3 * j) * ((1 + |y|) ^ (11 / 2 + x) * (1 + |y|) ^ (11 / 2 + x))) *
            (Real.exp (π * |y| / 2) * Real.exp (π * |y| / 2)) * Real.exp (-1 * y ^ 2)) := by ring
      _ ≤ B / (1 + |u|) ^ j * (C * C) * (Tq u ^ x * Tq (u + v) ^ x) *
          ((2 * π)⁻¹ * (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹)) *
          (E * Real.exp (-(1 / 2) * y ^ 2)) := by
          rw [hpow, hexp]
          gcongr
      _ = _ := by simp only [P]; rw [hTm]; ring
  have hint := (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul P
  have hI := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
  rw [integral_const_mul, show (∫ a : ℝ, Real.exp (-(1 / 2) * a ^ 2)) = J from rfl] at hI
  refine hI.trans (le_of_eq ?_)
  have hdiv : (Tq u * Tq (u + v) / ξ) ^ x = (Tq u * Tq (u + v)) ^ x * ξ ^ (-x) := by
    rw [Real.div_rpow (mul_nonneg (Tq_pos u).le (Tq_pos (u + v)).le) hξ.le, Real.rpow_neg hξ.le,
      div_eq_mul_inv]
  rw [hdiv]
  simp only [P, K]
  field_simp

/-! ## Identification with `W̃` -/

lemma W2sh_eq_int (x v ξ u : ℝ) :
    W2sh (6 + u * I) (6 - ((u + v : ℝ) : ℂ) * I) ξ x /
        (Gamma (6 + u * I) * Gamma (6 - ((u + v : ℝ) : ℂ) * I)) =
      Wl x v ξ u := by
  unfold W2sh vline Wl Pf Rf Kf
  have h6 : (6 - ((u + v : ℝ) : ℂ) * I) = 6 + ((-(u + v) : ℝ) : ℂ) * I := by push_cast; ring
  rw [mul_div_assoc, ← integral_div, ← integral_const_mul]
  congr 1; funext y
  push_cast
  rw [show (6 : ℂ) - (↑u + ↑v) * I = 6 + -(↑u + ↑v) * I by ring]
  field_simp

/-- For `x > 0`: `W̃_{u,u+v}(ξ) = Wl x v ξ u`. -/
lemma Wsh_eq_Wl_pos {x ξ : ℝ} (hx : 0 < x) (hξ : 0 < ξ) (u v : ℝ) :
    Wsh u (u + v) ξ = Wl x v ξ u := by
  rw [← W2sh_eq_int]
  unfold Wsh
  congr 1
  rcases le_total x 2 with h | h
  · exact (W2sh_shift hξ hx h (by simp; linarith) (by simp; linarith)).symm
  · exact W2sh_shift hξ (by norm_num) h (by simp; norm_num) (by simp; norm_num)

/-- `W̃_{u,u+v}(ξ) = 1 + Wl (−1) v ξ u`. -/
lemma Wsh_eq_one_add_Wl {ξ : ℝ} (hξ : 0 < ξ) (u v : ℝ) :
    Wsh u (u + v) ξ = 1 + Wl (-1) v ξ u := by
  rw [← W2sh_eq_int]
  have hres := W2sh_residue (a := 6 + u * I) (b := 6 - ((u + v : ℝ) : ℂ) * I) hξ
    (by norm_num : (0:ℝ) < 2) one_pos (by simp) (by simp)
  have hG : Gamma (6 + u * I) * Gamma (6 - ((u + v : ℝ) : ℂ) * I) ≠ 0 := Gpair_ne (u, u + v)
  unfold Wsh
  rw [div_eq_iff hG, add_mul, div_mul_cancel₀ _ hG, one_mul]
  linear_combination hres

/-- Combining the two regimes. -/
lemma combine_r {A a b r f : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 < r)
    (h1 : f ≤ a * r ^ (-(A + 1))) (h2 : f ≤ b * r) :
    f ≤ 2 ^ (A + 1) * (a + b) * (1 + r) ^ (-A) := by
  have h1r : 0 < 1 + r := by linarith
  rcases le_total r 1 with hr1 | hr1
  · have hlow : (2 : ℝ) ^ (-A) ≤ (1 + r) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have h2A : (2 : ℝ) ^ (A + 1) * (2 : ℝ) ^ (-A) = 2 := by
      rw [← Real.rpow_add (by norm_num)]; norm_num
    have : f ≤ b := h2.trans (by nlinarith)
    calc f ≤ b := this
      _ ≤ 2 ^ (A + 1) * (a + b) * 2 ^ (-A) := by
          rw [mul_comm (2 ^ (A + 1)) _, mul_assoc, h2A]; nlinarith
      _ ≤ 2 ^ (A + 1) * (a + b) * (1 + r) ^ (-A) := by gcongr
  · have hle : r ^ (-(A + 1)) ≤ 2 ^ (A + 1) * (1 + r) ^ (-A) := by
      have h2r : 1 + r ≤ 2 * r := by linarith
      rw [Real.rpow_neg hr.le, Real.rpow_neg h1r.le, ← div_eq_mul_inv,
        le_div_iff₀ (Real.rpow_pos_of_pos h1r _), inv_mul_eq_div,
        div_le_iff₀ (Real.rpow_pos_of_pos hr _)]
      calc (1 + r) ^ A ≤ (2 * r) ^ A := Real.rpow_le_rpow h1r.le h2r hA
        _ = 2 ^ A * r ^ A := Real.mul_rpow (by norm_num) hr.le
        _ ≤ 2 ^ (A + 1) * r ^ (A + 1) := by
            rw [Real.rpow_add (by norm_num), Real.rpow_add hr, Real.rpow_one, Real.rpow_one]
            have : 0 < 2 ^ A * r ^ A := by positivity
            nlinarith
    calc f ≤ a * r ^ (-(A + 1)) := h1
      _ ≤ a * (2 ^ (A + 1) * (1 + r) ^ (-A)) := by gcongr
      _ ≤ 2 ^ (A + 1) * (a + b) * (1 + r) ^ (-A) := by
          have : 0 ≤ (2 : ℝ) ^ (A + 1) * (1 + r) ^ (-A) := by positivity
          nlinarith

/-- **M1(c): all `u`-derivatives of the lag weight.** For `j ≥ 1`, `A ≥ 0` there is `C` such that
for all `u`, `|v| ≤ 1`, `ξ > 0`:  `u ↦ W̃_{u,u+v}(ξ)` has `j`-th derivative with derivative the
`(j+1)`-th, and `|∂_u^j W̃_{u,u+v}(ξ)| ≤ C (1+|u|)^{−j} (1 + ξ/(T(u)T(u+v)))^{−A}`. -/
theorem Wlag_iteratedDeriv_bound {j : ℕ} (hj : 1 ≤ j) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v ξ : ℝ, |v| ≤ 1 → 0 < ξ →
      HasDerivAt (iteratedDeriv j (fun w : ℝ => Wsh w (w + v) ξ))
        (iteratedDeriv (j + 1) (fun w : ℝ => Wsh w (w + v) ξ) u) u ∧
      ‖iteratedDeriv j (fun w : ℝ => Wsh w (w + v) ξ) u‖ ≤
        C / (1 + |u|) ^ j * (1 + ξ / (Tq u * Tq (u + v))) ^ (-A) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := norm_intPd_le (x := A + 1) (by linarith) (ne_of_gt (by linarith)) j
  obtain ⟨K₂, hK₂0, hK₂⟩ := norm_intPd_le (x := -1) le_rfl (by norm_num) j
  refine ⟨2 ^ (A + 1) * (K₁ + K₂), by positivity, fun u v ξ hv hξ => ?_⟩
  have hx1 : (0:ℝ) < A + 1 := by linarith
  have e1 : ∀ k : ℕ, iteratedDeriv k (fun w : ℝ => Wsh w (w + v) ξ) =
      fun u => ∫ y : ℝ, Pd (A + 1) v k u y * Kf (A + 1) ξ y := by
    intro k
    have : (fun w : ℝ => Wsh w (w + v) ξ) = Wl (A + 1) v ξ := by
      funext w; exact Wsh_eq_Wl_pos hx1 hξ w v
    rw [this, iteratedDeriv_Wl (by linarith) hx1.ne' hξ hv]
  have e2 : iteratedDeriv j (fun w : ℝ => Wsh w (w + v) ξ) u =
      ∫ y : ℝ, Pd (-1) v j u y * Kf (-1) ξ y := by
    have : (fun w : ℝ => Wsh w (w + v) ξ) = fun w => 1 + Wl (-1) v ξ w := by
      funext w; exact Wsh_eq_one_add_Wl hξ w v
    rw [this, iteratedDeriv_const_add (by omega), iteratedDeriv_Wl le_rfl (by norm_num) hξ hv]
  refine ⟨?_, ?_⟩
  · rw [e1 j, e1 (j + 1)]
    exact hasDerivAt_intPd (by linarith) hx1.ne' hξ j hv u
  have hpj : 0 < (1 + |u|) ^ j := by positivity
  have hTT : 0 < Tq u * Tq (u + v) := mul_pos (Tq_pos u) (Tq_pos (u + v))
  set r : ℝ := ξ / (Tq u * Tq (u + v))
  have hr : 0 < r := div_pos hξ hTT
  set f : ℝ := ‖iteratedDeriv j (fun w : ℝ => Wsh w (w + v) ξ) u‖ * (1 + |u|) ^ j
  have hf1 : f ≤ K₁ * r ^ (-(A + 1)) := by
    simp only [f]; rw [e1 j, ← le_div_iff₀ hpj]
    refine (hK₁ v u ξ hv hξ).trans (le_of_eq ?_)
    rw [show Tq u * Tq (u + v) / ξ = r⁻¹ by simp only [r]; rw [inv_div],
      Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
  have hf2 : f ≤ K₂ * r := by
    simp only [f]; rw [e2, ← le_div_iff₀ hpj]
    refine (hK₂ v u ξ hv hξ).trans (le_of_eq ?_)
    rw [show Tq u * Tq (u + v) / ξ = r⁻¹ by simp only [r]; rw [inv_div],
      Real.inv_rpow hr.le, Real.rpow_neg_one, inv_inv]
  have hc := combine_r hA hK₁0 hK₂0 hr hf1 hf2
  rw [div_mul_eq_mul_div, le_div_iff₀ hpj]
  linarith

end RamanujanTau.SelbergKey3
