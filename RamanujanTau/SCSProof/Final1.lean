/-
# Final step 1: uniform bound for `A(N)` and the weight `f(t) = t^{−11/2}(t+h)^{−11/2}`
-/
import RamanujanTau.SCSProof.Tauber6

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open Finset MeasureTheory Set
open RamanujanTau.SubconvexityCond RamanujanTau.RankinError
open scoped Real

/-- **Uniform bound** `|A(N)| ≤ C h (N+h)^{12−ρ}` for all `N`. -/
theorem Asum_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℕ, 1 ≤ h → ∀ N : ℕ,
    |Asum h N| ≤ C * h * ((N : ℝ) + h) ^ (12 - ρ) := by
  obtain ⟨C₁, hC₁, hL⟩ := Asum_bound_large
  obtain ⟨A, hA0, hA⟩ := sum_aabs_le
  refine ⟨C₁ + 2 * A, by positivity, fun h hh N => ?_⟩
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hM1 : 1 ≤ (N : ℝ) + h := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hMp : 0 ≤ ((N : ℝ) + h) ^ (12 - ρ) := Real.rpow_nonneg (by linarith) _
  rcases le_or_gt h N with hN | hN
  · refine (hL h hh N hN).trans ?_
    have : 0 ≤ (2 * A) * h * ((N : ℝ) + h) ^ (12 - ρ) := by positivity
    nlinarith
  · have hNR : (N : ℝ) < h := by exact_mod_cast hN
    have h1 : |Asum h N| ≤ A * ((N : ℝ) + h) ^ 12 := by
      unfold Asum
      refine (abs_sum_le_sum_abs _ _).trans ?_
      simp_rw [abs_aR]; exact hA h N
    have h2 : ((N : ℝ) + h) ^ 12 ≤ 2 * h * ((N : ℝ) + h) ^ (12 - ρ) := by
      have hρ := ρ_pos; have hρ8 := ρ_le
      have e : ((N : ℝ) + h) ^ 12 = ((N : ℝ) + h) ^ (12 - ρ) * ((N : ℝ) + h) ^ ρ := by
        rw [← Real.rpow_add (by linarith), ← Real.rpow_natCast]; norm_num
      rw [e]
      have h3 : ((N : ℝ) + h) ^ ρ ≤ 2 * h := by
        calc ((N : ℝ) + h) ^ ρ ≤ ((N : ℝ) + h) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
          _ = (N : ℝ) + h := Real.rpow_one _
          _ ≤ 2 * h := by linarith
      calc ((N : ℝ) + h) ^ (12 - ρ) * ((N : ℝ) + h) ^ ρ ≤ ((N : ℝ) + h) ^ (12 - ρ) * (2 * h) := by
            gcongr
        _ = 2 * h * ((N : ℝ) + h) ^ (12 - ρ) := by ring
    calc |Asum h N| ≤ A * (2 * h * ((N : ℝ) + h) ^ (12 - ρ)) := h1.trans (by gcongr)
      _ ≤ (C₁ + 2 * A) * h * ((N : ℝ) + h) ^ (12 - ρ) := by
          have : 0 ≤ C₁ * h * ((N : ℝ) + h) ^ (12 - ρ) := by positivity
          nlinarith

/-- The weight `f(t) = t^{−11/2}(t+h)^{−11/2}`. -/
noncomputable def wf (h : ℕ) (t : ℝ) : ℝ := t ^ (-(11 / 2 : ℝ)) * (t + h) ^ (-(11 / 2 : ℝ))

/-- Its derivative for `t > 0`. -/
noncomputable def wf' (h : ℕ) (t : ℝ) : ℝ :=
  (-(11 / 2 : ℝ)) * t ^ (-(11 / 2 : ℝ) - 1) * (t + h) ^ (-(11 / 2 : ℝ)) +
    t ^ (-(11 / 2 : ℝ)) * ((-(11 / 2 : ℝ)) * (t + h) ^ (-(11 / 2 : ℝ) - 1))

lemma hasDerivAt_wf (h : ℕ) {t : ℝ} (ht : 0 < t) : HasDerivAt (wf h) (wf' h t) t := by
  have h1 := Real.hasDerivAt_rpow_const (x := t) (p := -(11 / 2 : ℝ)) (Or.inl ht.ne')
  have h2 : HasDerivAt (fun t : ℝ => (t + h) ^ (-(11 / 2 : ℝ)))
      ((-(11 / 2 : ℝ)) * (t + h) ^ (-(11 / 2 : ℝ) - 1)) t := by
    have := (Real.hasDerivAt_rpow_const (x := t + h) (p := -(11 / 2 : ℝ))
      (Or.inl (by have := Nat.cast_nonneg (α := ℝ) h; linarith))).comp t
      ((hasDerivAt_id t).add_const (h : ℝ))
    simpa using this
  exact h1.mul h2

lemma deriv_wf (h : ℕ) {t : ℝ} (ht : 0 < t) : deriv (wf h) t = wf' h t := (hasDerivAt_wf h ht).deriv

lemma continuousOn_wf' (h : ℕ) : ContinuousOn (wf' h) (Ioi 0) := by
  intro t ht
  have ht0 : 0 < t := ht
  have hth : 0 < t + h := by have := Nat.cast_nonneg (α := ℝ) h; linarith
  unfold wf'
  refine ContinuousAt.continuousWithinAt ?_
  have c1 : ContinuousAt (fun t : ℝ => t ^ (-(11 / 2 : ℝ) - 1)) t :=
    Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')
  have c2 : ContinuousAt (fun t : ℝ => t ^ (-(11 / 2 : ℝ))) t :=
    Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')
  have c3 : ContinuousAt (fun t : ℝ => (t + h) ^ (-(11 / 2 : ℝ))) t :=
    (Real.continuousAt_rpow_const (t + h) _ (Or.inl hth.ne')).comp
      (f := fun t : ℝ => t + (h : ℝ)) (continuous_add_const _).continuousAt
  have c4 : ContinuousAt (fun t : ℝ => (t + h) ^ (-(11 / 2 : ℝ) - 1)) t :=
    (Real.continuousAt_rpow_const (t + h) _ (Or.inl hth.ne')).comp
      (f := fun t : ℝ => t + (h : ℝ)) (continuous_add_const _).continuousAt
  exact ((continuousAt_const.mul c1).mul c3).add (c2.mul (continuousAt_const.mul c4))

/-- `|f'(t)| ≤ 11 t^{−13/2}(t+h)^{−11/2}`. -/
lemma abs_wf'_le (h : ℕ) {t : ℝ} (ht : 0 < t) :
    |wf' h t| ≤ 11 * t ^ (-(13 / 2 : ℝ)) * (t + h) ^ (-(11 / 2 : ℝ)) := by
  have hth : t ≤ t + h := by have := Nat.cast_nonneg (α := ℝ) h; linarith
  have hth0 : 0 < t + h := by linarith
  unfold wf'
  have e1 : (-(11 / 2 : ℝ)) - 1 = -(13 / 2 : ℝ) := by norm_num
  rw [e1]
  have p1 : 0 < t ^ (-(13 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  have p2 : 0 < (t + h) ^ (-(11 / 2 : ℝ)) := Real.rpow_pos_of_pos hth0 _
  have p3 : 0 < t ^ (-(11 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  have p4 : 0 < (t + h) ^ (-(13 / 2 : ℝ)) := Real.rpow_pos_of_pos hth0 _
  have key : t ^ (-(11 / 2 : ℝ)) * (t + h) ^ (-(13 / 2 : ℝ)) ≤
      t ^ (-(13 / 2 : ℝ)) * (t + h) ^ (-(11 / 2 : ℝ)) := by
    have a1 : t ^ (-(11 / 2 : ℝ)) = t ^ (-(13 / 2 : ℝ)) * t := by
      rw [← Real.rpow_add_one ht.ne']; norm_num
    have a2 : (t + h) ^ (-(11 / 2 : ℝ)) = (t + h) ^ (-(13 / 2 : ℝ)) * (t + h) := by
      rw [← Real.rpow_add_one hth0.ne']; norm_num
    rw [a1, a2]
    have : t ^ (-(13 / 2 : ℝ)) * (t + h) ^ (-(13 / 2 : ℝ)) * t ≤
        t ^ (-(13 / 2 : ℝ)) * (t + h) ^ (-(13 / 2 : ℝ)) * (t + h) := by gcongr
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

end RamanujanTau.SCSProof
