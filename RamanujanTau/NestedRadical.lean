import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Ramanujan's nested radical, with a quantitative convergence proof

The finite truncations end in `a`, not in an unspecified infinite tail.
For `a > 0` and `x ≥ 0`, the radical with constant radicand `a²` and
successive multipliers `x, x+a, x+2a, ...` converges to `x+a`.
In particular, `sqrt (1 + 2 * sqrt (1 + 3 * sqrt (1 + ...))) = 3`.
-/

namespace Ramanujan.NestedRadical
open Filter
open scoped Topology

/-- A depth-zero truncation is the innermost square root `sqrt (a²) = a`
when `a ≥ 0`. Each further step adds one multiplier. -/
noncomputable def trunc (a : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => a
  | N+1, x => Real.sqrt (a^2+x*trunc a N (x+a))

@[simp] theorem trunc_zero (a x : ℝ) : trunc a 0 x = a := rfl

@[simp] theorem trunc_succ (a x : ℝ) (N : ℕ) :
    trunc a (N+1) x = Real.sqrt (a^2+x*trunc a N (x+a)) := rfl

theorem bounds {a : ℝ} (ha : 0 ≤ a) (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    a ≤ trunc a N x ∧ trunc a N x ≤ x+a := by
  induction N generalizing x with
  | zero => simp; exact hx
  | succ N ih =>
    obtain ⟨hlo,hhi⟩ := ih (x := x+a) (by positivity)
    rw [trunc_succ]
    constructor
    · calc
        a = Real.sqrt (a^2) := (Real.sqrt_sq ha).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
    · apply (Real.sqrt_le_left (by positivity : 0 ≤ x+a)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hhi hx]

/-- Rationalizing one square root gives the exact propagation of the error. -/
theorem error_identity {a : ℝ} (ha : 0 ≤ a) (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x+a-trunc a (N+1) x)*(x+a+trunc a (N+1) x) =
      x*(x+2*a-trunc a N (x+a)) := by
  have hlo := (bounds ha N (x := x+a) (by positivity)).1
  have hs : (trunc a (N+1) x)^2 = a^2+x*trunc a N (x+a) := by
    rw [trunc_succ,Real.sq_sqrt (by nlinarith [mul_nonneg hx (le_trans ha hlo)])]
  nlinarith [hs]

/-- Every finite truncation has an explicit error tending to zero. -/
theorem error_bound {a : ℝ} (ha : 0 < a) (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x+a-trunc a N x ∧
      x+a-trunc a N x ≤ x*(x+a)/(x+((N : ℝ)+1)*a) := by
  refine ⟨sub_nonneg.mpr (bounds ha.le N hx).2,?_⟩
  induction N generalizing x with
  | zero =>
    simp only [trunc_zero,Nat.cast_zero,zero_add,one_mul,add_sub_cancel_right]
    rw [mul_div_cancel_right₀ _ (by positivity : x+a ≠ 0)]
  | succ N ih =>
    have hstep : x+a-trunc a (N+1) x ≤
        x/(x+2*a)*(x+2*a-trunc a N (x+a)) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (by positivity : 0 < x+2*a)).mpr
      have hb := bounds ha.le (N+1) hx
      have he := error_identity ha.le N hx
      nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (sub_nonneg.mpr hb.1)]
    calc
      x+a-trunc a (N+1) x ≤ x/(x+2*a)*(x+2*a-trunc a N (x+a)) := hstep
      _ ≤ x/(x+2*a)*((x+a)*(x+2*a)/(x+a+((N : ℝ)+1)*a)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [add_assoc,← two_mul a] using ih (x := x+a) (by positivity)
      _ = x*(x+a)/(x+(((N+1 : ℕ) : ℝ)+1)*a) := by
        push_cast
        have h1 : x+2*a ≠ 0 := by positivity
        have h2 : x+a+((N : ℝ)+1)*a ≠ 0 := by positivity
        have h3 : x+((N : ℝ)+1+1)*a ≠ 0 := by positivity
        field_simp
        ring

/-- The infinite radical is defined as the limit of the stated finite truncations. -/
theorem tendsto_trunc {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    Tendsto (fun N => trunc a N x) atTop (𝓝 (x+a)) := by
  have hd : Tendsto (fun N : ℕ => x+((N : ℝ)+1)*a) atTop atTop := by
    have h := (tendsto_atTop_add_const_right atTop (1 : ℝ)
      tendsto_natCast_atTop_atTop).atTop_mul_const ha
    exact tendsto_atTop_add_const_left _ _ h
  have hz : Tendsto (fun N : ℕ => x*(x+a)/(x+((N : ℝ)+1)*a)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hd
  have he : Tendsto (fun N => x+a-trunc a N x) atTop (𝓝 0) :=
    squeeze_zero (fun N => (error_bound ha N hx).1)
      (fun N => (error_bound ha N hx).2) hz
  simpa only [sub_sub_cancel,sub_zero] using he.const_sub (x+a)

/-- Ramanujan's classical nested radical equals three. -/
theorem ramanujan_radical : Tendsto (fun N => trunc 1 N 2) atTop (𝓝 3) := by
  have h := tendsto_trunc (a := 1) (x := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- An explicit certified error for the classical radical. -/
theorem ramanujan_radical_error (N : ℕ) :
    0 ≤ 3-trunc 1 N 2 ∧ 3-trunc 1 N 2 ≤ 6/((N : ℝ)+3) := by
  have h := error_bound (a := 1) (by norm_num) N (x := 2) (by norm_num)
  norm_num [add_assoc,add_comm,add_left_comm] at h
  constructor <;> linarith [h.1,h.2]

end Ramanujan.NestedRadical
