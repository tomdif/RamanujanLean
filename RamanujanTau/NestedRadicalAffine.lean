import RamanujanTau.NestedRadical
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Affine nested radicals and exponential error bounds

For `d > 0`, `0 ≤ h ≤ d`, and `x ≥ 0`, successive multipliers `x+n*h`
and radicands `d²+(d-h)*(x+n*h)` give an infinite radical with value `x+d`.
The proof uses finite truncations and an explicit logarithmic error bound.
-/

namespace Ramanujan.NestedRadical
open Filter
open scoped Topology

/-- This classifies the affine radicands compatible with a linear exact tail.
It is an algebraic statement, separate from the convergence theorem below. -/
theorem affine_identity_iff (A B d h : ℝ) :
    (∀ x : ℝ, 0 ≤ x → (x+d)^2 = A+B*x+x*(x+h+d)) ↔
      A=d^2 ∧ B=d-h := by
  constructor
  · intro H
    have h0 := H 0 (by norm_num)
    have h1 := H 1 (by norm_num)
    constructor <;> nlinarith
  · rintro ⟨rfl,rfl⟩ x _
    ring

/-- The finite radical stops at the square root of its last radicand. -/
noncomputable def affineTrunc (d h : ℝ) : ℕ → ℝ → ℝ
  | 0, x => Real.sqrt (d^2+(d-h)*x)
  | N+1, x => Real.sqrt (d^2+(d-h)*x+x*affineTrunc d h N (x+h))

@[simp] theorem affineTrunc_zero (d h x : ℝ) :
    affineTrunc d h 0 x = Real.sqrt (d^2+(d-h)*x) := rfl

@[simp] theorem affineTrunc_succ (d h x : ℝ) (N : ℕ) :
    affineTrunc d h (N+1) x =
      Real.sqrt (d^2+(d-h)*x+x*affineTrunc d h N (x+h)) := rfl

theorem affine_bounds {d h : ℝ} (hd : 0 ≤ d) (hh : 0 ≤ h) (hhd : h ≤ d)
    (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    d ≤ affineTrunc d h N x ∧ affineTrunc d h N x ≤ x+d := by
  have hdh : 0 ≤ d-h := sub_nonneg.mpr hhd
  have hc : 0 ≤ (d-h)*x := mul_nonneg (sub_nonneg.mpr hhd) hx
  induction N generalizing x with
  | zero =>
    rw [affineTrunc_zero]
    constructor
    · calc
        d = Real.sqrt (d^2) := (Real.sqrt_sq hd).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
    · apply (Real.sqrt_le_left (by positivity : 0 ≤ x+d)).mpr
      nlinarith [mul_nonneg hx (show 0 ≤ x+d+h by positivity)]
  | succ N ih =>
    obtain ⟨hlo,hhi⟩ := ih (x := x+h) (by positivity) (by positivity)
    rw [affineTrunc_succ]
    constructor
    · calc
        d = Real.sqrt (d^2) := (Real.sqrt_sq hd).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hx (le_trans hd hlo)])
    · apply (Real.sqrt_le_left (by positivity : 0 ≤ x+d)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hhi hx]

/-- An absolute error is bounded by the corresponding logarithmic gap. -/
theorem error_le_log_gap {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    s-r ≤ s*(Real.log s-Real.log r) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hr hs)
  rw [Real.log_div hr.ne' hs.ne'] at h
  have hmul := mul_le_mul_of_nonneg_left h hs.le
  have he : s*(r/s-1)=r-s := by field_simp
  rw [he] at hmul
  linarith

/-- One positive square-root layer halves the logarithmic error. -/
theorem log_gap_contract {c b s t r y : ℝ}
    (hc : 0 ≤ c) (hs : 0 < s) (ht : 0 < t) (hr : 0 < r) (hy : 0 < y)
    (hyt : y ≤ t) (hsq : s^2=c+b*t) (hrq : r^2=c+b*y) :
    Real.log s-Real.log r ≤ (Real.log t-Real.log y)/2 := by
  have hprod : s^2*y ≤ r^2*t := by
    rw [hsq,hrq]
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hyt)]
  have hlog := Real.log_le_log (by positivity : 0 < s^2*y) hprod
  rw [Real.log_mul (by positivity) hy.ne', Real.log_mul (by positivity) ht.ne',
    Real.log_pow,Real.log_pow] at hlog
  norm_num at hlog
  linarith

/-- A quantitative bound on the logarithmic gap, uniform over the whole family. -/
theorem affine_log_gap {d h : ℝ} (hd : 0 < d) (hh : 0 ≤ h) (hhd : h ≤ d)
    (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Real.log (x+d)-Real.log (affineTrunc d h N x) ≤
      (Real.log (x+(N : ℝ)*h+d)-Real.log d)/2^N := by
  induction N generalizing x with
  | zero =>
    simp only [Nat.cast_zero,zero_mul,add_zero,pow_zero,div_one]
    have hlog := Real.log_le_log hd (affine_bounds hd.le hh hhd 0 hx).1
    linarith
  | succ N ih =>
    have ht := affine_bounds hd.le hh hhd N (x := x+h) (by positivity)
    have hr := affine_bounds hd.le hh hhd (N+1) hx
    have hc : 0 ≤ d^2+(d-h)*x :=
      add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hhd) hx)
    have hrq : (affineTrunc d h (N+1) x)^2 =
        d^2+(d-h)*x+x*affineTrunc d h N (x+h) := by
      rw [affineTrunc_succ,Real.sq_sqrt (by nlinarith [mul_nonneg hx (hd.le.trans ht.1)])]
    have hs := log_gap_contract hc (by positivity : 0 < x+d)
      (by positivity : 0 < x+h+d) (hd.trans_le hr.1) (hd.trans_le ht.1)
      ht.2 (by ring : (x+d)^2 = d^2+(d-h)*x+x*(x+h+d)) hrq
    calc
      Real.log (x+d)-Real.log (affineTrunc d h (N+1) x) ≤
          (Real.log (x+h+d)-Real.log (affineTrunc d h N (x+h)))/2 := hs
      _ ≤ ((Real.log (x+h+(N : ℝ)*h+d)-Real.log d)/2^N)/2 :=
        div_le_div_of_nonneg_right (ih (x := x+h) (by positivity)) (by norm_num)
      _ = (Real.log (x+((N+1 : ℕ) : ℝ)*h+d)-Real.log d)/2^(N+1) := by
        simp only [Nat.cast_add,Nat.cast_one,pow_succ]
        rw [show x+h+(N : ℝ)*h+d=x+((N : ℝ)+1)*h+d by ring]
        ring

/-- Exponentially decreasing error, with only a logarithmic factor in the depth. -/
theorem affine_error_bound {d h : ℝ} (hd : 0 < d) (hh : 0 ≤ h) (hhd : h ≤ d)
    (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x+d-affineTrunc d h N x ∧
      x+d-affineTrunc d h N x ≤
        (x+d)*(Real.log (x+(N : ℝ)*h+d)-Real.log d)/2^N := by
  have hb := affine_bounds hd.le hh hhd N hx
  refine ⟨sub_nonneg.mpr hb.2,?_⟩
  calc
    x+d-affineTrunc d h N x ≤
        (x+d)*(Real.log (x+d)-Real.log (affineTrunc d h N x)) :=
      error_le_log_gap (by positivity) (hd.trans_le hb.1)
    _ ≤ (x+d)*((Real.log (x+(N : ℝ)*h+d)-Real.log d)/2^N) :=
      mul_le_mul_of_nonneg_left (affine_log_gap hd hh hhd N hx) (by positivity)
    _ = _ := by ring

/-- A simpler bound convenient for proving convergence by geometric decay. -/
theorem affine_error_linear_bound {d h : ℝ} (hd : 0 < d) (hh : 0 ≤ h) (hhd : h ≤ d)
    (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x+d-affineTrunc d h N x ≤
      (x+d)/d*(x/2^N+h*((N : ℝ)/2^N)) := by
  have ht : 0 < x+(N : ℝ)*h+d := by positivity
  have hl := Real.log_le_sub_one_of_pos (div_pos ht hd)
  rw [Real.log_div ht.ne' hd.ne'] at hl
  calc
    x+d-affineTrunc d h N x ≤
        (x+d)*(Real.log (x+(N : ℝ)*h+d)-Real.log d)/2^N :=
      (affine_error_bound hd hh hhd N hx).2
    _ ≤ (x+d)*((x+(N : ℝ)*h+d)/d-1)/2^N := by
      gcongr
    _ = _ := by field_simp; ring

/-- The affine family converges, including the constant-step-zero case. -/
theorem tendsto_affineTrunc {d h x : ℝ} (hd : 0 < d) (hh : 0 ≤ h)
    (hhd : h ≤ d) (hx : 0 ≤ x) :
    Tendsto (fun N => affineTrunc d h N x) atTop (𝓝 (x+d)) := by
  have hX : Tendsto (fun N : ℕ => x/(2 : ℝ)^N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hN : Tendsto (fun N : ℕ => (N : ℝ)/(2 : ℝ)^N) atTop (𝓝 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ)<2)
  have hz : Tendsto (fun N : ℕ => (x+d)/d*(x/2^N+h*((N : ℝ)/2^N))) atTop (𝓝 0) := by
    simpa using (hX.add (hN.const_mul h)).const_mul ((x+d)/d)
  have he : Tendsto (fun N => x+d-affineTrunc d h N x) atTop (𝓝 0) :=
    squeeze_zero (fun N => sub_nonneg.mpr (affine_bounds hd.le hh hhd N hx).2)
      (fun N => affine_error_linear_bound hd hh hhd N hx) hz
  simpa only [sub_sub_cancel,sub_zero] using he.const_sub (x+d)

theorem affineTrunc_self {a : ℝ} (ha : 0 ≤ a) (N : ℕ) (x : ℝ) :
    affineTrunc a a N x = trunc a N x := by
  induction N generalizing x with
  | zero => simp [Real.sqrt_sq ha]
  | succ N ih => simp [ih]

/-- The sharper logarithmic error bound for the classical radical. -/
theorem ramanujan_radical_fast_error (N : ℕ) :
    0 ≤ 3-trunc 1 N 2 ∧
      3-trunc 1 N 2 ≤ 3*Real.log ((N : ℝ)+3)/2^N := by
  have h := affine_error_bound (d := 1) (h := 1) (by norm_num) (by norm_num)
    (by norm_num) N (x := 2) (by norm_num)
  rw [affineTrunc_self (by norm_num)] at h
  norm_num [add_assoc,add_comm,add_left_comm] at h
  constructor <;> linarith [h.1,h.2]

/-- Ramanujan's other classical radical, starting with `sqrt (6+2*sqrt (7+...))`. -/
theorem ramanujan_second_radical :
    Tendsto (fun N => affineTrunc 2 1 N 2) atTop (𝓝 4) := by
  have h := tendsto_affineTrunc (d := 2) (h := 1) (x := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- Forty inserted multipliers already give a certified error below 10⁻¹⁰. -/
theorem ramanujan_radical_40_accuracy :
    0 ≤ 3-trunc 1 40 2 ∧ 3-trunc 1 40 2 < 1/10^10 := by
  have hlog : Real.log 43 ≤ 6 := by
    calc
      Real.log 43 ≤ Real.log ((2 : ℝ)^6) :=
        Real.log_le_log (by norm_num) (by norm_num)
      _ = 6*Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 6 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
        linarith
  have h := ramanujan_radical_fast_error 40
  norm_num at h ⊢
  constructor <;> linarith [h.1,h.2]

end Ramanujan.NestedRadical
