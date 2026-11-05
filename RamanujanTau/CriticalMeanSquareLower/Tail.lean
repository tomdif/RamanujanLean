/-
# From the weighted mean square to `∫_0^T`: dyadic tail control
-/
import RamanujanTau.CriticalMeanSquareLower.Weight

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquareLower

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.HeckeL RamanujanTau.CriticalMeanSquare
open scoped Real

/-- The one-sided weight `(1+t)¹¹ e^{−2δt} |L(6+it)|²`. -/
noncomputable def Phi0 (δ t : ℝ) : ℝ := (1 + t) ^ 11 * Real.exp (-2 * δ * t) * Lsq t

lemma continuous_Phi0 (δ : ℝ) : Continuous (Phi0 δ) :=
  (by fun_prop : Continuous fun t : ℝ => (1 + t) ^ 11 * Real.exp (-2 * δ * t)).mul continuous_Lsq

/-- `∫_ℝ |Λ|² e^{2βt} ≤ 2 C_Γ ∫_0^∞ Φ₀`. -/
theorem lhs_le {CΓ : ℝ} (hCΓ : 0 < CΓ) (hw : ∀ β : ℝ, 0 ≤ β → ∀ t : ℝ,
      ‖heckeLambda (6 + t * I)‖ ^ 2 * Real.exp (2 * β * t) ≤
        CΓ * ((1 + |t|) ^ 11 * Real.exp (-2 * (π / 2 - β) * |t|) * Lsq t))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 2) :
    ∫ t : ℝ, ‖heckeLambda (6 + t * I)‖ ^ 2 * Real.exp (2 * β * t) ≤
      2 * CΓ * ∫ t in Ioi 0, Phi0 (π / 2 - β) t := by
  have hδ : 0 < π / 2 - β := by linarith
  have hmaj := (integrable_major hδ).const_mul CΓ
  calc ∫ t : ℝ, ‖heckeLambda (6 + t * I)‖ ^ 2 * Real.exp (2 * β * t)
      ≤ ∫ t : ℝ, CΓ * ((1 + |t|) ^ 11 * Real.exp (-2 * (π / 2 - β) * |t|) * Lsq t) :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => by positivity) hmaj
          (Eventually.of_forall fun t => hw β hβ0 t)
    _ = CΓ * ∫ t : ℝ, Phi0 (π / 2 - β) |t| := by
        rw [integral_const_mul]
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        simp only [Phi0, abs_abs, Lsq_abs]
    _ = 2 * CΓ * ∫ t in Ioi 0, Phi0 (π / 2 - β) t := by
        rw [integral_comp_abs (f := Phi0 (π / 2 - β))]; ring

/-- The numerical dyadic tail bound. -/
lemma tail_num {δ T : ℝ} (hT : 1 ≤ T) (hK : 1 ≤ δ * T) (n : ℕ) :
    (1 + 2 * (2 ^ n * T)) ^ 11 * Real.exp (-2 * δ * (2 ^ n * T)) *
        ((2 ^ n * T) * (1 + Real.log (2 ^ n * T))) ≤
      3 ^ 11 * (Nat.factorial 13 : ℝ) * Real.exp 1 * Real.exp (-2 * δ * T) * T ^ 12 *
        (1 + Real.log T) * (1 / 2) ^ n := by
  set x : ℝ := 2 ^ n with hx
  have hx1 : 1 ≤ x := one_le_pow₀ (by norm_num)
  have hxn : (n : ℝ) + 1 ≤ x := by
    rw [hx]
    have : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    exact_mod_cast this
  have hT0 : 0 < T := by linarith
  have hlogT := Real.log_nonneg hT
  set X : ℝ := x * T with hXdef
  have hX1 : 1 ≤ X := by rw [hXdef]; nlinarith
  -- (1 + 2X)^11 · X ≤ 3^11 x^12 T^12
  have h1 : (1 + 2 * X) ^ 11 * X ≤ 3 ^ 11 * x ^ 12 * T ^ 12 := by
    have : 1 + 2 * X ≤ 3 * X := by linarith
    calc (1 + 2 * X) ^ 11 * X ≤ (3 * X) ^ 11 * X := by gcongr
      _ = 3 ^ 11 * x ^ 12 * T ^ 12 := by rw [hXdef]; ring
  -- 1 + log X ≤ (1+n)(1+log T)
  have h2 : 1 + Real.log X ≤ ((n : ℝ) + 1) * (1 + Real.log T) := by
    rw [hXdef, Real.log_mul (by positivity) hT0.ne', hx, Real.log_pow]
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have : (n : ℝ) * Real.log 2 ≤ n := by
      have := Nat.cast_nonneg (α := ℝ) n
      nlinarith
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  -- x^12 (n+1) e^{−2Kx} ≤ 13! e · e^{−2K} (1/2)^n
  set K : ℝ := δ * T with hKdef
  have h3 : x ^ 12 * ((n : ℝ) + 1) * Real.exp (-2 * K * x) ≤
      (Nat.factorial 13 : ℝ) * Real.exp 1 * Real.exp (-2 * K) * (1 / 2) ^ n := by
    have hf := Real.pow_div_factorial_le_exp x (by linarith) 13
    rw [div_le_iff₀ (by positivity)] at hf
    have hx13 : x ^ 12 * ((n : ℝ) + 1) ≤ x ^ 13 := by
      calc x ^ 12 * ((n : ℝ) + 1) ≤ x ^ 12 * x := by gcongr
        _ = x ^ 13 := by ring
    have he : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
      have := Real.add_one_le_exp 1; linarith
    have hhalf : Real.exp (-(n : ℝ)) ≤ (1 / 2) ^ n := by
      rw [show -(n : ℝ) = n * (-1) by ring, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos _).le he n
    have hexp : Real.exp x * Real.exp (-2 * K * x) ≤ Real.exp 1 * Real.exp (-2 * K) *
        Real.exp (-(n : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : (2 * K - 1) * ((n : ℝ) + 1) ≤ (2 * K - 1) * x :=
        mul_le_mul_of_nonneg_left hxn (by linarith)
      nlinarith
    calc x ^ 12 * ((n : ℝ) + 1) * Real.exp (-2 * K * x)
        ≤ x ^ 13 * Real.exp (-2 * K * x) := by gcongr
      _ ≤ Real.exp x * (Nat.factorial 13 : ℝ) * Real.exp (-2 * K * x) := by gcongr
      _ = (Nat.factorial 13 : ℝ) * (Real.exp x * Real.exp (-2 * K * x)) := by ring
      _ ≤ (Nat.factorial 13 : ℝ) * (Real.exp 1 * Real.exp (-2 * K) * Real.exp (-(n : ℝ))) := by
          gcongr
      _ ≤ (Nat.factorial 13 : ℝ) * (Real.exp 1 * Real.exp (-2 * K) * (1 / 2) ^ n) := by gcongr
      _ = _ := by ring
  have heX : Real.exp (-2 * δ * X) = Real.exp (-2 * K * x) := by
    congr 1; rw [hXdef, hKdef]; ring
  have heT : Real.exp (-2 * δ * T) = Real.exp (-2 * K) := by
    congr 1; rw [hKdef]; ring
  rw [heX, heT]
  have hlX : 0 ≤ 1 + Real.log X := by linarith [Real.log_nonneg hX1]
  have hE0 : 0 ≤ Real.exp (-2 * K * x) := (Real.exp_pos _).le
  calc (1 + 2 * X) ^ 11 * Real.exp (-2 * K * x) * (X * (1 + Real.log X))
      = ((1 + 2 * X) ^ 11 * X) * (1 + Real.log X) * Real.exp (-2 * K * x) := by ring
    _ ≤ (3 ^ 11 * x ^ 12 * T ^ 12) * (((n : ℝ) + 1) * (1 + Real.log T)) *
          Real.exp (-2 * K * x) := by gcongr
    _ = 3 ^ 11 * T ^ 12 * (1 + Real.log T) *
          (x ^ 12 * ((n : ℝ) + 1) * Real.exp (-2 * K * x)) := by ring
    _ ≤ 3 ^ 11 * T ^ 12 * (1 + Real.log T) *
          ((Nat.factorial 13 : ℝ) * Real.exp 1 * Real.exp (-2 * K) * (1 / 2) ^ n) := by gcongr
    _ = _ := by ring

/-- **Tail control**: `∫_0^∞ Φ₀ ≤ (1+T)¹¹ ∫_0^T |L|² + 2·Cd·3¹¹·13!·e · e^{−2δT} T¹² (1+log T)`. -/
theorem ioi_le {Cd : ℝ} (hCd0 : 0 ≤ Cd)
    (hCd : ∀ T : ℝ, 1 ≤ T → ∫ t in Icc T (2 * T), ‖tauL (6 + t * I)‖ ^ 2 ≤ Cd * T * (1 + Real.log T))
    {δ T : ℝ} (hδ : 0 < δ) (hT : 1 ≤ T) (hK : 1 ≤ δ * T) :
    ∫ t in Ioi 0, Phi0 δ t ≤ (1 + T) ^ 11 * (∫ t in (0 : ℝ)..T, Lsq t) +
      2 * (Cd * (3 ^ 11 * (Nat.factorial 13 : ℝ) * Real.exp 1 * Real.exp (-2 * δ * T) * T ^ 12 *
        (1 + Real.log T))) := by
  have hT0 : 0 < T := by linarith
  set B : ℝ := Cd * (3 ^ 11 * (Nat.factorial 13 : ℝ) * Real.exp 1 * Real.exp (-2 * δ * T) *
    T ^ 12 * (1 + Real.log T)) with hBdef
  have hB0 : 0 ≤ B := by
    have := Real.log_nonneg hT
    rw [hBdef]; positivity
  have hii : ∀ a b : ℝ, IntervalIntegrable (Phi0 δ) volume a b := fun a b =>
    (continuous_Phi0 δ).intervalIntegrable a b
  -- integrability on `Ioi 0`
  have hint : IntegrableOn (Phi0 δ) (Ioi 0) := by
    refine ((integrable_major hδ).integrableOn).congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [Phi0, abs_of_pos (show (0 : ℝ) < t from ht)]
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hint
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hT0)
  -- head
  have hhead : ∫ t in (0 : ℝ)..T, Phi0 δ t ≤ (1 + T) ^ 11 * ∫ t in (0 : ℝ)..T, Lsq t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hT0.le (hii 0 T)
      ((continuous_Lsq.intervalIntegrable 0 T).const_mul _) ?_
    · intro t ht
      have hL := Lsq_nonneg t
      unfold Phi0
      have h1 : (1 + t) ^ 11 ≤ (1 + T) ^ 11 := by gcongr; linarith [ht.1]; exact ht.2
      have h2 : Real.exp (-2 * δ * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
      have h3 : 0 ≤ (1 + t) ^ 11 := by have := ht.1; positivity
      calc (1 + t) ^ 11 * Real.exp (-2 * δ * t) * Lsq t ≤ (1 + T) ^ 11 * 1 * Lsq t := by
            gcongr
        _ = _ := by ring
  -- one dyadic block
  have hblock : ∀ j : ℕ, ∫ t in (2 ^ j * T)..(2 ^ (j + 1) * T), Phi0 δ t ≤ B * (1 / 2) ^ j := by
    intro j
    set X : ℝ := 2 ^ j * T with hX
    have hX1 : 1 ≤ X := by rw [hX]; nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (n := j) (by norm_num)]
    have hX2 : 2 ^ (j + 1) * T = 2 * X := by rw [hX, pow_succ]; ring
    rw [hX2]
    have hpt : ∀ t ∈ Icc X (2 * X), Phi0 δ t ≤
        (1 + 2 * X) ^ 11 * Real.exp (-2 * δ * X) * Lsq t := by
      intro t ht
      have hL := Lsq_nonneg t
      unfold Phi0
      have h1 : (1 + t) ^ 11 ≤ (1 + 2 * X) ^ 11 := by
        gcongr; linarith [ht.1]; exact ht.2
      have h2 : Real.exp (-2 * δ * t) ≤ Real.exp (-2 * δ * X) :=
        Real.exp_le_exp.mpr (by nlinarith [ht.1])
      gcongr
    have hmono := intervalIntegral.integral_mono_on (by linarith) (hii X (2 * X))
      ((continuous_Lsq.intervalIntegrable X (2 * X)).const_mul _) hpt
    rw [intervalIntegral.integral_const_mul] at hmono
    have hdy := hCd X hX1
    rw [show (∫ t in Icc X (2 * X), ‖tauL (6 + t * I)‖ ^ 2) = ∫ t in Icc X (2 * X), Lsq t from rfl,
      setIntegral_Icc_eq_interval (by linarith)] at hdy
    have hnum := tail_num hT hK j
    rw [← hX] at hnum
    have hc0 : 0 ≤ (1 + 2 * X) ^ 11 * Real.exp (-2 * δ * X) := by positivity
    calc ∫ t in X..2 * X, Phi0 δ t
        ≤ (1 + 2 * X) ^ 11 * Real.exp (-2 * δ * X) * ∫ t in X..2 * X, Lsq t := hmono
      _ ≤ (1 + 2 * X) ^ 11 * Real.exp (-2 * δ * X) * (Cd * X * (1 + Real.log X)) := by gcongr
      _ = Cd * ((1 + 2 * X) ^ 11 * Real.exp (-2 * δ * X) * (X * (1 + Real.log X))) := by ring
      _ ≤ Cd * (3 ^ 11 * (Nat.factorial 13 : ℝ) * Real.exp 1 * Real.exp (-2 * δ * T) * T ^ 12 *
            (1 + Real.log T) * (1 / 2) ^ j) := by gcongr
      _ = B * (1 / 2) ^ j := by rw [hBdef]; ring
  -- all blocks
  have hblocks : ∀ n : ℕ, ∫ t in T..(2 ^ n * T), Phi0 δ t ≤
      ∑ j ∈ Finset.range n, B * (1 / 2) ^ j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ← intervalIntegral.integral_add_adjacent_intervals
        (hii T (2 ^ n * T)) (hii (2 ^ n * T) (2 ^ (n + 1) * T))]
      linarith [hblock n]
  have hgeom : ∀ n : ℕ, ∑ j ∈ Finset.range n, B * (1 / 2) ^ j ≤ 2 * B := by
    intro n
    rw [← Finset.mul_sum]
    have := sum_geometric_two_le n
    nlinarith
  refine le_of_tendsto' hlim (fun n => ?_)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 T) (hii T (2 ^ n * T))]
  exact add_le_add hhead ((hblocks n).trans (hgeom n))

end RamanujanTau.CriticalMeanSquareLower
