/-
# Riemann–von Mangoldt for every nonzero level-one cusp form: all `T ≥ 2`

* `riemann_von_mangoldt_gen`: `N_f(T) = (T/π) log(T/(2π e n₀)) + O(log T)`, `n₀` the first index
  with `a_f(n₀) ≠ 0`.
* `riemann_von_mangoldt_of_coef_one`: if `a_f(1) ≠ 0` (e.g. normalized eigenforms),
  `N_f(T) = (T/π) log(T/(2πe)) + O(log T)`.
* `zeroCount_ge_T_log_T_gen`: `N_f(T) ≥ (T/(2π)) log T` for large `T`.
-/
import RamanujanTau.GeneralZeros.RvM
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

namespace RamanujanTau.GeneralZeros

open Complex Set ModularForm
open RamanujanTau.HeckeConvexGeneral
open scoped Real MatrixGroups

variable {k : ℕ}

/-- **Riemann–von Mangoldt formula for `L(f,s)`**, `f ∈ S_k(SL₂(ℤ))` nonzero, `n₀` the first index
with `a_f(n₀) ≠ 0`: `N_f(T) = (T/π) log(T/(2π e n₀)) + O(log T)` for `T ≥ 2`. -/
theorem riemann_von_mangoldt_gen (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) {n₀ : ℕ}
    (ha₀ : coef f n₀ ≠ 0) (hmin : ∀ n < n₀, coef f n = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
      |(zeroCount f T : ℝ) - T / π * Real.log (T / (2 * π * Real.exp 1 * n₀))| ≤
        C * Real.log T := by
  have hn₀ : 1 ≤ n₀ := one_le_of_coef_ne_zero f ha₀
  have hn₀R : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  obtain ⟨C₁, hC₁0, hC₁⟩ := rvm_nonordinate_gen f hf ha₀ hmin
  obtain ⟨Cw, hCw0, -, hCw⟩ := zeroCount_window f hf
  set K : ℝ := Real.log (2 * π * n₀) with hKdef
  have hK0 : 0 ≤ K := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  refine ⟨2 * Cw + 3 * C₁ / π + (6 + 2 * K) / π, by positivity, fun T hT2 => ?_⟩
  have hT0 : 0 < T := by linarith
  -- a non-ordinate `T' ∈ (T, T+1)`
  have hfin : ((fun u : ℂ => u.im) '' zeroSet f T (T + 1)).Finite :=
    (zeroSet_finite f hf T (T + 1)).image _
  obtain ⟨T', hT'mem, hT'not⟩ :=
    (Set.Ioo_infinite (by linarith : T < T + 1)).exists_notMem_finite hfin
  have hnon : ∀ u : ℂ, heckeLambda f u = 0 → u.im ≠ T' := by
    intro u h0 h3
    apply hT'not
    exact ⟨u, ⟨h0, by rw [h3]; exact hT'mem.1, by rw [h3]; exact hT'mem.2.le⟩, h3⟩
  have hT'1 : 1 ≤ T' := by linarith [hT'mem.1]
  have hR := hC₁ T' hT'1 hnon
  have hmono1 : (zeroCount f T : ℝ) ≤ zeroCount f T' := by
    have := zeroCountAB_add f hf (le_of_lt hT0) hT'mem.1.le
    unfold zeroCount; rw [this]; push_cast
    linarith [Nat.cast_nonneg (α := ℝ) (zeroCountAB f T T')]
  have hmono2 : (zeroCount f T' : ℝ) ≤ zeroCount f (T + 1) := by
    have := zeroCountAB_add f hf (le_of_lt (by linarith [hT'mem.1] : (0 : ℝ) < T')) hT'mem.2.le
    unfold zeroCount; rw [this]; push_cast
    linarith [Nat.cast_nonneg (α := ℝ) (zeroCountAB f T' (T + 1))]
  have hwin := hCw T hT0.le
  -- logs
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT2
  have hl2 : (2 : ℝ) / 3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hp2 : Real.log (T ^ 2) = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  have hp3 : Real.log (T ^ 3) = 3 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  have hlogT2 : Real.log (T + 2) ≤ 2 * Real.log T := by
    rw [← hp2]; apply Real.log_le_log (by linarith); nlinarith
  have hlogT1 : Real.log (T + 1) ≤ 2 * Real.log T := by
    rw [← hp2]; apply Real.log_le_log (by linarith); nlinarith
  have hlogT5 : Real.log (T' + 5) ≤ 3 * Real.log T := by
    rw [← hp3]; apply Real.log_le_log (by linarith [hT'mem.1])
    nlinarith [hT'mem.2]
  -- main-term comparison
  have hmain : ∀ x : ℝ, 0 < x → x / π * Real.log (x / (2 * π * Real.exp 1 * n₀)) =
      (x * Real.log x - x - x * K) / π := by
    intro x hx
    have h1 : 2 * π * Real.exp 1 * n₀ = (2 * π * n₀) * Real.exp 1 := by ring
    rw [h1, Real.log_div hx.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, ← hKdef]
    field_simp; ring
  rw [hmain T hT0]
  have hTT' : T < T' := hT'mem.1
  have hT'T : T' < T + 1 := hT'mem.2
  have hd1 : 0 ≤ T' * Real.log T' - T * Real.log T := by
    have : Real.log T ≤ Real.log T' := Real.log_le_log hT0 hTT'.le
    have h0 : 0 ≤ Real.log T := by linarith
    nlinarith
  have hd2 : T' * Real.log T' - T * Real.log T ≤ Real.log (T + 1) + 1 := by
    have hq : Real.log T' - Real.log T ≤ T' / T - 1 := by
      rw [← Real.log_div (by linarith) hT0.ne']
      exact Real.log_le_sub_one_of_pos (by positivity)
    have hTq : T * (T' / T - 1) = T' - T := by field_simp
    have hq' : T * (Real.log T' - Real.log T) ≤ T' - T := by
      have := mul_le_mul_of_nonneg_left hq hT0.le
      linarith
    have hlT' : Real.log T' ≤ Real.log (T + 1) := Real.log_le_log (by linarith) hT'T.le
    have hlT'0 : 0 ≤ Real.log T' := Real.log_nonneg (by linarith)
    have : (T' - T) * Real.log T' ≤ Real.log T' := by
      have : T' - T ≤ 1 := by linarith
      nlinarith
    nlinarith
  have hpi := Real.pi_pos
  have hR' := abs_le.mp hR
  have hprod1 : 0 ≤ (T' - T) * K := mul_nonneg (by linarith) hK0
  have hprod2 : (T' - T) * K ≤ K := by nlinarith
  have hz1 : π * (zeroCount f T : ℝ) ≤ π * (zeroCount f T' : ℝ) :=
    mul_le_mul_of_nonneg_left hmono1 hpi.le
  have hz2 : π * (zeroCount f T' : ℝ) ≤ π * (zeroCount f T : ℝ) + π * Cw * Real.log (T + 2) := by
    have := mul_le_mul_of_nonneg_left (show (zeroCount f T' : ℝ) ≤ zeroCount f T +
      Cw * Real.log (T + 2) by linarith) hpi.le
    linarith
  have hlT1 : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by linarith)
  have hCwl : 0 ≤ π * Cw * Real.log (T + 2) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ T + 2 by linarith); positivity
  have hX : |π * (zeroCount f T : ℝ) - (T * Real.log T - T - T * K)| ≤
      π * Cw * Real.log (T + 2) + C₁ * Real.log (T' + 5) + (Real.log (T + 1) + 2 + K) := by
    have hM : (T' * Real.log T' - T' - T' * K) - (T * Real.log T - T - T * K) =
        (T' * Real.log T' - T * Real.log T) - (T' - T) - (T' - T) * K := by ring
    rw [abs_le]; constructor <;> linarith
  have key : |(zeroCount f T : ℝ) - (T * Real.log T - T - T * K) / π| ≤
      Cw * Real.log (T + 2) + C₁ * Real.log (T' + 5) / π + (Real.log (T + 1) + 2 + K) / π := by
    have e : (zeroCount f T : ℝ) - (T * Real.log T - T - T * K) / π =
        (π * (zeroCount f T : ℝ) - (T * Real.log T - T - T * K)) / π := by
      field_simp
    have e2 : Cw * Real.log (T + 2) + C₁ * Real.log (T' + 5) / π + (Real.log (T + 1) + 2 + K) / π =
        (π * Cw * Real.log (T + 2) + C₁ * Real.log (T' + 5) + (Real.log (T + 1) + 2 + K)) / π := by
      field_simp
    rw [e, e2, abs_div, abs_of_pos hpi]
    exact div_le_div_of_nonneg_right hX hpi.le
  refine key.trans ?_
  have hlT0 : 0 ≤ Real.log T := by linarith
  have e1 : Cw * Real.log (T + 2) ≤ 2 * Cw * Real.log T := by
    have := mul_le_mul_of_nonneg_left hlogT2 hCw0; linarith
  have e2 : C₁ * Real.log (T' + 5) / π ≤ 3 * C₁ / π * Real.log T := by
    have : 3 * C₁ / π * Real.log T = (3 * C₁ * Real.log T) / π := by ring
    rw [this]
    exact div_le_div_of_nonneg_right (by have := mul_le_mul_of_nonneg_left hlogT5 hC₁0; linarith)
      hpi.le
  have e3 : (Real.log (T + 1) + 2 + K) / π ≤ (6 + 2 * K) / π * Real.log T := by
    have : (6 + 2 * K) / π * Real.log T = ((6 + 2 * K) * Real.log T) / π := by ring
    rw [this]
    apply div_le_div_of_nonneg_right _ hpi.le
    have h1 : 1 ≤ 3 / 2 * Real.log T := by linarith
    have h2 : K * 1 ≤ K * (3 / 2 * Real.log T) := mul_le_mul_of_nonneg_left h1 hK0
    have hKl : 0 ≤ K * Real.log T := mul_nonneg hK0 hlT0
    have e : (6 + 2 * K) * Real.log T = 6 * Real.log T + 2 * (K * Real.log T) := by ring
    have e' : K * (3 / 2 * Real.log T) = 3 / 2 * (K * Real.log T) := by ring
    rw [e]; rw [e'] at h2
    linarith
  have : (2 * Cw + 3 * C₁ / π + (6 + 2 * K) / π) * Real.log T =
      2 * Cw * Real.log T + 3 * C₁ / π * Real.log T + (6 + 2 * K) / π * Real.log T := by ring
  linarith

/-- **Riemann–von Mangoldt when `a_f(1) ≠ 0`** (in particular for every normalized Hecke
eigenform): `N_f(T) = (T/π) log(T/(2πe)) + O(log T)`. -/
theorem riemann_von_mangoldt_of_coef_one (f : CuspForm 𝒮ℒ (k : ℤ)) (h1 : coef f 1 ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
      |(zeroCount f T : ℝ) - T / π * Real.log (T / (2 * π * Real.exp 1))| ≤ C * Real.log T := by
  have hf : f ≠ 0 := by
    rintro rfl
    apply h1
    simp [coef, UpperHalfPlane.qExpansion_zero]
  have hmin : ∀ n < 1, coef f n = 0 := by
    intro n hn; obtain rfl : n = 0 := by omega
    exact coef_zero f
  obtain ⟨C, hC0, hC⟩ := riemann_von_mangoldt_gen f hf h1 hmin
  refine ⟨C, hC0, fun T hT => ?_⟩
  have := hC T hT
  simpa using this

/-- **Lower bound `N_f(T) ≫ T log T`**: `N_f(T) ≥ (T/(2π)) log T` for all large `T`. -/
theorem zeroCount_ge_T_log_T_gen (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → T / (2 * π) * Real.log T ≤ zeroCount f T := by
  have hk1 : 1 ≤ k := by have := weight_ge f hf; omega
  obtain ⟨n₀, ha₀, hmin⟩ := exists_first f hf hk1
  have hn₀R : (1 : ℝ) ≤ n₀ := by exact_mod_cast one_le_of_coef_ne_zero f ha₀
  obtain ⟨C, hC0, hC⟩ := riemann_von_mangoldt_gen f hf ha₀ hmin
  set K := Real.log (2 * π * n₀) + 1 with hK
  have hK0 : 0 ≤ K := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * π * n₀ by nlinarith [Real.pi_gt_three])
    linarith
  refine ⟨max (max 2 (Real.exp (4 * K))) (4 * π * C), le_max_of_le_left (le_max_left _ _),
    fun T hT => ?_⟩
  have hT2 : 2 ≤ T := le_trans (le_max_of_le_left (le_max_left _ _)) hT
  have hTe : Real.exp (4 * K) ≤ T := le_trans (le_max_of_le_left (le_max_right _ _)) hT
  have hTC : 4 * π * C ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := by linarith
  have hlogT : 4 * K ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos _) hTe; rwa [Real.log_exp] at this
  have hlT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have h := abs_le.mp (hC T hT2)
  have hmain : T / π * Real.log (T / (2 * π * Real.exp 1 * n₀)) = T / π * (Real.log T - K) := by
    have e : 2 * π * Real.exp 1 * n₀ = (2 * π * n₀) * Real.exp 1 := by ring
    rw [e, Real.log_div hT0.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, hK]
  rw [hmain] at h
  have hpi := Real.pi_pos
  set A : ℝ := T * Real.log T / π with hA
  have h1 : T / π * K ≤ A / 4 := by
    have : T / π * K ≤ T / π * (Real.log T / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : T / π * (Real.log T / 4) = A / 4 := by rw [hA]; ring
    linarith
  have h2 : C * Real.log T ≤ A / 4 := by
    have e : A / 4 = (T / (4 * π)) * Real.log T := by rw [hA]; field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hlT0
    rw [le_div_iff₀ (by positivity)]; linarith
  have eA : T / π * (Real.log T - K) = A - T / π * K := by rw [hA]; ring
  have e2 : T / (2 * π) * Real.log T = A / 2 := by rw [hA]; field_simp
  rw [e2]
  linarith

end RamanujanTau.GeneralZeros
