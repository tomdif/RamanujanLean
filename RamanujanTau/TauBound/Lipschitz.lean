/-
# The Lipschitz integral `∫_ℝ (x+i)^{-k} e(-(x+i)) dx = (-2πi)^k/(k-1)!`  (`k ≥ 12`)

Derived from Mathlib's Lipschitz summation `EisensteinSeries.qExpansion_identity` by computing
`∫₀¹ e(-w) ∑_d (w+d)^{-k} du` two ways (periodisation vs. the `q`-series), both by dominated
convergence.
-/
import RamanujanTau.TauBound.Honest

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Complex MeasureTheory
open scoped Real Nat

/-- `∫₀¹ e(-a w) e(b w) du = [a = b]` on the line `w = u + iy`. -/
lemma integral_ee_pair (a b : ℕ) (y : ℝ) :
    ∫ u in (0 : ℝ)..1, ee (-(a : ℂ) * ((u : ℂ) + y * I)) * ee ((b : ℂ) * ((u : ℂ) + y * I)) =
      if a = b then 1 else 0 := by
  have hpt : ∀ u : ℝ, ee (-(a : ℂ) * ((u : ℂ) + y * I)) * ee ((b : ℂ) * ((u : ℂ) + y * I)) =
      ee (((b : ℂ) - a) * (y * I)) * Complex.exp ((2 * π * I * ((b : ℂ) - a)) * u) := by
    intro u; rw [← ee_add, ee, ee, ← Complex.exp_add]; congr 1; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  split_ifs with h
  · subst h; simp [ee]
  · have hne : (2 * π * I * ((b : ℂ) - a)) ≠ 0 := by
      have : ((b : ℂ) - a) ≠ 0 := by
        intro h0; apply h
        have : (b : ℂ) = a := by linear_combination h0
        exact_mod_cast this.symm
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
        I_ne_zero) this
    rw [integral_exp_mul_complex hne]
    have h1 : Complex.exp (2 * π * I * ((b : ℂ) - a) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show 2 * π * I * ((b : ℂ) - a) * ((1 : ℝ) : ℂ) = (((b : ℤ) - a : ℤ) : ℂ) * (2 * π * I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [h1]; simp

/-- The Lipschitz integrand on the line `Im w = 1`. -/
noncomputable def lipInt (k : ℕ) (x : ℝ) : ℂ :=
  1 / ((x : ℂ) + I) ^ k * ee (-((x : ℂ) + I))

lemma norm_w1 (x : ℝ) : ‖(x : ℂ) + I‖ ^ 2 = x ^ 2 + 1 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

lemma one_le_norm_w1 (x : ℝ) : 1 ≤ ‖(x : ℂ) + I‖ := by
  have h := norm_w1 x
  nlinarith [norm_nonneg ((x : ℂ) + I), sq_nonneg x]

lemma norm_inv_pow_w1_le (k : ℕ) (hk : 12 ≤ k) (x : ℝ) :
    ‖1 / ((x : ℂ) + I) ^ k‖ ≤ (x ^ 2 + 1) ^ (-6 : ℝ) := by
  have h1 := one_le_norm_w1 x
  rw [norm_div, norm_one, norm_pow]
  have hpos : (0 : ℝ) < x ^ 2 + 1 := by positivity
  rw [Real.rpow_neg hpos.le, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← norm_w1, ← pow_mul]
  rw [one_div]
  gcongr

lemma norm_ee_neg_w1 (x : ℝ) : ‖ee (-((x : ℂ) + I))‖ = Real.exp (2 * π) := by
  rw [norm_ee]; congr 1; simp

lemma continuous_lipInt (k : ℕ) : Continuous (lipInt k) := by
  unfold lipInt
  have hw : Continuous fun x : ℝ => (x : ℂ) + I := by fun_prop
  refine Continuous.mul ?_ (continuous_ee.comp hw.neg)
  refine continuous_const.div (hw.pow k) (fun x => pow_ne_zero _ ?_)
  intro h; have := congrArg Complex.im h; simp at this

lemma integrable_lipInt (k : ℕ) (hk : 12 ≤ k) : Integrable (lipInt k) := by
  have hb := (integrable_bracket (r := 0) (by norm_num) (y := 1) one_pos).const_mul
    (Real.exp (2 * π))
  refine hb.mono' (continuous_lipInt k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [lipInt, norm_mul, norm_ee_neg_w1, mul_comm]
  have := norm_inv_pow_w1_le k hk x
  simp only [zero_sub, one_pow]
  gcongr

/-- **Lipschitz integral.** -/
theorem integral_lipInt (m : ℕ) (hm : 11 ≤ m) :
    ∫ x, lipInt (m + 1) x = (-2 * π * I) ^ (m + 1) / (m ! : ℂ) := by
  set k := m + 1
  have hk : 12 ≤ k := by omega
  set C : ℂ := (-2 * π * I) ^ (m + 1) / (m ! : ℂ)
  -- the line `u + i`
  have him : ∀ u : ℝ, 0 < ((u : ℂ) + I).im := by intro u; simp
  set z : ℝ → UpperHalfPlane := fun u => ⟨(u : ℂ) + I, him u⟩
  set F : ℤ → ℝ → ℂ := fun d u => 1 / ((u : ℂ) + I + d) ^ k * ee (-((u : ℂ) + I))
  set S : ℝ → ℂ := fun u => ∑' d : ℤ, F d u
  have hIoc : Set.uIoc (0 : ℝ) 1 = Set.Ioc 0 1 := Set.uIoc_of_le zero_le_one
  -- Eisenstein-type majorant
  set z0 : UpperHalfPlane := ⟨⟨1, 1⟩, one_pos⟩
  set Rr : ℝ := EisensteinSeries.r z0 ^ (-(k : ℝ))
  have hinj : Function.Injective (fun d : ℤ => (![1, d] : Fin 2 → ℤ)) := by
    intro a b h; have := congrFun h 1; simpa using this
  have hsumM : Summable (fun d : ℤ => Real.exp (2 * π) * (Rr * ‖(![1, d] : Fin 2 → ℤ)‖ ^ (-(k : ℝ)))) :=
    (((EisensteinSeries.summable_one_div_norm_rpow (k := k) (by
      have : (12 : ℝ) ≤ k := by exact_mod_cast hk
      linarith)).comp_injective hinj).mul_left Rr).mul_left _
  have hFb : ∀ d u, 0 ≤ u → u ≤ 1 →
      ‖F d u‖ ≤ Real.exp (2 * π) * (Rr * ‖(![1, d] : Fin 2 → ℤ)‖ ^ (-(k : ℝ))) := by
    intro d u h0 h1
    have hz : z u ∈ UpperHalfPlane.verticalStrip 1 1 := by
      refine ⟨?_, ?_⟩
      · show |((u : ℂ) + I).re| ≤ 1
        simp [abs_of_nonneg h0, h1]
      · show (1 : ℝ) ≤ ((u : ℂ) + I).im
        simp
    have h := EisensteinSeries.summand_bound_of_mem_verticalStrip (z := z u) (k := k)
      (by positivity) (![1, d] : Fin 2 → ℤ) one_pos hz
    simp only [F, norm_mul, norm_ee_neg_w1]
    rw [mul_comm]
    gcongr
    refine le_of_eq_of_le ?_ h
    rw [norm_div, norm_one, norm_pow, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, one_div]
    congr 2
    simp [z]
  have hFs : ∀ u, 0 ≤ u → u ≤ 1 → Summable (fun d => F d u) := fun u h0 h1 =>
    Summable.of_norm_bounded hsumM (fun d => hFb d u h0 h1)
  have hcontF : ∀ d : ℤ, Continuous (F d) := by
    intro d
    have hw : Continuous fun x : ℝ => (x : ℂ) + I + d := by fun_prop
    refine Continuous.mul ?_ (continuous_ee.comp (by fun_prop))
    refine continuous_const.div (hw.pow k) (fun x => pow_ne_zero _ ?_)
    intro h; have := congrArg Complex.im h; simp at this
  have hDCT1 : HasSum (fun d => ∫ u in (0 : ℝ)..1, F d u) (∫ u in (0 : ℝ)..1, S u) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun d _ => Real.exp (2 * π) * (Rr * ‖(![1, d] : Fin 2 → ℤ)‖ ^ (-(k : ℝ))))
      (fun d => (hcontF d).aestronglyMeasurable)
      (fun d => Filter.Eventually.of_forall fun u hu => ?_)
      (Filter.Eventually.of_forall fun u _ => hsumM) intervalIntegrable_const
      (Filter.Eventually.of_forall fun u hu => ?_)
    · rw [hIoc] at hu; exact hFb d u hu.1.le hu.2
    · rw [hIoc] at hu; exact (hFs u hu.1.le hu.2).hasSum
  -- way 1: periodisation
  have hper : HasSum (fun d => ∫ u in (0 : ℝ)..1, F d u) (∫ x, lipInt k x) := by
    have := (integrable_lipInt k hk).hasSum_intervalIntegral_comp_add_int
    refine this.congr_fun (fun d => ?_)
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    simp only [F, lipInt]
    have : ee (-((u : ℂ) + I)) = ee (-(((u + d : ℝ) : ℂ) + I)) := by
      rw [show -(((u + d : ℝ) : ℂ) + I) = -((u : ℂ) + I) + ((-d : ℤ) : ℂ) by push_cast; ring,
        ee_add, ee_intCast, mul_one]
    rw [this]; push_cast; ring_nf
  have hS1 : ∫ u in (0 : ℝ)..1, S u = ∫ x, lipInt k x := hDCT1.unique hper
  -- way 2: the q-series
  set G : ℕ → ℝ → ℂ := fun j u => C * ((j : ℂ) ^ m *
    (ee (-(1 : ℕ) * ((u : ℂ) + (1 : ℝ) * I)) * ee ((j : ℂ) * ((u : ℂ) + (1 : ℝ) * I))))
  have hSG : ∀ u : ℝ, S u = ∑' j : ℕ, G j u := by
    intro u
    have hq := EisensteinSeries.qExpansion_identity (k := m) (by omega) (z u)
    simp only [S, F]
    rw [tsum_mul_right]
    simp only [z] at hq
    rw [show (fun d : ℤ => 1 / ((u : ℂ) + I + d) ^ k) = fun d : ℤ => 1 / ((u : ℂ) + I + d) ^ (m + 1)
      from rfl]
    erw [hq]
    simp only [G]
    rw [← tsum_mul_left, ← tsum_mul_right]
    refine tsum_congr (fun j => ?_)
    have hpow : Complex.exp (2 * π * I * ((u : ℂ) + I)) ^ j = ee ((j : ℂ) * ((u : ℂ) + (1 : ℝ) * I)) := by
      rw [ee, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [hpow]
    push_cast
    simp only [C]
    ring
  have hGb : ∀ j u, ‖G j u‖ ≤ ‖C‖ * (Real.exp (2 * π) * ((j : ℝ) ^ m * Real.exp (-(2 * π) * j))) := by
    intro j u
    simp only [G, norm_mul, norm_pow, Complex.norm_natCast, norm_ee]
    have e1 : (-(2 * π) * ((-((1 : ℕ) : ℂ)) * ((u : ℂ) + (1 : ℝ) * I)).im) = 2 * π := by simp
    have e2 : (-(2 * π) * (((j : ℂ)) * ((u : ℂ) + (1 : ℝ) * I)).im) = -(2 * π) * j := by simp
    rw [show -2 * π * ((-((1 : ℕ) : ℂ)) * ((u : ℂ) + (1 : ℝ) * I)).im = 2 * π by simp,
      show -2 * π * (((j : ℂ)) * ((u : ℂ) + (1 : ℝ) * I)).im = -(2 * π) * j by simp]
    apply le_of_eq; ring
  have hGsum : Summable (fun j : ℕ => ‖C‖ * (Real.exp (2 * π) * ((j : ℝ) ^ m * Real.exp (-(2 * π) * j)))) :=
    ((Real.summable_pow_mul_exp_neg_nat_mul m (by positivity : 0 < 2 * π)).mul_left
      (Real.exp (2 * π))).mul_left ‖C‖
  have hcontG : ∀ j, Continuous (G j) := by
    intro j
    exact continuous_const.mul (continuous_const.mul
      ((continuous_ee.comp (by fun_prop)).mul (continuous_ee.comp (by fun_prop))))
  have hDCT2 : HasSum (fun j => ∫ u in (0 : ℝ)..1, G j u) (∫ u in (0 : ℝ)..1, S u) := by
    simp_rw [hSG]
    exact intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun j _ => ‖C‖ * (Real.exp (2 * π) * ((j : ℝ) ^ m * Real.exp (-(2 * π) * j))))
      (fun j => (hcontG j).aestronglyMeasurable)
      (fun j => Filter.Eventually.of_forall fun u _ => hGb j u)
      (Filter.Eventually.of_forall fun u _ => hGsum) intervalIntegrable_const
      (Filter.Eventually.of_forall fun u _ =>
        (Summable.of_norm_bounded hGsum (fun j => hGb j u)).hasSum)
  have hG1 : HasSum (fun j => ∫ u in (0 : ℝ)..1, G j u) C := by
    have : (fun j => ∫ u in (0 : ℝ)..1, G j u) = fun j => if j = 1 then C else 0 := by
      funext j
      simp only [G]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_ee_pair]
      split_ifs with h1 h2 h2
      · subst h2; simp
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
    rw [this]
    convert hasSum_ite_eq 1 C using 1
  rw [← hS1]
  exact hDCT2.unique hG1

end RamanujanTau.TauBound
