/-
# Upper bound for the weighted mean square of `Λ(Δ,6+it)` by plain mean squares of `L`

With `δ = π/2 − β`, Stirling gives `|Λ(6+it)|² e^{2βt} ≤ C_Γ (1+|t|)¹¹ e^{−2δ|t|} |L(6+it)|²`
(`exists_weight_bound`), so (`lhs_le`)

    ∫_ℝ |Λ(6+it)|² e^{2βt} dt ≤ 2C_Γ ∫_0^∞ (1+t)¹¹ e^{−2δt} |L(6+it)|² dt,

and splitting `(0,∞)` into `[0,T]` and the dyadic blocks `[2ʲT, 2ʲ⁺¹T]`, on which the proven
upper bound `∫_X^{2X}|L|² ≤ C X(1+log X)` applies, gives (`ioi_le`)

    ∫_0^∞ (1+t)¹¹ e^{−2δt}|L|² ≤ (1+T)¹¹ ∫_0^T |L|² + D e^{−2δT} T¹² (1+log T)     (δT ≥ 1).
-/
import RamanujanTau.CriticalMeanSquare.Cumulative
import RamanujanTau.Stirling.Absolute
import RamanujanTau.HeckeConvex.Main
import RamanujanTau.HeckeZeros.Zeros

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquareLower

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.HeckeL RamanujanTau.CriticalMeanSquare
open scoped Real

lemma Lsq_neg (t : ℝ) : Lsq (-t) = Lsq t := by
  unfold Lsq
  have h : (6 : ℂ) + ((-t : ℝ) : ℂ) * I = (starRingEnd ℂ) (6 + t * I) := by
    apply Complex.ext <;> simp
  rw [h, RamanujanTau.HeckeZeros.tauL_conj, Complex.norm_conj]

lemma Lsq_abs (t : ℝ) : Lsq |t| = Lsq t := by
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, Lsq_neg]

/-- **Stirling weight.** -/
theorem exists_weight_bound : ∃ CΓ : ℝ, 0 < CΓ ∧ ∀ β : ℝ, 0 ≤ β → ∀ t : ℝ,
    ‖heckeLambda (6 + t * I)‖ ^ 2 * Real.exp (2 * β * t) ≤
      CΓ * ((1 + |t|) ^ 11 * Real.exp (-2 * (π / 2 - β) * |t|) * Lsq t) := by
  set K0 : ℝ := (2 * π) ^ (-6 : ℝ) * (((4 + 1).factorial : ℝ) * Real.exp 10 * Real.sqrt (2 * π)) *
    2 ^ (11 / 2 : ℝ) with hK0
  have hK0pos : 0 < K0 := by
    rw [hK0]
    have : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
    positivity
  refine ⟨K0 ^ 2, by positivity, fun β hβ0 t => ?_⟩
  set s : ℂ := 6 + t * I with hsdef
  have hs : ∀ n : ℕ, s ≠ -n := RamanujanTau.HeckeZeros.ne_neg_nat_of_re_pos (by simp [hsdef])
  have hΛ : ‖heckeLambda s‖ ≤
      K0 * ((1 + |t|) ^ (11 / 2 : ℝ) * Real.exp (-(π * |t|) / 2)) * ‖tauL s‖ := by
    rw [heckeLambda_eq_tauL hs, norm_mul, norm_mul]
    have h2π : ‖(2 * π : ℂ) ^ (-s)‖ = (2 * π) ^ (-6 : ℝ) := by
      have e : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
      rw [e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      congr 1; simp [hsdef]
    have hΓ := RamanujanTau.Stirling.norm_Gamma_le_stirling (σ := 6) (by norm_num) 4
      (by norm_num) t
    have e6 : ((6 : ℝ) : ℂ) = 6 := by norm_num
    rw [e6] at hΓ
    have hn : ‖(3 / 2 : ℂ) + t * I‖ ≤ 2 * (1 + |t|) := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp; norm_num; linarith [abs_nonneg t]
    have hpow : ‖(3 / 2 : ℂ) + t * I‖ ^ ((6 : ℝ) - 1 / 2) ≤
        2 ^ (11 / 2 : ℝ) * (1 + |t|) ^ (11 / 2 : ℝ) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      rw [show (6 : ℝ) - 1 / 2 = 11 / 2 by norm_num]
      exact Real.rpow_le_rpow (norm_nonneg _) hn (by norm_num)
    have hΓ' : ‖Complex.Gamma s‖ ≤ ((4 + 1).factorial : ℝ) * Real.exp 10 * Real.sqrt (2 * π) *
        (2 ^ (11 / 2 : ℝ) * (1 + |t|) ^ (11 / 2 : ℝ)) * Real.exp (-(π * |t|) / 2) := by
      refine hΓ.trans ?_
      gcongr
    rw [h2π]
    calc (2 * π) ^ (-6 : ℝ) * ‖Complex.Gamma s‖ * ‖tauL s‖
        ≤ (2 * π) ^ (-6 : ℝ) * (((4 + 1).factorial : ℝ) * Real.exp 10 * Real.sqrt (2 * π) *
          (2 ^ (11 / 2 : ℝ) * (1 + |t|) ^ (11 / 2 : ℝ)) * Real.exp (-(π * |t|) / 2)) *
            ‖tauL s‖ := by gcongr
      _ = _ := by rw [hK0]; ring
  have hsq : ‖heckeLambda s‖ ^ 2 ≤
      K0 ^ 2 * ((1 + |t|) ^ 11 * Real.exp (-(π * |t|))) * Lsq t := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hΛ 2
    have e1 : ((1 + |t|) ^ (11 / 2 : ℝ)) ^ 2 = (1 + |t|) ^ 11 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    have e2 : Real.exp (-(π * |t|) / 2) ^ 2 = Real.exp (-(π * |t|)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    calc ‖heckeLambda s‖ ^ 2
        ≤ (K0 * ((1 + |t|) ^ (11 / 2 : ℝ) * Real.exp (-(π * |t|) / 2)) * ‖tauL s‖) ^ 2 := h
      _ = K0 ^ 2 * (((1 + |t|) ^ (11 / 2 : ℝ)) ^ 2 * Real.exp (-(π * |t|) / 2) ^ 2) *
          ‖tauL s‖ ^ 2 := by ring
      _ = _ := by rw [e1, e2]; rfl
  have hexp : Real.exp (-(π * |t|)) * Real.exp (2 * β * t) ≤
      Real.exp (-2 * (π / 2 - β) * |t|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : β * t ≤ β * |t| := mul_le_mul_of_nonneg_left (le_abs_self t) hβ0
    nlinarith
  have hL0 := Lsq_nonneg t
  calc ‖heckeLambda s‖ ^ 2 * Real.exp (2 * β * t)
      ≤ K0 ^ 2 * ((1 + |t|) ^ 11 * Real.exp (-(π * |t|))) * Lsq t * Real.exp (2 * β * t) := by
        gcongr
    _ = K0 ^ 2 * ((1 + |t|) ^ 11 * (Real.exp (-(π * |t|)) * Real.exp (2 * β * t)) * Lsq t) := by
        ring
    _ ≤ _ := by gcongr

/-- The majorant is integrable (convexity bound `|L(6+it)| ≪ 1+|t|`). -/
lemma integrable_major {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ => (1 + |t|) ^ 11 * Real.exp (-2 * δ * |t|) * Lsq t) := by
  obtain ⟨C, hC0, hC⟩ := RamanujanTau.HeckeConvex.tauL_convexity (ε := 1 / 2) (by norm_num)
  set B : ℝ := (Nat.factorial 15 : ℝ) * Real.exp (2 * δ) / (2 * δ) ^ 15 with hB
  have hcont : Continuous (fun t : ℝ => (1 + |t|) ^ 11 * Real.exp (-2 * δ * |t|) * Lsq t) :=
    (by fun_prop : Continuous fun t : ℝ => (1 + |t|) ^ 11 * Real.exp (-2 * δ * |t|)).mul
      continuous_Lsq
  refine (integrable_inv_one_add_sq.const_mul (C ^ 2 * B)).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  set X : ℝ := 1 + |t| with hX
  have hX1 : 1 ≤ X := by rw [hX]; linarith [abs_nonneg t]
  have hX0 : 0 < X := by linarith
  have hL : Lsq t ≤ C ^ 2 * X ^ 2 := by
    have h := hC t
    rw [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] at h
    unfold Lsq
    have := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [hX]; nlinarith
  have hfact := Real.pow_div_factorial_le_exp (2 * δ * X) (by positivity) 15
  have h1t : 1 + t ^ 2 ≤ X ^ 2 := by
    rw [hX]; nlinarith [sq_abs t, abs_nonneg t]
  have hE : Real.exp (2 * δ * X) * Real.exp (-2 * δ * |t|) = Real.exp (2 * δ) := by
    rw [← Real.exp_add]; congr 1; rw [hX]; ring
  have hkey : X ^ 15 * Real.exp (-2 * δ * |t|) ≤ B := by
    rw [hB, le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity), mul_pow] at hfact
    have hpos : 0 < Real.exp (-2 * δ * |t|) := Real.exp_pos _
    calc X ^ 15 * Real.exp (-2 * δ * |t|) * (2 * δ) ^ 15
        = (2 * δ) ^ 15 * X ^ 15 * Real.exp (-2 * δ * |t|) := by ring
      _ ≤ Real.exp (2 * δ * X) * (Nat.factorial 15 : ℝ) * Real.exp (-2 * δ * |t|) := by gcongr
      _ = (Nat.factorial 15 : ℝ) * (Real.exp (2 * δ * X) * Real.exp (-2 * δ * |t|)) := by ring
      _ = _ := by rw [hE]
  have hnn : 0 ≤ (1 + |t|) ^ 11 * Real.exp (-2 * δ * |t|) * Lsq t := by
    have := Lsq_nonneg t; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  show X ^ 11 * Real.exp (-2 * δ * |t|) * Lsq t ≤ C ^ 2 * B * (1 + t ^ 2)⁻¹
  have he0 : 0 < Real.exp (-2 * δ * |t|) := Real.exp_pos _
  have h1t0 : 0 < 1 + t ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ h1t0]
  calc X ^ 11 * Real.exp (-2 * δ * |t|) * Lsq t * (1 + t ^ 2)
      ≤ X ^ 11 * Real.exp (-2 * δ * |t|) * (C ^ 2 * X ^ 2) * X ^ 2 := by
        gcongr
    _ = C ^ 2 * (X ^ 15 * Real.exp (-2 * δ * |t|)) := by ring
    _ ≤ C ^ 2 * B := by gcongr

end RamanujanTau.CriticalMeanSquareLower
