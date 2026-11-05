/-
# The exact Gamma weight on the critical line

    |Γ(6+it)|² = (1+t²)(4+t²)(9+t²)(16+t²)(25+t²) · πt / sinh(πt)      (t ≠ 0),

from `Γ(1+it)Γ(1−it) = πt/sinh(πt)` (reflection formula) and `Γ(s+1) = sΓ(s)`.  Hence

    |Λ(6+it)|² e^{2βt} = kΓ(t) e^{−(π−2β)t} |L(6+it)|²,
    kΓ(t) = P(t) · πt e^{πt} / sinh(πt) / (2π)¹²,

with `kΓ(t) ≥ t¹¹/(2π)¹¹` and `kΓ(t) (2π)¹¹ / t¹¹ → 1` as `t → ∞`.
-/
import RamanujanTau.CriticalMeanSquareLower.Weight

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquareAsymp

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.HeckeL RamanujanTau.CriticalMeanSquare
open scoped Real

lemma norm_Gamma_one_add_sq {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (1 + t * I)‖ ^ 2 = π * t / Real.sinh (π * t) := by
  have htI : (t : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast ht) I_ne_zero
  have h1 : Complex.Gamma (1 + t * I) = (t * I) * Complex.Gamma (t * I) := by
    rw [add_comm]; exact Complex.Gamma_add_one _ htI
  have hconj : (starRingEnd ℂ) (Complex.Gamma (1 + t * I)) = Complex.Gamma (1 - t * I) := by
    rw [← Complex.Gamma_conj]; congr 1; simp [map_add, map_mul]; ring
  have h2 := Complex.Gamma_mul_Gamma_one_sub ((t : ℂ) * I)
  have hsin : Complex.sin (π * (t * I)) = (Real.sinh (π * t) : ℂ) * I := by
    rw [show (π : ℂ) * (t * I) = ((π * t : ℝ) : ℂ) * I by push_cast; ring, Complex.sin_mul_I,
      Complex.ofReal_sinh]
  have hsh : Real.sinh (π * t) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero ht
  have key : Complex.Gamma (1 + t * I) * (starRingEnd ℂ) (Complex.Gamma (1 + t * I)) =
      ((π * t / Real.sinh (π * t) : ℝ) : ℂ) := by
    rw [hconj, h1, mul_assoc, h2, hsin]
    have : (Real.sinh (π * t) : ℂ) ≠ 0 := by exact_mod_cast hsh
    push_cast
    field_simp
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at key
  exact_mod_cast key

lemma norm_add_mul_I_sq (k t : ℝ) : ‖(k : ℂ) + t * I‖ ^ 2 = k ^ 2 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]

/-- The polynomial `P(t) = ∏_{k=1}^5 (k² + t²)`. -/
noncomputable def Pq (t : ℝ) : ℝ := (1 + t ^ 2) * (4 + t ^ 2) * (9 + t ^ 2) * (16 + t ^ 2) * (25 + t ^ 2)

lemma norm_Gamma_six_sq {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (6 + t * I)‖ ^ 2 = Pq t * (π * t / Real.sinh (π * t)) := by
  have hne : ∀ k : ℝ, 0 < k → (k : ℂ) + t * I ≠ 0 := by
    intro k hk h
    have := congrArg Complex.re h
    simp at this; linarith
  have step : ∀ k : ℝ, 0 < k → Complex.Gamma (((k + 1 : ℝ) : ℂ) + t * I) =
      ((k : ℂ) + t * I) * Complex.Gamma ((k : ℂ) + t * I) := by
    intro k hk
    rw [show (((k + 1 : ℝ) : ℂ) + t * I) = ((k : ℂ) + t * I) + 1 by push_cast; ring]
    exact Complex.Gamma_add_one _ (hne k hk)
  have e6 : Complex.Gamma (6 + t * I) = ((5 : ℝ) + t * I) * (((4 : ℝ) + t * I) *
      (((3 : ℝ) + t * I) * (((2 : ℝ) + t * I) * (((1 : ℝ) + t * I) *
        Complex.Gamma (((1 : ℝ) : ℂ) + t * I))))) := by
    have s5 := step 5 (by norm_num)
    have s4 := step 4 (by norm_num)
    have s3 := step 3 (by norm_num)
    have s2 := step 2 (by norm_num)
    have s1 := step 1 (by norm_num)
    norm_num at s5 s4 s3 s2 s1 ⊢
    rw [s5, s4, s3, s2, s1]
  rw [e6]
  simp only [norm_mul, mul_pow, norm_add_mul_I_sq]
  have h1 : ((1 : ℝ) : ℂ) + t * I = 1 + t * I := by norm_num
  rw [h1, norm_Gamma_one_add_sq ht]
  unfold Pq; ring

/-- The Gamma kernel. -/
noncomputable def kG (t : ℝ) : ℝ :=
  Pq t * (π * t / Real.sinh (π * t)) / (2 * π) ^ 12 * Real.exp (π * t)

lemma norm_heckeLambda_sq {t : ℝ} (ht : t ≠ 0) :
    ‖heckeLambda (6 + t * I)‖ ^ 2 = Pq t * (π * t / Real.sinh (π * t)) / (2 * π) ^ 12 * Lsq t := by
  set s : ℂ := 6 + t * I with hsdef
  have hs : ∀ n : ℕ, s ≠ -n := RamanujanTau.HeckeZeros.ne_neg_nat_of_re_pos (by simp [hsdef])
  rw [heckeLambda_eq_tauL hs, norm_mul, norm_mul, mul_pow, mul_pow, norm_Gamma_six_sq ht]
  have h2π : ‖(2 * π : ℂ) ^ (-s)‖ = (2 * π) ^ (-6 : ℝ) := by
    have e : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
    rw [e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    congr 1; simp [hsdef]
  rw [h2π, Real.rpow_neg (by positivity), inv_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  unfold Lsq
  rw [← hsdef]
  norm_num
  left; ring

/-- **The weight identity**, `t ≠ 0`. -/
lemma weight_eq {t : ℝ} (ht : t ≠ 0) (β : ℝ) :
    ‖heckeLambda (6 + t * I)‖ ^ 2 * Real.exp (2 * β * t) =
      kG t * Real.exp (-((π - 2 * β) * t)) * Lsq t := by
  rw [norm_heckeLambda_sq ht]
  unfold kG
  have : Real.exp (2 * β * t) = Real.exp (π * t) * Real.exp (-((π - 2 * β) * t)) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]; ring

lemma sinh_le_half_exp (x : ℝ) : Real.sinh x ≤ Real.exp x / 2 := by
  rw [Real.sinh_eq]
  have := Real.exp_pos (-x)
  linarith

lemma Pq_ge (t : ℝ) : t ^ 10 ≤ Pq t := by
  unfold Pq
  have h : ∀ k : ℝ, 0 ≤ k → t ^ 2 ≤ k + t ^ 2 := fun k hk => by linarith
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  calc t ^ 10 = t ^ 2 * t ^ 2 * t ^ 2 * t ^ 2 * t ^ 2 := by ring
    _ ≤ _ := by gcongr <;> linarith

/-- `kΓ(t) ≥ t¹¹/(2π)¹¹` for `t > 0`. -/
lemma kG_ge {t : ℝ} (ht : 0 < t) : t ^ 11 / (2 * π) ^ 11 ≤ kG t := by
  unfold kG
  have hsh : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
  have hsh2 := sinh_le_half_exp (π * t)
  have hE : 0 < Real.exp (π * t) := Real.exp_pos _
  have h1 : 2 * π * t ≤ π * t / Real.sinh (π * t) * Real.exp (π * t) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hsh]
    have : 0 < π * t := by positivity
    nlinarith
  have hP := Pq_ge t
  have e : Pq t * (π * t / Real.sinh (π * t)) / (2 * π) ^ 12 * Real.exp (π * t) =
      Pq t * (π * t / Real.sinh (π * t) * Real.exp (π * t)) / (2 * π) ^ 12 := by ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  calc t ^ 11 * (2 * π) ^ 12 = t ^ 10 * (2 * π * t) * (2 * π) ^ 11 := by ring
    _ ≤ Pq t * (π * t / Real.sinh (π * t) * Real.exp (π * t)) * (2 * π) ^ 11 := by
        have : 0 ≤ Pq t := le_trans (by positivity) hP
        gcongr

/-- `kΓ ≤ P(T) e^{πT}/(2π)¹²` on `(0, T]`. -/
lemma kG_le {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    kG t ≤ Pq T * Real.exp (π * T) / (2 * π) ^ 12 := by
  unfold kG
  have hsh : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
  have h1 : π * t / Real.sinh (π * t) ≤ 1 := by
    rw [div_le_one hsh]; exact Real.self_le_sinh_iff.mpr (by positivity)
  have hP : Pq t ≤ Pq T := by unfold Pq; gcongr
  have hE : Real.exp (π * t) ≤ Real.exp (π * T) := Real.exp_le_exp.mpr (by gcongr)
  have h0 : 0 ≤ π * t / Real.sinh (π * t) := by positivity
  have hPt : 0 ≤ Pq t := by unfold Pq; positivity
  have hPT : 0 ≤ Pq T := by unfold Pq; positivity
  calc Pq t * (π * t / Real.sinh (π * t)) / (2 * π) ^ 12 * Real.exp (π * t)
      ≤ Pq T * 1 / (2 * π) ^ 12 * Real.exp (π * T) := by gcongr
    _ = _ := by ring

/-- `kΓ(t)(2π)¹¹/t¹¹ → 1`. -/
lemma tendsto_kG_ratio : Tendsto (fun t => kG t * (2 * π) ^ 11 / t ^ 11) atTop (𝓝 1) := by
  have hq : ∀ k : ℝ, Tendsto (fun t : ℝ => 1 + k / t ^ 2) atTop (𝓝 1) := by
    intro k
    have : Tendsto (fun t : ℝ => k / t ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
    simpa using this.const_add 1
  have he : Tendsto (fun t : ℝ => (1 - Real.exp (-(2 * π * t)))⁻¹) atTop (𝓝 1) := by
    have h1 : Tendsto (fun t : ℝ => Real.exp (-(2 * π * t))) atTop (𝓝 0) := by
      have : Tendsto (fun t : ℝ => -(2 * π * t)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by positivity))
      exact Real.tendsto_exp_atBot.comp this
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub h1).inv₀ (by norm_num)
    simpa using this
  have hlim := (((((hq 1).mul (hq 4)).mul (hq 9)).mul (hq 16)).mul (hq 25)).mul he
  norm_num at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hsh : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
  have hsh' : Real.sinh (π * t) = Real.exp (π * t) * (1 - Real.exp (-(2 * π * t))) / 2 := by
    rw [Real.sinh_eq, mul_sub, mul_one, ← Real.exp_add]
    congr 1; congr 1; congr 1; ring
  have h1e : 0 < 1 - Real.exp (-(2 * π * t)) := by
    have : Real.exp (-(2 * π * t)) < 1 := Real.exp_lt_one_iff.mpr (by
      have : 0 < 2 * π * t := by positivity
      linarith)
    linarith
  unfold kG Pq
  rw [hsh']
  field_simp
  ring

end RamanujanTau.CriticalMeanSquareAsymp
