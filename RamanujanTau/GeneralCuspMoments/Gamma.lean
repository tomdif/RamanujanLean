/-
# The exact Gamma weight on the line `Re s = p + 1`

For `p : ℕ` and `t ≠ 0`,

    |Γ(p+1+it)|² = ∏_{j<p} ((j+1)² + t²) · πt / sinh(πt),

from `Γ(1+it)Γ(1−it) = πt/sinh(πt)` and `Γ(s+1) = sΓ(s)` (induction on `p`).  The kernel

    kG p t = P_p(t) · πt / sinh(πt) / (2π)^{2p+2} · e^{πt}

satisfies `kG p t ≥ t^{2p+1}/(2π)^{2p+1}` and `kG p t (2π)^{2p+1} / t^{2p+1} → 1`.
(The weight of a level-one cusp form is `k = 2p + 2`.)
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.GeneralCuspMoments

open Complex Filter Topology Set
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

lemma norm_add_mul_I_sq (a t : ℝ) : ‖(a : ℂ) + t * I‖ ^ 2 = a ^ 2 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]

/-- `P_p(t) = ∏_{j<p} ((j+1)² + t²)`. -/
noncomputable def Pq (p : ℕ) (t : ℝ) : ℝ := ∏ j ∈ Finset.range p, (((j : ℝ) + 1) ^ 2 + t ^ 2)

lemma Pq_nonneg (p : ℕ) (t : ℝ) : 0 ≤ Pq p t :=
  Finset.prod_nonneg fun j _ => by positivity

/-- **`|Γ(p+1+it)|² = P_p(t) · πt/sinh(πt)`.** -/
lemma norm_Gamma_sq (p : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma ((p : ℂ) + 1 + t * I)‖ ^ 2 = Pq p t * (π * t / Real.sinh (π * t)) := by
  induction p with
  | zero =>
    simp only [Nat.cast_zero, zero_add, Pq, Finset.range_zero, Finset.prod_empty, one_mul]
    exact norm_Gamma_one_add_sq ht
  | succ p ih =>
    have hne : (p : ℂ) + 1 + t * I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    have e : ((p + 1 : ℕ) : ℂ) + 1 + t * I = ((p : ℂ) + 1 + t * I) + 1 := by push_cast; ring
    rw [e, Complex.Gamma_add_one _ hne, norm_mul, mul_pow, ih]
    have e2 : (p : ℂ) + 1 + t * I = (((p : ℝ) + 1 : ℝ) : ℂ) + t * I := by push_cast; ring
    rw [e2, norm_add_mul_I_sq]
    unfold Pq
    rw [Finset.prod_range_succ]
    ring

/-- The Gamma kernel. -/
noncomputable def kG (p : ℕ) (t : ℝ) : ℝ :=
  Pq p t * (π * t / Real.sinh (π * t)) / (2 * π) ^ (2 * p + 2) * Real.exp (π * t)

lemma sinh_le_half_exp (x : ℝ) : Real.sinh x ≤ Real.exp x / 2 := by
  rw [Real.sinh_eq]
  have := Real.exp_pos (-x)
  linarith

lemma Pq_ge (p : ℕ) (t : ℝ) : t ^ (2 * p) ≤ Pq p t := by
  have e : t ^ (2 * p) = ∏ _j ∈ Finset.range p, t ^ 2 := by
    rw [Finset.prod_const, Finset.card_range, ← pow_mul, mul_comm]
  rw [e, Pq]
  exact Finset.prod_le_prod (fun _ _ => sq_nonneg t) (fun j _ => by
    have : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := sq_nonneg _
    linarith)

/-- `kΓ(t) ≥ t^{2p+1}/(2π)^{2p+1}` for `t > 0`. -/
lemma kG_ge (p : ℕ) {t : ℝ} (ht : 0 < t) : t ^ (2 * p + 1) / (2 * π) ^ (2 * p + 1) ≤ kG p t := by
  unfold kG
  have hsh : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
  have hsh2 := sinh_le_half_exp (π * t)
  have hE : 0 < Real.exp (π * t) := Real.exp_pos _
  have h1 : 2 * π * t ≤ π * t / Real.sinh (π * t) * Real.exp (π * t) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hsh]
    have : 0 < π * t := by positivity
    nlinarith
  have hP := Pq_ge p t
  have e : Pq p t * (π * t / Real.sinh (π * t)) / (2 * π) ^ (2 * p + 2) * Real.exp (π * t) =
      Pq p t * (π * t / Real.sinh (π * t) * Real.exp (π * t)) / (2 * π) ^ (2 * p + 2) := by ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  calc t ^ (2 * p + 1) * (2 * π) ^ (2 * p + 2) = t ^ (2 * p) * (2 * π * t) * (2 * π) ^ (2 * p + 1) := by
        ring
    _ ≤ Pq p t * (π * t / Real.sinh (π * t) * Real.exp (π * t)) * (2 * π) ^ (2 * p + 1) := by
        have : 0 ≤ Pq p t := Pq_nonneg p t
        gcongr

lemma kG_nonneg (p : ℕ) {t : ℝ} (ht : 0 < t) : 0 ≤ kG p t :=
  le_trans (by positivity) (kG_ge p ht)

/-- `kΓ ≤ P(T) e^{πT}/(2π)^{2p+2}` on `(0, T]`. -/
lemma kG_le (p : ℕ) {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    kG p t ≤ Pq p T * Real.exp (π * T) / (2 * π) ^ (2 * p + 2) := by
  unfold kG
  have hsh : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
  have h1 : π * t / Real.sinh (π * t) ≤ 1 := by
    rw [div_le_one hsh]; exact Real.self_le_sinh_iff.mpr (by positivity)
  have hP : Pq p t ≤ Pq p T := by
    unfold Pq
    exact Finset.prod_le_prod (fun _ _ => by positivity) (fun j _ => by gcongr)
  have hE : Real.exp (π * t) ≤ Real.exp (π * T) := Real.exp_le_exp.mpr (by gcongr)
  have h0 : 0 ≤ π * t / Real.sinh (π * t) := by positivity
  have hPt := Pq_nonneg p t
  have hPT := Pq_nonneg p T
  calc Pq p t * (π * t / Real.sinh (π * t)) / (2 * π) ^ (2 * p + 2) * Real.exp (π * t)
      ≤ Pq p T * 1 / (2 * π) ^ (2 * p + 2) * Real.exp (π * T) := by gcongr
    _ = _ := by ring

lemma Pq_div_eq (p : ℕ) {t : ℝ} (ht : t ≠ 0) :
    Pq p t / t ^ (2 * p) = ∏ j ∈ Finset.range p, (1 + ((j : ℝ) + 1) ^ 2 / t ^ 2) := by
  have e : t ^ (2 * p) = ∏ _j ∈ Finset.range p, t ^ 2 := by
    rw [Finset.prod_const, Finset.card_range, ← pow_mul, mul_comm]
  rw [e, Pq, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  field_simp
  ring

/-- `kΓ(t)(2π)^{2p+1}/t^{2p+1} → 1`. -/
lemma tendsto_kG_ratio (p : ℕ) :
    Tendsto (fun t => kG p t * (2 * π) ^ (2 * p + 1) / t ^ (2 * p + 1)) atTop (𝓝 1) := by
  have hq : ∀ c : ℝ, Tendsto (fun t : ℝ => 1 + c / t ^ 2) atTop (𝓝 1) := by
    intro c
    have : Tendsto (fun t : ℝ => c / t ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
    simpa using this.const_add 1
  have hP : Tendsto (fun t : ℝ => ∏ j ∈ Finset.range p, (1 + ((j : ℝ) + 1) ^ 2 / t ^ 2)) atTop
      (𝓝 1) := by
    have := tendsto_finsetProd (Finset.range p) (fun j _ => hq (((j : ℝ) + 1) ^ 2))
    simpa using this
  have he : Tendsto (fun t : ℝ => (1 - Real.exp (-(2 * π * t)))⁻¹) atTop (𝓝 1) := by
    have h1 : Tendsto (fun t : ℝ => Real.exp (-(2 * π * t))) atTop (𝓝 0) := by
      have : Tendsto (fun t : ℝ => -(2 * π * t)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by positivity))
      exact Real.tendsto_exp_atBot.comp this
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub h1).inv₀ (by norm_num)
    simpa using this
  have hlim := hP.mul he
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hsh' : Real.sinh (π * t) = Real.exp (π * t) * (1 - Real.exp (-(2 * π * t))) / 2 := by
    rw [Real.sinh_eq, mul_sub, mul_one, ← Real.exp_add]
    congr 1; congr 1; congr 1; ring
  have h1e : 0 < 1 - Real.exp (-(2 * π * t)) := by
    have : Real.exp (-(2 * π * t)) < 1 := Real.exp_lt_one_iff.mpr (by
      have : 0 < 2 * π * t := by positivity
      linarith)
    linarith
  rw [← Pq_div_eq p ht.ne']
  unfold kG
  rw [hsh']
  have hE := Real.exp_pos (π * t)
  field_simp
  ring

end RamanujanTau.GeneralCuspMoments
