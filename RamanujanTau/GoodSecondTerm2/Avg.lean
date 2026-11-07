/-
# The `u`-average of `Off(u)` equals `Σ_p zz(p)`

`avgOff_eq`: `(1/H) ∫_T^{T+H} Off(u) du = Σ_p zz T H p`.
-/
import RamanujanTau.GoodSecondTerm2.OffTotal

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm2

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.SubconvexityCond
open scoped Interval

/-- Continuity of `t ↦ boD t p` at `t > 0`. -/
lemma continuousAt_boD (p : ℕ × ℕ) {t : ℝ} (ht : 0 < t) : ContinuousAt (fun t => boD t p) t := by
  unfold boD
  by_cases h : p.1 = p.2
  · simp only [h, if_true]; exact continuousAt_const
  · simp only [h, if_false]
    unfold bD
    have hE : ContinuousAt ellT t := (hasDerivAt_ellT ht).continuousAt
    refine ContinuousAt.mul (ContinuousAt.mul continuousAt_const (by fun_prop)) ?_
    exact Complex.continuous_ofReal.continuousAt.comp (continuous_V.continuousAt.comp
      (continuousAt_const.sub (continuousAt_const.mul hE)))

lemma continuousOn_boD' (p : ℕ × ℕ) : ContinuousOn (fun t => boD t p) (Ioi 0) := fun t ht =>
  (continuousAt_boD p ht).continuousWithinAt

/-- The `u`-average identity: `∫_T^{T'} G = H G(T) + ∫_T^{T'} (T'−t) g(t) dt`. -/
lemma avg_identity {g : ℝ → ℂ} (hg : ContinuousOn g (Ioi 0)) {T H : ℝ} (hT : 16 ≤ T) (hH : 0 < H) :
    ∫ u in T..T + H, (∫ t in (16 : ℝ)..u, g t) =
      (H : ℂ) * (∫ t in (16 : ℝ)..T, g t) + ∫ t in T..T + H, ((T + H - t : ℝ) : ℂ) * g t := by
  have hTH : T ≤ T + H := by linarith
  have hII : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable g volume a b := fun a b ha hb =>
    (hg.mono (by
      intro x hx
      rcases le_total a b with h | h
      · rw [uIcc_of_le h] at hx; exact lt_of_lt_of_le ha hx.1
      · rw [uIcc_of_ge h] at hx; exact lt_of_lt_of_le hb hx.1)).intervalIntegrable
  have hF : ∀ x ∈ [[T, T + H]], HasDerivAt (fun u => ∫ t in (16 : ℝ)..u, g t) (g x) x := by
    intro x hx
    rw [uIcc_of_le hTH] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    exact intervalIntegral.integral_hasDerivAt_right (hII 16 x (by norm_num) hx0)
      ((hg.mono (Set.Subset.refl _)).stronglyMeasurableAtFilter isOpen_Ioi x hx0)
      (hg.continuousAt (isOpen_Ioi.mem_nhds hx0))
  have hv : ∀ x ∈ [[T, T + H]], HasDerivAt (fun u : ℝ => ((u - (T + H) : ℝ) : ℂ)) 1 x := by
    intro x _
    simpa using ((hasDerivAt_id x).sub_const (T + H)).ofReal_comp
  have hgi : IntervalIntegrable g volume T (T + H) := hII T (T + H) (by linarith) (by linarith)
  have h1i : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume T (T + H) := intervalIntegrable_const
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hF hv hgi h1i
  simp only [mul_one] at hibp
  rw [hibp]
  have e : (∫ x in T..T + H, g x * ((x - (T + H) : ℝ) : ℂ)) = -∫ t in T..T + H, ((T + H - t : ℝ) : ℂ) * g t := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext t; push_cast; ring
  rw [e]
  push_cast
  ring

lemma boD_off (t : ℝ) {p : ℕ × ℕ} (hp : p.1 ≠ p.2) :
    boD t p = (coefD p : ℂ) * (cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) * (WV (lg p.1 + lg p.2) t : ℂ)) := by
  unfold boD bD WV
  rw [if_neg hp]; ring

/-- Per pair: the `u`-average of `∫_{16}^u b_p` is `zz T H p`. -/
lemma avg_pair {T H : ℝ} (hT : 16 ≤ T) (hH : 0 < H) (p : ℕ × ℕ) :
    (1 / (H : ℂ)) * ∫ u in T..T + H, (∫ t in (16 : ℝ)..u, boD t p) = zz T H p := by
  rw [avg_identity (continuousOn_boD' p) hT hH]
  by_cases hp : p.1 = p.2
  · simp [boD, hp, zz]
  · unfold zz Ptil
    rw [if_neg hp]
    simp_rw [boD_off _ hp]
    rw [intervalIntegral.integral_const_mul]
    have e : (∫ t in T..T + H, ((T + H - t : ℝ) : ℂ) * ((coefD p : ℂ) *
        (cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) * (WV (lg p.1 + lg p.2) t : ℂ)))) =
        (coefD p : ℂ) * ∫ t in T..T + H, cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) *
          (((T + H - t) * WV (lg p.1 + lg p.2) t : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; push_cast; ring
    rw [e]
    have hH0 : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
    set A := ∫ t in (16 : ℝ)..T, cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) * (WV (lg p.1 + lg p.2) t : ℂ)
    set B := ∫ t in T..T + H, cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) *
      (((T + H - t) * WV (lg p.1 + lg p.2) t : ℝ) : ℂ)
    rw [mul_add, ← mul_assoc, ← mul_assoc, one_div, inv_mul_cancel₀ hH0, one_mul]
    ring

/-- **Average of `Off`.** -/
theorem avgOff_eq {T H : ℝ} (hT : 16 ≤ T) (hH : 0 < H) :
    (1 / (H : ℂ)) * ∫ u in T..T + H, OffInt u = ∑' p, zz T H p := by
  have h16 : (0 : ℝ) < 16 := by norm_num
  have hTH : T ≤ T + H := by linarith
  have hcont : ∀ p, ContinuousOn (fun u => ∫ t in (16 : ℝ)..u, boD t p) (Icc T (T + H)) := by
    intro p u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hII : IntervalIntegrable (fun t => boD t p) volume 16 u :=
      ((continuousOn_boD' p).mono (by
        intro x hx; rw [uIcc_of_le (by linarith [hu.1])] at hx; exact lt_of_lt_of_le h16 hx.1)).intervalIntegrable
    exact (intervalIntegral.integral_hasDerivAt_right hII
      ((continuousOn_boD' p).stronglyMeasurableAtFilter isOpen_Ioi u hu0)
      ((continuousOn_boD' p).continuousAt (isOpen_Ioi.mem_nhds hu0))).continuousAt.continuousWithinAt
  have hb : ∀ p u, u ∈ Icc T (T + H) → ‖∫ t in (16 : ℝ)..u, boD t p‖ ≤ (T + H) * (2 * (T + H) ^ 2 * tt7 p) := by
    intro p u hu
    have h16u : 16 ≤ u := by linarith [hu.1]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 * (T + H) ^ 2 * tt7 p) fun t ht => ?_).trans ?_
    · rw [uIoc_of_le h16u] at ht
      exact norm_boD_le h16 ⟨ht.1.le, ht.2.trans hu.2⟩ p
    · rw [abs_of_nonneg (by linarith)]
      have h7 : 0 ≤ tt7 p := by
        unfold tt7
        exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by positivity) _))
          (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by positivity) _))
      have : 0 ≤ 2 * (T + H) ^ 2 * tt7 p := mul_nonneg (by positivity) h7
      calc 2 * (T + H) ^ 2 * tt7 p * (u - 16) ≤ 2 * (T + H) ^ 2 * tt7 p * (T + H) :=
            mul_le_mul_of_nonneg_left (by linarith [hu.2]) this
        _ = _ := by ring
  have hswap := integral_tsum_Icc hTH hcont (summable_tt7.mul_left ((T + H) * (2 * (T + H) ^ 2))) (fun p u hu => by
    have := hb p u hu; linarith [show (T + H) * (2 * (T + H) ^ 2 * tt7 p) = (T + H) * (2 * (T + H) ^ 2) * tt7 p by ring])
  unfold OffInt
  rw [hswap, ← tsum_mul_left]
  exact tsum_congr fun p => avg_pair hT hH p

end RamanujanTau.GoodSecondTerm2
