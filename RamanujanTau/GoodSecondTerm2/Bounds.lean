/-
# Elementary bounds for the off-diagonal analysis

* `V_le_exp_k`: `V(L) ≤ e^{k²}/(k√π) · e^{−kL}` for every `k > 0`.
* `WV Λ t = V(Λ − 2 log(t/2π))` (the `t`-weight of the `(m,n)` term, `Λ = log(mn)`), with derivative
  `phiD Λ t = (2/t) g(Λ − 2 log(t/2π))`, and `phiD' = (2/t²) g(L)(L − 1)`.
* `phiD_eq`: `phiD = π^{−1} e^{−Λ/2} · e^{L/2} g(L)`, hence `phiD ≤ Kφ e^{−Λ/2} min(1, e^{−2L})`.
-/
import RamanujanTau.GoodSecondTerm.Main

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm2

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm

lemma gk_le_exp_k {k : ℝ} (u : ℝ) : gk u ≤ Real.exp (k ^ 2) * Real.exp (-(k * u)) / Real.sqrt Real.pi := by
  unfold gk
  rw [← Real.exp_add]
  gcongr
  nlinarith [sq_nonneg (u / 2 - k)]

lemma gk_le_exp_k' {k : ℝ} (u : ℝ) : gk u ≤ Real.exp (k ^ 2) * Real.exp (k * u) / Real.sqrt Real.pi := by
  have := gk_le_exp_k (k := -k) u
  simpa [neg_sq, neg_mul, neg_neg] using this

/-- `V(L) ≤ e^{k²}/(k√π) e^{−kL}`. -/
lemma V_le_exp_k {k : ℝ} (hk : 0 < k) (L : ℝ) :
    V L ≤ Real.exp (k ^ 2) / (k * Real.sqrt Real.pi) * Real.exp (-(k * L)) := by
  have hint : IntegrableOn (fun u : ℝ => Real.exp (k ^ 2) / Real.sqrt Real.pi * Real.exp ((-k) * u)) (Ioi L) :=
    (integrableOn_exp_mul_Ioi (by linarith) L).const_mul _
  have h1 : V L ≤ ∫ u in Ioi L, Real.exp (k ^ 2) / Real.sqrt Real.pi * Real.exp ((-k) * u) := by
    refine setIntegral_mono_on integrable_gk.integrableOn hint measurableSet_Ioi fun u _ => ?_
    have := gk_le_exp_k (k := k) u
    rw [show (-k) * u = -(k * u) by ring]; linarith [this, show Real.exp (k ^ 2) * Real.exp (-(k * u)) /
      Real.sqrt Real.pi = Real.exp (k ^ 2) / Real.sqrt Real.pi * Real.exp (-(k * u)) by ring]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)] at h1
  refine h1.trans (le_of_eq ?_)
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  rw [show (-k) * L = -(k * L) by ring]
  field_simp

/-- The `t`-weight `W(t) = V(Λ − 2 log(t/2π))`. -/
noncomputable def WV (Λ t : ℝ) : ℝ := V (Λ - 2 * ellT t)
/-- Its derivative `φ(t) = (2/t) g(Λ − 2 log(t/2π))`. -/
noncomputable def phiD (Λ t : ℝ) : ℝ := 2 / t * gk (Λ - 2 * ellT t)

lemma hasDerivAt_WV (Λ : ℝ) {t : ℝ} (ht : 0 < t) : HasDerivAt (WV Λ) (phiD Λ t) t := by
  have h := (hasDerivAt_V (Λ - 2 * ellT t)).comp t
    ((hasDerivAt_const t Λ).sub ((hasDerivAt_ellT ht).const_mul 2))
  unfold WV phiD
  convert h using 1
  ring

lemma hasDerivAt_gk (u : ℝ) : HasDerivAt gk (-(u / 2) * gk u) u := by
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 4) (-(u / 2)) u := by
    have := ((hasDerivAt_pow 2 u).neg).div_const 4
    convert this using 1; push_cast; ring
  have h := (h1.exp).div_const (Real.sqrt Real.pi)
  show HasDerivAt (fun x => Real.exp (-(x ^ 2) / 4) / Real.sqrt Real.pi) _ u
  convert h using 1
  unfold gk; ring

lemma hasDerivAt_phiD (Λ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (phiD Λ) (2 / t ^ 2 * gk (Λ - 2 * ellT t) * ((Λ - 2 * ellT t) - 1)) t := by
  have hL : HasDerivAt (fun t => Λ - 2 * ellT t) (-(2 * (1 / t))) t := by
    simpa using (hasDerivAt_const t Λ).sub ((hasDerivAt_ellT ht).const_mul 2)
  have hg := (hasDerivAt_gk (Λ - 2 * ellT t)).comp t hL
  have hinv : HasDerivAt (fun t : ℝ => 2 / t) (-(2 / t ^ 2)) t := by
    have := (hasDerivAt_inv ht.ne').const_mul 2
    convert this using 1
    ring
  have := hinv.mul hg
  unfold phiD
  convert this using 1
  simp only [Function.comp_apply]
  field_simp
  ring

lemma phiD_nonneg (Λ t : ℝ) (ht : 0 < t) : 0 ≤ phiD Λ t := by
  unfold phiD; have := gk_pos (Λ - 2 * ellT t); positivity

/-- `φ = π^{−1} e^{−Λ/2} e^{L/2} g(L)`, `L = Λ − 2 log(t/2π)`. -/
lemma phiD_eq (Λ : ℝ) {t : ℝ} (ht : 0 < t) :
    phiD Λ t = 1 / Real.pi * Real.exp (-(Λ / 2)) * (Real.exp ((Λ - 2 * ellT t) / 2) * gk (Λ - 2 * ellT t)) := by
  unfold phiD
  have h : Real.exp (-(Λ / 2)) * Real.exp ((Λ - 2 * ellT t) / 2) = 2 * Real.pi / t := by
    rw [← Real.exp_add, show -(Λ / 2) + (Λ - 2 * ellT t) / 2 = -(ellT t) by ring, Real.exp_neg,
      exp_ellT ht]
    field_simp
  rw [show 1 / Real.pi * Real.exp (-(Λ / 2)) * (Real.exp ((Λ - 2 * ellT t) / 2) * gk (Λ - 2 * ellT t)) =
    1 / Real.pi * (Real.exp (-(Λ / 2)) * Real.exp ((Λ - 2 * ellT t) / 2)) * gk (Λ - 2 * ellT t) by ring, h]
  field_simp

lemma exp_half_gk_le (L : ℝ) : Real.exp (L / 2) * gk L ≤ Real.exp (25 / 4) / Real.sqrt Real.pi := by
  unfold gk
  rw [mul_div_assoc', ← Real.exp_add]
  gcongr
  nlinarith [sq_nonneg (L / 2 - 1 / 2)]

lemma exp_half_gk_le' (L : ℝ) :
    Real.exp (L / 2) * gk L ≤ Real.exp (25 / 4) / Real.sqrt Real.pi * Real.exp (-(2 * L)) := by
  unfold gk
  rw [mul_div_assoc', ← Real.exp_add, div_mul_eq_mul_div, ← Real.exp_add]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (L / 2 - 5 / 2)]

/-- `Kφ = e^{25/4}/(π√π)`. -/
noncomputable def Kphi : ℝ := Real.exp (25 / 4) / (Real.pi * Real.sqrt Real.pi)

lemma Kphi_pos : 0 < Kphi := by
  unfold Kphi; have := Real.sqrt_pos.mpr Real.pi_pos; have := Real.pi_pos; positivity

lemma phiD_le (Λ : ℝ) {t : ℝ} (ht : 0 < t) : phiD Λ t ≤ Kphi * Real.exp (-(Λ / 2)) := by
  rw [phiD_eq Λ ht]
  have := exp_half_gk_le (Λ - 2 * ellT t)
  have hE := Real.exp_pos (-(Λ / 2))
  calc 1 / Real.pi * Real.exp (-(Λ / 2)) * (Real.exp ((Λ - 2 * ellT t) / 2) * gk (Λ - 2 * ellT t))
      ≤ 1 / Real.pi * Real.exp (-(Λ / 2)) * (Real.exp (25 / 4) / Real.sqrt Real.pi) := by gcongr
    _ = _ := by unfold Kphi; field_simp

lemma phiD_le' (Λ : ℝ) {t : ℝ} (ht : 0 < t) :
    phiD Λ t ≤ Kphi * Real.exp (-(Λ / 2)) * Real.exp (-(2 * (Λ - 2 * ellT t))) := by
  rw [phiD_eq Λ ht]
  have := exp_half_gk_le' (Λ - 2 * ellT t)
  have hE := Real.exp_pos (-(Λ / 2))
  calc 1 / Real.pi * Real.exp (-(Λ / 2)) * (Real.exp ((Λ - 2 * ellT t) / 2) * gk (Λ - 2 * ellT t))
      ≤ 1 / Real.pi * Real.exp (-(Λ / 2)) * (Real.exp (25 / 4) / Real.sqrt Real.pi *
          Real.exp (-(2 * (Λ - 2 * ellT t)))) := by gcongr
    _ = _ := by unfold Kphi; field_simp

lemma ellT_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : ellT s ≤ ellT t := by
  unfold ellT; exact Real.log_le_log (by positivity) (by gcongr)

/-- On `[a, T']`: `φ ≤ Kφ e^{−Λ/2} min(1, e^{−2(Λ − 2 log(T'/2π))})`. -/
lemma phiD_le_min (Λ : ℝ) {t T' : ℝ} (ht : 0 < t) (htT : t ≤ T') :
    phiD Λ t ≤ Kphi * Real.exp (-(Λ / 2)) * min 1 (Real.exp (-(2 * (Λ - 2 * ellT T')))) := by
  rcases le_total 1 (Real.exp (-(2 * (Λ - 2 * ellT T')))) with h | h
  · rw [min_eq_left h, mul_one]; exact phiD_le Λ ht
  · rw [min_eq_right h]
    refine (phiD_le' Λ ht).trans ?_
    have hm := ellT_mono ht htT
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (by have := Kphi_pos; positivity)

end RamanujanTau.GoodSecondTerm2
