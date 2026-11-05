/-
# Continuation and functional equation of the completed Epstein zeta function of `ℤ + zℤ`

For fixed `z ∈ ℍ`, `(Θ(z,·), Θ(z,·))` is a weak FE-pair of weight `1`, root number `1` and
constant terms `1` (`thetaFE z`): `Θ(z,1/t) = tΘ(z,t)` (`theta_inv`) and
`Θ(z,t) − 1 ≤ e^{−π m (t−1)}(Θ(z,1) − 1)`, `m = min(y, 1/y)`. Mathlib's `WeakFEPair` then gives

    E*(z,s) := Λ_z(s),   E*(z, 1−s) = E*(z, s)  (all s),
    E*(z,s) holomorphic on ℂ ∖ {0,1}, simple poles with residues 1 (at s = 1), −1 (at s = 0),
    E*(z,s) = ∑_{v ∈ ℤ² ∖ 0} Γ(s) (π Q_z(v))^{−s}      (Re s > 1),

with `Q_z(a,c) = |a − cz|²/Im z`. For real `s > 1` the right side is
`π^{−s} Γ(s) ∑_{v≠0} y^s |a − cz|^{−2s} = 2 π^{−s} Γ(s) ζ(2s) E(z,s)` (classical), i.e. `E*(z,s)/2`
is the completed real-analytic Eisenstein series.
-/
import RamanujanTau.RankinSelbergFE.Lattice
import RamanujanTau.EisensteinReal.Eisenstein
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace RamanujanTau.RankinSelbergFE

open Real Filter Topology Asymptotics Set MeasureTheory
open UpperHalfPlane hiding I

/-! ### Elementary properties of `Θ(z, ·)` -/

lemma thetaTerm_anti (z : ℍ) (p : ℤ × ℤ) {s t : ℝ} (hst : s ≤ t) :
    thetaTerm z t p ≤ thetaTerm z s p := by
  unfold thetaTerm
  rw [Real.exp_le_exp]
  have := lq_nonneg z p
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le this) (sub_nonneg.2 hst)]

lemma Theta_antitoneOn (z : ℍ) : AntitoneOn (Theta z) (Ioi 0) := fun s hs t _ hst =>
  (summable_thetaTerm z (lt_of_lt_of_le hs hst)).tsum_le_tsum
    (fun p => thetaTerm_anti z p hst) (summable_thetaTerm z hs)

lemma locallyIntegrableOn_Theta (z : ℍ) :
    LocallyIntegrableOn (fun t => (Theta z t : ℂ)) (Ioi 0) := by
  refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun K hK hKc => ?_
  exact (((Theta_antitoneOn z).mono hK).integrableOn_isCompact hKc).ofReal

/-- `Θ(z,t) − 1 = ∑_{v ≠ 0} exp(−π t Q_z(v))`. -/
lemma hasSum_Theta_sub_one (z : ℍ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun v : ℤ × ℤ => if v = 0 then 0 else thetaTerm z t v) (Theta z t - 1) := by
  have h := (summable_thetaTerm z ht).hasSum
  have h0 := hasSum_ite_eq (0 : ℤ × ℤ) (thetaTerm z t 0)
  rw [thetaTerm_zero] at h0
  convert h.sub h0 using 1
  funext v
  by_cases hv : v = 0
  · subst hv; simp [thetaTerm_zero]
  · simp [hv]

/-- The minimum of `Q_z` on `ℤ² ∖ 0` is at least `min(y, 1/y)`. -/
lemma min_le_lq (z : ℍ) {v : ℤ × ℤ} (hv : v ≠ 0) : min z.im (1 / z.im) ≤ lq z v := by
  have hy := z.im_pos
  unfold lq
  by_cases hc : v.2 = 0
  · have ha : v.1 ≠ 0 := fun ha => hv (Prod.ext ha hc)
    have ha1 : (1 : ℝ) ≤ (v.1 : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ v.1 ^ 2 := by nlinarith [Int.one_le_abs ha, sq_abs v.1]
      exact_mod_cast this
    rw [hc]
    simp only [Int.cast_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero]
    refine (min_le_right _ _).trans ?_
    rw [div_le_div_iff_of_pos_right hy]
    exact ha1
  · have hc1 : (1 : ℝ) ≤ (v.2 : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ v.2 ^ 2 := by nlinarith [Int.one_le_abs hc, sq_abs v.2]
      exact_mod_cast this
    refine (min_le_left _ _).trans ?_
    have : 0 ≤ ((v.1 : ℝ) - v.2 * z.re) ^ 2 / z.im := by positivity
    nlinarith

/-- `0 ≤ Θ(z,t) − 1 ≤ e^{−π m (t−1)} (Θ(z,1) − 1)` for `t ≥ 1`. -/
lemma Theta_sub_one_le (z : ℍ) {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ Theta z t - 1 ∧
      Theta z t - 1 ≤ Real.exp (-π * min z.im (1 / z.im) * (t - 1)) * (Theta z 1 - 1) := by
  have ht0 : 0 < t := by linarith
  set m := min z.im (1 / z.im)
  have h1 := hasSum_Theta_sub_one z ht0
  have h2 := (hasSum_Theta_sub_one z one_pos).mul_left (Real.exp (-π * m * (t - 1)))
  constructor
  · exact h1.nonneg fun v => by by_cases hv : v = 0 <;> simp [hv, (thetaTerm_pos z t v).le]
  · refine hasSum_le (fun v => ?_) h1 h2
    by_cases hv : v = 0
    · simp [hv]
    · simp only [hv, if_false]
      unfold thetaTerm
      rw [← Real.exp_add, Real.exp_le_exp]
      have hq := min_le_lq z hv
      have ht1 : 0 ≤ t - 1 := by linarith
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le ht1) (sub_nonneg.2 hq)]

lemma Theta_top (z : ℍ) (r : ℝ) : (fun t => (Theta z t : ℂ) - 1) =O[atTop] (· ^ r) := by
  have hm : 0 < min z.im (1 / z.im) := lt_min z.im_pos (one_div_pos.2 z.im_pos)
  set m := min z.im (1 / z.im)
  have hE : (fun t : ℝ => (Theta z t : ℂ) - 1) =O[atTop]
      fun t => Real.exp (-(π * m) * t) := by
    refine IsBigO.of_bound (Real.exp (π * m) * (Theta z 1 - 1)) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    obtain ⟨h0, h1⟩ := Theta_sub_one_le z ht
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg h0,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Theta z t - 1 ≤ Real.exp (-π * m * (t - 1)) * (Theta z 1 - 1) := h1
      _ = Real.exp (π * m) * (Theta z 1 - 1) * Real.exp (-(π * m) * t) := by
        have e : Real.exp (-π * m * (t - 1)) = Real.exp (π * m) * Real.exp (-(π * m) * t) := by
          rw [← Real.exp_add]; ring_nf
        rw [e]; ring
  exact hE.trans (isLittleO_exp_neg_mul_rpow_atTop (by positivity) r).isBigO

/-! ### The FE-pair -/

/-- The weak FE-pair `(Θ(z,·), Θ(z,·))`, weight `1`, root number `1`, constants `1`. -/
noncomputable def thetaFE (z : ℍ) : WeakFEPair ℂ where
  f := fun t => (Theta z t : ℂ)
  g := fun t => (Theta z t : ℂ)
  k := 1
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := locallyIntegrableOn_Theta z
  hg_int := locallyIntegrableOn_Theta z
  hk := one_pos
  hε := one_ne_zero
  h_feq := fun x hx => by
    simp only [Real.rpow_one, one_mul]
    rw [theta_inv z hx]; push_cast; ring
  hf_top := Theta_top z
  hg_top := Theta_top z

/-- **The completed Epstein zeta function** `E*(z,s)` of the lattice `ℤ + zℤ` (normalized to
covolume one), continued to `ℂ ∖ {0, 1}`. -/
noncomputable def EpsteinStar (z : ℍ) (s : ℂ) : ℂ := (thetaFE z).Λ s

lemma thetaFE_symm_Λ₀ (z : ℍ) : (thetaFE z).symm.Λ₀ = (thetaFE z).Λ₀ := by
  funext s
  simp only [WeakFEPair.Λ₀, WeakFEPair.f_modif, WeakFEPair.symm, thetaFE, inv_one]

theorem EpsteinStar_eq (z : ℍ) (s : ℂ) :
    EpsteinStar z s = (thetaFE z).Λ₀ s - 1 / s - 1 / (1 - s) := by
  change (thetaFE z).Λ₀ s - (1 / s) • (1 : ℂ) - ((1:ℂ) / (((1:ℝ):ℂ) - s)) • (1 : ℂ) = _
  simp

/-- **Functional equation** `E*(z, 1−s) = E*(z, s)`. -/
theorem EpsteinStar_one_sub (z : ℍ) (s : ℂ) : EpsteinStar z (1 - s) = EpsteinStar z s := by
  have h := (thetaFE z).functional_equation₀ s
  rw [thetaFE_symm_Λ₀] at h
  have h' : (thetaFE z).Λ₀ (1 - s) = (thetaFE z).Λ₀ s := by simpa [thetaFE] using h
  rw [EpsteinStar_eq, EpsteinStar_eq, h', sub_sub_cancel]
  ring

theorem differentiableAt_EpsteinStar (z : ℍ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (EpsteinStar z) s :=
  (thetaFE z).differentiableAt_Λ (Or.inl h0) (Or.inl (by simpa [thetaFE] using h1))

/-- Residue `1` at `s = 1`. -/
theorem EpsteinStar_residue_one (z : ℍ) :
    Tendsto (fun s : ℂ => (s - 1) * EpsteinStar z s) (𝓝[≠] 1) (𝓝 1) := by
  have h := (thetaFE z).Λ_residue_k
  have hk : (((thetaFE z).k : ℝ) : ℂ) = 1 := by simp [thetaFE]
  have hε : (thetaFE z).ε • (thetaFE z).g₀ = (1 : ℂ) := by simp [thetaFE]
  rw [hk, hε] at h
  simpa only [smul_eq_mul] using h

/-- Residue `−1` at `s = 0`. -/
theorem EpsteinStar_residue_zero (z : ℍ) :
    Tendsto (fun s : ℂ => s * EpsteinStar z s) (𝓝[≠] 0) (𝓝 (-1)) := by
  have h := (thetaFE z).Λ_residue_zero
  simp only [smul_eq_mul] at h
  exact h

/-! ### The Dirichlet series on `Re s > 1` -/

/-- `1 / Q_z(a,c)^σ = y^σ |(−c) z + a|^{−2σ}` (the repo's `eSummand`). -/
lemma one_div_lq_rpow (z : ℍ) {v : ℤ × ℤ} (hv : v ≠ 0) (σ : ℝ) :
    1 / lq z v ^ σ = EisensteinReal.eSummand σ z ![-v.2, v.1] := by
  have hy := z.im_pos
  set w : ℂ := (v.1 : ℂ) - v.2 * (z : ℂ)
  have hw : lq z v = ‖w‖ ^ 2 / z.im := by
    rw [lq_eq_normSq, Complex.normSq_eq_norm_sq]
  have hw0 : 0 < ‖w‖ := by
    have := lq_pos z v hv
    rw [hw] at this
    rcases (norm_nonneg w).lt_or_eq with h | h
    · exact h
    · rw [← h] at this; simp at this
  have e : ((![-v.2, v.1] : Fin 2 → ℤ) 0 : ℂ) * (z : ℂ) + ((![-v.2, v.1] : Fin 2 → ℤ) 1 : ℂ) = w := by
    simp [w]; ring
  unfold EisensteinReal.eSummand
  rw [e, hw, Real.div_rpow (by positivity) hy.le, one_div_div, Real.rpow_neg hw0.le,
    ← Real.rpow_natCast, ← Real.rpow_mul hw0.le]
  push_cast
  rw [div_eq_mul_inv]

lemma summable_lq_rpow (z : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : ℤ × ℤ => (if v = 0 then (0 : ℝ) else 1) / lq z v ^ σ := by
  have hinj : Function.Injective fun v : ℤ × ℤ => (![-v.2, v.1] : Fin 2 → ℤ) := by
    intro v w h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    exact Prod.ext h1 h0
  refine Summable.of_nonneg_of_le (fun v => ?_) (fun v => ?_)
    ((EisensteinReal.summable_eSummand hσ z).comp_injective hinj)
  · by_cases hv : v = 0
    · simp [hv]
    · simp only [hv, if_false]
      exact div_nonneg zero_le_one (Real.rpow_nonneg (lq_nonneg z v) _)
  · by_cases hv : v = 0
    · simp only [hv, if_true, zero_div, Function.comp]
      exact EisensteinReal.eSummand_nonneg _ _ _
    · simp only [hv, if_false, Function.comp]
      rw [one_div_lq_rpow z hv]

/-- **Dirichlet series of `E*` on `Re s > 1`:**
`E*(z,s) = ∑_{v ∈ ℤ² ∖ 0} Γ(s) (π Q_z(v))^{−s}`. -/
theorem hasSum_EpsteinStar (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun v : ℤ × ℤ => Complex.Gamma s * (if v = 0 then (0 : ℂ) else 1) /
      ((π * lq z v : ℝ) : ℂ) ^ s) (EpsteinStar z s) := by
  have hM := ((thetaFE z).hasMellin (s := s) (by simp [thetaFE]; linarith)).2
  have hM' : mellin (fun t => (Theta z t : ℂ) - 1) s = EpsteinStar z s := hM
  rw [← hM']
  refine hasSum_mellin (a := fun v : ℤ × ℤ => if v = 0 then (0 : ℂ) else 1)
    (p := fun v => π * lq z v) (fun v => ?_) (by linarith) (fun t ht => ?_) ?_
  · by_cases hv : v = 0
    · left; simp [hv]
    · right; exact mul_pos Real.pi_pos (lq_pos z v hv)
  · have h := (hasSum_Theta_sub_one z ht).mapL Complex.ofRealCLM
    simp only [Complex.ofRealCLM_apply] at h
    rw [Complex.ofReal_sub, Complex.ofReal_one] at h
    refine h.congr_fun fun v => ?_
    by_cases hv : v = 0
    · simp [hv]
    · simp only [hv, if_false, one_mul, thetaTerm]
      congr 2; ring
  · have h := (summable_lq_rpow z hs).mul_left ((π ^ s.re)⁻¹)
    refine h.congr fun v => ?_
    by_cases hv : v = 0
    · simp [hv]
    · simp only [hv, if_false, norm_one]
      rw [Real.mul_rpow Real.pi_pos.le (lq_nonneg z v)]
      field_simp

end RamanujanTau.RankinSelbergFE
