/-
# `−L'/L(s) = ∑ Λ_Δ(n) n^{−s}` on `Re s > 1`, and continuity of `−L'/L` on `Re s ≥ 1`

`L = exp ∘ (∑ cc(n) n^{−·})` on the open half-plane, and `log · cc = Λ_Δ` (`vM_eq_logMul`),
so Mathlib's `LSeries_deriv` gives the logarithmic derivative.  Since `L` is entire and has
no zeros on `Re s ≥ 1` (`EdgeNonvanishing.tauL_ne_zero_of_ge`), `−L'/L` is continuous on the
closed half-plane: there is no pole at `s = 1`.
-/
import RamanujanTau.TauPNT.LogEuler

set_option autoImplicit false

namespace RamanujanTau.TauPNT

open Complex Filter Topology LSeries
open RamanujanTau.EdgeNonvanishing RamanujanTau.HeckeL

/-- `−L'/L`. -/
noncomputable def negLogDeriv (s : ℂ) : ℂ := -deriv Lnorm s / Lnorm s

lemma abscissa_vM_le : abscissaOfAbsConv (fun n => (vM n : ℂ)) ≤ 1 := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  rw [vM_eq_logMul]
  exact LSeriesSummable_logMul_of_lt_re (abscissa_cc_le.trans_lt (by simpa using (by exact_mod_cast hy : (1 : EReal) < y)))

lemma LSeriesSummable_vM {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (fun n => (vM n : ℂ)) s := by
  rw [vM_eq_logMul]
  exact LSeriesSummable_logMul_of_lt_re (abscissa_cc_le.trans_lt (by exact_mod_cast hs))

/-- **`−L'/L(s) = ∑ Λ_Δ(n) n^{−s}`** for `Re s > 1`. -/
theorem negLogDeriv_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    negLogDeriv s = LSeries (fun n => (vM n : ℂ)) s := by
  set G := LSeries (fun n => (cc n : ℂ))
  have hab : abscissaOfAbsConv (fun n => (cc n : ℂ)) < s.re :=
    abscissa_cc_le.trans_lt (by exact_mod_cast hs)
  have hG : HasDerivAt G (-LSeries (logMul fun n => (cc n : ℂ)) s) s := LSeries_hasDerivAt hab
  have hev : (fun z => cexp (G z)) =ᶠ[𝓝 s] Lnorm := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact exp_LSeries_cc hz
  have hd : HasDerivAt Lnorm (cexp (G s) * -LSeries (logMul fun n => (cc n : ℂ)) s) s :=
    (hG.cexp).congr_of_eventuallyEq hev.symm
  have hE : cexp (G s) = Lnorm s := exp_LSeries_cc hs
  rw [negLogDeriv, hd.deriv, hE, vM_eq_logMul]
  have h0 : Lnorm s ≠ 0 := Lnorm_ne_zero hs.le
  field_simp

lemma deriv_Lnorm_continuous : Continuous (deriv Lnorm) :=
  continuousOn_univ.mp
    ((Lnorm_differentiable.differentiableOn (s := Set.univ)).deriv isOpen_univ).continuousOn

/-- **`−L'/L` is continuous on `Re s ≥ 1`** (no pole: `L(1+it) ≠ 0`). -/
theorem continuousOn_negLogDeriv : ContinuousOn negLogDeriv {s | 1 ≤ s.re} := by
  intro s hs
  have h0 : Lnorm s ≠ 0 := Lnorm_ne_zero hs
  exact ((deriv_Lnorm_continuous.continuousAt.neg).div
    Lnorm_differentiable.continuous.continuousAt h0).continuousWithinAt

lemma continuousAt_negLogDeriv {s : ℂ} (hs : 1 ≤ s.re) : ContinuousAt negLogDeriv s :=
  (deriv_Lnorm_continuous.continuousAt.neg).div Lnorm_differentiable.continuous.continuousAt
    (Lnorm_ne_zero hs)

end RamanujanTau.TauPNT
