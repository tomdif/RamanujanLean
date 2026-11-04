/-
# GORZ Theorem 2 for `d = 2`: the Turán inequalities for `Ξ`, for every `n ≥ 0`

* **`gamma_eq_mom`** (unconditional): `γ(n) = 32 · n!/(2n)! · ∫_0^∞ u^{2n} Φ(u) du` for all `n`, where `γ` is
  `gammaMathlib` (from Mathlib's `completedRiemannZeta`) and `Φ = PhiR` is Riemann's kernel as an explicit series.
* **`CVHyp`** (named hypothesis): `R(u) = −Φ'(u)/(uΦ(u))` is nondecreasing on `(0,∞)`, with `Φ' = PhiD` the
  termwise derivative.  Equivalently `log Φ(√v)` is concave in `v > 0`; this is the theorem of
  Csordas–Varga (Constr. Approx. 4 (1988)), the key input of Csordas–Norfolk–Varga (Trans. AMS 296 (1986)).
* **`turan_gamma`**: `γ(n)γ(n+2) ≤ γ(n+1)²` for every `n ≥ 0`, and **`jensen2_gamma`**: `J^{2,n}_γ` is
  hyperbolic for every `n ≥ 0`, both conditional on `CVHyp` only.
-/
import RamanujanTau.GORZXiEff.Gamma0

set_option autoImplicit false

namespace GORZXiEff

open Real Set GORZXi JensenThreshold

/-- `PhiD` is the genuine derivative of `PhiR` on `(0,∞)` (so `CVHyp` is a statement about `Φ'/Φ`). -/
theorem hasDerivAt_PhiR {u : ℝ} (hu : 0 < u) : HasDerivAt PhiR (PhiD u) u := by
  show HasDerivAt (fun z => ∑' k, phik k z) (∑' k, phik' k u) u
  refine hasDerivAt_tsum_of_isPreconnected (g := phik) (g' := phik')
    (u := fun k => (|15 * π ^ 2| + |-4 * π ^ 3| + |-(15 / 2) * π|) * cK k)
    (summable_cK.mul_left _) isOpen_Ioi isPreconnected_Ioi (fun k y _ => hasDerivAt_phik k y)
    (fun k y hy => ?_) (y₀ := 1) (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (dom_phik.summable zero_le_one) hu
  have hy' : (0 : ℝ) ≤ y := le_of_lt hy
  rw [Real.norm_eq_abs]
  refine (dom_phik'.bound k y hy').trans ?_
  have : rexp (-y) ≤ 1 := exp_le_one_iff.2 (by linarith)
  have := mul_nonneg dom_phik'.L_nonneg (cK_nonneg k)
  nlinarith

/-- **Named hypothesis (Csordas–Varga 1988)**: `u ↦ −Φ'(u)/(uΦ(u))` is nondecreasing on `(0,∞)`. -/
def CVHyp : Prop := MonotoneOn (ratioR PhiR PhiD) (Ioi 0)

/-- `γ(n) = 32 · n!/(2n)! · ∫_0^∞ u^{2n} Φ`, every `n ≥ 0` (unconditional). -/
theorem gamma_eq_mom (n : ℕ) : gammaMathlib n = 32 * fq n * mom PhiR (2 * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact gammaMathlib_zero_eq_mom
  · exact gammaMathlib_eq_mom n hn

/-- **Turán inequalities for `Ξ`** (Csordas–Norfolk–Varga), conditional on `CVHyp`. -/
theorem turan_gamma (hCV : CVHyp) (n : ℕ) :
    gammaMathlib n * gammaMathlib (n + 2) ≤ gammaMathlib (n + 1) ^ 2 :=
  turan_seq kernelMom_PhiR hCV (by norm_num : (0 : ℝ) < 32) gamma_eq_mom n

/-- **GORZ Theorem 2, `d = 2`**: `J^{2,n}_γ` is hyperbolic for every `n ≥ 0`, conditional on `CVHyp`. -/
theorem jensen2_gamma (hCV : CVHyp) (n : ℕ) : Hyperbolic (jensenSeq gammaMathlib 2 n) :=
  jensen2_hyperbolic kernelMom_PhiR hCV (by norm_num : (0 : ℝ) < 32) gamma_eq_mom n

end GORZXiEff

#print axioms GORZXiEff.jensen2_gamma
#print axioms GORZXiEff.turan_gamma
#print axioms GORZXiEff.gamma_eq_mom
#print axioms GORZXiEff.turan_mom
#print axioms GORZXiEff.kernelMom_PhiR
#print axioms GORZXiEff.Tth'_one
#print axioms GORZXiEff.hasDerivAt_PhiR
