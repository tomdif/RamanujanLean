/-
# The strip side of the Rankin–Selberg unfolding (milestone E3a)

    ∫₀^∞ I(y) y^{s-2} dy = Γ(s+11) ∑ₙ τ(n)² (4πn)^{-(s+11)},     I(y) = ∫₀¹ G(x+iy) dx,

as an identity in `[0, ∞]` for every real `s > -11` (`lintegral_mellin_horocycle`).
This is `∫_{Γ∞\ℍ} G(z) y^s dμ` written over the strip `0 ≤ x ≤ 1`. Combined with the unfolding
`∫_{Γ\ℍ} G E(·,s) dμ = ∫_{Γ∞\ℍ} G y^s dμ` (milestone E3b, not done: it needs `ModularGroup.fd` as
a measure-theoretic fundamental domain) it is the Rankin–Selberg integral.

Proof: Parseval (`hasSum_tau_sq`), Tonelli (`lintegral_tsum`), Euler's integral.
-/
import RamanujanTau.EisensteinReal.Asymptotic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false

namespace RamanujanTau.EisensteinReal

open Real MeasureTheory Filter Topology Set
open RamanujanTau.RankinSelberg
open UpperHalfPlane hiding I

/-- The horocycle mean `I(y) = ∫₀¹ G(x+iy) dx` (`0` for `y ≤ 0`). -/
noncomputable def Ihor (y : ℝ) : ℝ :=
  if h : 0 < y then ∫ x in (0 : ℝ)..1, G (hp h x) else 0

/-- The `n`-th term `τ(n)² y^{s+10} e^{-4πny}`. -/
noncomputable def mterm (s : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  ((tau n : ℝ)) ^ 2 * (y ^ (s + 10) * Real.exp (-(4 * π * n) * y))

lemma mterm_nonneg (s : ℝ) (n : ℕ) {y : ℝ} (hy : 0 < y) : 0 ≤ mterm s n y := by
  unfold mterm
  exact mul_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg hy.le _) (Real.exp_pos _).le)

lemma hasSum_mterm (s : ℝ) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n => mterm s n y) (Ihor y * y ^ (s - 2)) := by
  have h := (hasSum_tau_sq hy).mul_right (y ^ 12 * y ^ (s - 2))
  have e1 : ∀ n : ℕ, Real.exp (-2 * π * y) ^ (2 * n) = Real.exp (-(4 * π * n) * y) := by
    intro n; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : y ^ (s + 10) = y ^ 12 * y ^ (s - 2) := by
    rw [show s + 10 = ((12 : ℕ) : ℝ) + (s - 2) by push_cast; ring, Real.rpow_add hy,
      Real.rpow_natCast]
  unfold Ihor
  rw [dif_pos hy, integral_G hy]
  convert h using 1
  · funext n; unfold mterm; rw [e1, e2]; ring
  · ring

lemma integral_mterm {s : ℝ} (hs : -11 < s) {n : ℕ} (hn : 1 ≤ n) :
    ∫ y in Ioi (0 : ℝ), mterm s n y =
      ((tau n : ℝ)) ^ 2 * Real.Gamma (s + 11) / (4 * π * n) ^ (s + 11) := by
  have hb : 0 < 4 * π * (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  unfold mterm
  rw [integral_const_mul]
  have e : ∀ y : ℝ, y ^ (s + 10) * Real.exp (-(4 * π * n) * y) =
      y ^ ((s + 11) - 1) * Real.exp (-((4 * π * n) * y)) := by
    intro y; rw [show s + 11 - 1 = s + 10 by ring, neg_mul]
  simp_rw [e]
  rw [integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hb, Real.div_rpow zero_le_one hb.le,
    Real.one_rpow]
  ring

lemma integrableOn_mterm {s : ℝ} (hs : -11 < s) {n : ℕ} (hn : 1 ≤ n) :
    IntegrableOn (mterm s n) (Ioi 0) := by
  have hb : 0 < 4 * π * (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := s + 10) (p := 1) (by linarith) le_rfl
    hb).const_mul (((tau n : ℝ)) ^ 2)
  simp only [Real.rpow_one] at h
  exact h

/-- **Strip side of the unfolding** (in `[0, ∞]`, any real `s > -11`):
`∫₀^∞ I(y) y^{s-2} dy = ∑ₙ τ(n)² Γ(s+11) / (4πn)^{s+11}`. -/
theorem lintegral_mellin_horocycle {s : ℝ} (hs : -11 < s) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Ihor y * y ^ (s - 2)) =
      ∑' n : ℕ, ENNReal.ofReal (((tau n : ℝ)) ^ 2 * Real.Gamma (s + 11) /
        (4 * π * n) ^ (s + 11)) := by
  calc ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Ihor y * y ^ (s - 2))
      = ∫⁻ y in Ioi (0 : ℝ), ∑' n : ℕ, ENNReal.ofReal (mterm s n y) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
        rw [← (hasSum_mterm s hy).tsum_eq,
          ENNReal.ofReal_tsum_of_nonneg (fun n => mterm_nonneg s n hy) (hasSum_mterm s hy).summable]
    _ = ∑' n : ℕ, ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (mterm s n y) := by
        refine lintegral_tsum fun n => ?_
        refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
        unfold mterm; fun_prop
    _ = _ := by
        refine tsum_congr fun n => ?_
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [mterm, tau_zero]
        · rw [← integral_mterm hs hn, ofReal_integral_eq_lintegral_ofReal (integrableOn_mterm hs hn)
            ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy =>
              mterm_nonneg s n hy))]

end RamanujanTau.EisensteinReal

#print axioms RamanujanTau.EisensteinReal.lintegral_mellin_horocycle
