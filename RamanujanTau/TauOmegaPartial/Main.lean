/-
# `∑_{n≤x} τ(n) = Ω(x^{23/4})` — the Ω-counterpart of `TauPartialSumsSharp`

Headlines (evidence level (1): Lean, axiom-clean, unconditional; no Deligne):

* `cuspForm_partial_sum_omega`: for every nonzero `f ∈ S_k(SL₂(ℤ))`, `∃ c > 0` such that
  `‖∑_{n≤x} a_f(n)‖ ≥ c x^{(k−1)/2+1/4}` for arbitrarily large `x`;
* `cuspForm_partial_sum_not_isLittleO`: `∑_{n≤x} a_f(n) ≠ o(x^{(k−1)/2+1/4})`;
* `tau_partial_sum_omega`, `tau_partial_sum_not_isLittleO`: the case `f = Δ`, exponent `23/4`.

Combined with `TauPartialSumsSharp.tau_partial_sum_sharp` (`≪ x^{59/10+ε}`) the true exponent
of `∑_{n≤x} τ(n)` lies in `[23/4, 59/10]`.

Build: `nice -n 10 lake build RamanujanTau.TauOmegaPartial.Main`.
-/
import RamanujanTau.TauOmegaPartial.Omega
import RamanujanTau.HardyZerosGeneral.Main

set_option autoImplicit false

namespace RamanujanTau.TauOmegaPartial

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups

variable {k : ℕ}

/-- **`∑_{n≤x} a_f(n)` is not `o(x^{(k−1)/2+1/4})`** for `f ≠ 0`. -/
theorem cuspForm_partial_sum_not_isLittleO (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    ¬ (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n) =o[atTop]
      (fun x : ℝ => x ^ (((k : ℝ) - 1) / 2 + 1 / 4)) := by
  intro ho
  obtain ⟨c, hc0, hc⟩ := cuspForm_partial_sum_omega f hf
  have hev := ho.def (show 0 < c / 2 by positivity)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hev
  obtain ⟨x, hx, hcx⟩ := hc (max X 1)
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have h := hX x (le_trans (le_max_left _ _) hx)
  have hp : 0 < x ^ (((k : ℝ) - 1) / 2 + 1 / 4) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.norm_of_nonneg hp.le] at h
  nlinarith [mul_pos hc0 hp]

/-- **`∑_{n≤x} τ(n) = Ω(x^{23/4})`**: there is `c > 0` with `|∑_{n≤x} τ(n)| ≥ c x^{23/4}` for
arbitrarily large `x`. -/
theorem tau_partial_sum_omega :
    ∃ c : ℝ, 0 < c ∧ ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      c * x ^ ((23 : ℝ) / 4) ≤ |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)| := by
  obtain ⟨c, hc0, hc⟩ := cuspForm_partial_sum_omega (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ))
    RamanujanTau.HardyZerosGeneral.discriminant_ne_zero'
  refine ⟨c, hc0, fun X => ?_⟩
  obtain ⟨x, hx, h⟩ := hc X
  refine ⟨x, hx, ?_⟩
  simp_rw [coef_discriminant] at h
  have e1 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, tauC n =
      ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [e1, Complex.norm_real, Real.norm_eq_abs] at h
  have e2 : (((12 : ℕ) : ℝ) - 1) / 2 + 1 / 4 = (23 : ℝ) / 4 := by norm_num
  rw [e2] at h
  exact h

/-- **`∑_{n≤x} τ(n) ≠ o(x^{23/4})`.** -/
theorem tau_partial_sum_not_isLittleO :
    ¬ (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) =o[atTop]
      (fun x : ℝ => x ^ ((23 : ℝ) / 4)) := by
  intro ho
  obtain ⟨c, hc0, hc⟩ := tau_partial_sum_omega
  have hev := ho.def (show 0 < c / 2 by positivity)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hev
  obtain ⟨x, hx, hcx⟩ := hc (max X 1)
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have h := hX x (le_trans (le_max_left _ _) hx)
  have hp : 0 < x ^ ((23 : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.norm_of_nonneg hp.le, Real.norm_eq_abs] at h
  nlinarith [mul_pos hc0 hp]

end RamanujanTau.TauOmegaPartial

#print axioms RamanujanTau.TauOmegaPartial.plancherel_of_integrable
#print axioms RamanujanTau.TauOmegaPartial.mellin_A_eq
#print axioms RamanujanTau.TauOmegaPartial.fourier_hfun
#print axioms RamanujanTau.TauOmegaPartial.hfun_L1L2
#print axioms RamanujanTau.TauOmegaPartial.fe_lower
#print axioms RamanujanTau.TauOmegaPartial.tail_small
#print axioms RamanujanTau.TauOmegaPartial.first_moment
#print axioms RamanujanTau.TauOmegaPartial.block_lower
#print axioms RamanujanTau.TauOmegaPartial.cuspForm_partial_sum_omega
#print axioms RamanujanTau.TauOmegaPartial.cuspForm_partial_sum_not_isLittleO
#print axioms RamanujanTau.TauOmegaPartial.tau_partial_sum_omega
#print axioms RamanujanTau.TauOmegaPartial.tau_partial_sum_not_isLittleO
