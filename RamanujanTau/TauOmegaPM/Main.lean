/-
# Ω± for the partial sums of `τ(n)` (and of every level-one cusp form with real coefficients)

Headlines (evidence level (1): Lean, axiom-clean, unconditional; no Deligne):

* `cuspForm_partial_sum_omega_pm`: for `f ≠ 0` in `S_k(SL₂(ℤ))` with real coefficients, every
  `β < (k−1)/2 + 1/10` and every `c ∈ ℝ`, there are arbitrarily large `x` with
  `∑_{n≤x} a_f(n) < −c x^β`, and arbitrarily large `x` with `∑_{n≤x} a_f(n) > c x^β`;
* `tau_partial_sum_omega_pm`: the case `f = Δ`: every `β < 28/5 = 11/2 + 1/10`.

So `∑_{n≤x} τ(n) = Ω±(x^{28/5−ε})` (in the strong form `limsup = +∞`, `liminf = −∞` after
dividing by `x^β`). The threshold is `(k−1)/2 + 1/10 = 2α − θ`, where `α = (2k−1)/4` is the
exact Ω-exponent of `TauOmegaPartial` and `θ = (k−1)/2 + 2/5` is the unconditional upper
exponent of `TauPartialSumsSharp`. The loss against `α` is `θ − α = 3/20`.

Build: `nice -n 10 lake build RamanujanTau.TauOmegaPM.Main`.
-/
import RamanujanTau.TauOmegaPM.OmegaPM
import RamanujanTau.HardyZerosGeneral.Main

set_option autoImplicit false

namespace RamanujanTau.TauOmegaPM

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.HeckeConvexGeneral RamanujanTau.TauOmegaPartial
open scoped MatrixGroups

variable {k : ℕ}

/-- **Ω± for cusp-form partial sums**: for every nonzero level-one cusp form `f` of weight `k`
with real Fourier coefficients, every `β < (k−1)/2 + 1/10`, every `c ∈ ℝ` and every `X`, there
are `x ≥ X` with `∑_{n≤x} a_f(n) < −c x^β` and `x ≥ X` with `∑_{n≤x} a_f(n) > c x^β`. -/
theorem cuspForm_partial_sum_omega_pm (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) {β : ℝ} (hβ : β < ((k : ℝ) - 1) / 2 + 1 / 10)
    (c X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧ (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n).re < -c * x ^ β) ∧
    (∃ x : ℝ, X ≤ x ∧ c * x ^ β < (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n).re) := by
  have hk : 12 ≤ k := by
    by_contra h; exact hf (eq_zero_of_lt_twelve f (by omega))
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  set β' : ℝ := max β (((k : ℝ) - 1) / 2) with hβ'
  have hβ'0 : 0 < β' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hβ'b : β' < ((k : ℝ) - 1) / 2 + 1 / 10 := max_lt hβ (by linarith)
  have hcmp : ∀ x : ℝ, 1 ≤ x → -|c| * x ^ β' ≤ -c * x ^ β := by
    intro x hx
    have h1 : x ^ β ≤ x ^ β' := Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
    have h2 : 0 ≤ x ^ β := Real.rpow_nonneg (by linarith) _
    nlinarith [le_abs_self c, abs_nonneg c]
  constructor
  · by_contra hno
    push Not at hno
    refine no_one_sided f hf hreal hβ'0 hβ'b (ε := 1) (Or.inl rfl) (c := |c|) (X0 := max X 1)
      fun x hx => ?_
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
    have := hno x (le_trans (le_max_left _ _) hx)
    rw [one_mul]
    exact (hcmp x hx1).trans this
  · by_contra hno
    push Not at hno
    refine no_one_sided f hf hreal hβ'0 hβ'b (ε := -1) (Or.inr rfl) (c := |c|) (X0 := max X 1)
      fun x hx => ?_
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
    have := hno x (le_trans (le_max_left _ _) hx)
    have h2 := hcmp x hx1
    have e : (A f x).re = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n).re := rfl
    rw [e]; linarith

/-- **`∑_{n≤x} τ(n) = Ω±(x^β)` for every `β < 28/5`**, in the strong form: for every `c ∈ ℝ` the
sum is `< −c x^β` for arbitrarily large `x`, and `> c x^β` for arbitrarily large `x`. -/
theorem tau_partial_sum_omega_pm {β : ℝ} (hβ : β < (28 : ℝ) / 5) (c X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) < -c * x ^ β) ∧
    (∃ x : ℝ, X ≤ x ∧ c * x ^ β < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) := by
  have hreal : ∀ n, (coef (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ))
      n).im = 0 := fun n => by
    rw [coef_discriminant]; simp [tauC]
  have hβ' : β < (((12 : ℕ) : ℝ) - 1) / 2 + 1 / 10 := by norm_num; linarith
  obtain ⟨⟨x1, hx1, h1⟩, ⟨x2, hx2, h2⟩⟩ := cuspForm_partial_sum_omega_pm (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ))
    RamanujanTau.HardyZerosGeneral.discriminant_ne_zero' hreal hβ' c X
  have e : ∀ x : ℝ, (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      coef (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) n).re =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) := by
    intro x
    simp_rw [coef_discriminant]
    rw [Complex.re_sum]
    simp [tauC]
  rw [e] at h1 h2
  exact ⟨⟨x1, hx1, h1⟩, ⟨x2, hx2, h2⟩⟩

end RamanujanTau.TauOmegaPM

#print axioms RamanujanTau.TauOmegaPM.landau_mellin
#print axioms RamanujanTau.TauOmegaPM.hasDerivAt_mellin_neg
#print axioms RamanujanTau.TauOmegaPM.iteratedDeriv_mellin_neg
#print axioms RamanujanTau.TauOmegaPM.mellin_eq_of_eventually
#print axioms RamanujanTau.TauOmegaPM.conv_of_one_sided
#print axioms RamanujanTau.TauOmegaPM.false_of_conv
#print axioms RamanujanTau.TauOmegaPM.no_one_sided
#print axioms RamanujanTau.TauOmegaPM.cuspForm_partial_sum_omega_pm
#print axioms RamanujanTau.TauOmegaPM.tau_partial_sum_omega_pm
