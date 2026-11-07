/-
# Localization of the zeros of `L(Δ,s)`

Unnormalized coordinates: weight 12, critical line `Re s = 6`, critical strip `11/2 ≤ Re s ≤ 13/2`.

* `tauL_ne_zero_of_gt`      : no zeros for `Re s > 13/2` (absolutely convergent Euler product);
* `tauL_eq_zero_iff_of_lt`  : for `Re s < 11/2`, `tauL s = 0 ↔ s ∈ {0, −1, −2, …}` (functional equation);
* `tauL_zeros_in_strip`     : every non-trivial zero has `11/2 ≤ Re s ≤ 13/2`;
* symmetries `s ↦ 12 − s` and `s ↦ conj s` of the non-trivial zeros.
-/
import RamanujanTau.HeckeZeros.EulerProduct
import RamanujanTau.HeckeL.Positivity

set_option autoImplicit false

namespace RamanujanTau.HeckeZeros

open Complex MeasureTheory Set
open RamanujanTau.HeckeL RamanujanTau.HeckeConvex
open scoped ComplexConjugate Real

lemma ne_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) : ∀ n : ℕ, s ≠ -n := by
  intro n h
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-- `Λ(s) ≠ 0` for `Re s > 13/2`. -/
theorem heckeLambda_ne_zero_of_gt {s : ℂ} (hs : 13 / 2 < s.re) : heckeLambda s ≠ 0 := by
  have h0 : 0 < s.re := by linarith
  rw [heckeLambda_eq_tauL (ne_neg_nat_of_re_pos h0)]
  exact mul_ne_zero (mul_ne_zero (two_pi_cpow_ne_zero _) (Gamma_ne_zero_of_re_pos h0))
    (tauL_ne_zero_of_gt hs)

/-- `Λ(s) ≠ 0` for `Re s < 11/2` (functional equation `Λ(12 − s) = Λ(s)`). -/
theorem heckeLambda_ne_zero_of_lt {s : ℂ} (hs : s.re < 11 / 2) : heckeLambda s ≠ 0 := by
  rw [← heckeLambda_functional_equation]
  exact heckeLambda_ne_zero_of_gt (by simp; linarith)

/-- A zero of `tauL` is either trivial or a zero of `Λ`. -/
lemma tauL_eq_zero_iff (s : ℂ) :
    tauL s = 0 ↔ (∃ n : ℕ, s = -n) ∨ heckeLambda s = 0 := by
  rw [tauL, mul_eq_zero, mul_eq_zero, inv_eq_zero, Complex.Gamma_eq_zero_iff]
  simp

/-- **Left of the strip only the trivial zeros**: for `Re s < 11/2`,
`tauL s = 0 ↔ s ∈ {0, −1, −2, …}`. -/
theorem tauL_eq_zero_iff_of_lt {s : ℂ} (hs : s.re < 11 / 2) :
    tauL s = 0 ↔ ∃ n : ℕ, s = -n := by
  rw [tauL_eq_zero_iff]
  simp [heckeLambda_ne_zero_of_lt hs]

/-- **Headline: the non-trivial zeros of `L(Δ,s)` lie in the closed strip `11/2 ≤ Re s ≤ 13/2`.** -/
theorem tauL_zeros_in_strip {s : ℂ} (h : tauL s = 0) (hs : ∀ n : ℕ, s ≠ -n) :
    11 / 2 ≤ s.re ∧ s.re ≤ 13 / 2 := by
  constructor
  · by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := (tauL_eq_zero_iff_of_lt hlt).1 h
    exact hs n hn
  · by_contra hgt
    push Not at hgt
    exact tauL_ne_zero_of_gt hgt h

/-- For a non-trivial zero, `tauL s = 0 ↔ Λ(s) = 0`. -/
lemma tauL_eq_zero_iff_heckeLambda {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    tauL s = 0 ↔ heckeLambda s = 0 := by
  rw [tauL_eq_zero_iff]
  simp only [or_iff_right_iff_imp]
  rintro ⟨n, hn⟩; exact absurd hn (hs n)

/-- **Functional-equation symmetry of the non-trivial zeros**: `s ↦ 12 − s`. -/
theorem tauL_zero_twelve_sub {s : ℂ} (h : tauL s = 0) (hs : ∀ n : ℕ, s ≠ -n) :
    tauL (12 - s) = 0 ∧ ∀ n : ℕ, 12 - s ≠ -n := by
  have hΛ := (tauL_eq_zero_iff_heckeLambda hs).1 h
  have hstrip := tauL_zeros_in_strip h hs
  have h' : ∀ n : ℕ, 12 - s ≠ -n := ne_neg_nat_of_re_pos (by simp; linarith)
  refine ⟨(tauL_eq_zero_iff_heckeLambda h').2 ?_, h'⟩
  rw [heckeLambda_functional_equation]; exact hΛ

/-! ### Complex-conjugation symmetry -/

lemma ofReal_cpow_conj {t : ℝ} (ht : 0 ≤ t) (w : ℂ) :
    (t : ℂ) ^ (conj w) = conj ((t : ℂ) ^ w) := by
  have harg : (t : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg ht]; exact Real.pi_pos.ne
  rw [cpow_conj _ _ harg, Complex.conj_ofReal]

/-- `Λ(conj s) = conj Λ(s)` (the Mellin transform of the real function `Δ(it)`). -/
theorem heckeLambda_conj (s : ℂ) : heckeLambda (conj s) = conj (heckeLambda s) := by
  rw [heckeLambda_eq_mellin, mellin, mellin, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp only [smul_eq_mul, map_mul]
  rw [heckeF_real ht, Complex.conj_ofReal, ← ofReal_cpow_conj ht.le]
  simp

/-- `tauL (conj s) = conj (tauL s)`. -/
theorem tauL_conj (s : ℂ) : tauL (conj s) = conj (tauL s) := by
  have h2π : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
  rw [tauL, tauL, heckeLambda_conj, Complex.Gamma_conj, map_mul, map_mul, map_inv₀, h2π,
    ofReal_cpow_conj (by positivity)]

/-- **Conjugation symmetry of the zeros**. -/
theorem tauL_zero_conj {s : ℂ} (h : tauL s = 0) : tauL (conj s) = 0 := by
  rw [tauL_conj, h, map_zero]

end RamanujanTau.HeckeZeros
