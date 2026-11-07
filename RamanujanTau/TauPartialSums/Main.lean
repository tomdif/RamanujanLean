/-
# `TauPartialSums/`: cancellation in `∑_{n≤x} τ(n)` and `∑_{n≤x} a_f(n)`

Build: `nice -n 10 lake build RamanujanTau.TauPartialSums.Main`. See `docs/TAU_PARTIAL_SUMS.md`.

Headlines (unconditional, axiom-clean):

* `cuspForm_partial_sum_bound`: for every level-one cusp form `f` of weight `k` and every
  `ε > 0`, `‖∑_{n≤x} a_f(n)‖ ≤ C x^{(k−1)/2 + 8/15 + ε}`;
* `tau_partial_sum_bound`: `|∑_{n≤x} τ(n)| ≤ C x^{181/30 + ε}`  (`181/30 = 11/2 + 8/15`),

to be compared with the Rankin bound `∑_{n≤x} |τ(n)| ≪ x^{13/2}` (`HeckeConvex`) — a saving
of `x^{7/15 − ε}`.

Ingredients: Perron for the first Riesz mean, contour shift to `Re s = (k−1)/2 + 2ε` with the
convexity bound (`HeckeConvexGeneral`), one difference, and short sums of `|a_f(n)|` via
Cauchy–Schwarz and Rankin's `O(N^{3/5})` (`RankinExact`). No Deligne, no pointwise bound.
-/
import RamanujanTau.TauPartialSums.Differencing
import RamanujanTau.RankinExact.Main
import RamanujanTau.HeckeConvexGeneral.Main

set_option autoImplicit false

namespace RamanujanTau.TauPartialSums

open Complex Finset ModularForm
open RamanujanTau.HeckeConvexGeneral RamanujanTau.RankinSelbergGeneral
open scoped MatrixGroups

variable {k : ℕ}

/-- Strip bound used for the contour shift: on `(k−1)/2 + 2ε ≤ Re s ≤ k/2 + 1`,
`‖L(f,s)‖ ≤ K (1+|t|)^{1−ε}`. -/
lemma fL_strip_bound (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {ε : ℝ} (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 2) :
    ∃ K : ℝ, ∀ s : ℂ, ((k : ℝ) - 1) / 2 + 2 * ε ≤ s.re → s.re ≤ (k : ℝ) / 2 + 1 →
      ‖fL f s‖ ≤ K * (1 + |s.im|) ^ (2 - (1 + ε)) := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨C, hC0, hC⟩ := fC_bound f hk hε0 hε
  obtain ⟨D, hD0, hD⟩ := fL_bounded_of_gt f hk1 (σ := ((k : ℝ) + 1) / 2 + ε) (by linarith)
  set c : ℝ := (k : ℝ) / 2 + 1 with hc
  refine ⟨2 * Real.exp 10 * C * c + D, fun s h1 h2 => ?_⟩
  have hexp : (2 : ℝ) - (1 + ε) = 1 - ε := by ring
  rw [hexp]
  have ht1 : (1 : ℝ) ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  have hpow1 : 1 ≤ (1 + |s.im|) ^ (1 - ε) := Real.one_le_rpow ht1 (by linarith)
  have hc1 : 1 ≤ c := by rw [hc]; linarith
  rcases le_or_gt s.re (((k : ℝ) + 1) / 2 + ε) with h3 | h3
  · have hL := fL_line f hk hε0 hε hC (s := s) (by linarith) h3
    set θ : ℝ := ((k : ℝ) + 1) / 2 + ε - s.re with hθ
    have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
    have hθ1 : θ ≤ 1 - ε := by rw [hθ]; linarith
    have hs1 : 1 ≤ ‖s / 2‖ := by
      rw [norm_div, Complex.norm_two, le_div_iff₀ (by norm_num)]
      have := Complex.abs_re_le_norm s
      rw [abs_of_nonneg (by linarith)] at this
      linarith
    have hs2 : ‖s / 2‖ ≤ c * (1 + |s.im|) := by
      rw [norm_div, Complex.norm_two, div_le_iff₀ (by norm_num)]
      refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
      rw [abs_of_nonneg (by linarith)]
      nlinarith [abs_nonneg s.im]
    have hp1 : ‖s / 2‖ ^ θ ≤ ‖s / 2‖ ^ (1 - ε) :=
      Real.rpow_le_rpow_of_exponent_le hs1 hθ1
    have hp2 : ‖s / 2‖ ^ (1 - ε) ≤ (c * (1 + |s.im|)) ^ (1 - ε) :=
      Real.rpow_le_rpow (norm_nonneg _) hs2 (by linarith)
    have hp3 : (c * (1 + |s.im|)) ^ (1 - ε) = c ^ (1 - ε) * (1 + |s.im|) ^ (1 - ε) :=
      Real.mul_rpow (by linarith) (by linarith)
    have hp4 : c ^ (1 - ε) ≤ c := by
      calc c ^ (1 - ε) ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 (by linarith)
        _ = c := Real.rpow_one c
    have hK0 : 0 ≤ 2 * Real.exp 10 * C := by positivity
    calc ‖fL f s‖ ≤ 2 * Real.exp 10 * C * ‖s / 2‖ ^ θ := hL
      _ ≤ 2 * Real.exp 10 * C * (c * (1 + |s.im|) ^ (1 - ε)) := by
          gcongr
          calc ‖s / 2‖ ^ θ ≤ (c * (1 + |s.im|)) ^ (1 - ε) := hp1.trans hp2
            _ = c ^ (1 - ε) * (1 + |s.im|) ^ (1 - ε) := hp3
            _ ≤ c * (1 + |s.im|) ^ (1 - ε) := by gcongr
      _ ≤ (2 * Real.exp 10 * C * c + D) * (1 + |s.im|) ^ (1 - ε) := by nlinarith
  · have h4 := hD s h3.le
    have h5 : D ≤ D * (1 + |s.im|) ^ (1 - ε) := le_mul_of_one_le_right hD0 hpow1
    have h6 : 0 ≤ 2 * Real.exp 10 * C * c * (1 + |s.im|) ^ (1 - ε) := by positivity
    nlinarith

/-- **Cancellation in the partial sums of a level-one cusp form**, `ε`-version with the
exponent `(k−1)/2 + 8/15 + 2ε`, `0 < ε ≤ 1/4`. -/
theorem cuspForm_partial_sum_bound_aux (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 4) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n‖ ≤
        C * x ^ ((((k - 1 : ℕ) : ℝ)) / 2 + 8 / 15 + 2 * ε) := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1]; simp
  obtain ⟨K, hK⟩ := fL_strip_bound f hk hε0 (by linarith)
  have hsum : Summable fun n : ℕ => ‖coef f n‖ * (n : ℝ) ^ (-((k : ℝ) / 2 + 1)) := by
    refine (summable_norm_coef_div_rpow f hk1 (σ := (k : ℝ) / 2 + 1) (by linarith)).congr
      fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  obtain ⟨K', hK'⟩ := F1_bound (coef f) (coef_zero f) (fL_entire f hk1)
    (c := (k : ℝ) / 2 + 1) (σ₁ := ((k : ℝ) - 1) / 2 + 2 * ε) (p := 1 + ε) (K := K)
    (by linarith) (by linarith) (by linarith) hsum
    (fun s hs => (fL_eq_LSeries f hk1 (by rw [hs]; linarith)).symm)
    (fun s h1 h2 => hK s h1 h2)
  obtain ⟨Crs, hRS⟩ := RankinExact.rankinSelberg_exact_general f
  have hT : ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ‖coef f n‖ ^ 2 / (n : ℝ) ^ (k - 1) - rsConst f * N| ≤
        Crs * (N : ℝ) ^ ((3 : ℝ) / 5) := fun N hN => hRS N hN
  obtain ⟨C', hC'⟩ := partial_sum_bound (coef f) (k - 1) (δ := 2 * ε) (K := K') (by linarith)
    (fun y hy => by
      have := hK' y hy
      have e : (1 + (((k : ℝ) - 1) / 2 + 2 * ε)) = (((k - 1 : ℕ) : ℝ)) / 2 + 1 + 2 * ε := by
        rw [hkm]; ring
      rw [e] at this; exact this) hT
  exact ⟨C', fun x hx => hC' x hx⟩

/-- **Cancellation in the partial sums of a level-one cusp form** (unconditional): for every
`f ∈ S_k(SL₂(ℤ))` and `ε > 0`,
`‖∑_{n≤x} a_f(n)‖ ≤ C x^{(k−1)/2 + 8/15 + ε}` for all `x ≥ 1`. Compare `≪ x^{(k+1)/2}` from
Rankin–Selberg and Cauchy–Schwarz alone. -/
theorem cuspForm_partial_sum_bound (f : CuspForm 𝒮ℒ (k : ℤ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n‖ ≤ C * x ^ (((k : ℝ) - 1) / 2 + 8 / 15 + ε) := by
  rcases lt_or_ge k 12 with hk | hk
  · obtain rfl := eq_zero_of_lt_twelve f hk
    refine ⟨0, fun x _ => ?_⟩
    have h0 : ∀ n, coef (0 : CuspForm 𝒮ℒ (k : ℤ)) n = 0 := fun n => by
      simp [coef, UpperHalfPlane.qExpansion_zero]
    simp [h0]
  · have hk1 : 1 ≤ k := by omega
    have hkm : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1]; simp
    set ε' : ℝ := min (ε / 2) (1 / 4) with hε'
    have hε'0 : 0 < ε' := lt_min (by linarith) (by norm_num)
    have hε'1 : ε' ≤ 1 / 4 := min_le_right _ _
    have hε'2 : 2 * ε' ≤ ε := by have := min_le_left (ε / 2) (1 / 4); linarith
    obtain ⟨C, hC⟩ := cuspForm_partial_sum_bound_aux f hk hε'0 hε'1
    refine ⟨|C|, fun x hx => ?_⟩
    refine (hC x hx).trans ?_
    rw [hkm]
    have hle : x ^ (((k : ℝ) - 1) / 2 + 8 / 15 + 2 * ε') ≤
        x ^ (((k : ℝ) - 1) / 2 + 8 / 15 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have hx0 : 0 ≤ x ^ (((k : ℝ) - 1) / 2 + 8 / 15 + 2 * ε') := by positivity
    calc C * x ^ (((k : ℝ) - 1) / 2 + 8 / 15 + 2 * ε')
        ≤ |C| * x ^ (((k : ℝ) - 1) / 2 + 8 / 15 + 2 * ε') :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hx0
      _ ≤ |C| * x ^ (((k : ℝ) - 1) / 2 + 8 / 15 + ε) := by gcongr

/-- **Cancellation in `∑ τ(n)`** (unconditional): for every `ε > 0` there is `C` with
`|∑_{n≤x} τ(n)| ≤ C x^{181/30 + ε}` for all `x ≥ 1`, where `181/30 = 11/2 + 8/15`.
(The Rankin bound `∑ |τ(n)| ≪ x^{13/2}` is beaten by `x^{7/15−ε}`.) -/
theorem tau_partial_sum_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)| ≤ C * x ^ ((181 : ℝ) / 30 + ε) := by
  obtain ⟨C, hC⟩ := cuspForm_partial_sum_bound (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) hε
  refine ⟨C, fun x hx => ?_⟩
  have h := hC x hx
  simp_rw [coef_discriminant] at h
  have e1 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, tauC n = ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [e1, Complex.norm_real, Real.norm_eq_abs] at h
  have e2 : (((12 : ℕ) : ℝ) - 1) / 2 + 8 / 15 + ε = (181 : ℝ) / 30 + ε := by norm_num
  rw [e2] at h
  exact h

/-- The exponent is below the Rankin (Cauchy–Schwarz) exponent `13/2`. -/
lemma exponent_lt : (181 : ℝ) / 30 < 13 / 2 := by norm_num

end RamanujanTau.TauPartialSums

#print axioms RamanujanTau.TauPartialSums.riesz_one_bound
#print axioms RamanujanTau.TauPartialSums.F1_bound
#print axioms RamanujanTau.TauPartialSums.short_sq
#print axioms RamanujanTau.TauPartialSums.partial_sum_bound
#print axioms RamanujanTau.TauPartialSums.fL_strip_bound
#print axioms RamanujanTau.TauPartialSums.cuspForm_partial_sum_bound
#print axioms RamanujanTau.TauPartialSums.tau_partial_sum_bound
