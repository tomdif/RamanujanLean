/-
# Seventh pass, R3 (near part): Abel summation along one line

`abel_line`: if every line partial sum `lineSum P Q ℓ M` (`M ≤ M₂`) is `≤ B` in absolute value,
and on `[R, ∞)` (`R ≤ M₁ + 1`) the weight satisfies `‖f‖ ≤ H₀`, `‖f'‖ ≤ V`, then

    ‖Σ_{M₁<m≤M₂} lineTerm(P,Q,ℓ,m) f(m)‖ ≤ 2B (H₀ + M₂ V).

Level 1.
-/
import RamanujanTau.SelbergKey7.NearDeriv

set_option autoImplicit false

namespace RamanujanTau.SelbergKey7

open Complex Finset RamanujanTau.SelbergKey4

/-- Mean value on a unit step. -/
lemma norm_sub_le_of_deriv {f : ℝ → ℂ} {R V a : ℝ} (ha : R ≤ a)
    (hH : ∀ r, R ≤ r → ∃ D, HasDerivAt f D r ∧ ‖D‖ ≤ V) : ‖f (a + 1) - f a‖ ≤ V := by
  have hd : ∀ x ∈ Set.Icc a (a + 1), HasDerivWithinAt f (deriv f x) (Set.Icc a (a + 1)) x := by
    intro x hx
    obtain ⟨D, hD, _⟩ := hH x (ha.trans hx.1)
    rw [hD.deriv]; exact hD.hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico a (a + 1), ‖deriv f x‖ ≤ V := by
    intro x hx
    obtain ⟨D, hD, hDV⟩ := hH x (ha.trans hx.1)
    rw [hD.deriv]; exact hDV
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (a + 1) ⟨by linarith, le_rfl⟩
  simpa using this

/-- Partial sums of the shifted line terms. -/
lemma sum_range_shift (g : ℕ → ℝ) (M1 n : ℕ) :
    ∑ i ∈ range n, g (M1 + 1 + i) = ∑ m ∈ Icc 1 (M1 + n), g m - ∑ m ∈ Icc 1 M1, g m := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih, show M1 + (k + 1) = M1 + k + 1 by ring,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ M1 + k + 1)]
    rw [show M1 + 1 + k = M1 + k + 1 by ring]
    ring

/-- **Abel summation along one line.** -/
theorem abel_line {P Q : ℕ} {ℓ : ℤ} {M1 M2 : ℕ} {f : ℝ → ℂ} {R B H0 V : ℝ}
    (hR : R ≤ (M1 : ℝ) + 1) (hB : ∀ M ≤ M2, |lineSum P Q ℓ M| ≤ B)
    (hH0 : ∀ r, R ≤ r → ‖f r‖ ≤ H0) (hH : ∀ r, R ≤ r → ∃ D, HasDerivAt f D r ∧ ‖D‖ ≤ V)
    (hV : 0 ≤ V) :
    ‖∑ m ∈ Icc (M1 + 1) M2, ((lineTerm P Q ℓ m : ℝ) : ℂ) * f m‖ ≤ 2 * B * (H0 + M2 * V) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (Nat.zero_le _))
  set N := M2 - M1
  have hIcc : (∑ m ∈ Icc (M1 + 1) M2, ((lineTerm P Q ℓ m : ℝ) : ℂ) * f m) =
      ∑ i ∈ range N, f (((M1 + 1 + i : ℕ) : ℝ)) * ((lineTerm P Q ℓ (M1 + 1 + i) : ℝ) : ℂ) := by
    have hI : Icc (M1 + 1) M2 = Ico (M1 + 1) (M2 + 1) := by
      ext k; simp only [mem_Icc, mem_Ico]; omega
    rw [hI, Finset.sum_Ico_eq_sum_range, show M2 + 1 - (M1 + 1) = N by omega]
    exact sum_congr rfl fun i _ => mul_comm _ _
  rw [hIcc]
  have hpart : ∀ n ≤ N, ‖∑ i ∈ range n, ((lineTerm P Q ℓ (M1 + 1 + i) : ℝ) : ℂ)‖ ≤ 2 * B := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp; positivity
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
      sum_range_shift (lineTerm P Q ℓ) M1 n]
    have h1 : M1 + n ≤ M2 := by omega
    have h2 : M1 ≤ M2 := by omega
    have e1 := hB (M1 + n) h1
    have e2 := hB M1 h2
    unfold lineSum at e1 e2
    calc |∑ m ∈ Icc 1 (M1 + n), lineTerm P Q ℓ m - ∑ m ∈ Icc 1 M1, lineTerm P Q ℓ m|
        ≤ |∑ m ∈ Icc 1 (M1 + n), lineTerm P Q ℓ m| + |∑ m ∈ Icc 1 M1, lineTerm P Q ℓ m| :=
          abs_sub _ _
      _ ≤ 2 * B := by linarith
  refine (norm_sum_mul_le_abel (fun i => f (((M1 + 1 + i : ℕ) : ℝ)))
    (fun i => ((lineTerm P Q ℓ (M1 + 1 + i) : ℝ) : ℂ)) N hpart).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hRi : ∀ i : ℕ, R ≤ (((M1 + 1 + i : ℕ) : ℝ)) := by
    intro i; push_cast; have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
  have h1 := hH0 _ (hRi (N - 1))
  have h2 : ∑ i ∈ range (N - 1), ‖f (((M1 + 1 + (i + 1) : ℕ) : ℝ)) - f (((M1 + 1 + i : ℕ) : ℝ))‖ ≤
      (N - 1 : ℕ) * V := by
    have : ∀ i ∈ range (N - 1),
        ‖f (((M1 + 1 + (i + 1) : ℕ) : ℝ)) - f (((M1 + 1 + i : ℕ) : ℝ))‖ ≤ V := by
      intro i _
      have e : (((M1 + 1 + (i + 1) : ℕ) : ℝ)) = (((M1 + 1 + i : ℕ) : ℝ)) + 1 := by push_cast; ring
      rw [e]
      exact norm_sub_le_of_deriv (hRi i) hH
    refine (sum_le_sum this).trans (le_of_eq ?_)
    rw [sum_const, card_range, nsmul_eq_mul]
  have h3 : ((N - 1 : ℕ) : ℝ) * V ≤ M2 * V := by
    refine mul_le_mul_of_nonneg_right ?_ hV
    exact_mod_cast (show N - 1 ≤ M2 by omega)
  linarith

end RamanujanTau.SelbergKey7
