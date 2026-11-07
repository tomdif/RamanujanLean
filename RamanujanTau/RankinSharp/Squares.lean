/-
# Twisting by `ζ(2s)` and undoing it with Möbius

`sqPull h` is the arithmetic function `n ↦ h(m)` if `n = m²` (`m ≥ 1`), else `0`; its
`L`-series at `s` is `L(h, 2s)` (`LSeries_sqPull`). With `χ = sqPull 1` (`L(χ,s) = ζ(2s)`) and
`μ₂ = sqPull μ` we get `μ₂ * χ = 1` (`mu2_mul_chi`, by uniqueness of `L`-series), so for
`b = χ * a` (the coefficients of `ζ(2s) D(s)`):

    ∑_{n≤N} aₙ = ∑_{m≤N} μ(m) B(⌊N/m²⌋),    B(M) = ∑_{n≤M} bₙ      (`sum_a_eq_mobius`).
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.RankinSharp

open Complex Real Finset
open ArithmeticFunction
open scoped LSeries.notation

/-- `n ↦ h(√n)` on nonzero squares, `0` elsewhere. -/
noncomputable def sqPull (h : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≠ 0 ∧ Nat.sqrt n * Nat.sqrt n = n then h (Nat.sqrt n) else 0, by simp⟩

lemma sqPull_apply (h : ℕ → ℝ) (n : ℕ) :
    sqPull h n = if n ≠ 0 ∧ Nat.sqrt n * Nat.sqrt n = n then h (Nat.sqrt n) else 0 := rfl

lemma sqPull_mul_self (h : ℕ → ℝ) {m : ℕ} (hm : m ≠ 0) : sqPull h (m * m) = h m := by
  rw [sqPull_apply, Nat.sqrt_eq, if_pos ⟨mul_ne_zero hm hm, rfl⟩]

lemma mul_self_injective : Function.Injective fun m : ℕ => m * m :=
  fun _ _ h => Nat.mul_self_inj.1 h

lemma sqPull_eq_zero_of_not_mem (h : ℕ → ℝ) {n : ℕ} (hn : n ∉ Set.range fun m : ℕ => m * m) :
    sqPull h n = 0 := by
  rw [sqPull_apply, if_neg]
  rintro ⟨_, h2⟩
  exact hn ⟨Nat.sqrt n, h2⟩

lemma term_sqPull (h : ℕ → ℝ) (s : ℂ) (m : ℕ) :
    LSeries.term (fun n => (sqPull h n : ℂ)) s (m * m) =
      LSeries.term (fun n => (h n : ℂ)) (2 * s) m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [LSeries.term_of_ne_zero (mul_ne_zero hm hm), LSeries.term_of_ne_zero hm,
      sqPull_mul_self h hm, Nat.cast_mul, natCast_mul_natCast_cpow,
      show (2 : ℂ) * s = ((2 : ℕ) : ℂ) * s by norm_num, cpow_nat_mul, sq]

lemma term_sqPull_eq_zero (h : ℕ → ℝ) (s : ℂ) {n : ℕ}
    (hn : n ∉ Set.range fun m : ℕ => m * m) :
    LSeries.term (fun n => (sqPull h n : ℂ)) s n = 0 := by
  rcases eq_or_ne n 0 with rfl | h0
  · simp
  · rw [LSeries.term_of_ne_zero h0, sqPull_eq_zero_of_not_mem h hn]; simp

lemma LSeriesSummable_sqPull (h : ℕ → ℝ) {s : ℂ}
    (hs : LSeriesSummable (fun n => (h n : ℂ)) (2 * s)) :
    LSeriesSummable (fun n => (sqPull h n : ℂ)) s := by
  unfold LSeriesSummable
  rw [← mul_self_injective.summable_iff (fun n hn => term_sqPull_eq_zero h s hn)]
  simpa [Function.comp_def, term_sqPull] using hs

lemma LSeries_sqPull (h : ℕ → ℝ) (s : ℂ) :
    LSeries (fun n => (sqPull h n : ℂ)) s = LSeries (fun n => (h n : ℂ)) (2 * s) := by
  unfold LSeries
  rw [← mul_self_injective.tsum_eq (f := LSeries.term (fun n => (sqPull h n : ℂ)) s)]
  · simp only [term_sqPull]
  · intro n hn
    by_contra h'
    exact hn (term_sqPull_eq_zero h s h')

/-- The indicator of nonzero squares. -/
noncomputable def chi : ArithmeticFunction ℝ := sqPull fun _ => 1

/-- `μ` on squares. -/
noncomputable def mu2 : ArithmeticFunction ℝ := sqPull fun n => (moebius n : ℝ)

lemma chi_nonneg (n : ℕ) : 0 ≤ chi n := by
  unfold chi; rw [sqPull_apply]; split_ifs <;> norm_num

lemma LSeries_chi {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeries (fun n => (chi n : ℂ)) s = riemannZeta (2 * s) := by
  unfold chi
  rw [LSeries_sqPull, ← LSeries_one_eq_riemannZeta (by simp; linarith)]
  rfl

lemma LSeriesSummable_chi {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeriesSummable (fun n => (chi n : ℂ)) s := by
  unfold chi
  refine LSeriesSummable_sqPull _ ?_
  have : LSeriesSummable 1 (2 * s) := LSeriesSummable_one_iff.2 (by simp; linarith)
  exact this

lemma LSeries_mu2 {s : ℂ} : LSeries (fun n => (mu2 n : ℂ)) s = LSeries (fun n => ((moebius n : ℤ) : ℂ)) (2 * s) := by
  unfold mu2; rw [LSeries_sqPull]; congr 1

lemma LSeriesSummable_mu2 {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeriesSummable (fun n => (mu2 n : ℂ)) s := by
  unfold mu2
  refine LSeriesSummable_sqPull _ ?_
  have : LSeriesSummable (fun n => ((moebius n : ℤ) : ℂ)) (2 * s) := LSeriesSummable_moebius_iff.2 (by simp; linarith)
  convert this using 2 with n

lemma coe_mul_apply (f g : ArithmeticFunction ℝ) (n : ℕ) :
    (((f * g) n : ℝ) : ℂ) = ((fun n => (f n : ℂ)) ⍟ (fun n => (g n : ℂ))) n := by
  rw [LSeries.convolution_def, mul_apply]; push_cast; rfl

/-- `μ₂ * χ = 1`. -/
theorem mu2_mul_chi : mu2 * chi = 1 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  set f : ℕ → ℂ := fun n => (((mu2 * chi) n : ℝ) : ℂ) with hf
  set g : ℕ → ℂ := fun n => (((1 : ArithmeticFunction ℝ) n : ℝ) : ℂ) with hg
  have hfconv : f = (fun n => (mu2 n : ℂ)) ⍟ (fun n => (chi n : ℂ)) := by
    funext n; exact coe_mul_apply mu2 chi n
  have hgδ : g = LSeries.delta := by
    funext n
    show (((1 : ArithmeticFunction ℝ) n : ℝ) : ℂ) = LSeries.delta n
    rw [one_apply]; unfold LSeries.delta; split_ifs <;> simp
  have hf2 : LSeriesSummable f 2 := by
    rw [hfconv]
    exact (LSeriesSummable_mu2 (by norm_num)).convolution (LSeriesSummable_chi (by norm_num))
  have habsf : LSeries.abscissaOfAbsConv f < ⊤ :=
    lt_of_le_of_lt hf2.abscissaOfAbsConv_le (EReal.coe_lt_top _)
  have habsg : LSeries.abscissaOfAbsConv g < ⊤ := by
    refine lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => ?_⟩)
      (EReal.coe_lt_top _)
    rw [hgδ]; unfold LSeries.delta; split_ifs <;> simp
  have hev : (fun x : ℝ => LSeries f x) =ᶠ[Filter.atTop] fun x => LSeries g x := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hx2 : 1 < (2 * (x : ℂ)).re := by simp; linarith
    rw [hgδ, LSeries_delta, hfconv, LSeries_convolution' (LSeriesSummable_mu2 (by simp; linarith))
      (LSeriesSummable_chi (by simp; linarith)), LSeries_mu2, LSeries_chi (by simp; linarith),
      ← LSeries_one_eq_riemannZeta hx2, mul_comm]
    exact LSeries_one_mul_Lseries_moebius hx2
  have := LSeries.eq_of_LSeries_eventually_eq habsf habsg hev hn
  exact Complex.ofReal_injective this

/-- Reindexing a sum over squares. -/
lemma sum_sqPull (h : ℕ → ℝ) (F : ℕ → ℝ) (N : ℕ) (hF : ∀ i, N < i → F i = 0) :
    ∑ n ∈ Ioc 0 N, sqPull h n * F n = ∑ m ∈ Ioc 0 N, h m * F (m * m) := by
  symm
  refine Finset.sum_bij_ne_zero (fun m _ _ => m * m) ?_ ?_ ?_ ?_
  · intro m hm hne
    rw [mem_Ioc] at hm ⊢
    refine ⟨Nat.mul_pos hm.1 hm.1, ?_⟩
    by_contra hlt
    exact hne (by rw [hF _ (not_le.1 hlt), mul_zero])
  · intro m₁ _ _ m₂ _ _ h12
    exact Nat.mul_self_inj.1 h12
  · intro n hn hne
    have hsq : n ≠ 0 ∧ Nat.sqrt n * Nat.sqrt n = n := by
      by_contra hc
      exact hne (by rw [sqPull_apply, if_neg hc, zero_mul])
    rw [mem_Ioc] at hn
    have hr0 : Nat.sqrt n ≠ 0 := by
      intro h0; rw [h0] at hsq; exact hsq.1 (by simpa using hsq.2.symm)
    refine ⟨Nat.sqrt n, ?_, ?_, hsq.2⟩
    · rw [mem_Ioc]
      exact ⟨Nat.pos_of_ne_zero hr0, (Nat.sqrt_le_self n).trans hn.2⟩
    · rw [hsq.2]
      intro h0
      apply hne
      rw [sqPull_apply, if_pos hsq]
      exact h0
  · intro m hm _
    rw [sqPull_mul_self h (Nat.pos_iff_ne_zero.1 (mem_Ioc.1 hm).1)]

/-- **Möbius inversion of the `ζ(2s)` twist.** For `b = χ * a`,
`∑_{n≤N} aₙ = ∑_{m≤N} μ(m) B(⌊N/m²⌋)`. -/
theorem sum_a_eq_mobius (a : ArithmeticFunction ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, a n =
      ∑ m ∈ Ioc 0 N, (moebius m : ℝ) * ∑ n ∈ Ioc 0 (N / (m * m)), (chi * a) n := by
  have e : a = mu2 * (chi * a) := by rw [← mul_assoc, mu2_mul_chi, one_mul]
  conv_lhs => rw [e]
  rw [sum_Ioc_mul_eq_sum_sum]
  unfold mu2
  rw [sum_sqPull _ (fun n => ∑ m ∈ Ioc 0 (N / n), (chi * a) m) N
    (fun i hi => by simp [Nat.div_eq_of_lt hi])]

end RamanujanTau.RankinSharp
