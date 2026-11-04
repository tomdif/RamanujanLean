import RamanujanTau.TauDensity.Structure
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Almost all `n` below `exp(10¹⁰)` have `τ(n) ≠ 0`

Every zero `n ≤ N` of `τ` is divisible by a prime zero `p ≤ N`, and every prime zero is
`p = iM + (M − 1)` with `M = 10 746 432 000`, `1 ≤ i ≤ N` (`prime_zero_candidate`). Hence
`#{n ≤ N : τ(n) = 0} ≤ ∑_{i ≤ N} N/(iM) ≤ N(1 + log N)/M`.
-/

set_option autoImplicit false

namespace RamanujanTau.TauDensity
open RamanujanTau Finset

/-- **Zero count upper bound.** `#{n ∈ [1,N] : τ(n) = 0} ≤ N(1 + log N)/10 746 432 000`. -/
theorem card_tau_eq_zero_le (N : ℕ) :
    (((Icc 1 N).filter (fun n => τ n = 0)).card : ℝ) ≤ N * (1 + Real.log N) / 10746432000 := by
  set M : ℕ := 10746432000
  set q : ℕ → ℕ := fun i => i * M + (M - 1)
  have hsub : (Icc 1 N).filter (fun n => τ n = 0) ⊆
      (Icc 1 N).biUnion (fun i => (Icc 1 N).filter (fun n => q i ∣ n)) := by
    intro n hn
    obtain ⟨hnI, h0⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hnI
    obtain ⟨p, hp, hodd, hp0⟩ := (tau_eq_zero_iff hn1).mp h0
    have hpn : p ∣ n := by
      by_contra hc; rw [Nat.factorization_eq_zero_of_not_dvd hc] at hodd; simp at hodd
    have hpN : p ≤ N := (Nat.le_of_dvd (by omega) hpn).trans hnN
    obtain ⟨hbig, hmod, -⟩ := prime_zero_candidate hp hp0
    have hpq : p = q (p / M) := by
      simp only [q, M]; have := Nat.div_add_mod p 10746432000; rw [hmod] at this; omega
    rw [mem_biUnion]
    refine ⟨p / M, mem_Icc.mpr ⟨?_, ?_⟩, mem_filter.mpr ⟨hnI, hpq ▸ hpn⟩⟩
    · exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by simp only [M]; omega)
    · exact (Nat.div_le_self _ _).trans hpN
  have hcard := (card_le_card hsub).trans card_biUnion_le
  have hterm : ∀ i ∈ Icc 1 N, ((((Icc 1 N).filter (fun n => q i ∣ n)).card : ℕ) : ℝ) ≤
      (N : ℝ) / M * (i : ℝ)⁻¹ := by
    intro i hi
    have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
    have hI : Icc 1 N = Ioc 0 N := by ext x; simp; omega
    rw [hI, Nat.Ioc_filter_dvd_card_eq_div]
    have hqpos : (0 : ℝ) < (q i : ℝ) := by
      have : 0 < q i := by simp only [q, M]; positivity
      exact_mod_cast this
    have hiM : ((i * M : ℕ) : ℝ) ≤ (q i : ℝ) := by exact_mod_cast Nat.le_add_right _ _
    have hiMpos : (0 : ℝ) < ((i * M : ℕ) : ℝ) := by
      have : 0 < i * M := by simp only [M]; positivity
      exact_mod_cast this
    calc ((N / q i : ℕ) : ℝ) ≤ (N : ℝ) / q i := Nat.cast_div_le
      _ ≤ (N : ℝ) / ((i * M : ℕ) : ℝ) := div_le_div_of_nonneg_left (by positivity) hiMpos hiM
      _ = (N : ℝ) / M * (i : ℝ)⁻¹ := by push_cast; field_simp
  calc (((Icc 1 N).filter (fun n => τ n = 0)).card : ℝ)
      ≤ ((∑ i ∈ Icc 1 N, ((Icc 1 N).filter (fun n => q i ∣ n)).card : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ ∑ i ∈ Icc 1 N, (N : ℝ) / M * (i : ℝ)⁻¹ := by push_cast; exact sum_le_sum hterm
    _ = (N : ℝ) / M * (harmonic N : ℝ) := by rw [← mul_sum, harmonic_eq_sum_Icc]; push_cast; rfl
    _ ≤ (N : ℝ) / M * (1 + Real.log N) := by gcongr; exact harmonic_le_one_add_log N
    _ = N * (1 + Real.log N) / 10746432000 := by simp only [M]; push_cast; ring

/-- **Positive proportion in a huge range.** `N·(1 − (1 + log N)/10 746 432 000) ≤ #{n ≤ N : τ(n) ≠ 0}`;
e.g. for `N ≤ e^{10⁹}` more than 90 % of `n ≤ N` have `τ(n) ≠ 0`. -/
theorem card_tau_ne_zero_ge_proportion (N : ℕ) :
    (N : ℝ) * (1 - (1 + Real.log N) / 10746432000) ≤
      (((Icc 1 N).filter (fun n => τ n ≠ 0)).card : ℝ) := by
  have hsplit := card_filter_add_card_filter_not (s := Icc 1 N) (fun n => τ n ≠ 0)
  simp only [not_not, Nat.card_Icc, add_tsub_cancel_right] at hsplit
  have h := card_tau_eq_zero_le N
  have : ((((Icc 1 N).filter (fun n => τ n ≠ 0)).card : ℕ) : ℝ) +
      (((Icc 1 N).filter (fun n => τ n = 0)).card : ℝ) = N := by exact_mod_cast hsplit
  nlinarith

/-- Numerical corollary: for `1 ≤ N ≤ e^{10⁹}`, `0.9·N ≤ #{n ≤ N : τ(n) ≠ 0}`. -/
theorem card_tau_ne_zero_ge_nine_tenths {N : ℕ} (hN : Real.log N ≤ 10 ^ 9) :
    (9 / 10 : ℝ) * N ≤ (((Icc 1 N).filter (fun n => τ n ≠ 0)).card : ℝ) := by
  refine le_trans ?_ (card_tau_ne_zero_ge_proportion N)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have : (9 / 10 : ℝ) ≤ 1 - (1 + Real.log N) / 10746432000 := by
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by norm_num)]; linarith
  nlinarith

end RamanujanTau.TauDensity

#print axioms RamanujanTau.TauDensity.card_tau_eq_zero_le
#print axioms RamanujanTau.TauDensity.card_tau_ne_zero_ge_proportion
#print axioms RamanujanTau.TauDensity.card_tau_ne_zero_ge_nine_tenths
