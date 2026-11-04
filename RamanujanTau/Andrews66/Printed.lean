/-
# Andrews' printed main term

With Rademacher's/Andrews' Kloosterman sum `A_K(x) = Σ_{h mod K, (h,K)=1} e^{πi s(h,K) − 2πixh/K}` (`AAnd`; for natural
`x` it is `Rademacher.Ak`, `AAnd_nat`) and Andrews' shift `n − k(1+(−1)^k)/4` (`shiftA`):

* `Ab_printed`: `(−1)^k A_b(k,n) = (−1)^{⌊(k+1)/2⌋} A_{2k}(n − k(1+(−1)^k)/4)` — termwise, from the Dedekind-sum
  congruence `T_cong` and `omegaB_eq_dsum`;
* `andrews_1966_printed_of_Hb`: under `Hb C D` (`D ≥ 1`), for all `n ≥ 1`, `N = ⌊√n⌋`,
  `|α(n) − Σ_{k=1}^{N} (−1)^{⌊(k+1)/2⌋} A_{2k}(n − k(1+(−1)^k)/4) M_{2k}(n)| ≤ A₁N^{2D−1}(1+log N) + A₂N`,
  with `M_{2k}(n) = π(24n−1)^{−1/4} I_{1/2}(π√(24n−1)/(12k))/k` (`MK_two`): Andrews' theorem as printed,
  over Andrews' range `k ≤ √n` (the terms `N/2 < k ≤ N` are `O(1)` each, `extra_term_le`).
-/
import RamanujanTau.Andrews66.Ded

set_option autoImplicit false

namespace Andrews66
open Complex Filter Rademacher
open scoped Real

noncomputable section

/-- Andrews'/Rademacher's Kloosterman sum `A_K(x) = Σ_{h mod K, (h,K)=1} e^{πi s(h,K)} e^{−2πixh/K}`. -/
def AAnd (K : ℕ) (x : ℝ) : ℂ :=
  ∑ h ∈ (Finset.range K).filter (fun h => Nat.Coprime h K), cexp (π * I * dsum h K - 2 * π * I * x * h / K)

lemma AAnd_nat {K : ℕ} (hK : 0 < K) (n : ℕ) : AAnd K n = Rademacher.Ak K n := by
  rw [Ak_eq_dedekind K n hK, AAnd]; push_cast; rfl

/-- Andrews' shift `n − k(1+(−1)^k)/4`. -/
def shiftA (k n : ℕ) : ℝ := n - k * (1 + (-1) ^ k) / 4

lemma cexp_shift (B : ℂ) (l : ℕ) (j : ℤ) : cexp (B + l * (π * I) + j * (2 * π * I)) = (-1) ^ l * cexp B := by
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_nat_mul,
    Complex.exp_pi_mul_I]
  ring

lemma term_eq {h k : ℕ} (hk : 0 < k) (hc : Nat.Coprime h (2 * k)) (n : ℕ) :
    (-1 : ℂ) ^ k * cexp (π * I * (2 * dsum h k - 3 * dsum h (2 * k)) - 2 * π * I * n * h / ((2 * k : ℕ) : ℂ)) =
      (-1 : ℂ) ^ ((k + 1) / 2) *
        cexp (π * I * dsum h (2 * k) - 2 * π * I * (shiftA k n : ℝ) * h / ((2 * k : ℕ) : ℂ)) := by
  obtain ⟨m, hm⟩ := T_cong k hk h hc
  unfold Tq Gq at hm
  rcases Nat.even_or_odd k with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · have hl : 0 < l := by omega
    have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    rw [show (l + l + 1) / 2 = l by omega, Even.neg_one_pow ⟨l, rfl⟩, one_mul]
    simp only [show (l + l) % 2 = 0 by omega, ↓reduceIte] at hm
    push_cast at hm
    have hs : (shiftA (l + l) n : ℂ) = n - l := by
      unfold shiftA; rw [Even.neg_one_pow ⟨l, rfl⟩]; push_cast; ring
    rw [hs]
    have hT : ((2 * dsum h (l + l) - 4 * dsum h (2 * (l + l)) : ℝ) : ℂ) = -l + h / 2 + 2 * m := by
      have : 2 * dsum h (l + l) - 4 * dsum h (2 * (l + l)) = -l + h / 2 + 2 * m := by linarith
      rw [this]; push_cast; ring
    push_cast at hT ⊢
    have hdiv : 2 * π * I * ((n : ℂ) - l) * h / (2 * (l + l)) = 2 * π * I * n * h / (2 * (l + l)) - π * I * h / 2 := by
      field_simp; ring
    rw [hdiv, ← cexp_shift _ l (m - l)]
    congr 1
    push_cast
    linear_combination (π * I) * hT
  · rw [show (2 * l + 1 + 1) / 2 = l + 1 by omega, Odd.neg_one_pow ⟨l, rfl⟩, pow_succ (-1 : ℂ) l]
    simp only [show (2 * l + 1) % 2 = 1 by omega, one_ne_zero, ↓reduceIte] at hm
    push_cast at hm
    have hs : (shiftA (2 * l + 1) n : ℂ) = n := by
      unfold shiftA; rw [Odd.neg_one_pow ⟨l, rfl⟩]; push_cast; ring
    rw [hs]
    have hT : ((2 * dsum h (2 * l + 1) - 4 * dsum h (2 * (2 * l + 1)) : ℝ) : ℂ) = -l + 2 * m := by
      have : 2 * dsum h (2 * l + 1) - 4 * dsum h (2 * (2 * l + 1)) = -l + 2 * m := by linarith
      rw [this]; push_cast; ring
    push_cast at hT ⊢
    have key : cexp (π * I * (2 * (dsum h (2 * l + 1) : ℂ) - 3 * dsum h (2 * (2 * l + 1))) -
        2 * π * I * n * h / (2 * (2 * l + 1))) =
        (-1) ^ l * cexp (π * I * dsum h (2 * (2 * l + 1)) - 2 * π * I * n * h / (2 * (2 * l + 1))) := by
      rw [← cexp_shift _ l (m - l)]
      congr 1
      push_cast
      linear_combination (π * I) * hT
    rw [key]; ring

/-- **Andrews' sign and shift**: `(−1)^k A_b(k,n) = (−1)^{⌊(k+1)/2⌋} A_{2k}(n − k(1+(−1)^k)/4)`. -/
theorem Ab_printed {k : ℕ} (hk : 0 < k) (n : ℕ) :
    (-1 : ℂ) ^ k * Ab k n = (-1 : ℂ) ^ ((k + 1) / 2) * AAnd (2 * k) (shiftA k n) := by
  rw [Ab_eq_dedekind hk, AAnd, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  have := term_eq hk (Finset.mem_filter.mp hh).2 n
  push_cast at this ⊢
  exact this

/-! ### the terms `N/2 < k ≤ N` -/

lemma norm_AAnd_le (K : ℕ) (x : ℝ) : ‖AAnd K x‖ ≤ K := by
  unfold AAnd
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ h ∈ (Finset.range K).filter (fun h => Nat.Coprime h K),
      ‖cexp (π * I * dsum h K - 2 * π * I * x * h / K)‖ = 1 := by
    intro h _
    rw [norm_exp]
    have : (π * I * dsum h K - 2 * π * I * x * h / K : ℂ).re = 0 := by
      rw [show (π * I * dsum h K - 2 * π * I * x * h / K : ℂ) = ((π * dsum h K - 2 * π * x * h / K : ℝ) : ℂ) * I by
        push_cast; ring, re_ofReal_mul]
      simp
    rw [this, Real.exp_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)

lemma extra_term_le {n N k : ℕ} (hn : 1 ≤ n) (hN : N = Nat.sqrt n) (hk1 : N / 2 < k) (hkN : k ≤ N) :
    ‖(-1 : ℂ) ^ ((k + 1) / 2) * AAnd (2 * k) (shiftA k n) * (MK (2 * k) n : ℂ)‖ ≤
      2 * √24 * Real.exp 3 := by
  have hk : 0 < k := by omega
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h24 : 0 < 24 * (n : ℝ) - 1 := by linarith
  have hs24 : 0 < √(24 * (n : ℝ) - 1) := Real.sqrt_pos.mpr h24
  have hNn : n < (N + 1) * (N + 1) := by rw [hN]; exact Nat.lt_succ_sqrt n
  have hkn : (k : ℝ) ≤ 24 * n - 1 := by
    have : k ≤ n := le_trans hkN (by rw [hN]; exact Nat.sqrt_le_self n)
    have : (k : ℝ) ≤ n := by exact_mod_cast this
    linarith
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real, MK_two]
  -- the sinh argument is `≤ 3`
  have harg : π * √(24 * (n : ℝ) - 1) / (12 * k) ≤ 3 := by
    have h2k : (N : ℝ) + 1 ≤ 2 * k := by
      have : N + 1 ≤ 2 * k := by omega
      exact_mod_cast this
    have hsq : √(24 * (n : ℝ) - 1) ≤ 5 * (N + 1) := by
      rw [Real.sqrt_le_left (by positivity)]
      have : (n : ℝ) + 1 ≤ ((N : ℝ) + 1) ^ 2 := by
        have : n + 1 ≤ (N + 1) * (N + 1) := hNn
        have : ((n + 1 : ℕ) : ℝ) ≤ ((N + 1) * (N + 1) : ℕ) := by exact_mod_cast this
        push_cast at this; nlinarith
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    have : π * √(24 * (n : ℝ) - 1) ≤ 3.15 * (10 * k) :=
      mul_le_mul Real.pi_lt_d2.le (hsq.trans (by linarith)) (Real.sqrt_nonneg _) (by norm_num)
    linarith
  have hsinh : Real.sinh (π * √(24 * (n : ℝ) - 1) / (12 * k)) ≤ Real.exp 3 := by
    rw [Real.sinh_eq]
    have := Real.exp_le_exp.mpr harg
    have := Real.exp_pos (-(π * √(24 * (n : ℝ) - 1) / (12 * k)))
    have := Real.exp_pos 3
    linarith
  have hsinh0 : 0 ≤ Real.sinh (π * √(24 * (n : ℝ) - 1) / (12 * k)) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hA := norm_AAnd_le (2 * k) (shiftA k n)
  push_cast at hA
  have hsk : √(k : ℝ) ≤ √(24 * (n : ℝ) - 1) := Real.sqrt_le_sqrt hkn
  have hk0 : 0 < √(k : ℝ) := Real.sqrt_pos.mpr (by linarith)
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖AAnd (2 * k) (shiftA k n)‖ * (√24 / (√(k : ℝ) * √(24 * (n : ℝ) - 1)) *
        Real.sinh (π * √(24 * (n : ℝ) - 1) / (12 * k)))
      ≤ (2 * k) * (√24 / (√(k : ℝ) * √(24 * (n : ℝ) - 1)) * Real.exp 3) := by gcongr
    _ = 2 * √24 * Real.exp 3 * (√(k : ℝ) / √(24 * (n : ℝ) - 1)) := by
        have : (k : ℝ) = √(k : ℝ) * √(k : ℝ) := (Real.mul_self_sqrt (by linarith)).symm
        rw [this]; field_simp
        exact (Real.sq_sqrt (by positivity)).symm
    _ ≤ 2 * √24 * Real.exp 3 * 1 := by
        gcongr; rw [div_le_one hs24]; exact hsk
    _ = _ := mul_one _

/-- Andrews' printed main sum over `k ≤ ⌊√n⌋`. -/
def andrewsPrinted (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 (Nat.sqrt n), (-1 : ℂ) ^ ((k + 1) / 2) * AAnd (2 * k) (shiftA k n) * (MK (2 * k) n : ℂ)

/-- **Andrews' 1966 theorem as printed, conditional on `Hb`**: for `Hb C D` with `D ≥ 1` and all `n ≥ 1`
(`N = ⌊√n⌋`),
`|α(n) − Σ_{k=1}^{N} (−1)^{⌊(k+1)/2⌋} A_{2k}(n − k(1+(−1)^k)/4) M_{2k}(n)| ≤ A₁ N^{2D−1}(1 + log N) + A₂ N`. -/
theorem andrews_1966_printed_of_Hb {C D : ℝ} (hHb : Hb C D) (hC : 0 ≤ C) (hD : 1 ≤ D) :
    ∃ A₁ A₂ : ℝ, ∀ n : ℕ, 1 ≤ n →
      ‖(Dragonette.α n : ℂ) - andrewsPrinted n‖ ≤
        A₁ * ((Nat.sqrt n : ℝ) ^ (2 * D - 1) * (1 + Real.log (Nat.sqrt n))) + A₂ * Nat.sqrt n := by
  obtain ⟨A₁, A₂, hA⟩ := andrews_1966_of_Hb hHb hC hD
  refine ⟨A₁, A₂ + 2 * √24 * Real.exp 3, fun n hn => ?_⟩
  set N := Nat.sqrt n with hNdef
  set f : ℕ → ℂ := fun k => (-1 : ℂ) ^ ((k + 1) / 2) * AAnd (2 * k) (shiftA k n) * (MK (2 * k) n : ℂ) with hf
  have hhalf : ∑ k ∈ Finset.Icc 1 (N / 2), (-1) ^ k * Ab k n * (MK (2 * k) n : ℂ) =
      ∑ k ∈ Finset.Icc 1 (N / 2), f k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hf]; simp only
    rw [Ab_printed (by have := (Finset.mem_Icc.mp hk).1; omega) n]
  have hsplit : andrewsPrinted n = ∑ k ∈ Finset.Icc 1 (N / 2), f k +
      ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k ≤ N / 2), f k := by
    rw [andrewsPrinted, ← hNdef, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun k => k ≤ N / 2)]
    congr 2
    ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  have hextra : ‖∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k ≤ N / 2), f k‖ ≤ 2 * √24 * Real.exp 3 * N := by
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k ≤ N / 2), ‖f k‖ ≤ 2 * √24 * Real.exp 3 := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk
      exact extra_term_le hn hNdef (by omega) hk.1.2
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    gcongr
    have : ((Finset.Icc 1 N).filter (fun k => ¬ k ≤ N / 2)).card ≤ N :=
      (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  have h1 := hA n hn
  rw [hhalf] at h1
  rw [hsplit, show (Dragonette.α n : ℂ) - (∑ k ∈ Finset.Icc 1 (N / 2), f k +
      ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k ≤ N / 2), f k) =
      ((Dragonette.α n : ℂ) - ∑ k ∈ Finset.Icc 1 (N / 2), f k) -
      ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k ≤ N / 2), f k by ring]
  refine (norm_sub_le _ _).trans ?_
  linarith

/-- **`O`-form, Andrews' `O(√n log n)`**: if `Hb C D` holds with `D ≤ 1`, then
`α(n) = Σ_{k ≤ √n} (−1)^{⌊(k+1)/2⌋} A_{2k}(n − k(1+(−1)^k)/4) π(24n−1)^{−1/4} I_{1/2}(π√(24n−1)/(12k))/k + O(√n log n)`. -/
theorem andrews_1966_printed_isBigO_of_Hb {C D : ℝ} (hHb : Hb C D) (hC : 0 ≤ C) (hD : D ≤ 1) :
    (fun n : ℕ => (Dragonette.α n : ℂ) - andrewsPrinted n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log n)) := by
  obtain ⟨A₁, A₂, hA⟩ := andrews_1966_printed_of_Hb (Hb_mono hHb hC hD) (by positivity) le_rfl
  refine Asymptotics.IsBigO.of_bound (|A₁| + |A₂|) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set N := Nat.sqrt n
  have hN : 1 ≤ N := Nat.sqrt_pos.mpr hn
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNs : (N : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast Nat.sqrt_le' n
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hnr
  have hG : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log n) := by positivity
  rw [Real.norm_of_nonneg hG]
  have hb := hA n hn
  norm_num at hb
  have h2 : 1 + Real.log N ≤ 1 + Real.log n := by
    have : (N : ℝ) ≤ n := by exact_mod_cast Nat.sqrt_le_self n
    linarith [Real.log_le_log (by positivity) this]
  have hsq : (N : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by rw [← Real.sqrt_eq_rpow]; exact hNs
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  have e1 : A₁ * ((N : ℝ) * (1 + Real.log N)) ≤ |A₁| * ((n : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log n)) := by
    calc A₁ * ((N : ℝ) * (1 + Real.log N)) ≤ |A₁| * ((N : ℝ) * (1 + Real.log N)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ _ := by gcongr
  have e2 : A₂ * N ≤ |A₂| * ((n : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log n)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
      (by gcongr; exact hsq.trans (le_mul_of_one_le_right (by positivity) (by linarith)))
  linarith

end

end Andrews66
