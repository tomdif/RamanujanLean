/-
# Andrews' 1966 theorem for the coefficients of `f(q)`, conditional on `Hb`

`andrews_1966_of_Hb`: if `Hb C D` holds with `D ≥ 1`, then for all `n ≥ 1`, with `N = ⌊√n⌋`,

  `|α(n) − Σ_{k=1}^{⌊N/2⌋} (−1)^k A_b(k,n) M_{2k}(n)| ≤ A₁ N^{2D−1}(1 + log N) + A₂ N`,

where `M_{2k}(n) = √24/(√k √(24n−1)) sinh(π√(24n−1)/(12k)) = π(24n−1)^{−1/4} I_{1/2}(π√(24n−1)/(12k))/k`
(`MK_two`) and `A_b(k,n) = Σ_{h mod 2k, (h,2k)=1} ω_b(h,k) e^{−2πinh/(2k)}` is the Kloosterman sum of the
multiplier `ω_b` of `b = (q;q)³_∞/(q²;q²)²_∞` (`omegaB`). For `D = 1` the error is Andrews' `O(√n log n)`.

Numerically (`docs/ANDREWS_1966_ASYMPTOTIC.md`): `(−1)^k A_b(k,n) = (−1)^{⌊(k+1)/2⌋} A_{2k}(n − k(1+(−1)^k)/4)`
with Rademacher's `A_{2k}`, i.e. the main sum is exactly Andrews' sum.
-/
import RamanujanTau.Andrews66.Arc

set_option autoImplicit false

namespace Andrews66
open Complex Filter Metric MeasureTheory Set
open scoped Real Topology

noncomputable section

/-- the Kloosterman sum of `ω_b` at denominator `2k`. -/
def Ab (k n : ℕ) : ℂ :=
  ∑ h ∈ (Finset.range (2 * k)).filter (fun h => Nat.Coprime h (2 * k)),
    omegaB h (2 * k / 2) * cexp (-(2 * π * I * n * h / ((2 * k : ℕ) : ℂ)))

/-- `M_{2k}(n)` in Andrews' normalization. -/
lemma MK_two (k n : ℕ) :
    MK (2 * k) n = √24 / (√k * √(24 * (n : ℝ) - 1)) * Real.sinh (π * √(24 * (n : ℝ) - 1) / (12 * k)) := by
  unfold MK
  push_cast
  rw [show (6 : ℝ) * (2 * k) = 12 * k by ring, Real.sqrt_mul (by norm_num), show (48 : ℝ) = 2 * 24 by norm_num,
    Real.sqrt_mul (by norm_num)]
  have h2 : (0 : ℝ) < √2 := by positivity
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have : (0 : ℝ) < √(k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  rcases eq_or_ne (√(24 * (n : ℝ) - 1)) 0 with h0 | h0
  · rw [h0]; simp
  field_simp

/-! ### summing the arc errors -/

lemma E_le {n N : ℕ} (hN : 1 ≤ N) (hn : n < (N + 1) * (N + 1)) :
    Real.exp (2 * π * n * (1 / (N : ℝ) ^ 2)) ≤ Real.exp (8 * π) := by
  apply Real.exp_le_exp.mpr
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn' : (n : ℝ) ≤ 4 * N ^ 2 := by
    have : n ≤ 4 * N ^ 2 := by nlinarith
    exact_mod_cast this
  rw [show 2 * π * n * (1 / (N : ℝ) ^ 2) = 2 * π * (n / N ^ 2) by ring]
  have : (n : ℝ) / N ^ 2 ≤ 4 := by rw [div_le_iff₀ (by positivity)]; linarith
  nlinarith [Real.pi_pos]

lemma rpow_term {K N : ℕ} (hK : 1 ≤ K) (hN : 1 ≤ N) {D : ℝ} (hD : 1 ≤ D) :
    2 / (N : ℝ) * ((K : ℝ) * (1 / (N : ℝ) ^ 2)) ^ (-D) ≤ 2 * (N : ℝ) ^ (2 * D - 1) / K := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hK0 : (0 : ℝ) < K := by linarith
  have key : ((K : ℝ) * (1 / (N : ℝ) ^ 2)) ^ (-D) = (K : ℝ) ^ (-D) * (N : ℝ) ^ (2 * D) := by
    rw [Real.mul_rpow hK0.le (by positivity)]
    congr 1
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_neg,
      ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  rw [key]
  have hKD : (K : ℝ) ^ (-D) ≤ (K : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hKr (by linarith)
  rw [Real.rpow_neg_one] at hKD
  rw [Real.rpow_sub_one hN0.ne']
  push_cast
  have hp : 0 < (N : ℝ) ^ (2 * D) := Real.rpow_pos_of_pos hN0 _
  calc 2 / (N : ℝ) * ((K : ℝ) ^ (-D) * (N : ℝ) ^ (2 * D)) ≤ 2 / (N : ℝ) * ((K : ℝ)⁻¹ * (N : ℝ) ^ (2 * D)) := by
        gcongr
    _ = _ := by field_simp

lemma sqrt_term {K N : ℕ} (hK : 1 ≤ K) (hN : 1 ≤ N) :
    2 / (N : ℝ) * (√((K : ℝ) * (1 / (N : ℝ) ^ 2)))⁻¹ ≤ 2 := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [Real.sqrt_mul (by linarith), one_div, Real.sqrt_inv, Real.sqrt_sq hN0.le]
  have hs : 1 ≤ √(K : ℝ) := by rw [Real.one_le_sqrt]; exact hKr
  rw [mul_inv, inv_inv]
  calc 2 / (N : ℝ) * ((√(K : ℝ))⁻¹ * N) = 2 * (√(K : ℝ))⁻¹ := by field_simp
    _ ≤ 2 * 1 := by gcongr; exact inv_le_one_of_one_le₀ hs
    _ = 2 := mul_one 2

/-- the per-`K` bound `K·Barc ≤ A₁N^{2D−1}/K + A₂`. -/
lemma K_Barc_le {C D Cb : ℝ} (hC : 0 ≤ C) (hCb : 0 ≤ Cb) (hD : 1 ≤ D) {n N K : ℕ} (hK : 1 ≤ K) (hN : 1 ≤ N)
    (hn : n < (N + 1) * (N + 1)) :
    (K : ℝ) * Barc C D Cb n N K ≤ 2 * Real.exp (8 * π) * C * (N : ℝ) ^ (2 * D - 1) / K +
      (2 * Real.exp (8 * π) * (Cb + Real.exp (π / 3)) + 4 * √10 * Real.exp (π / 3) * Real.exp (8 * π)) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨E, hEdef⟩ : ∃ E, E = Real.exp (2 * π * n * (1 / (N : ℝ) ^ 2)) := ⟨_, rfl⟩
  have hE := E_le hN hn
  rw [← hEdef] at hE
  have hE0 : 0 ≤ E := by rw [hEdef]; exact (Real.exp_pos _).le
  have e : (K : ℝ) * Barc C D Cb n N K =
      E * C * (2 / (N : ℝ) * ((K : ℝ) * (1 / (N : ℝ) ^ 2)) ^ (-D)) +
      E * (Cb + Real.exp (π / 3)) * (2 / (N : ℝ) * (√((K : ℝ) * (1 / (N : ℝ) ^ 2)))⁻¹) +
      4 * √10 * Real.exp (π / 3) * E := by
    unfold Barc; rw [← hEdef]; field_simp
  rw [e]
  have h1 := rpow_term hK hN hD
  have h2 := sqrt_term hK hN
  have hc1 : 0 ≤ Cb + Real.exp (π / 3) := by positivity
  have t1 : E * C * (2 / (N : ℝ) * ((K : ℝ) * (1 / (N : ℝ) ^ 2)) ^ (-D)) ≤
      Real.exp (8 * π) * C * (2 * (N : ℝ) ^ (2 * D - 1) / K) := by
    have : 0 ≤ 2 / (N : ℝ) * ((K : ℝ) * (1 / (N : ℝ) ^ 2)) ^ (-D) := by positivity
    calc E * C * (2 / (N : ℝ) * ((K : ℝ) * (1 / (N : ℝ) ^ 2)) ^ (-D))
        ≤ Real.exp (8 * π) * C * (2 / (N : ℝ) * ((K : ℝ) * (1 / (N : ℝ) ^ 2)) ^ (-D)) := by gcongr
      _ ≤ _ := by gcongr
  have t2 : E * (Cb + Real.exp (π / 3)) * (2 / (N : ℝ) * (√((K : ℝ) * (1 / (N : ℝ) ^ 2)))⁻¹) ≤
      Real.exp (8 * π) * (Cb + Real.exp (π / 3)) * 2 := by
    have : 0 ≤ 2 / (N : ℝ) * (√((K : ℝ) * (1 / (N : ℝ) ^ 2)))⁻¹ := by positivity
    calc _ ≤ Real.exp (8 * π) * (Cb + Real.exp (π / 3)) * (2 / (N : ℝ) * (√((K : ℝ) * (1 / (N : ℝ) ^ 2)))⁻¹) := by
          gcongr
      _ ≤ _ := by gcongr
  have t3 : 4 * √10 * Real.exp (π / 3) * E ≤ 4 * √10 * Real.exp (π / 3) * Real.exp (8 * π) := by gcongr
  have : Real.exp (8 * π) * C * (2 * (N : ℝ) ^ (2 * D - 1) / K) =
      2 * Real.exp (8 * π) * C * (N : ℝ) ^ (2 * D - 1) / K := by ring
  linarith

lemma sum_Barc_le {C D Cb : ℝ} (hC : 0 ≤ C) (hCb : 0 ≤ Cb) (hD : 1 ≤ D) {n N : ℕ} (hN : 1 ≤ N)
    (hn : n < (N + 1) * (N + 1)) :
    ∑ K ∈ Finset.Icc 1 N, (K : ℝ) * Barc C D Cb n N K ≤
      2 * Real.exp (8 * π) * C * ((N : ℝ) ^ (2 * D - 1) * (1 + Real.log N)) +
      (2 * Real.exp (8 * π) * (Cb + Real.exp (π / 3)) + 4 * √10 * Real.exp (π / 3) * Real.exp (8 * π)) * N := by
  set A₂ := 2 * Real.exp (8 * π) * (Cb + Real.exp (π / 3)) + 4 * √10 * Real.exp (π / 3) * Real.exp (8 * π)
  have hsum := Finset.sum_le_sum fun K (hK : K ∈ Finset.Icc 1 N) =>
    K_Barc_le (n := n) hC hCb hD (Finset.mem_Icc.mp hK).1 hN hn
  refine hsum.trans (le_of_eq_of_le (Finset.sum_add_distrib) ?_)
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, show N + 1 - 1 = N by omega]
  have e : ∑ K ∈ Finset.Icc 1 N, 2 * Real.exp (8 * π) * C * (N : ℝ) ^ (2 * D - 1) / (K : ℝ) =
      2 * Real.exp (8 * π) * C * (N : ℝ) ^ (2 * D - 1) * ∑ K ∈ Finset.Icc 1 N, ((K : ℝ))⁻¹ := by
    rw [Finset.mul_sum]; rfl
  rw [e]
  have hH : ∑ K ∈ Finset.Icc 1 N, ((K : ℝ))⁻¹ ≤ 1 + Real.log N := by
    have := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    exact this
  have h0 : 0 ≤ 2 * Real.exp (8 * π) * C * (N : ℝ) ^ (2 * D - 1) := by positivity
  have := mul_le_mul_of_nonneg_left hH h0
  nlinarith

/-! ### the main sum over even denominators -/

lemma epsK_two (k : ℕ) : epsK (2 * k) = (-1) ^ k := by
  unfold epsK; rw [if_pos (even_two_mul k)]; congr 1; omega

/-- the contribution of denominator `K`. -/
def Gterm (n K : ℕ) : ℂ := epsK K * (∑ h ∈ (Finset.range K).filter (fun h => Nat.Coprime h K),
      omegaB h (K / 2) * cexp (-(2 * π * I * n * h / K))) * MK K n

lemma main_reindex (n N : ℕ) :
    ∑ K ∈ Finset.Icc 1 N, ∑ h ∈ (Finset.range K).filter (fun h => Nat.Coprime h K),
        cexp (-(2 * π * I * n * h / K)) * (epsK K * omegaB h (K / 2) * MK K n) =
      ∑ k ∈ Finset.Icc 1 (N / 2), (-1) ^ k * Ab k n * MK (2 * k) n := by
  have e1 : ∀ K, (∑ h ∈ (Finset.range K).filter (fun h => Nat.Coprime h K),
      cexp (-(2 * π * I * n * h / K)) * (epsK K * omegaB h (K / 2) * MK K n)) = Gterm n K := by
    intro K
    rw [Gterm, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun h _ => by ring
  simp only [e1]
  have hinj : Set.InjOn (fun k : ℕ => 2 * k) (Finset.Icc 1 (N / 2) : Set ℕ) := fun a _ b _ h => by
    simp only at h; omega
  have e2 : ∑ k ∈ Finset.Icc 1 (N / 2), (-1) ^ k * Ab k n * MK (2 * k) n =
      ∑ k ∈ Finset.Icc 1 (N / 2), Gterm n (2 * k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Gterm, epsK_two, Ab]
  rw [e2, ← Finset.sum_image (f := Gterm n) hinj]
  symm
  refine Finset.sum_subset (fun K hK => ?_) (fun K hK hK' => ?_)
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hK
    rw [Finset.mem_Icc] at hk ⊢; omega
  · have hodd : ¬ Even K := by
      rintro ⟨k, rfl⟩
      apply hK'
      rw [Finset.mem_Icc] at hK
      exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by ring⟩
    rw [Gterm]
    unfold epsK; rw [if_neg hodd]; ring

/-! ### the theorem -/

/-- **Andrews' 1966 asymptotic for `α(n) = [qⁿ]f(q)`, conditional on `Hb`**: if `Hb C D` holds with
`D ≥ 1`, then for every `n ≥ 1`, with `N = ⌊√n⌋`,
`|α(n) − Σ_{k ≤ N/2} (−1)^k A_b(k,n) M_{2k}(n)| ≤ A₁ N^{2D−1}(1 + log N) + A₂ N`. -/
theorem andrews_1966_of_Hb {C D : ℝ} (hHb : Hb C D) (hC : 0 ≤ C) (hD : 1 ≤ D) :
    ∃ A₁ A₂ : ℝ, ∀ n : ℕ, 1 ≤ n →
      ‖(Dragonette.α n : ℂ) - ∑ k ∈ Finset.Icc 1 (Nat.sqrt n / 2), (-1) ^ k * Ab k n * MK (2 * k) n‖ ≤
        A₁ * ((Nat.sqrt n : ℝ) ^ (2 * D - 1) * (1 + Real.log (Nat.sqrt n))) + A₂ * Nat.sqrt n := by
  obtain ⟨Cb, hCb, hbn⟩ := bE_near
  refine ⟨2 * Real.exp (8 * π) * C,
    2 * Real.exp (8 * π) * (Cb + Real.exp (π / 3)) + 4 * √10 * Real.exp (π / 3) * Real.exp (8 * π),
    fun n hn => ?_⟩
  set N := Nat.sqrt n with hNdef
  have hN : 1 ≤ N := Nat.sqrt_pos.mpr hn
  have hnN : n < (N + 1) * (N + 1) := Nat.lt_succ_sqrt n
  have hB0 : ∀ K, 0 ≤ Barc C D Cb n N K := by
    intro K; unfold Barc
    have : 0 ≤ C * ((K : ℝ) * (1 / (N : ℝ) ^ 2)) ^ (-D) := by
      have : 0 ≤ ((K : ℝ) * (1 / (N : ℝ) ^ 2)) ^ (-D) := Real.rpow_nonneg (by positivity) _
      positivity
    positivity
  have H := arcs_approx n N hN (y := 1 / (N : ℝ) ^ 2) (by positivity)
    (fun x => cexp (-(2 * π * I * n * x.1 / x.2)) * (epsK x.2 * omegaB x.1 (x.2 / 2) * MK x.2 n))
    (Barc C D Cb n N) hB0
    (fun h K kp kn hK hKN hkp hkn hNp hNn hcop hdvd =>
      arc_bound hHb (by linarith) hC hCb hbn hn hK hKN hkp hkn hNp hNn hcop hdvd)
  simp only at H
  rw [main_reindex] at H
  exact H.trans (sum_Barc_le hC hCb hD hN hnN)

/-- Andrews' main sum `Σ_{k ≤ ⌊√n⌋/2} (−1)^k A_b(k,n) M_{2k}(n)`. -/
def andrewsMain (n : ℕ) : ℂ := ∑ k ∈ Finset.Icc 1 (Nat.sqrt n / 2), (-1) ^ k * Ab k n * MK (2 * k) n

/-- **Andrews' 1966 asymptotic, `O`-form**: under `Hb C D` (`D ≥ 1`),
`α(n) = Σ_{k ≤ √n/2} (−1)^k A_b(k,n) M_{2k}(n) + O(n^{D−1/2} log n)`; for `D = 1` this is `O(√n log n)`. -/
theorem andrews_1966_isBigO_of_Hb {C D : ℝ} (hHb : Hb C D) (hC : 0 ≤ C) (hD : 1 ≤ D) :
    (fun n : ℕ => (Dragonette.α n : ℂ) - andrewsMain n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (D - 1 / 2) * (1 + Real.log n)) := by
  obtain ⟨A₁, A₂, hA⟩ := andrews_1966_of_Hb hHb hC hD
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
  have hG : 0 ≤ (n : ℝ) ^ (D - 1 / 2) * (1 + Real.log n) := by positivity
  rw [Real.norm_of_nonneg hG]
  have h1 : (N : ℝ) ^ (2 * D - 1) ≤ (n : ℝ) ^ (D - 1 / 2) := by
    calc (N : ℝ) ^ (2 * D - 1) ≤ (√(n : ℝ)) ^ (2 * D - 1) :=
          Real.rpow_le_rpow (by positivity) hNs (by linarith)
      _ = (n : ℝ) ^ (D - 1 / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]; congr 1; ring
  have h2 : 1 + Real.log N ≤ 1 + Real.log n := by
    have : (N : ℝ) ≤ n := by exact_mod_cast Nat.sqrt_le_self n
    linarith [Real.log_le_log (by positivity) this]
  have h3 : (N : ℝ) ≤ (n : ℝ) ^ (D - 1 / 2) * (1 + Real.log n) := by
    calc (N : ℝ) ≤ √(n : ℝ) := hNs
      _ = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      _ ≤ (n : ℝ) ^ (D - 1 / 2) := Real.rpow_le_rpow_of_exponent_le hnr (by linarith)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hX : 0 ≤ (N : ℝ) ^ (2 * D - 1) * (1 + Real.log N) := by positivity
  have hb := hA n hn
  have e1 : A₁ * ((N : ℝ) ^ (2 * D - 1) * (1 + Real.log N)) ≤
      |A₁| * ((n : ℝ) ^ (D - 1 / 2) * (1 + Real.log n)) := by
    calc A₁ * ((N : ℝ) ^ (2 * D - 1) * (1 + Real.log N)) ≤ |A₁| * ((N : ℝ) ^ (2 * D - 1) * (1 + Real.log N)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hX
      _ ≤ _ := by
          gcongr
  have e2 : A₂ * N ≤ |A₂| * ((n : ℝ) ^ (D - 1 / 2) * (1 + Real.log n)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans (by gcongr)
  unfold andrewsMain
  linarith

end

end Andrews66
