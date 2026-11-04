import RamanujanTau.TauDensity.NormFormCount

/-! # `#{n ≤ N : τ(n) ≠ 0} ≥ N / (221 120 (1 + log N)²)`

Every value `n = x² + 691y²` (`1 ≤ x ≤ A = ⌊√(N/2)⌋`, `1 ≤ y ≤ B = ⌊√(N/1382)⌋`) lies in `[1, N]` and has
`τ(n) ≠ 0` (`tau_norm_form_ne_zero`). By Cauchy–Schwarz the number of distinct values is at least
`(AB)² / E`, where `E` counts coincidences `x² + 691y² = u² + 691v²`; `E ≤ AB + 2(M(1+log M))²`
with `M = 2A` (`card_energy_le`, `card_hyp_le`). With `A² ≥ N/8`, `B² ≥ N/5528` this gives the headline.

* `card_tau_ne_zero_ge_div_log_sq`: `∀ N, N / (221120·(1 + log N)²) ≤ #{n ∈ [1,N] : τ(n) ≠ 0}`.
* `card_tau_ne_zero_ge_rpow_one_sub`: `∀ ε > 0, ∃ c > 0, ∀ N ≥ 1, c·N^{1−ε} ≤ #{n ∈ [1,N] : τ(n) ≠ 0}`.
-/

set_option autoImplicit false

namespace RamanujanTau.TauDensity
open RamanujanTau Finset

theorem card_tau_ne_zero_ge_div_log_sq_of_le {N : ℕ} (hN : 1382 ≤ N) :
    (N : ℝ) / (221120 * (1 + Real.log N) ^ 2) ≤
      (((Icc 1 N).filter (fun n => τ n ≠ 0)).card : ℝ) := by
  set A := Nat.sqrt (N / 2) with hAdef
  set B := Nat.sqrt (N / 1382) with hBdef
  set Z := ((Icc 1 N).filter (fun n => τ n ≠ 0)).card
  set I := ((box A B).image nf).card
  set E := ((box A B ×ˢ box A B).filter (fun pq => nf pq.1 = nf pq.2)).card
  set H := (hyp (2 * A)).card
  -- natural-number facts about `A`, `B`
  have hA2 : A ^ 2 ≤ N / 2 := Nat.sqrt_le' _
  have hB2 : B ^ 2 ≤ N / 1382 := Nat.sqrt_le' _
  have hA1 : 1 ≤ A := Nat.le_sqrt.mpr (by omega)
  have hB1 : 1 ≤ B := Nat.le_sqrt.mpr (by omega)
  have hAl : N / 2 < (A + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hBl : N / 1382 < (B + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hNA : N ≤ 8 * A ^ 2 := by have := Nat.div_add_mod N 2; have := Nat.mod_lt N (show 2 > 0 by omega); nlinarith
  have hNB : N ≤ 5528 * B ^ 2 := by
    have := Nat.div_add_mod N 1382; have := Nat.mod_lt N (show 1382 > 0 by omega); nlinarith
  have hA2N : 2 * A ^ 2 ≤ N := by have := Nat.div_mul_le_self N 2; omega
  have hB2N : 1382 * B ^ 2 ≤ N := by have := Nat.div_mul_le_self N 1382; omega
  -- the values land in the non-vanishing set
  have hIZ : I ≤ Z := by
    refine card_le_card fun n hn => ?_
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := mem_image.mp hn
    simp only [box, mem_product, mem_Icc] at hxy
    obtain ⟨⟨hx1, hxA⟩, hy1, hyB⟩ := hxy
    have hx2 : x ^ 2 ≤ A ^ 2 := Nat.pow_le_pow_left hxA 2
    have hy2 : y ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hyB 2
    have hx0 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx1
    simp only [nf, mem_filter, mem_Icc]
    exact ⟨⟨by omega, by omega⟩, tau_norm_form_ne_zero (by omega)⟩
  -- Cauchy–Schwarz and the energy bound
  have hCS : (A * B) ^ 2 ≤ I * E := by
    have := card_sq_le_card_image_mul_energy (box A B) nf
    simpa [box, card_product] using this
  have hE : E ≤ A * B + 2 * H ^ 2 := card_energy_le A B
  -- pass to ℝ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  set L := Real.log N
  have hM1 : (1 : ℝ) ≤ ((2 * A : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * A by omega)
  have hMN : ((2 * A : ℕ) : ℝ) ≤ N := by
    have : 2 * A ≤ N := by nlinarith
    exact_mod_cast this
  have hlogM : Real.log ((2 * A : ℕ) : ℝ) ≤ L := Real.log_le_log (by linarith) hMN
  have hlogM0 : 0 ≤ Real.log ((2 * A : ℕ) : ℝ) := Real.log_nonneg hM1
  have hH : (H : ℝ) ≤ ((2 * A : ℕ) : ℝ) * (1 + L) := by
    refine (card_hyp_le (2 * A)).trans ?_
    gcongr
  have hM2 : ((2 * A : ℕ) : ℝ) ^ 2 ≤ 2 * N := by
    have : (2 * A) ^ 2 ≤ 2 * N := by nlinarith
    exact_mod_cast this
  have hH2 : (H : ℝ) ^ 2 ≤ 2 * N * (1 + L) ^ 2 := by
    have h0 : (0 : ℝ) ≤ H := Nat.cast_nonneg _
    calc (H : ℝ) ^ 2 ≤ (((2 * A : ℕ) : ℝ) * (1 + L)) ^ 2 := pow_le_pow_left₀ h0 hH 2
      _ = ((2 * A : ℕ) : ℝ) ^ 2 * (1 + L) ^ 2 := by ring
      _ ≤ 2 * N * (1 + L) ^ 2 := by gcongr
  have hAB : ((A * B : ℕ) : ℝ) ≤ N := by
    have : A * B ≤ N := by nlinarith
    exact_mod_cast this
  have hD1 : (1 : ℝ) ≤ (1 + L) ^ 2 := by nlinarith
  have hER : (E : ℝ) ≤ 5 * N * (1 + L) ^ 2 := by
    have : (E : ℝ) ≤ ((A * B : ℕ) : ℝ) + 2 * (H : ℝ) ^ 2 := by exact_mod_cast hE
    nlinarith
  have hlow : (N : ℝ) ^ 2 ≤ 44224 * ((A * B : ℕ) : ℝ) ^ 2 := by
    have : N ^ 2 ≤ 44224 * (A * B) ^ 2 := by
      have := Nat.mul_le_mul hNA hNB
      calc N ^ 2 = N * N := sq N
        _ ≤ 8 * A ^ 2 * (5528 * B ^ 2) := this
        _ = 44224 * (A * B) ^ 2 := by ring
    exact_mod_cast this
  have hCSR : ((A * B : ℕ) : ℝ) ^ 2 ≤ (I : ℝ) * E := by exact_mod_cast hCS
  have hIZR : (I : ℝ) ≤ Z := by exact_mod_cast hIZ
  have hI0 : (0 : ℝ) ≤ I := Nat.cast_nonneg _
  -- conclude
  have key : (N : ℝ) * N ≤ 221120 * (1 + L) ^ 2 * N * Z := by
    have h1 : (I : ℝ) * E ≤ I * (5 * N * (1 + L) ^ 2) := mul_le_mul_of_nonneg_left hER hI0
    have h2 : (I : ℝ) * (5 * N * (1 + L) ^ 2) ≤ Z * (5 * N * (1 + L) ^ 2) :=
      mul_le_mul_of_nonneg_right hIZR (by positivity)
    calc (N : ℝ) * N = (N : ℝ) ^ 2 := (sq _).symm
      _ ≤ 44224 * ((A * B : ℕ) : ℝ) ^ 2 := hlow
      _ ≤ 44224 * ((I : ℝ) * E) := by linarith
      _ ≤ 44224 * ((Z : ℝ) * (5 * N * (1 + L) ^ 2)) := by linarith
      _ = 221120 * (1 + L) ^ 2 * N * Z := by ring
  rw [div_le_iff₀ (by positivity)]
  have key' : (N : ℝ) * N ≤ (Z * (221120 * (1 + L) ^ 2)) * N := by linarith
  exact le_of_mul_le_mul_right key' hN0

/-- **Headline.** For every `N`, `N / (221 120 (1 + log N)²) ≤ #{n ∈ [1,N] : τ(n) ≠ 0}`. -/
theorem card_tau_ne_zero_ge_div_log_sq (N : ℕ) :
    (N : ℝ) / (221120 * (1 + Real.log N) ^ 2) ≤
      (((Icc 1 N).filter (fun n => τ n ≠ 0)).card : ℝ) := by
  rcases Nat.lt_or_ge N 1382 with hN | hN
  · have h1 : min N 21492863998 = N := min_eq_left (by omega)
    have h2 := (le_max_right _ _).trans (card_tau_ne_zero_ge N)
    rw [h1] at h2
    have h2' : (N : ℝ) ≤ (((Icc 1 N).filter (fun n => τ n ≠ 0)).card : ℝ) := by exact_mod_cast h2
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · simp
    have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hpos)
    refine le_trans ?_ h2'
    rw [div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have h3 : (1 : ℝ) ≤ 221120 * (1 + Real.log N) ^ 2 := by nlinarith
    nlinarith
  · exact card_tau_ne_zero_ge_div_log_sq_of_le hN

/-- **Corollary.** `∀ ε > 0, ∃ c > 0, ∀ N ≥ 1, c·N^{1−ε} ≤ #{n ∈ [1,N] : τ(n) ≠ 0}`. -/
theorem card_tau_ne_zero_ge_rpow_one_sub (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
      c * (N : ℝ) ^ (1 - ε) ≤ (((Icc 1 N).filter (fun n => τ n ≠ 0)).card : ℝ) := by
  set K : ℝ := 1 + 2 / ε
  have hK : 0 < K := by positivity
  refine ⟨1 / (221120 * K ^ 2), by positivity, fun N hN => ?_⟩
  refine le_trans ?_ (card_tau_ne_zero_ge_div_log_sq N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  set R := (N : ℝ) ^ (ε / 2)
  have hR1 : 1 ≤ R := Real.one_le_rpow hN1 (by positivity)
  have hlog : Real.log N ≤ R / (ε / 2) := Real.log_le_rpow_div hN0.le (by positivity)
  have hlog' : 1 + Real.log N ≤ K * R := by
    have : R / (ε / 2) = (2 / ε) * R := by field_simp
    simp only [K]; nlinarith
  have hRR : R ^ 2 = (N : ℝ) ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hD : (1 + Real.log N) ^ 2 ≤ K ^ 2 * (N : ℝ) ^ ε := by
    rw [← hRR, ← mul_pow]; exact pow_le_pow_left₀ (by positivity) hlog' 2
  have hpow : (N : ℝ) ^ (1 - ε) = N / (N : ℝ) ^ ε := by
    rw [Real.rpow_sub hN0, Real.rpow_one]
  have hNe : 0 < (N : ℝ) ^ ε := Real.rpow_pos_of_pos hN0 _
  rw [hpow, show 1 / (221120 * K ^ 2) * ((N : ℝ) / (N : ℝ) ^ ε) =
    (N : ℝ) / (221120 * (K ^ 2 * (N : ℝ) ^ ε)) by field_simp]
  have hD0 : 0 < (1 + Real.log N) ^ 2 := by positivity
  exact div_le_div_of_nonneg_left hN0.le (by positivity) (by linarith)

end RamanujanTau.TauDensity

#print axioms RamanujanTau.TauDensity.card_sq_le_card_image_mul_energy
#print axioms RamanujanTau.TauDensity.card_energy_le
#print axioms RamanujanTau.TauDensity.card_hyp_le
#print axioms RamanujanTau.TauDensity.card_tau_ne_zero_ge_div_log_sq
#print axioms RamanujanTau.TauDensity.card_tau_ne_zero_ge_rpow_one_sub
