/-
# Every exponent `δ < 1/5` for the Rankin–Selberg mean square of `τ`

**`rankinSelberg_power_saving_sharp`** (unconditional, axiom-clean): for every `0 < δ < 1/5`,

    ∑_{n≤N} τ(n)²/n¹¹ = (3/π)(4π)¹²‖Δ‖²/11! · N + O(N^{1−δ}).

Route. Work with `ζ(2s)D(s) = ∑ bₙ n^{−s}` (`b = χ * a`, `bₙ ≥ 0`) instead of `D(s)`: it has no
`1/ζ(2s)`, so the contour can go to any `σ₁ > 0`. There `E(s) = (s−1)ζ(2s)D(s)` satisfies
`‖E‖ ≪ ‖s+3‖⁴` (`Efun_bound`, `σ_L = 0`, the convexity bound through the exact line
`Re s = 0`), so `F_b = dslope E 1 = ζ(2s)D(s) − c₀/(s−1)` is `O((1+|t|)³)` on `[0, 5/2]`.
`rieszAsymp_of_continuation` (order `4`, saving `1−σ₁`) and `riesz_kdiff` (one 4-th
difference) give `B(N) = c₀N + O(N^{1−(1−σ₁)/5})`; `mobius_transfer` brings this back to
`∑ aₙ` (needs `δ < 1/2`), with `c₀ · 6/π² = κ · rsConst`.
-/
import RamanujanTau.RankinSharp.Sharp8
import RamanujanTau.RankinSharp.Squares
import RamanujanTau.RankinSharp.Mobius

set_option autoImplicit false

namespace RamanujanTau.RankinSharp

open Complex Real Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinSelberg RamanujanTau.EisensteinReal
open ArithmeticFunction

/-- Real summability from `L`-series summability, for nonnegative coefficients. -/
lemma summable_of_LSeriesSummable {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hf0 : f 0 = 0) {c : ℝ}
    (h : LSeriesSummable (fun n => (f n : ℂ)) (c : ℂ)) :
    Summable fun n : ℕ => f n * (n : ℝ) ^ (-c) := by
  refine h.norm.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [hf0]
  · rw [if_neg h.ne', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf n),
      Real.rpow_neg (Nat.cast_nonneg n)]
    simp [div_eq_mul_inv]

section B

variable {a : ℕ → ℝ} {κ : ℝ} (d : RSData a κ)

/-- The residue `E(1) = κ γ(1)⁻¹ = κ · rsConst · ζ(2)`. -/
noncomputable def cB : ℝ := κ * rsConst * (π ^ 2 / 6)

lemma Efun_one : Efun d 1 = (cB (κ := κ) : ℂ) := by
  have hz : riemannZeta 2 ≠ 0 := by
    rw [riemannZeta_two]; exact div_ne_zero (pow_ne_zero 2 pi_ne_zero') (by norm_num)
  have hinv : invGam 1 = (rsConst : ℂ) * riemannZeta 2 := by
    have h := gfun_one
    unfold gfun at h
    rw [mul_one] at h
    rw [← h, mul_assoc, inv_mul_cancel₀ hz, mul_one]
  unfold Efun cB
  rw [hinv, riemannZeta_two]
  push_cast
  ring

/-- `F_b(s) = (E(s) − E(1))/(s − 1)`, entire. -/
noncomputable def Fb : ℂ → ℂ := dslope (Efun d) 1

lemma differentiable_Fb : Differentiable ℂ (Fb d) := by
  have := (differentiableOn_dslope (f := Efun d) (c := (1 : ℂ)) (s := univ) univ_mem).2
    (differentiable_Efun d).differentiableOn
  exact differentiableOn_univ.1 this

lemma Fb_eq {s : ℂ} (h1 : s ≠ 1) : Fb d s = (Efun d s - cB (κ := κ)) / (s - 1) := by
  unfold Fb
  rw [dslope_of_ne _ h1, slope_def_field, Efun_one]

variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

include habs in
/-- `‖F_b(s)‖ ≤ B (1+|t|)³` on `0 ≤ Re s ≤ 5/2`. -/
theorem Fb_bound : ∃ B : ℝ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 5 / 2 →
    ‖Fb d s‖ ≤ B * (1 + |s.im|) ^ 3 := by
  obtain ⟨B₀, hB₀⟩ := Efun_bound d habs (σL := 0) (n := 3) (by norm_num) le_rfl (by norm_num)
  have hK : IsCompact (Icc (0 : ℝ) (5 / 2) ×ℂ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn (differentiable_Fb d).continuous.continuousOn
  set B : ℝ := |B₀| * 1080 + |cB (κ := κ)| + |C₂| with hB
  refine ⟨B, fun s h1 h2 => ?_⟩
  have hT : 1 ≤ (1 + |s.im|) ^ 3 := one_le_pow₀ (by linarith [abs_nonneg s.im])
  rcases le_or_gt |s.im| 1 with ht | ht
  · have := hC₂ s (by rw [mem_reProdIm]; exact ⟨⟨h1, h2⟩, abs_le.1 ht⟩)
    calc ‖Fb d s‖ ≤ |C₂| := this.trans (le_abs_self _)
      _ ≤ B * 1 := by rw [hB]; nlinarith [abs_nonneg B₀, abs_nonneg (cB (κ := κ))]
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (by positivity)
  · have hs1 : s ≠ 1 := by intro h; rw [h] at ht; simp at ht; linarith
    have hs1n : 1 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1); simp at this; linarith
    have hs3 : ‖s + 3‖ ≤ 5 * ‖s - 1‖ := by
      have := norm_add_le (s - 1) 4
      rw [show s - 1 + 4 = s + 3 by ring, show ‖(4 : ℂ)‖ = 4 by simp] at this
      linarith
    have hs6 := norm_add_three_le (s := s) (by linarith) (by linarith)
    have hE' : ‖Efun d s‖ ≤ |B₀| * ‖s + 3‖ ^ 4 :=
      (hB₀ s h1 h2).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hq : ‖Efun d s‖ / ‖s - 1‖ ≤ |B₀| * 1080 * (1 + |s.im|) ^ 3 := by
      rw [div_le_iff₀ (by linarith)]
      have h216 : ‖s + 3‖ ^ 3 ≤ 216 * (1 + |s.im|) ^ 3 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hs6 3; nlinarith
      calc ‖Efun d s‖ ≤ |B₀| * (‖s + 3‖ ^ 3 * ‖s + 3‖) := by rw [← pow_succ]; exact hE'
        _ ≤ |B₀| * ((216 * (1 + |s.im|) ^ 3) * (5 * ‖s - 1‖)) := by gcongr
        _ = |B₀| * 1080 * (1 + |s.im|) ^ 3 * ‖s - 1‖ := by ring
    rw [Fb_eq d hs1, norm_div]
    have hc : ‖(cB (κ := κ) : ℂ)‖ / ‖s - 1‖ ≤ |cB (κ := κ)| := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact div_le_self (abs_nonneg _) hs1n
    calc ‖Efun d s - cB (κ := κ)‖ / ‖s - 1‖ ≤ (‖Efun d s‖ + ‖(cB (κ := κ) : ℂ)‖) / ‖s - 1‖ := by
          gcongr; exact norm_sub_le _ _
      _ = ‖Efun d s‖ / ‖s - 1‖ + ‖(cB (κ := κ) : ℂ)‖ / ‖s - 1‖ := add_div _ _ _
      _ ≤ |B₀| * 1080 * (1 + |s.im|) ^ 3 + |cB (κ := κ)| := add_le_add hq hc
      _ ≤ B * (1 + |s.im|) ^ 3 := by
          rw [hB]; nlinarith [abs_nonneg C₂, abs_nonneg (cB (κ := κ))]

end B

/-- **Every `δ < 1/5`** from the Rankin–Selberg data and absolute convergence on `Re s > 1`. -/
theorem power_saving_fifth_of_RSData (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0)
    {κ : ℝ} (hκ : 0 ≤ κ) (d : RSData a κ)
    (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 5) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, a n - κ * rsConst * N| ≤ C * (N : ℝ) ^ (1 - δ) := by
  set aF : ArithmeticFunction ℝ := ⟨a, ha0⟩ with haF
  set b : ArithmeticFunction ℝ := chi * aF with hbdef
  have hb : ∀ n, 0 ≤ b n := by
    intro n; rw [hbdef, mul_apply]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (chi_nonneg _) (ha _)
  have hb0 : b 0 = 0 := by simp
  have hbconv : (fun n => ((b n : ℝ) : ℂ)) =
      LSeries.convolution (fun n => (chi n : ℂ)) (fun n => (a n : ℂ)) := by
    funext n; rw [hbdef, coe_mul_apply]; rfl
  have hb52 : LSeriesSummable (fun n => ((b n : ℝ) : ℂ)) ((5 / 2 : ℝ) : ℂ) := by
    rw [hbconv]
    exact (LSeriesSummable_chi (by simp; norm_num)).convolution
      (LSeriesSummable_of_one_lt habs (by simp; norm_num))
  have hsum := summable_of_LSeriesSummable hb hb0 hb52
  have hD : ∀ s : ℂ, s.re = 5 / 2 →
      LSeries (fun n => ((b n : ℝ) : ℂ)) s = Fb d s + (cB (κ := κ) : ℂ) / (s - 1) := by
    intro s hs
    have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 h1
    rw [hbconv, LSeries_convolution' (LSeriesSummable_chi (by rw [hs]; norm_num))
      (LSeriesSummable_of_one_lt habs (by rw [hs]; norm_num)), LSeries_chi (by rw [hs]; norm_num),
      Fb_eq d h1, Efun_eq_LSeries d (by rw [hs]; norm_num)]
    field_simp
    ring
  obtain ⟨B, hB⟩ := Fb_bound d habs
  have hR := rieszAsymp_of_continuation (fun n => b n) hb hb0 (K := 3) (c := 5 / 2) (σ₀ := -1)
    (σ₁ := 1 - 5 * δ) (c₀ := cB (κ := κ)) (B := B) (by norm_num) (by linarith) (by linarith)
    (by linarith) (by linarith) (by simpa using hsum) (Fb d) (differentiable_Fb d).differentiableOn
    hD (fun s h1 h2 => hB s (by linarith) h2)
  have hc0 : 0 ≤ cB (κ := κ) := by unfold cB rsConst; positivity
  have hK := riesz_kdiff (fun n => b n) hb hc0 4 (θ := 1 - (1 - 5 * δ)) (by linarith) (by linarith) hR
  obtain ⟨C, hC⟩ := partial_sum_of_riesz0 (fun n => b n) hK
  have hIcc : ∀ M : ℕ, Finset.Icc 1 M = Finset.Ioc 0 M := by
    intro M; ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  obtain ⟨C', hC'⟩ := mobius_transfer (A := fun N => ∑ n ∈ Finset.Ioc 0 N, a n)
    (B := fun M => ∑ n ∈ Finset.Ioc 0 M, b n) (c₀ := cB (κ := κ)) (C := C) (δ := δ) hδ0.le
    (by linarith) (fun N => sum_a_eq_mobius aF N) (by simp)
    (fun M hM => by
      have := hC M hM
      rw [hIcc] at this
      convert this using 3
      push_cast; ring)
  refine ⟨C', fun N hN => ?_⟩
  have := hC' N hN
  rw [hIcc]
  have e : cB (κ := κ) * (6 / π ^ 2) = κ * rsConst := by
    unfold cB; have := Real.pi_pos; field_simp
  rw [e] at this
  exact this

/-- **Rankin–Selberg with error `O(N^{1−δ})` for every `δ < 1/5`, unconditionally.** -/
theorem rankinSelberg_power_saving_sharp {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 5) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - δ) := by
  obtain ⟨C, hC⟩ := power_saving_fifth_of_RSData aTau aTau_nonneg aTau_zero
    petNormSq_pos.le (rsData_of_unfold rsUnfold) abscissa_aTau_le_one hδ0 hδ
  refine ⟨C, fun N hN => ?_⟩
  have h := hC N hN
  have e : petNormSq * rsConst = 3 / π * (4 * π) ^ 12 * petNormSq / (Nat.factorial 11 : ℝ) := by
    unfold rsConst
    have hπ := Real.pi_pos
    field_simp
  rw [e] at h
  exact h

/-- A concrete instance: error `O(N^{81/100})`. -/
theorem rankinSelberg_power_saving_81_100 :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (81 / 100 : ℝ) := by
  obtain ⟨C, hC⟩ := rankinSelberg_power_saving_sharp (δ := 19 / 100) (by norm_num) (by norm_num)
  exact ⟨C, fun N hN => by have := hC N hN; norm_num at this ⊢; exact this⟩

end RamanujanTau.RankinSharp

#print axioms RamanujanTau.RankinSharp.rankinSelberg_power_saving_sharp
#print axioms RamanujanTau.RankinSharp.rankinSelberg_power_saving_81_100
#print axioms RamanujanTau.RankinSharp.rankinSelberg_power_saving_lt_eighth
#print axioms RamanujanTau.RankinSharp.power_saving_fifth_of_RSData
