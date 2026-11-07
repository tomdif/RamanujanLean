/-
# Rankin–Selberg with error `O(N^{1−δ})` for every `δ < 1/3`

The convexity bound with edges `−ε`, `1+ε` (`ConvexEps`, made possible by the `Γ`-ratio
bounds of `GammaRatio`) gives, for `0 < σ₁ ≤ 1`,

    F_b(s) = ζ(2s)D(s) − c₀/(s−1) = O((1+|t|)^{2+2ε−2σ₁})   on  σ₁ ≤ Re s ≤ 5/2.

With `ε = σ₁/4` the exponent `r = 2 − 3σ₁/2` is `< 2`, so the Riesz mean of order `k = 2`
already converges absolutely on the shifted line (`rieszAsymp_of_continuation_rpow`, real
exponent). One second difference (`riesz_kdiff`, loss `k+1 = 3`) gives
`δ = (1 − σ₁)/3 → 1/3`. The Möbius step (`mobius_transfer`, needs `δ < 1/2`) is unchanged.

Compare: `RankinSharp` (integer exponent `3`, order `4`, `δ < 1/5`); Rankin–Selberg's
classical `δ = 2/5` needs the dual-sum (Landau) method on top of this.
-/
import RamanujanTau.Stirling.ConvexEps
import RamanujanTau.Stirling.RieszReal
import RamanujanTau.RankinSharpGeneral.Main

set_option autoImplicit false

namespace RamanujanTau.Stirling

open Complex Real Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open RamanujanTau.RankinSharp (chi chi_nonneg LSeriesSummable_chi LSeries_chi coe_mul_apply
  sum_a_eq_mobius mobius_transfer summable_of_LSeriesSummable norm_add_three_le
  LSeriesSummable_of_one_lt)
open ArithmeticFunction

section B

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ)
  (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

include habs in
/-- `‖F_b(s)‖ ≤ B (1+|t|)^{2+2ε−2σ₁}` on `σ₁ ≤ Re s ≤ 5/2`. -/
theorem Fb_bound_eps (hm : 1 ≤ m) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) {σ₁ : ℝ}
    (h0 : 0 ≤ σ₁) (h1 : σ₁ ≤ 1) :
    ∃ B : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 5 / 2 →
      ‖Fb d s‖ ≤ B * (1 + |s.im|) ^ (2 + 2 * ε - 2 * σ₁) := by
  set r : ℝ := 2 + 2 * ε - 2 * σ₁ with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hr3 : r ≤ 3 := by rw [hr]; linarith
  obtain ⟨B₀, hB₀⟩ := Efun_bound_eps d habs hm hε0 hε h0 h1
  have hK : IsCompact (Icc (0 : ℝ) (5 / 2) ×ℂ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn (differentiable_Fb d).continuous.continuousOn
  set B : ℝ := |B₀| * 1080 + |cB m κ| + |C₂| with hB
  refine ⟨B, fun s hsr1 hs2 => ?_⟩
  have hT : 1 ≤ (1 + |s.im|) ^ r := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hr0
  rcases le_or_gt |s.im| 1 with ht | ht
  · have := hC₂ s (by rw [mem_reProdIm]; exact ⟨⟨by linarith [hsr1], hs2⟩, abs_le.1 ht⟩)
    calc ‖Fb d s‖ ≤ |C₂| := this.trans (le_abs_self _)
      _ ≤ B * 1 := by rw [hB]; nlinarith [abs_nonneg B₀, abs_nonneg (cB m κ)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (by positivity)
  · have hs1 : s ≠ 1 := by intro h; rw [h] at ht; simp at ht; linarith
    have hs1n : 1 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1); simp at this; linarith
    have hs3 : ‖s + 3‖ ≤ 5 * ‖s - 1‖ := by
      have := norm_add_le (s - 1) 4
      rw [show s - 1 + 4 = s + 3 by ring, show ‖(4 : ℂ)‖ = 4 by simp] at this
      linarith
    have hs6 := norm_add_three_le (s := s) (by linarith) (by linarith)
    have h3pos : 0 < ‖s + 3‖ := lt_of_lt_of_le one_pos (one_le_norm_add_three (by linarith))
    have hE' : ‖Efun d s‖ ≤ |B₀| * (‖s + 3‖ ^ r * ‖s + 3‖) := by
      have := hB₀ s hsr1 hs2
      rw [show 3 + 2 * ε - 2 * σ₁ = r + 1 by rw [hr]; ring, Real.rpow_add_one h3pos.ne'] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hq : ‖Efun d s‖ / ‖s - 1‖ ≤ |B₀| * 1080 * (1 + |s.im|) ^ r := by
      rw [div_le_iff₀ (by linarith)]
      have h216 : ‖s + 3‖ ^ r ≤ 216 * (1 + |s.im|) ^ r := by
        have ht0 : 0 ≤ 1 + |s.im| := by positivity
        calc ‖s + 3‖ ^ r ≤ (6 * (1 + |s.im|)) ^ r := Real.rpow_le_rpow (norm_nonneg _) hs6 hr0
          _ = (6:ℝ) ^ r * (1 + |s.im|) ^ r := Real.mul_rpow (by norm_num) ht0
          _ ≤ (6:ℝ) ^ (3:ℝ) * (1 + |s.im|) ^ r := by
              exact mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 6 by norm_num) hr3) (by positivity)
          _ = 216 * (1 + |s.im|) ^ r := by norm_num
      calc ‖Efun d s‖ ≤ |B₀| * (‖s + 3‖ ^ r * ‖s + 3‖) := hE'
        _ ≤ |B₀| * ((216 * (1 + |s.im|) ^ r) * (5 * ‖s - 1‖)) := by gcongr
        _ = |B₀| * 1080 * (1 + |s.im|) ^ r * ‖s - 1‖ := by ring
    rw [Fb_eq d hs1, norm_div]
    have hc : ‖(cB m κ : ℂ)‖ / ‖s - 1‖ ≤ |cB m κ| := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact div_le_self (abs_nonneg _) hs1n
    calc ‖Efun d s - cB m κ‖ / ‖s - 1‖ ≤ (‖Efun d s‖ + ‖(cB m κ : ℂ)‖) / ‖s - 1‖ := by
          gcongr; exact norm_sub_le _ _
      _ = ‖Efun d s‖ / ‖s - 1‖ + ‖(cB m κ : ℂ)‖ / ‖s - 1‖ := add_div _ _ _
      _ ≤ |B₀| * 1080 * (1 + |s.im|) ^ r + |cB m κ| := add_le_add hq hc
      _ ≤ B * (1 + |s.im|) ^ r := by
          rw [hB]; nlinarith [abs_nonneg C₂, abs_nonneg (cB m κ), abs_nonneg B₀]

end B

/-- **Every `δ < 1/3`** from the weight-`(m+1)` Rankin–Selberg data and absolute convergence
on `Re s > 1`. -/
theorem power_saving_third_of_RSDataM {m : ℕ} (hm : 1 ≤ m) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ha0 : a 0 = 0) {κ : ℝ} (hκ : 0 ≤ κ) (d : RSDataM m a κ)
    (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 3) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, a n - κ * rsConstM m * N| ≤ C * (N : ℝ) ^ (1 - δ) := by
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
      LSeries (fun n => ((b n : ℝ) : ℂ)) s = Fb d s + (cB m κ : ℂ) / (s - 1) := by
    intro s hs
    have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 h1
    rw [hbconv, LSeries_convolution' (LSeriesSummable_chi (by rw [hs]; norm_num))
      (LSeriesSummable_of_one_lt habs (by rw [hs]; norm_num)), LSeries_chi (by rw [hs]; norm_num),
      Fb_eq d h1, Efun_eq_LSeries d (by rw [hs]; norm_num)]
    field_simp
    ring
  set σ₁ : ℝ := 1 - 3 * δ with hσ₁
  have hσ0 : 0 < σ₁ := by rw [hσ₁]; linarith
  have hσ1 : σ₁ ≤ 1 := by rw [hσ₁]; linarith
  obtain ⟨B, hB⟩ := Fb_bound_eps d habs hm (ε := σ₁ / 4) (by positivity) (by linarith)
    hσ0.le hσ1
  have hR := rieszAsymp_of_continuation_rpow (fun n => b n) hb hb0 2 (by norm_num)
    (r := 2 + 2 * (σ₁ / 4) - 2 * σ₁) (by push_cast; linarith) (c := 5 / 2) (σ₀ := -1)
    (σ₁ := σ₁) (c₀ := cB m κ) (B := B) (by norm_num) (by linarith) hσ0 (by linarith) hσ1
    (by simpa using hsum) (Fb d) (differentiable_Fb d).differentiableOn hD
    (fun s h1 h2 => hB s h1 h2)
  have hc0 : 0 ≤ cB m κ := by unfold cB rsConstM; positivity
  have hK := riesz_kdiff (fun n => b n) hb hc0 2 (θ := 1 - σ₁) (by linarith) (by linarith) hR
  obtain ⟨C, hC⟩ := partial_sum_of_riesz0 (fun n => b n) hK
  have hIcc : ∀ M : ℕ, Finset.Icc 1 M = Finset.Ioc 0 M := by
    intro M; ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  obtain ⟨C', hC'⟩ := mobius_transfer (A := fun N => ∑ n ∈ Finset.Ioc 0 N, a n)
    (B := fun M => ∑ n ∈ Finset.Ioc 0 M, b n) (c₀ := cB m κ) (C := C) (δ := δ) hδ0.le
    (by linarith) (fun N => sum_a_eq_mobius aF N) (by simp)
    (fun M hM => by
      have := hC M hM
      rw [hIcc] at this
      convert this using 3
      rw [hσ₁]; push_cast; ring)
  refine ⟨C', fun N hN => ?_⟩
  have := hC' N hN
  rw [hIcc]
  have e : cB m κ * (6 / π ^ 2) = κ * rsConstM m := by
    unfold cB; have := Real.pi_pos; field_simp
  rw [e] at this
  exact this

section RSFn

open RamanujanTau.RankinSelbergGeneral RamanujanTau.RankinSelbergGeneral.Horo HoroFn RSFn

variable [RSFn]

/-- **Every `δ < 1/3` for an abstract `RSFn` of weight `m + 1 ≥ 3`.** -/
theorem power_saving_third_RSFn (hm : 2 ≤ RSFn.m) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 3) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, aF n - petNormSq * rsConstM RSFn.m * N| ≤
        C * (N : ℝ) ^ (1 - δ) :=
  power_saving_third_of_RSDataM (by omega) aF aF_nonneg aF_zero petNormSq_nonneg rsDataG
    (abscissa_aF_le_one hm) hδ0 hδ

end RSFn

section Cusp

open Finset ModularForm BoylanWebb
open RamanujanTau.RankinSelberg hiding G G_smul continuous_G G_pos
open RamanujanTau.RankinSelbergGeneral
open UpperHalfPlane hiding I
open scoped MatrixGroups

variable {k : ℕ}

/-- **Rankin–Selberg with error `O(N^{1−δ})`, every `δ < 1/3`, for every level-one cusp
form** `f ∈ S_k(SL₂(ℤ))`: `|∑_{n≤N} |a_f(n)|²/n^{k−1} − c_f N| ≤ C N^{1−δ}`,
`c_f = (3/π)(4π)^k ‖f‖²/(k−1)!`. -/
theorem rankinSelberg_power_saving_third_general (f : CuspForm 𝒮ℒ (k : ℤ)) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 3) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) - rsConst f * N| ≤
        C * (N : ℝ) ^ (1 - δ) := by
  rcases lt_or_ge k 12 with hk | hk
  · obtain rfl := cuspForm_eq_zero_of_lt f hk
    refine ⟨0, fun N _ => ?_⟩
    have h1 : ∀ n, coeffSq (0 : CuspForm 𝒮ℒ (k : ℤ)) n = 0 := fun n => by
      simp [coeffSq, qExpansion_zero]
    have h2 : rsConst (0 : CuspForm 𝒮ℒ (k : ℤ)) = 0 := by
      simp [RankinSelbergGeneral.rsConst, petNormSqF, Gf]
    simp [h1, h2]
  · letI := rsFnCusp f (by omega)
    obtain ⟨C, hC⟩ := power_saving_third_RSFn (show 2 ≤ k - 1 by omega) hδ0 hδ
    refine ⟨C, fun N hN => ?_⟩
    have h : |∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) -
        petNormSqF f * rsConstM (k - 1) * N| ≤ C * (N : ℝ) ^ (1 - δ) := hC N hN
    rw [rsConst_eq f (by omega)] at h
    exact h

/-- The concrete exponent `67/100` (`δ = 33/100`), every level-one cusp form. -/
theorem rankinSelberg_power_saving_67_100_general (f : CuspForm 𝒮ℒ (k : ℤ)) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) - rsConst f * N| ≤
        C * (N : ℝ) ^ (67 / 100 : ℝ) := by
  obtain ⟨C, hC⟩ := rankinSelberg_power_saving_third_general f (δ := 33 / 100)
    (by norm_num) (by norm_num)
  exact ⟨C, fun N hN => by have := hC N hN; norm_num at this ⊢; exact this⟩

/-- **For `τ`: every `δ < 1/3`.**
`|∑_{n≤N} τ(n)²/n¹¹ − (3/π)(4π)¹²‖Δ‖²/11! · N| ≤ C N^{1−δ}`. -/
theorem rankinSelberg_power_saving_third {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 3) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - δ) := by
  obtain ⟨C, hC⟩ := rankinSelberg_power_saving_third_general (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) hδ0 hδ
  refine ⟨C, fun N hN => ?_⟩
  have h := hC N hN
  have e : ∀ n, coeffSq (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) n =
      ((tau n : ℝ)) ^ 2 := fun n => by
    unfold coeffSq
    have e := TauBound.qExpansion_discriminant_coeff_tau n
    erw [e, Complex.norm_intCast, sq_abs]
  simp only [e, RankinSelbergGeneral.rsConst, petNormSqF_discriminant] at h
  exact h

/-- For `τ`, the concrete exponent `67/100`. -/
theorem rankinSelberg_power_saving_67_100 :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (67 / 100 : ℝ) := by
  obtain ⟨C, hC⟩ := rankinSelberg_power_saving_third (δ := 33 / 100) (by norm_num) (by norm_num)
  exact ⟨C, fun N hN => by have := hC N hN; norm_num at this ⊢; exact this⟩

end Cusp

end RamanujanTau.Stirling

#print axioms RamanujanTau.Stirling.Fb_bound_eps
#print axioms RamanujanTau.Stirling.power_saving_third_of_RSDataM
#print axioms RamanujanTau.Stirling.power_saving_third_RSFn
#print axioms RamanujanTau.Stirling.rankinSelberg_power_saving_third_general
#print axioms RamanujanTau.Stirling.rankinSelberg_power_saving_67_100_general
#print axioms RamanujanTau.Stirling.rankinSelberg_power_saving_third
#print axioms RamanujanTau.Stirling.rankinSelberg_power_saving_67_100
