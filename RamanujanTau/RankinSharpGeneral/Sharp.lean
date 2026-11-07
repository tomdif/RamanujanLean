/-
# Every exponent `δ < 1/5` for the weight-`(m+1)` Rankin–Selberg mean square

Weight-general copy of `RankinSharp/Sharp.lean`.

* `power_saving_fifth_of_RSDataM` (`m ≥ 1`): from `RSDataM m a κ`, `a ≥ 0`, `a 0 = 0` and
  absolute convergence of `D` on `Re s > 1`,
  `|∑_{n≤N} aₙ − κ·rsConstM m·N| ≤ C N^{1−δ}` for every `0 < δ < 1/5`.
* `abscissa_le_one_of_bound`: any bound `∑_{n≤N} aₙ = cN + O(N^θ)`, `θ ≤ 1`, `a ≥ 0` gives
  abscissa of absolute convergence `≤ 1` (here fed by the `1/84` theorem of `RankinErrorGeneral`).
* `power_saving_sharp_RSFn` (`m ≥ 2`): the same for every `RSFn`.

The square twist `b = χ * a` and the Möbius step are generic (`RankinSharp.Squares`,
`RankinSharp.Mobius`), and so are the Perron/Riesz lemmas of `RankinError`.
-/
import RamanujanTau.RankinSharpGeneral.Convex
import RamanujanTau.RankinSharp.Sharp
import RamanujanTau.RankinErrorGeneral.UnfoldProofG

set_option autoImplicit false

namespace RamanujanTau.RankinSharpGeneral

open Complex Real Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral
open RamanujanTau.RankinSharp (chi chi_nonneg LSeriesSummable_chi LSeries_chi coe_mul_apply
  sum_a_eq_mobius mobius_transfer summable_of_LSeriesSummable norm_add_three_le
  LSeriesSummable_of_one_lt)
open ArithmeticFunction

section B

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ)

/-- The residue `E(1) = κ γₘ(1)⁻¹ = κ · rsConstM m · ζ(2)`. -/
noncomputable def cB (m : ℕ) (κ : ℝ) : ℝ := κ * rsConstM m * (π ^ 2 / 6)

lemma Efun_one : Efun d 1 = (cB m κ : ℂ) := by
  have hz : riemannZeta 2 ≠ 0 := by
    rw [riemannZeta_two]; exact div_ne_zero (pow_ne_zero 2 pi_ne_zero') (by norm_num)
  have hinv : invGamM m 1 = (rsConstM m : ℂ) * riemannZeta 2 := by
    have h := gfunM_one m
    unfold gfunM at h
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

lemma Fb_eq {s : ℂ} (h1 : s ≠ 1) : Fb d s = (Efun d s - cB m κ) / (s - 1) := by
  unfold Fb
  rw [dslope_of_ne _ h1, slope_def_field, Efun_one]

variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))
  (hm : 1 ≤ m)

include habs hm in
/-- `‖F_b(s)‖ ≤ B (1+|t|)³` on `0 ≤ Re s ≤ 5/2`. -/
theorem Fb_bound : ∃ B : ℝ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 5 / 2 →
    ‖Fb d s‖ ≤ B * (1 + |s.im|) ^ 3 := by
  obtain ⟨B₀, hB₀⟩ := Efun_bound d habs hm (σL := 0) (n := 3) (by norm_num) le_rfl (by norm_num)
  have hK : IsCompact (Icc (0 : ℝ) (5 / 2) ×ℂ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn (differentiable_Fb d).continuous.continuousOn
  set B : ℝ := |B₀| * 1080 + |cB m κ| + |C₂| with hB
  refine ⟨B, fun s h1 h2 => ?_⟩
  have hT : 1 ≤ (1 + |s.im|) ^ 3 := one_le_pow₀ (by linarith [abs_nonneg s.im])
  rcases le_or_gt |s.im| 1 with ht | ht
  · have := hC₂ s (by rw [mem_reProdIm]; exact ⟨⟨h1, h2⟩, abs_le.1 ht⟩)
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
    have hc : ‖(cB m κ : ℂ)‖ / ‖s - 1‖ ≤ |cB m κ| := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact div_le_self (abs_nonneg _) hs1n
    calc ‖Efun d s - cB m κ‖ / ‖s - 1‖ ≤ (‖Efun d s‖ + ‖(cB m κ : ℂ)‖) / ‖s - 1‖ := by
          gcongr; exact norm_sub_le _ _
      _ = ‖Efun d s‖ / ‖s - 1‖ + ‖(cB m κ : ℂ)‖ / ‖s - 1‖ := add_div _ _ _
      _ ≤ |B₀| * 1080 * (1 + |s.im|) ^ 3 + |cB m κ| := add_le_add hq hc
      _ ≤ B * (1 + |s.im|) ^ 3 := by
          rw [hB]; nlinarith [abs_nonneg C₂, abs_nonneg (cB m κ)]

end B

/-- **Every `δ < 1/5`** from the weight-`(m+1)` Rankin–Selberg data and absolute convergence
on `Re s > 1`. -/
theorem power_saving_fifth_of_RSDataM {m : ℕ} (hm : 1 ≤ m) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ha0 : a 0 = 0) {κ : ℝ} (hκ : 0 ≤ κ) (d : RSDataM m a κ)
    (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 5) :
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
  obtain ⟨B, hB⟩ := Fb_bound d habs hm
  have hR := rieszAsymp_of_continuation (fun n => b n) hb hb0 (K := 3) (c := 5 / 2) (σ₀ := -1)
    (σ₁ := 1 - 5 * δ) (c₀ := cB m κ) (B := B) (by norm_num) (by linarith) (by linarith)
    (by linarith) (by linarith) (by simpa using hsum) (Fb d) (differentiable_Fb d).differentiableOn
    hD (fun s h1 h2 => hB s (by linarith) h2)
  have hc0 : 0 ≤ cB m κ := by unfold cB rsConstM; positivity
  have hK := riesz_kdiff (fun n => b n) hb hc0 4 (θ := 1 - (1 - 5 * δ)) (by linarith) (by linarith) hR
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
      push_cast; ring)
  refine ⟨C', fun N hN => ?_⟩
  have := hC' N hN
  rw [hIcc]
  have e : cB m κ * (6 / π ^ 2) = κ * rsConstM m := by
    unfold cB; have := Real.pi_pos; field_simp
  rw [e] at this
  exact this

/-- Absolute convergence on `Re s > 1` from any linear bound for the partial sums. -/
lemma abscissa_le_one_of_bound {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {c C θ : ℝ} (hθ : θ ≤ 1)
    (h : ∀ N : ℕ, 1 ≤ N → |∑ n ∈ Finset.Icc 1 N, a n - c * N| ≤ C * (N : ℝ) ^ θ) :
    LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal) := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, a k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine IsBigO.of_bound (|c| + |C|) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have h' := h N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hpow : (N : ℝ) ^ θ ≤ N := by
      calc (N : ℝ) ^ θ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hθ
        _ = N := Real.rpow_one _
    have hS0 : 0 ≤ ∑ k ∈ Finset.Icc 1 N, a k := Finset.sum_nonneg fun k _ => ha k
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hS0, Real.rpow_one,
      abs_of_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
    have h1 := (abs_le.1 h').2
    have h2 : C * (N : ℝ) ^ θ ≤ |C| * N :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hpow (abs_nonneg C))
    have h3 : c * N ≤ |c| * N := mul_le_mul_of_nonneg_right (le_abs_self c) (Nat.cast_nonneg N)
    linarith
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  exact LSeriesSummable_of_sum_norm_bigO_and_nonneg hO ha (by norm_num) (by simpa using hy)

section RSFn

open RamanujanTau.RankinSelbergGeneral RamanujanTau.RankinSelbergGeneral.Horo HoroFn RSFn

variable [RSFn]

/-- `∑ (cₙ/n^m) n^{−s}` converges absolutely on `Re s > 1` (from the `1/84` theorem). -/
lemma abscissa_aF_le_one (hm : 2 ≤ RSFn.m) :
    LSeries.abscissaOfAbsConv (fun n => (aF n : ℂ)) ≤ ((1 : ℝ) : EReal) := by
  obtain ⟨C, hC⟩ := power_saving_RSFn hm
  exact abscissa_le_one_of_bound aF_nonneg (by norm_num) hC

/-- **Every `δ < 1/5` for an abstract `RSFn` of weight `m + 1 ≥ 3`.** -/
theorem power_saving_sharp_RSFn (hm : 2 ≤ RSFn.m) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 5) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, aF n - petNormSq * rsConstM RSFn.m * N| ≤
        C * (N : ℝ) ^ (1 - δ) :=
  power_saving_fifth_of_RSDataM (by omega) aF aF_nonneg aF_zero petNormSq_nonneg rsDataG
    (abscissa_aF_le_one hm) hδ0 hδ

end RSFn

end RamanujanTau.RankinSharpGeneral

#print axioms RamanujanTau.RankinSharpGeneral.power_saving_fifth_of_RSDataM
#print axioms RamanujanTau.RankinSharpGeneral.power_saving_sharp_RSFn
