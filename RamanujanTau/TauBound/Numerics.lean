/-
# Discharging `PoincareFirstCoeffNeZero`

`1 + ∑_{c≥1} c^{-12} S(1,1;c) K(1,c;1) ≠ 0`:
* `c = 1`: `K(1,1;1) = ∑_j t_j ≥ 1.8` (partial sum `j < 20` with `π ∈ (3.141592, 3.141593)`, tail
  `≤ (4π²)^6 e^{4π²}/31!`);
* `c ≥ 2`: `|K(1,c;1)| ≤ e^{2π} π`, `|S(1,1;c)| ≤ c`, `∑_{c≥2} c^{-11} ≤ 2^{-11} + 3^{-9}π²/6`;
so the real part is `≥ 1 + 1.8 − 1.98 > 0`.
-/
import RamanujanTau.TauBound.KSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Complex MeasureTheory
open scoped Real Nat

lemma summable_tTerm : Summable tTerm :=
  Complex.summable_ofReal.mp hasSum_kInt_one.summable

lemma kInt_one_one : kInt 1 1 1 = ((∑' j, tTerm j : ℝ) : ℂ) := by
  rw [← hasSum_kInt_one.tsum_eq, Complex.ofReal_tsum]

/-- Lower bound for each term. -/
noncomputable def tLo (j : ℕ) : ℝ :=
  if Even j then (4 * (3.141592 : ℝ) ^ 2) ^ (6 + j) / ((j ! : ℝ) * ((11 + j) ! : ℝ))
  else -((4 * (3.141593 : ℝ) ^ 2) ^ (6 + j) / ((j ! : ℝ) * ((11 + j) ! : ℝ)))

lemma tTerm_ge (j : ℕ) : tLo j ≤ tTerm j := by
  have hlo : (4 * (3.141592 : ℝ) ^ 2) ≤ 4 * π ^ 2 := by
    have := Real.pi_gt_d6; nlinarith
  have hhi : 4 * π ^ 2 ≤ (4 * (3.141593 : ℝ) ^ 2) := by
    have := Real.pi_lt_d6; nlinarith [Real.pi_pos]
  have hD : (0 : ℝ) < (j ! : ℝ) * ((11 + j) ! : ℝ) := by positivity
  unfold tLo tTerm
  rw [show (-4 * π ^ 2) = -(4 * π ^ 2) by ring]
  split_ifs with h
  · have he : Even (6 + j) := by
      rcases h with ⟨r, hr⟩; exact ⟨r + 3, by omega⟩
    rw [he.neg_pow]
    gcongr
  · have ho : Odd (6 + j) := by
      rcases Nat.not_even_iff_odd.mp h with ⟨r, hr⟩; exact ⟨r + 3, by omega⟩
    rw [ho.neg_pow, neg_div, neg_le_neg_iff]
    gcongr

lemma partial_lo : (1.8254 : ℝ) ≤ ∑ j ∈ Finset.range 20, tLo j := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tLo]
  norm_num [Nat.factorial]

lemma exp_four_pi_sq_le : Real.exp (4 * π ^ 2) ≤ (2.7182818286 : ℝ) ^ 40 := by
  have h1 : 4 * π ^ 2 ≤ 40 := by have := Real.pi_lt_d6; nlinarith [Real.pi_pos]
  calc Real.exp (4 * π ^ 2) ≤ Real.exp 40 := Real.exp_le_exp.mpr h1
    _ = Real.exp 1 ^ 40 := by rw [Real.exp_one_pow]; norm_num
    _ ≤ _ := by gcongr; exact Real.exp_one_lt_d9.le

lemma tail_le : |∑' j, tTerm (j + 20)| ≤ (40 : ℝ) ^ 6 / ((31 ! : ℕ) : ℝ) * (2.7182818286 : ℝ) ^ 40 := by
  set s : ℝ := 4 * π ^ 2
  have hs0 : 0 ≤ s := by positivity
  have hs40 : s ≤ 40 := by have := Real.pi_lt_d6; nlinarith [Real.pi_pos]
  have hexp := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) s
  rw [← Real.exp_eq_exp_ℝ] at hexp
  set e : ℕ → ℝ := fun j => s ^ j / (j ! : ℝ)
  set F31 : ℝ := ((31 ! : ℕ) : ℝ) with hF31
  have hF31pos : 0 < F31 := by rw [hF31]; positivity
  have hb : ∀ j, |tTerm (j + 20)| ≤ s ^ 6 / F31 * e (j + 20) := by
    intro j
    have hf : F31 ≤ (((11 + (j + 20)) ! : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.factorial_le (by omega))
    have hjf : (0 : ℝ) < ((j + 20) ! : ℝ) := by positivity
    have habs : |tTerm (j + 20)| = s ^ (6 + (j + 20)) /
        (((j + 20) ! : ℝ) * (((11 + (j + 20)) ! : ℕ) : ℝ)) := by
      unfold tTerm
      rw [abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < ((j + 20) ! : ℝ) *
        (((11 + (j + 20)) ! : ℕ) : ℝ))]
      congr 2
      rw [abs_of_neg (by nlinarith [Real.pi_pos])]; ring
    rw [habs]
    calc s ^ (6 + (j + 20)) / (((j + 20) ! : ℝ) * (((11 + (j + 20)) ! : ℕ) : ℝ))
        ≤ s ^ (6 + (j + 20)) / (((j + 20) ! : ℝ) * F31) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hf hjf.le
      _ = s ^ 6 / F31 * e (j + 20) := by
          simp only [e]; rw [pow_add]; field_simp
  have hsum_e : Summable e := hexp.summable
  have hsh : Summable (fun j => e (j + 20)) := (summable_nat_add_iff 20).mpr hsum_e
  have hle1 : ∑' j, e (j + 20) ≤ Real.exp s := by
    rw [← hexp.tsum_eq, ← hsum_e.sum_add_tsum_nat_add 20]
    have : 0 ≤ ∑ i ∈ Finset.range 20, e i := Finset.sum_nonneg fun i _ => by positivity
    linarith
  have habs : Summable (fun j => ‖tTerm (j + 20)‖) :=
    ((summable_nat_add_iff 20).mpr summable_tTerm).norm
  have hb' : ∀ j, ‖tTerm (j + 20)‖ ≤ s ^ 6 / F31 * e (j + 20) := fun j => by
    rw [Real.norm_eq_abs]; exact hb j
  rw [← Real.norm_eq_abs]
  calc ‖∑' j, tTerm (j + 20)‖ ≤ ∑' j, ‖tTerm (j + 20)‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' j, s ^ 6 / F31 * e (j + 20) :=
        habs.tsum_le_tsum hb' (hsh.mul_left _)
    _ = s ^ 6 / F31 * ∑' j, e (j + 20) := tsum_mul_left
    _ ≤ (40 : ℝ) ^ 6 / F31 * (2.7182818286 : ℝ) ^ 40 := by
        gcongr
        exact hle1.trans exp_four_pi_sq_le

theorem kInt_one_one_ge : (1.8 : ℝ) ≤ ∑' j, tTerm j := by
  rw [← summable_tTerm.sum_add_tsum_nat_add 20]
  have h1 : (1.8254 : ℝ) ≤ ∑ j ∈ Finset.range 20, tTerm j :=
    partial_lo.trans (Finset.sum_le_sum fun j _ => tTerm_ge j)
  have h2 := tail_le
  have h3 : (40 : ℝ) ^ 6 / ((31 ! : ℕ) : ℝ) * (2.7182818286 : ℝ) ^ 40 ≤ 0.001 := by
    norm_num [Nat.factorial]
  have := (abs_le.mp (h2.trans h3)).1
  linarith

/-! ### The `c ≥ 2` tail -/

lemma norm_kInt_one_le (c : ℕ) (hc : c ≠ 0) : ‖kInt 1 c 1‖ ≤ Real.exp (2 * π) * π := by
  have hJ : ∫ x : ℝ, Real.exp (2 * π) * (1 + x ^ 2)⁻¹ = Real.exp (2 * π) * π := by
    rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [kInt_eq, ← hJ]
  refine norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
    (Filter.Eventually.of_forall fun x => ?_)
  unfold kIntegrand
  rw [norm_mul, norm_mul, norm_w_zpow one_pos]
  have him : (0 : ℝ) ≤ (-1 / ((c : ℂ) ^ 2 * ((x : ℂ) + ((1 : ℝ) : ℂ) * I))).im := by
    have := im_neg_inv (x := x) (y := 1) (c : ℝ) (by exact_mod_cast hc) one_pos
    push_cast at this ⊢
    rw [this]; positivity
  have h1 := norm_ee_le_one him
  have h2 : ‖ee (-((1 : ℕ) : ℂ) * ((x : ℂ) + ((1 : ℝ) : ℂ) * I))‖ = Real.exp (2 * π) := by
    rw [norm_ee]; congr 1; simp
  push_cast at h1 h2 him ⊢
  simp only [one_mul, one_pow] at h1 h2 ⊢
  rw [h2]
  have h3 : (x ^ 2 + 1) ^ (-6 : ℝ) ≤ (1 + x ^ 2)⁻¹ := by
    have hpos : (1 : ℝ) ≤ x ^ 2 + 1 := by nlinarith [sq_nonneg x]
    rw [Real.rpow_neg (by positivity), add_comm (x ^ 2)]
    gcongr
    calc (1 + x ^ 2) = (1 + x ^ 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 + x ^ 2) ^ (6 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hA : 0 ≤ (x ^ 2 + 1) ^ (-6 : ℝ) := by positivity
  have hE : 0 < Real.exp (2 * π) := Real.exp_pos _
  calc (x ^ 2 + 1) ^ (-6 : ℝ) * ‖ee (-1 / ((c : ℂ) ^ 2 * ((x : ℂ) + I)))‖ * Real.exp (2 * π)
      ≤ (x ^ 2 + 1) ^ (-6 : ℝ) * 1 * Real.exp (2 * π) := by gcongr
    _ ≤ (1 + x ^ 2)⁻¹ * 1 * Real.exp (2 * π) := by gcongr
    _ = Real.exp (2 * π) * (1 + x ^ 2)⁻¹ := by ring

lemma exp_two_pi_mul_pi_le : Real.exp (2 * π) * π ≤ 3450 := by
  have hp := Real.pi_lt_d6
  have h1 : Real.exp (2 * π) ≤ (2.7182818286 : ℝ) ^ 7 := by
    calc Real.exp (2 * π) ≤ Real.exp 7 := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp 1 ^ 7 := by rw [Real.exp_one_pow]; norm_num
      _ ≤ _ := by gcongr; exact Real.exp_one_lt_d9.le
  calc Real.exp (2 * π) * π ≤ (2.7182818286 : ℝ) ^ 7 * 3.141593 := by
        gcongr
    _ ≤ 3450 := by norm_num

/-- The majorant `g(c) = 2^{-11}[c=0] + 3^{-9}/(c+1)²` of `(c+2)^{-11}`. -/
lemma inv_pow_le_g (c : ℕ) :
    (((c + 2 : ℕ) : ℝ) ^ 11)⁻¹ ≤ (if c = 0 then (2 : ℝ)⁻¹ ^ 11 else 0) +
      (3 : ℝ)⁻¹ ^ 9 * (1 / ((c + 1 : ℕ) : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos c with h | h
  · subst h; norm_num
  · rw [if_neg h.ne', zero_add]
    have h1 : (1 : ℝ) ≤ c := by exact_mod_cast h
    have hc : (3 : ℝ) ≤ ((c + 2 : ℕ) : ℝ) := by push_cast; linarith
    have hc1 : (0 : ℝ) < ((c + 1 : ℕ) : ℝ) := by positivity
    have hle : ((c + 1 : ℕ) : ℝ) ≤ ((c + 2 : ℕ) : ℝ) := by push_cast; linarith
    rw [inv_pow, ← one_div, ← one_div, div_mul_div_comm, one_mul]
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
    calc (3 : ℝ) ^ 9 * ((c + 1 : ℕ) : ℝ) ^ 2 ≤ ((c + 2 : ℕ) : ℝ) ^ 9 * ((c + 2 : ℕ) : ℝ) ^ 2 := by
          gcongr
      _ = _ := by ring

lemma hasSum_g : HasSum (fun c : ℕ => (if c = 0 then (2 : ℝ)⁻¹ ^ 11 else 0) +
      (3 : ℝ)⁻¹ ^ 9 * (1 / ((c + 1 : ℕ) : ℝ) ^ 2)) ((2 : ℝ)⁻¹ ^ 11 + (3 : ℝ)⁻¹ ^ 9 * (π ^ 2 / 6)) := by
  refine (hasSum_ite_eq 0 _).add (HasSum.mul_left _ ?_)
  have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simp only [Finset.sum_range_one, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero, sub_zero] at this
  simpa using this

theorem poincareFirstCoeffNeZero : PoincareFirstCoeffNeZero := by
  unfold PoincareFirstCoeffNeZero
  have hs := summable_firstCoeff
  rw [hs.tsum_eq_zero_add]
  -- the `c = 1` term
  have hS1 : kloosterman 1 1 1 = 1 := by
    have hv : ∀ x : ZMod 1, x.val = 0 := fun x => Nat.lt_one_iff.mp (ZMod.val_lt x)
    simp [kloosterman, ee, hv]
  have h0 : (((0 + 1 : ℕ) : ℂ)) ^ (-12 : ℤ) * kloosterman 1 1 (0 + 1) * kInt 1 (0 + 1) 1 =
      ((∑' j, tTerm j : ℝ) : ℂ) := by
    simp only [zero_add, Nat.cast_one, one_zpow, one_mul, hS1, kInt_one_one]
  rw [h0]
  set R := ∑' c : ℕ, ((c + 1 + 1 : ℕ) : ℂ) ^ (-12 : ℤ) * kloosterman 1 1 (c + 1 + 1) *
    kInt 1 (c + 1 + 1) 1
  -- bound the remainder
  set g : ℕ → ℝ := fun c => (if c = 0 then (2 : ℝ)⁻¹ ^ 11 else 0) +
      (3 : ℝ)⁻¹ ^ 9 * (1 / ((c + 1 : ℕ) : ℝ) ^ 2)
  have hterm : ∀ c : ℕ, ‖((c + 1 + 1 : ℕ) : ℂ) ^ (-12 : ℤ) * kloosterman 1 1 (c + 1 + 1) *
      kInt 1 (c + 1 + 1) 1‖ ≤ 3450 * g c := by
    intro c
    have hC : (0 : ℝ) < ((c + 2 : ℕ) : ℝ) := by positivity
    rw [norm_mul, norm_mul, norm_zpow, Complex.norm_natCast]
    have h2 := norm_kloosterman_le 1 1 (c + 1 + 1)
    have h3 := (norm_kInt_one_le (c + 1 + 1) (by omega)).trans exp_two_pi_mul_pi_le
    have hg := inv_pow_le_g c
    calc ((c + 1 + 1 : ℕ) : ℝ) ^ (-12 : ℤ) * ‖kloosterman 1 1 (c + 1 + 1)‖ *
          ‖kInt 1 (c + 1 + 1) 1‖
        ≤ ((c + 2 : ℕ) : ℝ) ^ (-12 : ℤ) * ((c + 2 : ℕ) : ℝ) * 3450 := by gcongr
      _ = 3450 * (((c + 2 : ℕ) : ℝ) ^ 11)⁻¹ := by
          rw [zpow_neg, show (12 : ℤ) = ((11 + 1 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_succ]
          field_simp
      _ ≤ 3450 * g c := by gcongr
  have hRle : ‖R‖ ≤ 3450 * ((2 : ℝ)⁻¹ ^ 11 + (3 : ℝ)⁻¹ ^ 9 * (π ^ 2 / 6)) := by
    have hsR : Summable (fun c : ℕ => ((c + 1 + 1 : ℕ) : ℂ) ^ (-12 : ℤ) *
        kloosterman 1 1 (c + 1 + 1) * kInt 1 (c + 1 + 1) 1) :=
      (summable_nat_add_iff 1).mpr hs
    exact hsR.hasSum.norm_le_of_bounded (hasSum_g.mul_left 3450) hterm
  have hnum : 3450 * ((2 : ℝ)⁻¹ ^ 11 + (3 : ℝ)⁻¹ ^ 9 * (π ^ 2 / 6)) ≤ 1.99 := by
    have := Real.pi_lt_d6
    have hp2 : π ^ 2 ≤ 3.141593 ^ 2 := by nlinarith [Real.pi_pos]
    nlinarith
  have hT := kInt_one_one_ge
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at hre
  have hRre : |R.re| ≤ ‖R‖ := Complex.abs_re_le_norm R
  have := abs_le.mp (hRre.trans (hRle.trans hnum))
  linarith [this.1]

end RamanujanTau.TauBound
