/-
# `RankinOmega`: the Rankin–Selberg error term is `Ω(x^{3/8})`

For `τ` (and every nonzero level-one cusp form `f`, `aₙ = |a_f(n)|²/n^{k−1}`) and **every** real
constant `c` (in particular Rankin's `c = (3/π)(4π)¹²‖Δ‖²/11!` of `RankinExact.rankinSelberg_exact`):

    |∑_{n≤x} τ(n)²/n¹¹ − c x| ≥ c' x^{3/8}     for arbitrarily large x   (some c' > 0),

and the same along the integers `N`. Together with `RankinExact.rankinSelberg_exact` (`≪ N^{3/5}`)
the true order of the Rankin–Selberg error has exponent in `[3/8, 3/5]`. `3/8 = (d−1)/(2d)` for the
degree-4 function `ζ(s)L(sym²Δ, s)`.

Method (see `docs/RANKIN_OMEGA.md`): Landau–Mellin–Plancherel as in `TauOmegaPartial`, with three
new inputs forced by the denominator `ζ(2s)` of `D(s) = ζ(s)L(sym²,s)/ζ(2s)` and by the reflected
line `Re w = 5/8 − δ` lying inside the critical strip:
`zeta_mean_sq` (uniform `∫_T^{2T}|ζ(u−it)|² ≪ T`, `3/4 ≤ u ≤ 1`), `Zf_first_moment` (uniform first
moment of `ζ(2w)D(w)` on `9/16 ≤ Re w ≤ 5/8`, via convexity), and an optimized AM–GM in `block_lower`.
-/
import RamanujanTau.RankinOmega.Omega
import RamanujanTau.RankinExact.Main

set_option autoImplicit false

namespace RamanujanTau.RankinOmega

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral

section Data

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ)
variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

lemma exists_first (h : ∃ n, 0 < n ∧ a n ≠ 0) :
    ∃ n0 : ℕ, 1 ≤ n0 ∧ (∀ n, 0 < n → n < n0 → a n = 0) ∧ a n0 ≠ 0 := by
  classical
  refine ⟨Nat.find h, (Nat.find_spec h).1, fun n hn hlt => ?_, (Nat.find_spec h).2⟩
  have := Nat.find_min h hlt
  push Not at this
  exact this hn

include d habs in
/-- **Ω-theorem for Rankin–Selberg data, real variable.** -/
theorem rs_omega (hm : 1 ≤ m) (hne : ∃ n, 0 < n ∧ a n ≠ 0) (c : ℝ) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      c' * x ^ ((3 : ℝ) / 8) ≤ |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - c * x| := by
  obtain ⟨n0, hn0, hlow, ha0⟩ := exists_first hne
  obtain ⟨c', hc', h⟩ := rs_omega_core d habs hm hn0 hlow ha0 c
  refine ⟨c', hc', fun X => ?_⟩
  obtain ⟨x, hx, hxb⟩ := h (max X 2)
  refine ⟨x, le_trans (le_max_left _ _) hx, ?_⟩
  have hx1 : 1 < x := by linarith [le_max_right X 2]
  rw [Rf_of_one_lt c hx1, Asum] at hxb
  have e : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (a n : ℂ) - ((c * x : ℝ) : ℂ) =
      ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - c * x : ℝ) : ℂ) := by push_cast; ring
  rwa [e, Complex.norm_real, Real.norm_eq_abs] at hxb

include d habs in
/-- **Ω-theorem for Rankin–Selberg data, along the integers.** -/
theorem rs_omega_nat (hm : 1 ≤ m) (hne : ∃ n, 0 < n ∧ a n ≠ 0) (c : ℝ) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ N0 : ℕ, ∃ N : ℕ, N0 ≤ N ∧
      c' * (N : ℝ) ^ ((3 : ℝ) / 8) ≤ |∑ n ∈ Finset.Icc 1 N, a n - c * N| := by
  obtain ⟨c', hc', h⟩ := rs_omega d habs hm hne c
  refine ⟨c' / 2, by positivity, fun N0 => ?_⟩
  set q : ℝ := 2 * |c| / c' + 1 with hq
  have hq1 : 1 ≤ q := by rw [hq]; have : 0 ≤ 2 * |c| / c' := by positivity
                         linarith
  obtain ⟨x, hx, hxb⟩ := h (max (N0 : ℝ) (q ^ 3))
  have hxN0 : (N0 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hxq : q ^ 3 ≤ x := le_trans (le_max_right _ _) hx
  have hq3 : 1 ≤ q ^ 3 := one_le_pow₀ hq1
  have hx0 : 0 ≤ x := by linarith
  refine ⟨⌊x⌋₊, Nat.le_floor hxN0, ?_⟩
  set N : ℕ := ⌊x⌋₊ with hN
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x - N < 1 := by have := Nat.lt_floor_add_one x; linarith
  -- `x^{3/8} ≥ q ≥ 2|c|/c'`
  have hxq' : q ≤ x ^ ((3 : ℝ) / 8) := by
    have h1 : q ≤ (q ^ 3) ^ ((3 : ℝ) / 8) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      calc q = q ^ (1 : ℝ) := (Real.rpow_one q).symm
        _ ≤ q ^ (((3 : ℕ) : ℝ) * (3 / 8)) := Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
    exact h1.trans (Real.rpow_le_rpow (by positivity) hxq (by norm_num))
  have hc2 : 2 * |c| ≤ c' * x ^ ((3 : ℝ) / 8) := by
    have h3 : 2 * |c| / c' ≤ x ^ ((3 : ℝ) / 8) := by linarith
    calc 2 * |c| = (2 * |c| / c') * c' := by field_simp
      _ ≤ x ^ ((3 : ℝ) / 8) * c' := by gcongr
      _ = c' * x ^ ((3 : ℝ) / 8) := by ring
  have hdiff : |∑ n ∈ Finset.Icc 1 N, a n - c * x| ≤ |∑ n ∈ Finset.Icc 1 N, a n - c * N| + |c| := by
    have : ∑ n ∈ Finset.Icc 1 N, a n - c * x =
        (∑ n ∈ Finset.Icc 1 N, a n - c * N) - c * (x - N) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - N)]
    have := abs_nonneg c
    nlinarith
  have hNpow : (N : ℝ) ^ ((3 : ℝ) / 8) ≤ x ^ ((3 : ℝ) / 8) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hNx (by norm_num)
  calc c' / 2 * (N : ℝ) ^ ((3 : ℝ) / 8) ≤ c' / 2 * x ^ ((3 : ℝ) / 8) := by gcongr
    _ ≤ c' * x ^ ((3 : ℝ) / 8) - |c| := by linarith
    _ ≤ _ := by linarith

end Data

section Cusp

open RamanujanTau.RankinSelbergGeneral RamanujanTau.RankinSelbergGeneral.Horo HoroFn RSFn
open ModularForm
open scoped MatrixGroups

variable {k : ℕ}

/-- **Ω-theorem for every nonzero level-one cusp form** (every real `c`):
`|∑_{n≤x} |a_f(n)|²/n^{k−1} − c x| ≥ c' x^{3/8}` for arbitrarily large `x`. -/
theorem cuspForm_rankin_omega (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (c : ℝ) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      c' * x ^ ((3 : ℝ) / 8) ≤
        |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coeffSq f n / (n : ℝ) ^ (k - 1) - c * x| := by
  have hk : 12 ≤ k := by
    by_contra h; exact hf (cuspForm_eq_zero_of_lt f (by omega))
  letI := rsFnCusp f (by omega)
  have hm : 2 ≤ RSFn.m := show 2 ≤ k - 1 by omega
  obtain ⟨n, hn1, hn⟩ := exists_coeff_ne_zero f hf (by omega)
  have hne : ∃ n, 0 < n ∧ aF n ≠ 0 := by
    refine ⟨n, hn1, ?_⟩
    show coeffSq f n / (n : ℝ) ^ (k - 1) ≠ 0
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    exact div_ne_zero hn (by positivity)
  exact rs_omega rsDataG (abscissa_aF_le_one hm) (by omega) hne c

/-- The same along the integers. -/
theorem cuspForm_rankin_omega_nat (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (c : ℝ) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ N0 : ℕ, ∃ N : ℕ, N0 ≤ N ∧
      c' * (N : ℝ) ^ ((3 : ℝ) / 8) ≤
        |∑ n ∈ Finset.Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) - c * N| := by
  have hk : 12 ≤ k := by
    by_contra h; exact hf (cuspForm_eq_zero_of_lt f (by omega))
  letI := rsFnCusp f (by omega)
  have hm : 2 ≤ RSFn.m := show 2 ≤ k - 1 by omega
  obtain ⟨n, hn1, hn⟩ := exists_coeff_ne_zero f hf (by omega)
  have hne : ∃ n, 0 < n ∧ aF n ≠ 0 := by
    refine ⟨n, hn1, ?_⟩
    show coeffSq f n / (n : ℝ) ^ (k - 1) ≠ 0
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    exact div_ne_zero hn (by positivity)
  exact rs_omega_nat rsDataG (abscissa_aF_le_one hm) (by omega) hne c

lemma coeffSq_discriminant (n : ℕ) :
    coeffSq (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) n =
      ((tau n : ℝ)) ^ 2 := by
  unfold coeffSq
  have e := TauBound.qExpansion_discriminant_coeff_tau n
  erw [e, Complex.norm_intCast, sq_abs]

lemma discriminant_ne_zero' : (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) ≠ 0 := by
  intro h
  have := congrArg (fun g : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ) => g UpperHalfPlane.I) h
  exact ModularForm.discriminant_ne_zero UpperHalfPlane.I (by simpa using this)

end Cusp

/-- **Headline (τ, real variable, any constant `c`).** -/
theorem tau_rankin_omega (c : ℝ) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      c' * x ^ ((3 : ℝ) / 8) ≤
        |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 - c * x| := by
  obtain ⟨c', hc', h⟩ := cuspForm_rankin_omega (k := 12) _ discriminant_ne_zero' c
  refine ⟨c', hc', fun X => ?_⟩
  obtain ⟨x, hx, hb⟩ := h X
  refine ⟨x, hx, ?_⟩
  simp only [coeffSq_discriminant] at hb
  exact hb

/-- **Headline (τ, integers, any constant `c`).** -/
theorem tau_rankin_omega_nat (c : ℝ) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ N0 : ℕ, ∃ N : ℕ, N0 ≤ N ∧
      c' * (N : ℝ) ^ ((3 : ℝ) / 8) ≤
        |∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 - c * N| := by
  obtain ⟨c', hc', h⟩ := cuspForm_rankin_omega_nat (k := 12) _ discriminant_ne_zero' c
  refine ⟨c', hc', fun N0 => ?_⟩
  obtain ⟨N, hN, hb⟩ := h N0
  refine ⟨N, hN, ?_⟩
  simp only [coeffSq_discriminant] at hb
  exact hb

/-- **Headline with Rankin's constant**: `R(N) = ∑_{n≤N} τ(n)²/n¹¹ − (3/π)(4π)¹²‖Δ‖²/11!·N`
(the error term of `RankinExact.rankinSelberg_exact`, `|R(N)| ≤ C N^{3/5}`) is `Ω(N^{3/8})`. -/
theorem rankinSelberg_error_omega :
    ∃ c' : ℝ, 0 < c' ∧ ∀ N0 : ℕ, ∃ N : ℕ, N0 ≤ N ∧
      c' * (N : ℝ) ^ ((3 : ℝ) / 8) ≤
        |∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / Real.pi * (4 * Real.pi) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| :=
  tau_rankin_omega_nat _

/-- `R(N) ≠ o(N^{3/8})`. -/
theorem rankinSelberg_error_not_isLittleO :
    ¬ (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / Real.pi * (4 * Real.pi) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N)
        =o[atTop] (fun N : ℕ => (N : ℝ) ^ ((3 : ℝ) / 8)) := by
  intro ho
  obtain ⟨c', hc', h⟩ := rankinSelberg_error_omega
  have := ho.def (show 0 < c' / 2 by positivity)
  rw [eventually_atTop] at this
  obtain ⟨N1, hN1⟩ := this
  obtain ⟨N, hN, hb⟩ := h N1
  have h1 := hN1 N hN
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)] at h1
  have hp : 0 < (N : ℝ) ^ ((3 : ℝ) / 8) ∨ (N : ℝ) ^ ((3 : ℝ) / 8) = 0 := by
    rcases (Real.rpow_nonneg (Nat.cast_nonneg N) ((3 : ℝ) / 8)).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  rcases hp with hp | hp
  · nlinarith
  · -- `N = 0`: then the error term is `0`, but `R(0)` vanishes too; use `N1` large instead
    have hN0 : (N : ℝ) = 0 := by
      by_contra hne
      have : (0 : ℝ) < N := lt_of_le_of_ne (Nat.cast_nonneg N) (Ne.symm hne)
      have := Real.rpow_pos_of_pos this ((3 : ℝ) / 8)
      linarith
    obtain ⟨N', hN', hb'⟩ := h (max N1 1)
    have h1' := hN1 N' (le_trans (le_max_left _ _) hN')
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)] at h1'
    have hN'1 : (1 : ℝ) ≤ N' := by exact_mod_cast le_trans (le_max_right _ _) hN'
    have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < N') ((3 : ℝ) / 8)
    nlinarith

end RamanujanTau.RankinOmega

-- headlines
#print axioms RamanujanTau.RankinOmega.rankinSelberg_error_omega
#print axioms RamanujanTau.RankinOmega.rankinSelberg_error_not_isLittleO
#print axioms RamanujanTau.RankinOmega.tau_rankin_omega
#print axioms RamanujanTau.RankinOmega.tau_rankin_omega_nat
#print axioms RamanujanTau.RankinOmega.cuspForm_rankin_omega
#print axioms RamanujanTau.RankinOmega.cuspForm_rankin_omega_nat
#print axioms RamanujanTau.RankinOmega.rs_omega
#print axioms RamanujanTau.RankinOmega.rs_omega_nat
#print axioms RamanujanTau.RankinOmega.rs_omega_core
-- the new analytic inputs
#print axioms RamanujanTau.RankinOmega.zeta_formula
#print axioms RamanujanTau.RankinOmega.norm_zeta_sub_le
#print axioms RamanujanTau.RankinOmega.zeta_mean_sq
#print axioms RamanujanTau.RankinOmega.gamma_ratio_lower
#print axioms RamanujanTau.RankinOmega.tail_gen
#print axioms RamanujanTau.RankinOmega.Zf_horiz
#print axioms RamanujanTau.RankinOmega.Zf_tail
#print axioms RamanujanTau.RankinOmega.Zf_first_moment
#print axioms RamanujanTau.RankinOmega.mellin_Rf_large
#print axioms RamanujanTau.RankinOmega.Lam_eq_mellin
#print axioms RamanujanTau.RankinOmega.hfun_L1L2
#print axioms RamanujanTau.RankinOmega.block_lower
