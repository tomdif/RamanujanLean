/-
# Transferring a power saving through the Möbius inversion of the `ζ(2s)` twist

`mobius_transfer`: if `A(N) = ∑_{m≤N} μ(m) B(⌊N/m²⌋)`, `B(0) = 0` and
`B(M) = c₀M + O(M^{1−δ})` with `0 ≤ δ < 1/2`, then `A(N) = (6/π²) c₀ N + O(N^{1−δ})`.

The only analytic input is `∑ μ(m)/m² = 6/π²` (`tsum_moebius_div_sq`, from Mathlib's
`L(1,s)L(μ,s) = 1` and `ζ(2) = π²/6`), and the elementary `|⌊x⌋ − x| ≤ min(1,x) ≤ x^{1−δ}`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.RankinSharp

open Real Finset ArithmeticFunction

lemma tsum_moebius_div_sq : ∑' m : ℕ, (moebius m : ℝ) / ((m : ℝ) * m) = 6 / π ^ 2 := by
  have h := LSeries_one_mul_Lseries_moebius (s := 2) (by norm_num)
  rw [LSeries_one_eq_riemannZeta (by norm_num), riemannZeta_two] at h
  have hterm : ∀ m : ℕ, LSeries.term (fun n => ((moebius n : ℤ) : ℂ)) 2 m =
      (((moebius m : ℝ) / ((m : ℝ) * m) : ℝ) : ℂ) := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · rw [LSeries.term_of_ne_zero hm]
      push_cast
      rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast, sq]
  have hL : LSeries (fun n => ((moebius n : ℤ) : ℂ)) 2 =
      ((∑' m : ℕ, (moebius m : ℝ) / ((m : ℝ) * m) : ℝ) : ℂ) := by
    unfold LSeries; rw [Complex.ofReal_tsum]; congr 1; funext m; exact hterm m
  rw [hL] at h
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : ((∑' m : ℕ, (moebius m : ℝ) / ((m : ℝ) * m) : ℝ) : ℂ) = ((6 / π ^ 2 : ℝ) : ℂ) := by
    generalize ((∑' m : ℕ, (moebius m : ℝ) / ((m : ℝ) * m) : ℝ) : ℂ) = X at h ⊢
    push_cast
    field_simp at h ⊢
    linear_combination h
  exact_mod_cast e

lemma inv_mul_self_rpow {p : ℝ} (hp : 0 < p) (m : ℕ) :
    (((m : ℝ) * m)⁻¹) ^ p = (m : ℝ) ^ (-(2 * p)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [Real.zero_rpow hp.ne', Real.zero_rpow (by linarith : -(2 * p) ≠ 0)]
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    rw [Real.inv_rpow (by positivity), Real.mul_rpow hm0.le hm0.le, ← Real.rpow_add hm0,
      Real.rpow_neg hm0.le]
    ring_nf

/-- `|⌊x⌋ − x| ≤ x^p` for `x ≥ 0`, `0 ≤ p ≤ 1`. -/
lemma floor_sub_le_rpow {x p : ℝ} (hx : 0 ≤ x) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |(⌊x⌋₊ : ℝ) - x| ≤ x ^ p := by
  have h1 := Nat.floor_le hx
  have h2 := Nat.lt_floor_add_one x
  rw [abs_of_nonpos (by linarith)]
  rcases le_or_gt x 1 with h | h
  · have := Real.self_le_rpow_of_le_one hx h hp1
    have : (0 : ℝ) ≤ ⌊x⌋₊ := Nat.cast_nonneg _
    linarith
  · have := Real.one_le_rpow h.le hp0
    linarith

theorem mobius_transfer {A B : ℕ → ℝ} {c₀ C δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2)
    (hA : ∀ N, A N = ∑ m ∈ Ioc 0 N, (moebius m : ℝ) * B (N / (m * m)))
    (hB0 : B 0 = 0) (hB : ∀ M : ℕ, 1 ≤ M → |B M - c₀ * M| ≤ C * (M : ℝ) ^ (1 - δ)) :
    ∃ C' : ℝ, ∀ N : ℕ, 1 ≤ N → |A N - c₀ * (6 / π ^ 2) * N| ≤ C' * (N : ℝ) ^ (1 - δ) := by
  set p : ℝ := 1 - δ with hpdef
  have hp0 : 0 < p := by linarith
  have hp1 : p ≤ 1 := by linarith
  set g : ℕ → ℝ := fun m => (m : ℝ) ^ (-(2 * p)) with hg
  have hgs : Summable g := Real.summable_nat_rpow.2 (by linarith)
  have hg0 : ∀ m, 0 ≤ g m := fun m => by positivity
  set S₀ : ℝ := ∑' m, g m with hS₀
  have hS0 : 0 ≤ S₀ := tsum_nonneg hg0
  refine ⟨(|C| + |c₀|) * S₀, fun N hN => ?_⟩
  have hNp : 0 ≤ (N : ℝ) ^ p := by positivity
  -- notation
  set x : ℕ → ℝ := fun m => (N : ℝ) * ((m : ℝ) * m)⁻¹ with hx
  set fl : ℕ → ℝ := fun m => ((N / (m * m) : ℕ) : ℝ) with hfl
  have hx0 : ∀ m, 0 ≤ x m := fun m => by positivity
  have hxp : ∀ m, x m ^ p = (N : ℝ) ^ p * g m := by
    intro m
    rw [hx, Real.mul_rpow (Nat.cast_nonneg _) (by positivity), inv_mul_self_rpow hp0]
  have hflx : ∀ m, fl m = (⌊x m⌋₊ : ℝ) := by
    intro m
    show ((N / (m * m) : ℕ) : ℝ) = (⌊(N : ℝ) * ((m : ℝ) * m)⁻¹⌋₊ : ℝ)
    rw [← div_eq_mul_inv, show (m : ℝ) * m = ((m * m : ℕ) : ℝ) by push_cast; ring,
      Nat.floor_div_eq_div]
  have hfl_le : ∀ m, fl m ≤ x m := fun m => by rw [hflx]; exact Nat.floor_le (hx0 m)
  have hμ : ∀ m : ℕ, |(moebius m : ℝ)| ≤ 1 := by
    intro m; have := abs_moebius_le_one (n := m); exact_mod_cast this
  -- the error of `B`
  have hE : ∀ M : ℕ, |B M - c₀ * M| ≤ |C| * (M : ℝ) ^ p := by
    intro M
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp [hB0]; positivity
    · exact (hB M hM).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  -- decomposition
  have hdec : A N - c₀ * (6 / π ^ 2) * N =
      ∑ m ∈ Ioc 0 N, (moebius m : ℝ) * (B (N / (m * m)) - c₀ * fl m) +
        c₀ * (∑ m ∈ Ioc 0 N, (moebius m : ℝ) * fl m -
          ∑' m : ℕ, (moebius m : ℝ) * x m) := by
    have ht : ∑' m : ℕ, (moebius m : ℝ) * x m = N * (6 / π ^ 2) := by
      rw [← tsum_moebius_div_sq, ← tsum_mul_left]
      congr 1; funext m; rw [hx]; ring
    have hs : ∑ m ∈ Ioc 0 N, (moebius m : ℝ) * (B (N / (m * m)) - c₀ * fl m) =
        ∑ m ∈ Ioc 0 N, (moebius m : ℝ) * B (N / (m * m)) -
          c₀ * ∑ m ∈ Ioc 0 N, (moebius m : ℝ) * fl m := by
      rw [mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro m _; ring
    rw [hA N, ht, hs]; ring
  -- first part
  have h1 : |∑ m ∈ Ioc 0 N, (moebius m : ℝ) * (B (N / (m * m)) - c₀ * fl m)| ≤
      |C| * (N : ℝ) ^ p * S₀ := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ m ∈ Ioc 0 N, |(moebius m : ℝ) * (B (N / (m * m)) - c₀ * fl m)|
        ≤ ∑ m ∈ Ioc 0 N, |C| * (N : ℝ) ^ p * g m := by
          apply sum_le_sum; intro m _
          rw [abs_mul, mul_assoc, ← hxp]
          calc |(moebius m : ℝ)| * |B (N / (m * m)) - c₀ * fl m| ≤ 1 * (|C| * fl m ^ p) := by
                gcongr
                · exact hμ m
                · exact hE (N / (m * m))
            _ ≤ |C| * x m ^ p := by
                rw [one_mul]; gcongr
                exact hfl_le m
      _ = |C| * (N : ℝ) ^ p * ∑ m ∈ Ioc 0 N, g m := by rw [mul_sum]
      _ ≤ |C| * (N : ℝ) ^ p * S₀ := by
          gcongr; exact hgs.sum_le_tsum _ (fun m _ => hg0 m)
  -- second part
  have hfin : ∑ m ∈ Ioc 0 N, (moebius m : ℝ) * fl m = ∑' m : ℕ, (moebius m : ℝ) * fl m := by
    symm
    refine tsum_eq_sum fun m hm => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · have hmN : N < m := by
        by_contra h; exact hm (mem_Ioc.2 ⟨hm0, not_lt.1 h⟩)
      have : N / (m * m) = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hmN (Nat.le_mul_self m))
      simp [hfl, this]
  have hsum_fl : Summable fun m : ℕ => (moebius m : ℝ) * fl m := by
    refine summable_of_ne_finset_zero (s := Ioc 0 N) fun m hm => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · have hmN : N < m := by
        by_contra h; exact hm (mem_Ioc.2 ⟨hm0, not_lt.1 h⟩)
      have : N / (m * m) = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hmN (Nat.le_mul_self m))
      simp [hfl, this]
  have hpt : ∀ m : ℕ, |(moebius m : ℝ) * (fl m - x m)| ≤ (N : ℝ) ^ p * g m := by
    intro m
    rw [abs_mul, ← hxp, hflx]
    calc |(moebius m : ℝ)| * |(⌊x m⌋₊ : ℝ) - x m| ≤ 1 * x m ^ p := by
          gcongr
          · exact hμ m
          · exact floor_sub_le_rpow (hx0 m) hp0.le hp1
      _ = _ := one_mul _
  have hsum_x : Summable fun m : ℕ => (moebius m : ℝ) * x m := by
    have hsd : Summable fun m : ℕ => (moebius m : ℝ) * (fl m - x m) :=
      Summable.of_norm_bounded (hgs.mul_left ((N : ℝ) ^ p)) fun m => by
        rw [Real.norm_eq_abs]; exact hpt m
    have := hsum_fl.sub hsd
    refine this.congr fun m => ?_
    ring
  have h2 : |∑ m ∈ Ioc 0 N, (moebius m : ℝ) * fl m - ∑' m : ℕ, (moebius m : ℝ) * x m| ≤
      (N : ℝ) ^ p * S₀ := by
    rw [hfin, ← hsum_fl.tsum_sub hsum_x]
    have hsd : Summable fun m : ℕ => (moebius m : ℝ) * fl m - (moebius m : ℝ) * x m :=
      hsum_fl.sub hsum_x
    have hpt' : ∀ m : ℕ, ‖(moebius m : ℝ) * fl m - (moebius m : ℝ) * x m‖ ≤ (N : ℝ) ^ p * g m := by
      intro m; rw [Real.norm_eq_abs, ← mul_sub]; exact hpt m
    rw [← Real.norm_eq_abs, hS₀, ← tsum_mul_left]
    exact tsum_of_norm_bounded ((hgs.mul_left _).hasSum) hpt'
  rw [hdec]
  calc _ ≤ |∑ m ∈ Ioc 0 N, (moebius m : ℝ) * (B (N / (m * m)) - c₀ * fl m)| +
        |c₀ * (∑ m ∈ Ioc 0 N, (moebius m : ℝ) * fl m - ∑' m : ℕ, (moebius m : ℝ) * x m)| :=
        abs_add_le _ _
    _ ≤ |C| * (N : ℝ) ^ p * S₀ + |c₀| * ((N : ℝ) ^ p * S₀) := by
        rw [abs_mul]; gcongr
    _ = (|C| + |c₀|) * S₀ * (N : ℝ) ^ p := by ring

end RamanujanTau.RankinSharp
