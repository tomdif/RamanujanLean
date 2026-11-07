/-
# From the first Riesz sum to the sharp partial sum (complex coefficients)

* `F1_diff`: `F₁(x+h) − F₁(x) = h·A(x) + ∑_{x<n≤x+h} aₙ (x+h−n)`, where `A(x) = ∑_{n≤x} aₙ`.
  Hence `h‖A(x)‖ ≤ ‖F₁(x+h)‖ + ‖F₁(x)‖ + h ∑_{x<n≤x+h} ‖aₙ‖` (`main_ineq`).
* `short_sq`: Cauchy–Schwarz plus a Rankin–Selberg asymptotic with error `N^{3/5}`
  (for `‖aₙ‖²/n^β`) gives `(∑_{N<n≤M} ‖aₙ‖)² ≤ (M−N) M^β (|c|(M−N) + 2C M^{3/5})`.
  This replaces Deligne's bound in Landau's differencing: no pointwise bound on `aₙ` is used.
* `partial_sum_bound`: if `‖F₁(y)‖ ≤ K y^{β/2+1+δ}`, then with `h = x^{7/15}`,
  `‖A(x)‖ ≪ x^{β/2 + 8/15 + δ}`.

The choice `h = x^{7/15}` balances `x^{β/2+1}/h` against `h^{1/2} x^{β/2+3/10}`.
-/
import RamanujanTau.TauPartialSums.Riesz

set_option autoImplicit false

namespace RamanujanTau.TauPartialSums

open Finset Real

/-- The partial sum `A(x) = ∑_{1 ≤ n ≤ x} aₙ`. -/
noncomputable def A (a : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n

lemma Icc_one_eq_Ioc (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

lemma F1_diff (a : ℕ → ℂ) {x h : ℝ} (_hx : 0 ≤ x) (hh : 0 ≤ h) :
    F1 a (x + h) - F1 a x = (h : ℂ) * A a x +
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n) := by
  have hNM : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
  unfold F1 A
  rw [Icc_one_eq_Ioc, Icc_one_eq_Ioc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hNM,
    Finset.mul_sum]
  have e : ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n * (((x + h : ℝ) : ℂ) - n) =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ((h : ℂ) * a n + a n * ((x : ℂ) - n)) :=
    Finset.sum_congr rfl fun n _ => by push_cast; ring
  rw [e, Finset.sum_add_distrib]
  ring

lemma norm_tail_term (a : ℕ → ℂ) {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊) :
    ‖a n * (((x + h : ℝ) : ℂ) - n)‖ ≤ ‖a n‖ * h := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hn
  have hup : (n : ℝ) ≤ x + h :=
    (Nat.cast_le.2 h2).trans (Nat.floor_le (by linarith))
  have hlo : x < n := by
    have := Nat.lt_floor_add_one x
    have h1' : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast h1
    linarith
  rw [norm_mul]
  have e : (((x + h : ℝ) : ℂ) - n) = ((x + h - n : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  gcongr
  linarith

lemma main_ineq (a : ℕ → ℂ) {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    h * ‖A a x‖ ≤ ‖F1 a (x + h)‖ + ‖F1 a x‖ +
      h * ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖a n‖ := by
  have hd := F1_diff a hx hh
  have e : (h : ℂ) * A a x = F1 a (x + h) - F1 a x -
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n) := by
    rw [hd]; ring
  have hn : ‖(h : ℂ) * A a x‖ = h * ‖A a x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
  have ht : ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n)‖ ≤
      h * ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖a n‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn => (norm_tail_term a hx hh hn).trans_eq (by ring)
  rw [← hn, e]
  calc ‖F1 a (x + h) - F1 a x -
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n)‖
      ≤ ‖F1 a (x + h) - F1 a x‖ +
        ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n)‖ := norm_sub_le _ _
    _ ≤ (‖F1 a (x + h)‖ + ‖F1 a x‖) + h * ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖a n‖ :=
        add_le_add (norm_sub_le _ _) ht

/-- **Short sums of `‖aₙ‖` from a Rankin–Selberg asymptotic** (Cauchy–Schwarz). -/
lemma short_sq (a : ℕ → ℂ) (β : ℕ) {c C : ℝ}
    (hT : ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ β - c * N| ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5))
    {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Ioc N M, ‖a n‖) ^ 2 ≤
      ((M : ℝ) - N) * ((M : ℝ) ^ β * (|c| * ((M : ℝ) - N) + 2 * C * (M : ℝ) ^ ((3 : ℝ) / 5))) := by
  set T : ℕ → ℝ := fun N => ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ β with hTdef
  have hC0 : 0 ≤ C := by
    have h1 := (abs_nonneg _).trans (hT N hN)
    have hp : 0 < (N : ℝ) ^ ((3 : ℝ) / 5) := by
      apply Real.rpow_pos_of_pos; exact_mod_cast hN
    exact nonneg_of_mul_nonneg_left h1 hp
  have hcard : ((Finset.Ioc N M).card : ℝ) = (M : ℝ) - N := by
    rw [Nat.card_Ioc, Nat.cast_sub hNM]
  have hCS := sq_sum_le_card_mul_sum_sq (s := Finset.Ioc N M) (f := fun n => ‖a n‖)
  rw [hcard] at hCS
  have hMN : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  -- weights
  have hw : ∑ n ∈ Finset.Ioc N M, ‖a n‖ ^ 2 ≤
      (M : ℝ) ^ β * ∑ n ∈ Finset.Ioc N M, ‖a n‖ ^ 2 / (n : ℝ) ^ β := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hn
    have hn0 : (0 : ℝ) < (n : ℝ) ^ β := by
      apply pow_pos; exact_mod_cast (show 0 < n by omega)
    have hnM : (n : ℝ) ^ β ≤ (M : ℝ) ^ β := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg _); exact_mod_cast h2
    calc ‖a n‖ ^ 2 = (n : ℝ) ^ β * (‖a n‖ ^ 2 / (n : ℝ) ^ β) := by field_simp
      _ ≤ (M : ℝ) ^ β * (‖a n‖ ^ 2 / (n : ℝ) ^ β) := by gcongr
  have hsplit : ∑ n ∈ Finset.Ioc N M, ‖a n‖ ^ 2 / (n : ℝ) ^ β = T M - T N := by
    simp only [hTdef]
    rw [Icc_one_eq_Ioc, Icc_one_eq_Ioc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hNM]
    ring
  have hM : T M ≤ c * M + C * (M : ℝ) ^ ((3 : ℝ) / 5) := by
    have := (abs_le.1 (hT M (hN.trans hNM))).2; simp only [hTdef]; linarith
  have hNl : c * N - C * (N : ℝ) ^ ((3 : ℝ) / 5) ≤ T N := by
    have := (abs_le.1 (hT N hN)).1; simp only [hTdef]; linarith
  have hpow : (N : ℝ) ^ ((3 : ℝ) / 5) ≤ (M : ℝ) ^ ((3 : ℝ) / 5) :=
    Real.rpow_le_rpow (by linarith) hMN (by norm_num)
  have hcabs : c * ((M : ℝ) - N) ≤ |c| * ((M : ℝ) - N) :=
    mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith)
  have hdiff : T M - T N ≤ |c| * ((M : ℝ) - N) + 2 * C * (M : ℝ) ^ ((3 : ℝ) / 5) := by
    nlinarith
  rw [hsplit] at hw
  have hMN0 : (0 : ℝ) ≤ (M : ℝ) - N := by linarith
  calc (∑ n ∈ Finset.Ioc N M, ‖a n‖) ^ 2 ≤ ((M : ℝ) - N) * ∑ n ∈ Finset.Ioc N M, ‖a n‖ ^ 2 := hCS
    _ ≤ ((M : ℝ) - N) * ((M : ℝ) ^ β * (T M - T N)) := by gcongr
    _ ≤ _ := by gcongr

/-- **Landau-type differencing, order one, with Rankin–Selberg short sums.** -/
theorem partial_sum_bound (a : ℕ → ℂ) (β : ℕ) {δ K c C : ℝ} (hδ : 0 ≤ δ)
    (hF1 : ∀ y : ℝ, 1 ≤ y → ‖F1 a y‖ ≤ K * y ^ ((β : ℝ) / 2 + 1 + δ))
    (hT : ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ β - c * N| ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5)) :
    ∃ C' : ℝ, ∀ x : ℝ, 1 ≤ x → ‖A a x‖ ≤ C' * x ^ ((β : ℝ) / 2 + 8 / 15 + δ) := by
  have hC0 : 0 ≤ C := by
    have h1 := (abs_nonneg _).trans (hT 1 le_rfl)
    simpa using h1
  set e : ℝ := (β : ℝ) / 2 + 1 + δ with he
  set E : ℝ := (β : ℝ) / 2 + 8 / 15 + δ with hE
  set Q : ℝ := 2 * 2 ^ β * (2 * |c| + 4 * C) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨|K| * (2 ^ e + 1) + Real.sqrt Q, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set h : ℝ := x ^ ((7 : ℝ) / 15) with hh
  have hh1 : 1 ≤ h := Real.one_le_rpow hx (by norm_num)
  have hh0 : 0 < h := by linarith
  have hhx : h ≤ x := by
    calc h ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = x := Real.rpow_one x
  have hh35 : h ≤ x ^ ((3 : ℝ) / 5) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  set N : ℕ := ⌊x⌋₊ with hN
  set M : ℕ := ⌊x + h⌋₊ with hM
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa using hx)
  have hNM : N ≤ M := Nat.floor_le_floor (by linarith)
  have hMle : (M : ℝ) ≤ x + h := Nat.floor_le (by linarith)
  have hNgt : x - 1 < (N : ℝ) := by have := Nat.lt_floor_add_one x; linarith
  have hMN : (M : ℝ) - N ≤ 2 * h := by linarith
  have hMN0 : (0 : ℝ) ≤ (M : ℝ) - N := by
    have : (N : ℝ) ≤ M := by exact_mod_cast hNM
    linarith
  have hM2 : (M : ℝ) ≤ 2 * x := by linarith
  -- the short sum
  set S : ℝ := ∑ n ∈ Finset.Ioc N M, ‖a n‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hSq := short_sq a β hT hN1 hNM
  have hMb : (M : ℝ) ^ β ≤ 2 ^ β * x ^ β := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hM2 β
  have hM35 : (M : ℝ) ^ ((3 : ℝ) / 5) ≤ 2 * x ^ ((3 : ℝ) / 5) := by
    calc (M : ℝ) ^ ((3 : ℝ) / 5) ≤ (2 * x) ^ ((3 : ℝ) / 5) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hM2 (by norm_num)
      _ = 2 ^ ((3 : ℝ) / 5) * x ^ ((3 : ℝ) / 5) := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 2 * x ^ ((3 : ℝ) / 5) := by
          gcongr
          calc (2 : ℝ) ^ ((3 : ℝ) / 5) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have hx35 : 0 ≤ x ^ ((3 : ℝ) / 5) := by positivity
  have hinner : |c| * ((M : ℝ) - N) + 2 * C * (M : ℝ) ^ ((3 : ℝ) / 5) ≤
      (2 * |c| + 4 * C) * x ^ ((3 : ℝ) / 5) := by
    have h1 : |c| * ((M : ℝ) - N) ≤ |c| * (2 * x ^ ((3 : ℝ) / 5)) :=
      mul_le_mul_of_nonneg_left (hMN.trans (by linarith)) (abs_nonneg c)
    have h2 : 2 * C * (M : ℝ) ^ ((3 : ℝ) / 5) ≤ 2 * C * (2 * x ^ ((3 : ℝ) / 5)) :=
      mul_le_mul_of_nonneg_left hM35 (by positivity)
    nlinarith
  have hxb : (x : ℝ) ^ β = x ^ (β : ℝ) := (Real.rpow_natCast x β).symm
  have hS2 : S ^ 2 ≤ Q * x ^ ((β : ℝ) + 16 / 15) := by
    have hprod : x ^ ((β : ℝ) + 16 / 15) = x ^ ((7 : ℝ) / 15) * (x ^ β * x ^ ((3 : ℝ) / 5)) := by
      rw [hxb, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
    calc S ^ 2 ≤ ((M : ℝ) - N) * ((M : ℝ) ^ β *
          (|c| * ((M : ℝ) - N) + 2 * C * (M : ℝ) ^ ((3 : ℝ) / 5))) := hSq
      _ ≤ (2 * h) * ((2 ^ β * x ^ β) * ((2 * |c| + 4 * C) * x ^ ((3 : ℝ) / 5))) := by
          have hin0 : 0 ≤ |c| * ((M : ℝ) - N) + 2 * C * (M : ℝ) ^ ((3 : ℝ) / 5) := by
            positivity
          gcongr
      _ = Q * x ^ ((β : ℝ) + 16 / 15) := by rw [hprod, hQ, hh]; ring
  have hSle : S ≤ Real.sqrt Q * x ^ (E - δ) := by
    have hr : Real.sqrt (x ^ ((β : ℝ) + 16 / 15)) = x ^ (E - δ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, hE]; ring_nf
    calc S = Real.sqrt (S ^ 2) := (Real.sqrt_sq hS0).symm
      _ ≤ Real.sqrt (Q * x ^ ((β : ℝ) + 16 / 15)) := Real.sqrt_le_sqrt hS2
      _ = Real.sqrt Q * x ^ (E - δ) := by rw [Real.sqrt_mul hQ0, hr]
  -- the Riesz terms
  have hF1a : ‖F1 a (x + h)‖ ≤ |K| * (2 ^ e * x ^ e) := by
    refine (hF1 (x + h) (by linarith)).trans ?_
    have he0 : 0 ≤ e := by rw [he]; positivity
    calc K * (x + h) ^ e ≤ |K| * (x + h) ^ e :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
      _ ≤ |K| * (2 * x) ^ e := by gcongr; linarith
      _ = |K| * (2 ^ e * x ^ e) := by rw [Real.mul_rpow (by norm_num) hx0.le]
  have hF1b : ‖F1 a x‖ ≤ |K| * x ^ e :=
    (hF1 x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
  have hmain := main_ineq a hx0.le hh0.le
  rw [← hN, ← hM, ← hS] at hmain
  have hxe : x ^ e = h * x ^ E := by
    rw [hh, ← Real.rpow_add hx0, he, hE]; ring_nf
  have hxEd : x ^ (E - δ) ≤ x ^ E := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hkey : h * ‖A a x‖ ≤ h * ((|K| * (2 ^ e + 1)) * x ^ E + S) := by
    calc h * ‖A a x‖ ≤ ‖F1 a (x + h)‖ + ‖F1 a x‖ + h * S := hmain
      _ ≤ |K| * (2 ^ e * x ^ e) + |K| * x ^ e + h * S := by gcongr
      _ = h * ((|K| * (2 ^ e + 1)) * x ^ E + S) := by rw [hxe]; ring
  have hA := le_of_mul_le_mul_left hkey hh0
  have hsq0 : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
  calc ‖A a x‖ ≤ (|K| * (2 ^ e + 1)) * x ^ E + S := hA
    _ ≤ (|K| * (2 ^ e + 1)) * x ^ E + Real.sqrt Q * x ^ E := by
        gcongr; exact hSle.trans (mul_le_mul_of_nonneg_left hxEd hsq0)
    _ = (|K| * (2 ^ e + 1) + Real.sqrt Q) * x ^ E := by ring

end RamanujanTau.TauPartialSums
