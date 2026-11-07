/-
# `SCS2`: what follows cheaply — trivial bound, gcd reduction, the diagonal case `a = b`

* `abs_shiftSum2_le`, `scs2_trivial : SCS2 0 0` (Cauchy–Schwarz + Rankin);
* `shiftSum2_mul_left`: `S(ga, gb; gℓ) = S(a, b; ℓ)` (reduction to `gcd(a,b) = 1`),
  `shiftSum2_eq_zero_of_not_dvd`: `S(a,b;ℓ) = 0` unless `gcd(a,b) ∣ ℓ`;
* `shiftSum2_diag`: `S(a, a; a·j) = shiftSum |j| (N − |j|)` (the one-sided sum);
* **`scs2_diag`**: `|S(a, a; ℓ)| ≤ C N^{1−1/21} |ℓ|^{1/21}` for all `a ≥ 1`, `ℓ ≠ 0`, `N`
  (from the unconditional `SCSSharp2.shiftedConvolutionBound_sharp2`).
-/
import RamanujanTau.HeckeAFE.Hyp
import RamanujanTau.SCSSharp2.Main

set_option autoImplicit false

namespace RamanujanTau.SCS2

open Finset RamanujanTau.SubconvexityCond RamanujanTau.HeckeAFE

/-- Trivial bound: `|S(a,b;ℓ)| ≤ A N` (each `m` determines `n`; Cauchy–Schwarz + Rankin). -/
theorem abs_shiftSum2_le : ∃ A : ℝ, 0 ≤ A ∧ ∀ (a b : ℕ) (ℓ : ℤ) (N : ℕ), 1 ≤ a → 1 ≤ b →
    |shiftSum2 a b ℓ N| ≤ A * N := by
  obtain ⟨A, hA0, hA⟩ := exists_sum_lam_sq_le
  refine ⟨A, hA0, fun a b ℓ N ha hb => ?_⟩
  -- `|λ(m)λ(n)| ≤ (λ(m)² + λ(n)²)/2`, and each `m` (resp. `n`) has at most one partner
  have hterm : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N,
      |if (a : ℤ) * m - b * n = ℓ then lam m * lam n else 0| ≤
        (if (a : ℤ) * m - b * n = ℓ then lam m ^ 2 / 2 + lam n ^ 2 / 2 else 0) := by
    intro m _ n _
    split_ifs
    · rw [abs_mul]
      nlinarith [sq_nonneg (|lam m| - |lam n|), sq_abs (lam m), sq_abs (lam n)]
    · simp
  have hS : |shiftSum2 a b ℓ N| ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      (if (a : ℤ) * m - b * n = ℓ then lam m ^ 2 / 2 + lam n ^ 2 / 2 else 0) := by
    unfold shiftSum2
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => hterm m hm n hn)
  refine hS.trans ?_
  have hsplit : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N,
      (if (a : ℤ) * m - b * n = ℓ then lam m ^ 2 / 2 + lam n ^ 2 / 2 else 0) =
        (if (a : ℤ) * m - b * n = ℓ then lam m ^ 2 / 2 else 0) +
          (if (a : ℤ) * m - b * n = ℓ then lam n ^ 2 / 2 else 0) := by
    intro m _ n _; split_ifs <;> simp
  rw [sum_congr rfl fun m hm => sum_congr rfl fun n hn => hsplit m hm n hn]
  simp_rw [sum_add_distrib]
  -- for fixed `m` at most one `n`; for fixed `n` at most one `m` (needs `b ≥ 1` only for the first)
  have h1 : ∀ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      (if (a : ℤ) * m - b * n = ℓ then lam m ^ 2 / 2 else 0) ≤ lam m ^ 2 / 2 := by
    intro m _
    have hsub : ((Icc 1 N).filter fun n : ℕ => (a : ℤ) * m - b * n = ℓ).card ≤ 1 := by
      refine card_le_one.2 fun x hx y hy => ?_
      simp only [mem_filter] at hx hy
      have : (b : ℤ) * x = b * y := by linarith [hx.2, hy.2]
      have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
      exact_mod_cast mul_left_cancel₀ hb0 this
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have : (((Icc 1 N).filter fun n : ℕ => (a : ℤ) * m - b * n = ℓ).card : ℝ) ≤ 1 := by
      exact_mod_cast hsub
    nlinarith [sq_nonneg (lam m)]
  have h2 : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      (if (a : ℤ) * m - b * n = ℓ then lam n ^ 2 / 2 else 0) ≤ ∑ n ∈ Icc 1 N, lam n ^ 2 / 2 := by
    rw [sum_comm]
    refine sum_le_sum fun n _ => ?_
    have hsub : ((Icc 1 N).filter fun m : ℕ => (a : ℤ) * m - b * n = ℓ).card ≤ 1 := by
      refine card_le_one.2 fun x hx y hy => ?_
      simp only [mem_filter] at hx hy
      have : (a : ℤ) * x = a * y := by linarith [hx.2, hy.2]
      have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
      exact_mod_cast mul_left_cancel₀ ha0 this
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have : (((Icc 1 N).filter fun m : ℕ => (a : ℤ) * m - b * n = ℓ).card : ℝ) ≤ 1 := by
      exact_mod_cast hsub
    nlinarith [sq_nonneg (lam n)]
  have h1' := sum_le_sum h1
  have e : ∀ N : ℕ, ∑ n ∈ Icc 1 N, lam n ^ 2 / 2 = (∑ n ∈ Icc 1 N, lam n ^ 2) / 2 := fun N => by
    rw [sum_div]
  rw [e] at h1' h2
  have := hA N
  linarith

/-- **`SCS2(0, 0)`** (no saving): the trivial bound. -/
theorem scs2_trivial : SCS2 0 0 := by
  obtain ⟨A, hA0, hA⟩ := abs_shiftSum2_le
  refine ⟨A, hA0, fun a b ℓ N ha hb _ => (hA a b ℓ N ha hb).trans ?_⟩
  simp only [sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]
  have := abs_nonneg (ℓ : ℝ)
  nlinarith

/-- **gcd reduction**: `S(ga, gb; gℓ) = S(a, b; ℓ)`. -/
theorem shiftSum2_mul_left (g a b : ℕ) (hg : 1 ≤ g) (ℓ : ℤ) (N : ℕ) :
    shiftSum2 (g * a) (g * b) (g * ℓ) N = shiftSum2 a b ℓ N := by
  unfold shiftSum2
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have : ((g * a : ℕ) : ℤ) * m - ((g * b : ℕ) : ℤ) * n = g * ℓ ↔ (a : ℤ) * m - b * n = ℓ := by
    push_cast
    constructor
    · intro h; exact mul_left_cancel₀ hg0 (by linear_combination h)
    · intro h; linear_combination (g : ℤ) * h
  simp only [this]

/-- `S(a,b;ℓ) = 0` unless `gcd(a,b) ∣ ℓ`. -/
theorem shiftSum2_eq_zero_of_not_dvd (a b : ℕ) (ℓ : ℤ) (N : ℕ)
    (h : ¬ ((Nat.gcd a b : ℕ) : ℤ) ∣ ℓ) : shiftSum2 a b ℓ N = 0 := by
  unfold shiftSum2
  refine sum_eq_zero fun m _ => sum_eq_zero fun n _ => ?_
  rw [if_neg]
  intro he
  apply h
  rw [← he]
  exact dvd_sub (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left a b)) _)
    (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right a b)) _)

/-- Symmetry `S(a, a; −ℓ) = S(a, a; ℓ)`. -/
lemma shiftSum2_diag_neg (a : ℕ) (ℓ : ℤ) (N : ℕ) :
    shiftSum2 a a (-ℓ) N = shiftSum2 a a ℓ N := by
  unfold shiftSum2
  rw [sum_comm]
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
  by_cases h1 : (a : ℤ) * n - a * m = -ℓ
  · rw [if_pos h1, if_pos (by linarith)]; ring
  · rw [if_neg h1, if_neg (by intro h; apply h1; linarith)]

/-- **The diagonal case is the one-sided sum**: `S(a, a; a h) = Σ_{n ≤ N−h} λ(n)λ(n+h)`. -/
theorem shiftSum2_diag (a h N : ℕ) (ha : 1 ≤ a) :
    shiftSum2 a a ((a : ℤ) * h) N = shiftSum h (N - h) := by
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  unfold shiftSum2 shiftSum
  rw [sum_comm]
  have hc : ∀ m n : ℕ, ((a : ℤ) * m - a * n = a * h ↔ n + h = m) := by
    intro m n
    constructor
    · intro e
      have : (m : ℤ) - n = h := mul_left_cancel₀ ha0 (by linear_combination e)
      omega
    · intro e; subst e; push_cast; ring
  simp_rw [hc]
  have : ∀ n : ℕ, (∑ m ∈ Icc 1 N, if n + h = m then lam m * lam n else 0) =
      if n + h ∈ Icc 1 N then lam (n + h) * lam n else 0 := fun n => by
    rw [sum_ite_eq]
  simp_rw [this]
  rw [← sum_filter]
  refine sum_congr ?_ fun n _ => by ring
  ext n; simp only [mem_filter, mem_Icc]; omega

/-- **`SCS2` on the diagonal `a = b`** (unconditional):
`|Σ_{m,n ≤ N, a m − a n = ℓ} λ(m)λ(n)| ≤ C N^{1−1/21} |ℓ|^{1/21}` for all `a ≥ 1`, `ℓ ≠ 0`, `N`. -/
theorem scs2_diag : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ) (ℓ : ℤ) (N : ℕ), 1 ≤ a → ℓ ≠ 0 →
    |shiftSum2 a a ℓ N| ≤ C * (N : ℝ) ^ (1 - 1 / 21 : ℝ) * |(ℓ : ℝ)| ^ (1 / 21 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := (RamanujanTau.SCSSharp2.shiftedConvolutionBound_sharp2).bound
  refine ⟨C, hC0, fun a ℓ N ha hℓ => ?_⟩
  have hR : 0 ≤ C * (N : ℝ) ^ (1 - 1 / 21 : ℝ) * |(ℓ : ℝ)| ^ (1 / 21 : ℝ) := by positivity
  by_cases hd : (a : ℤ) ∣ ℓ
  swap
  · have : ¬ ((Nat.gcd a a : ℕ) : ℤ) ∣ ℓ := by rwa [Nat.gcd_self]
    rw [shiftSum2_eq_zero_of_not_dvd a a ℓ N this, abs_zero]; exact hR
  obtain ⟨j, rfl⟩ := hd
  have hj : j ≠ 0 := by rintro rfl; simp at hℓ
  set h := j.natAbs with hh
  have hh1 : 1 ≤ h := Int.natAbs_pos.2 hj
  have key : |shiftSum2 a a ((a : ℤ) * j) N| = |shiftSum h (N - h)| := by
    rcases le_or_gt 0 j with hj0 | hj0
    · have : j = (h : ℤ) := by rw [hh]; omega
      rw [this, shiftSum2_diag a h N ha]
    · have : j = -(h : ℤ) := by rw [hh]; omega
      rw [this, show (a : ℤ) * -(h : ℤ) = -((a : ℤ) * h) by ring, shiftSum2_diag_neg,
        shiftSum2_diag a h N ha]
  rw [key]
  rcases le_or_gt h N with hhN | hhN
  · have e := hC h (N - h) hh1
    have hN : ((N - h : ℕ) : ℝ) + h = N := by push_cast [Nat.cast_sub hhN]; ring
    rw [hN] at e
    refine e.trans ?_
    have hhℓ : (h : ℝ) ≤ |((a * j : ℤ) : ℝ)| := by
      have hjh : (h : ℝ) = |(j : ℝ)| := by rw [hh, Nat.cast_natAbs, Int.cast_abs]
      have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
      push_cast
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ a), hjh]
      nlinarith [abs_nonneg (j : ℝ)]
    gcongr
  · have : N - h = 0 := by omega
    rw [this, show shiftSum h 0 = 0 by simp [shiftSum], abs_zero]
    exact hR

end RamanujanTau.SCS2
