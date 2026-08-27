/-
# Coefficient specialization of the quintuple product identity

The formal quintuple product lives in `ℤ[z,z⁻¹]⟦q⟧`.  The specialization used
in the sparse-product papers is `q ↦ q^p`, `z ↦ q⁻ⁱ`.  It is deliberately not
treated as an unrestricted power-series homomorphism: negative Laurent powers
make such a homomorphism ill-defined.  Under `0 < i` and `2*i < p`, however,
the five product factors lie in a positive weight cone.  Consequently every
one-variable coefficient is a finite diagonal of the bivariate series.

This file first exposes that finite diagonal and transports the completed formal
quintuple identity through it.  The subsequent lemmas identify its product side
with the five stabilized Pochhammer factors and its theta side with Watson's two
bilateral branches.  All sums used for a coefficient are finite.
-/
import RamanujanTau.MockTheta5QuintIdentity
import RamanujanTau.MultiQuintuplePochhammer
import RamanujanTau.MultiQuintupleVanishing
import Mathlib.Data.Int.Interval

namespace Ramanujan.MultiQuintuple

open PowerSeries LaurentPolynomial
open MockTheta5.JTP MockTheta5.Bailey

/-- The one-variable coefficient of weight `k` obtained from the finite part
`0 ≤ q-degree ≤ k` of a bivariate Laurent-coefficient power series under
`q ↦ q^p`, `z ↦ q⁻ⁱ`. -/
noncomputable def quintDiagonalCoeff (p i k : ℕ)
    (A : PowerSeries (LaurentPolynomial ℤ)) : ℤ :=
  ∑ n ∈ Finset.range (k + 1),
    if (i : ℤ) ∣ (p : ℤ) * n - k then
      coeff n A (((p : ℤ) * n - k) / (i : ℤ))
    else 0

lemma quintDiagonalCoeff_congr (p i k : ℕ)
    {A B : PowerSeries (LaurentPolynomial ℤ)} (h : A = B) :
    quintDiagonalCoeff p i k A = quintDiagonalCoeff p i k B := by
  subst B
  rfl

lemma quintDiagonalCoeff_add (p i k : ℕ)
    (A B : PowerSeries (LaurentPolynomial ℤ)) :
    quintDiagonalCoeff p i k (A + B) =
      quintDiagonalCoeff p i k A + quintDiagonalCoeff p i k B := by
  simp only [quintDiagonalCoeff, map_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : (i : ℤ) ∣ (p : ℤ) * n - k
  · simp only [h, if_true]
    rfl
  · simp [h]

private lemma coeff_Xpow_C_Laurent (a b : ℕ) (d : ℤ) :
    coeff b ((X : PowerSeries (LaurentPolynomial ℤ)) ^ a *
        PowerSeries.C (LaurentPolynomial.T d)) =
      if b = a then LaurentPolynomial.T d else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with hle heq heq
  · subst b
    simp
  · rw [PowerSeries.coeff_C, if_neg (by omega)]
  · omega
  · rfl

lemma quintDiagonalCoeff_sub (p i k : ℕ)
    (A B : PowerSeries (LaurentPolynomial ℤ)) :
    quintDiagonalCoeff p i k (A - B) =
      quintDiagonalCoeff p i k A - quintDiagonalCoeff p i k B := by
  simp only [quintDiagonalCoeff, map_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : (i : ℤ) ∣ (p : ℤ) * n - k
  · simp only [h, if_true]
    rfl
  · simp [h]

/-- A monomial whose specialized weight is `k` contributes one to the finite
diagonal.  The condition `a ≤ k` is exactly the positive-cone cutoff. -/
lemma quintDiagonalCoeff_monomial_of_weight {p i k a : ℕ} {d : ℤ}
    (hi : 0 < i) (ha : a ≤ k)
    (hweight : (p : ℤ) * a - (i : ℤ) * d = k) :
    quintDiagonalCoeff p i k
        (X ^ a * PowerSeries.C (LaurentPolynomial.T d)) = 1 := by
  have hdiv : (i : ℤ) ∣ (p : ℤ) * a - k := by
    use d
    omega
  have hquot : ((p : ℤ) * a - k) / (i : ℤ) = d := by
    apply (Int.ediv_eq_iff_eq_mul_left (by omega) hdiv).2
    rw [mul_comm d]
    omega
  rw [quintDiagonalCoeff, Finset.sum_eq_single a]
  · simp [hdiv, hquot]
  · intro b hb hba
    by_cases hdivb : (i : ℤ) ∣ (p : ℤ) * b - k
    · rw [if_pos hdivb]
      rw [coeff_Xpow_C_Laurent, if_neg hba]
      rfl
    · rw [if_neg hdivb]
  · intro haout
    exact (haout (Finset.mem_range.mpr (by omega))).elim

/-- Exact diagonal value of a single bivariate monomial. -/
lemma quintDiagonalCoeff_monomial {p i k a : ℕ} {d : ℤ}
    (hi : 0 < i) :
    quintDiagonalCoeff p i k
        (X ^ a * PowerSeries.C (LaurentPolynomial.T d)) =
      if a ≤ k ∧ (p : ℤ) * a - (i : ℤ) * d = k then 1 else 0 := by
  by_cases hmain : a ≤ k ∧ (p : ℤ) * a - (i : ℤ) * d = k
  · rw [if_pos hmain]
    exact quintDiagonalCoeff_monomial_of_weight hi hmain.1 hmain.2
  · rw [if_neg hmain, quintDiagonalCoeff]
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hdivb : (i : ℤ) ∣ (p : ℤ) * b - k
    · rw [if_pos hdivb, coeff_Xpow_C_Laurent]
      by_cases hba : b = a
      · subst b
        rw [if_pos rfl, LaurentPolynomial.T_apply]
        have hne : d ≠ ((p : ℤ) * a - k) / (i : ℤ) := by
          intro heq
          have hmul := (Int.ediv_eq_iff_eq_mul_left (by omega) hdivb).1 heq.symm
          apply hmain
          constructor
          · have := Finset.mem_range.mp hb
            omega
          · rw [mul_comm d] at hmul
            omega
        rw [if_neg hne]
      · rw [if_neg hba]
        rfl
    · rw [if_neg hdivb]

@[simp] lemma quintDiagonalCoeff_zero (p i k : ℕ) :
    quintDiagonalCoeff p i k 0 = 0 := by
  rw [quintDiagonalCoeff]
  apply Finset.sum_eq_zero
  intro n hn
  by_cases h : (i : ℤ) ∣ (p : ℤ) * n - k
  · simp only [h, if_true]
    rfl
  · rw [if_neg h]

lemma quintDiagonalCoeff_sum {α : Type*} (p i k : ℕ) (s : Finset α)
    (f : α → PowerSeries (LaurentPolynomial ℤ)) :
    quintDiagonalCoeff p i k (∑ a ∈ s, f a) =
      ∑ a ∈ s, quintDiagonalCoeff p i k (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [quintDiagonalCoeff_add, ih]

/-- Up to target weight `k`, the stabilized quintuple theta may be replaced by
its `(k+1)`-term finite truncation. -/
lemma quintDiagonalCoeff_quintTheta_eq_finite (p i k : ℕ) :
    quintDiagonalCoeff p i k quintTheta =
      quintDiagonalCoeff p i k (quintFiniteP (k + 1)) := by
  rw [quintDiagonalCoeff]
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n + 1 ≤ k + 1 := by
    have := Finset.mem_range.mp hn
    omega
  rw [coeff_quintTheta hnle]

private lemma two_dvd_quintLow (m : ℕ) :
    2 ∣ (m + 1) * (3 * m + 2) := by
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · subst m
    use (2 * j + 1) * (3 * j + 1)
    ring
  · subst m
    use (j + 1) * (6 * j + 5)
    ring

private lemma two_dvd_quintHigh (m : ℕ) :
    2 ∣ (m + 1) * (3 * m + 4) := by
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · subst m
    use (2 * j + 1) * (3 * j + 2)
    ring
  · subst m
    use (j + 1) * (6 * j + 7)
    ring

private lemma quintLow_twice (m : ℕ) :
    2 * ((m + 1) * (3 * m + 2) / 2) = (m + 1) * (3 * m + 2) := by
  have h := Nat.div_mul_cancel (two_dvd_quintLow m)
  omega

private lemma quintHigh_twice (m : ℕ) :
    2 * ((m + 1) * (3 * m + 4) / 2) = (m + 1) * (3 * m + 4) := by
  have h := Nat.div_mul_cancel (two_dvd_quintHigh m)
  omega

private lemma quintLow_minus_weight_ge (p i m : ℕ) (hp : 2 * i < p) :
    (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) ≤
      (p : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) -
        (i : ℤ) * (3 * (m : ℤ) + 2) := by
  have hpz : (2 : ℤ) * i + 1 ≤ p := by exact_mod_cast hp
  have htwice := quintLow_twice m
  have htwicez : (2 : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) =
      ((m + 1 : ℕ) : ℤ) * (3 * (m : ℤ) + 2) := by exact_mod_cast htwice
  have htwicez' : (2 : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) =
      ((m : ℤ) + 1) * (3 * (m : ℤ) + 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using htwicez
  have hx : (3 : ℤ) * m + 2 ≤
      2 * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ m by positivity)
      (show (0 : ℤ) ≤ 3 * m + 2 by positivity)]
  have hi_nonneg : (0 : ℤ) ≤ i := by positivity
  have ha_nonneg : (0 : ℤ) ≤ (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) := by positivity
  nlinarith [mul_nonneg hi_nonneg (sub_nonneg.mpr hx),
    mul_nonneg (sub_nonneg.mpr (by omega : (1 : ℤ) ≤ p)) ha_nonneg]

private lemma quintHigh_minus_weight_ge (p i m : ℕ) (hp : 2 * i < p) :
    (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) ≤
      (p : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) -
        (i : ℤ) * (3 * (m : ℤ) + 3) := by
  have hpz : (2 : ℤ) * i + 1 ≤ p := by exact_mod_cast hp
  have htwice := quintHigh_twice m
  have htwicez : (2 : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) =
      ((m + 1 : ℕ) : ℤ) * (3 * (m : ℤ) + 4) := by exact_mod_cast htwice
  have htwicez' : (2 : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) =
      ((m : ℤ) + 1) * (3 * (m : ℤ) + 4) := by
    simpa only [Nat.cast_add, Nat.cast_one] using htwicez
  have hx : (3 : ℤ) * m + 3 ≤
      2 * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ m by positivity)
      (show (0 : ℤ) ≤ 3 * m + 4 by positivity)]
  have hi_nonneg : (0 : ℤ) ≤ i := by positivity
  have ha_nonneg : (0 : ℤ) ≤ (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) := by positivity
  nlinarith [mul_nonneg hi_nonneg (sub_nonneg.mpr hx),
    mul_nonneg (sub_nonneg.mpr (by omega : (1 : ℤ) ≤ p)) ha_nonneg]

private lemma quintWeight_plus_ge (p i a : ℕ) (d : ℤ) (hp : 2 * i < p)
    (hd : 0 ≤ d) :
    (a : ℤ) ≤ (p : ℤ) * a + (i : ℤ) * d := by
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have ha : (0 : ℤ) ≤ a := by positivity
  have hi : (0 : ℤ) ≤ i := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hp1) ha, mul_nonneg hi hd]

private lemma quintExpA2_posSucc (p i m : ℕ) :
    quintExp2 false p i ((m : ℤ) + 1) =
      2 * ((p : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) +
        (i : ℤ) * (3 * (m : ℤ) + 3)) := by
  have hlow := quintLow_twice m
  have hlowz : (2 : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) =
      ((m : ℤ) + 1) * (3 * (m : ℤ) + 2) := by
    exact_mod_cast hlow
  simp only [quintExp2, Bool.false_eq_true, ↓reduceIte, quintExpA2]
  linear_combination (-(p : ℤ)) * hlowz

private lemma quintExpB2_negSucc (p i m : ℕ) :
    quintExp2 true p i (-((m : ℤ) + 1)) =
      2 * ((p : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) -
        (i : ℤ) * (3 * (m : ℤ) + 2)) := by
  have hlow := quintLow_twice m
  have hlowz : (2 : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) =
      ((m : ℤ) + 1) * (3 * (m : ℤ) + 2) := by
    exact_mod_cast hlow
  simp only [quintExp2, ↓reduceIte, quintExpB2]
  linear_combination (-(p : ℤ)) * hlowz

private lemma quintExpA2_negSucc (p i m : ℕ) :
    quintExp2 false p i (-((m : ℤ) + 1)) =
      2 * ((p : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) -
        (i : ℤ) * (3 * (m : ℤ) + 3)) := by
  have hhigh := quintHigh_twice m
  have hhighz : (2 : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) =
      ((m : ℤ) + 1) * (3 * (m : ℤ) + 4) := by
    exact_mod_cast hhigh
  simp only [quintExp2, Bool.false_eq_true, ↓reduceIte, quintExpA2]
  linear_combination (-(p : ℤ)) * hhighz

private lemma quintExpB2_posSucc (p i m : ℕ) :
    quintExp2 true p i ((m : ℤ) + 1) =
      2 * ((p : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) +
        (i : ℤ) * (3 * (m : ℤ) + 4)) := by
  have hhigh := quintHigh_twice m
  have hhighz : (2 : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) =
      ((m : ℤ) + 1) * (3 * (m : ℤ) + 4) := by
    exact_mod_cast hhigh
  simp only [quintExp2, ↓reduceIte, quintExpB2]
  linear_combination (-(p : ℤ)) * hhighz

private lemma eq_iff_two_mul_eq_two_mul (a b : ℤ) :
    a = b ↔ 2 * a = 2 * b := by omega

/-- Signed contribution of one Watson branch to coefficient `q^k`.
`negative = false` is the `A` branch and `negative = true` is the subtracted
`B` branch. -/
noncomputable def quintBilateralTermCoeff (negative : Bool) (p i k : ℕ) (n : ℤ) : ℤ :=
  if quintExp2 negative p i n = 2 * (k : ℤ) then
    if negative then -1 else 1
  else 0

/-- A finite coefficient model for Watson's bilateral quintuple sum.  The
canonical inequalities make `|n| ≤ k+1` a valid coefficient cutoff. -/
noncomputable def quintBilateralCoeff (p i k : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc (-((k + 1 : ℕ) : ℤ)) (k + 1 : ℤ),
    (quintBilateralTermCoeff false p i k n +
      quintBilateralTermCoeff true p i k n)

/-- One paired formal quintuple term is exactly the four Watson branch
contributions at bilateral indices `±(m+1)`. -/
lemma quintDiagonalCoeff_quintTermP_eq_bilateral_pair
    (p i k m : ℕ) (hi : 0 < i) (hp : 2 * i < p) :
    quintDiagonalCoeff p i k (quintTermP m) =
      (quintBilateralTermCoeff false p i k ((m : ℤ) + 1) +
          quintBilateralTermCoeff true p i k ((m : ℤ) + 1)) +
        (quintBilateralTermCoeff false p i k (-((m : ℤ) + 1)) +
          quintBilateralTermCoeff true p i k (-((m : ℤ) + 1))) := by
  let lo : ℕ := (m + 1) * (3 * m + 2) / 2
  let hiExp : ℕ := (m + 1) * (3 * m + 4) / 2
  have hloPlus : (lo : ℤ) ≤ (p : ℤ) * lo + (i : ℤ) * (3 * (m : ℤ) + 3) :=
    quintWeight_plus_ge p i lo (3 * (m : ℤ) + 3) hp (by positivity)
  have hloMinus : (lo : ℤ) ≤ (p : ℤ) * lo - (i : ℤ) * (3 * (m : ℤ) + 2) := by
    simpa only [lo] using quintLow_minus_weight_ge p i m hp
  have hhiMinus : (hiExp : ℤ) ≤
      (p : ℤ) * hiExp - (i : ℤ) * (3 * (m : ℤ) + 3) := by
    simpa only [hiExp] using quintHigh_minus_weight_ge p i m hp
  have hhiPlus : (hiExp : ℤ) ≤
      (p : ℤ) * hiExp + (i : ℤ) * (3 * (m : ℤ) + 4) :=
    quintWeight_plus_ge p i hiExp (3 * (m : ℤ) + 4) hp (by positivity)
  have hc1 : (lo ≤ k ∧
      (p : ℤ) * lo - (i : ℤ) * (-3 * (m : ℤ) - 3) = k) ↔
      (p : ℤ) * lo + (i : ℤ) * (3 * (m : ℤ) + 3) = k := by
    constructor
    · rintro ⟨_, h⟩
      convert h using 1 <;> ring
    · intro h
      constructor
      · exact_mod_cast hloPlus.trans_eq h
      · convert h using 1 <;> ring
  have hc2 : (lo ≤ k ∧
      (p : ℤ) * lo - (i : ℤ) * (3 * (m : ℤ) + 2) = k) ↔
      (p : ℤ) * lo - (i : ℤ) * (3 * (m : ℤ) + 2) = k := by
    constructor
    · exact And.right
    · intro h
      exact ⟨by exact_mod_cast hloMinus.trans_eq h, h⟩
  have hc3 : (hiExp ≤ k ∧
      (p : ℤ) * hiExp - (i : ℤ) * (3 * (m : ℤ) + 3) = k) ↔
      (p : ℤ) * hiExp - (i : ℤ) * (3 * (m : ℤ) + 3) = k := by
    constructor
    · exact And.right
    · intro h
      exact ⟨by exact_mod_cast hhiMinus.trans_eq h, h⟩
  have hc4 : (hiExp ≤ k ∧
      (p : ℤ) * hiExp - (i : ℤ) * (-3 * (m : ℤ) - 4) = k) ↔
      (p : ℤ) * hiExp + (i : ℤ) * (3 * (m : ℤ) + 4) = k := by
    constructor
    · rintro ⟨_, h⟩
      convert h using 1 <;> ring
    · intro h
      constructor
      · exact_mod_cast hhiPlus.trans_eq h
      · convert h using 1 <;> ring
  have heApos :
      (quintExp2 false p i ((m : ℤ) + 1) = 2 * (k : ℤ)) ↔
        (p : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) +
          (i : ℤ) * (3 * (m : ℤ) + 3) = k := by
    rw [quintExpA2_posSucc]
    omega
  have heBpos :
      (quintExp2 true p i ((m : ℤ) + 1) = 2 * (k : ℤ)) ↔
        (p : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) +
          (i : ℤ) * (3 * (m : ℤ) + 4) = k := by
    rw [quintExpB2_posSucc]
    omega
  have heAneg :
      (quintExp2 false p i (-((m : ℤ) + 1)) = 2 * (k : ℤ)) ↔
        (p : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) -
          (i : ℤ) * (3 * (m : ℤ) + 3) = k := by
    rw [quintExpA2_negSucc]
    omega
  have heBneg :
      (quintExp2 true p i (-((m : ℤ) + 1)) = 2 * (k : ℤ)) ↔
        (p : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) -
          (i : ℤ) * (3 * (m : ℤ) + 2) = k := by
    rw [quintExpB2_negSucc]
    omega
  have hc1raw : (((m + 1) * (3 * m + 2) / 2) ≤ k ∧
      (p : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) -
        (i : ℤ) * (-3 * (m : ℤ) - 3) = k) ↔
      (p : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) +
        (i : ℤ) * (3 * (m : ℤ) + 3) = k := by
    simpa only [lo] using hc1
  have hc2raw : (((m + 1) * (3 * m + 2) / 2) ≤ k ∧
      (p : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) -
        (i : ℤ) * (3 * (m : ℤ) + 2) = k) ↔
      (p : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) -
        (i : ℤ) * (3 * (m : ℤ) + 2) = k := by
    simpa only [lo] using hc2
  have hc3raw : (((m + 1) * (3 * m + 4) / 2) ≤ k ∧
      (p : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) -
        (i : ℤ) * (3 * (m : ℤ) + 3) = k) ↔
      (p : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) -
        (i : ℤ) * (3 * (m : ℤ) + 3) = k := by
    simpa only [hiExp] using hc3
  have hc4raw : (((m + 1) * (3 * m + 4) / 2) ≤ k ∧
      (p : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) -
        (i : ℤ) * (-3 * (m : ℤ) - 4) = k) ↔
      (p : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) +
        (i : ℤ) * (3 * (m : ℤ) + 4) = k := by
    simpa only [hiExp] using hc4
  have hd1 : quintDiagonalCoeff p i k
      (X ^ ((m + 1) * (3 * m + 2) / 2) *
        PowerSeries.C (T (-3 * (m : ℤ) - 3))) =
      if (p : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) +
        (i : ℤ) * (3 * (m : ℤ) + 3) = k then 1 else 0 := by
    rw [quintDiagonalCoeff_monomial hi]
    simp only [hc1raw]
  have hd2 : quintDiagonalCoeff p i k
      (X ^ ((m + 1) * (3 * m + 2) / 2) *
        PowerSeries.C (T (3 * (m : ℤ) + 2))) =
      if (p : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) -
        (i : ℤ) * (3 * (m : ℤ) + 2) = k then 1 else 0 := by
    rw [quintDiagonalCoeff_monomial hi]
    simp only [hc2raw]
  have hd3 : quintDiagonalCoeff p i k
      (X ^ ((m + 1) * (3 * m + 4) / 2) *
        PowerSeries.C (T (3 * (m : ℤ) + 3))) =
      if (p : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) -
        (i : ℤ) * (3 * (m : ℤ) + 3) = k then 1 else 0 := by
    rw [quintDiagonalCoeff_monomial hi]
    simp only [hc3raw]
  have hd4 : quintDiagonalCoeff p i k
      (X ^ ((m + 1) * (3 * m + 4) / 2) *
        PowerSeries.C (T (-3 * (m : ℤ) - 4))) =
      if (p : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) +
        (i : ℤ) * (3 * (m : ℤ) + 4) = k then 1 else 0 := by
    rw [quintDiagonalCoeff_monomial hi]
    simp only [hc4raw]
  have hbApos : quintBilateralTermCoeff false p i k ((m : ℤ) + 1) =
      if (p : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) +
        (i : ℤ) * (3 * (m : ℤ) + 3) = k then 1 else 0 := by
    simp only [quintBilateralTermCoeff, Bool.false_eq_true, ↓reduceIte, heApos]
  have hbBpos : quintBilateralTermCoeff true p i k ((m : ℤ) + 1) =
      -(if (p : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) +
        (i : ℤ) * (3 * (m : ℤ) + 4) = k then 1 else 0) := by
    simp only [quintBilateralTermCoeff, ↓reduceIte, heBpos]
    split_ifs <;> simp
  have hbAneg : quintBilateralTermCoeff false p i k (-((m : ℤ) + 1)) =
      if (p : ℤ) * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) -
        (i : ℤ) * (3 * (m : ℤ) + 3) = k then 1 else 0 := by
    simp only [quintBilateralTermCoeff, Bool.false_eq_true, ↓reduceIte, heAneg]
  have hbBneg : quintBilateralTermCoeff true p i k (-((m : ℤ) + 1)) =
      -(if (p : ℤ) * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) -
        (i : ℤ) * (3 * (m : ℤ) + 2) = k then 1 else 0) := by
    simp only [quintBilateralTermCoeff, ↓reduceIte, heBneg]
    split_ifs <;> simp
  rw [quintTermP, quintDiagonalCoeff_add, mul_sub, mul_sub,
    quintDiagonalCoeff_sub, quintDiagonalCoeff_sub, hd1, hd2, hd3, hd4,
    hbApos, hbBpos, hbAneg, hbBneg]
  ring

lemma quintDiagonalCoeff_quintBase_eq_bilateral_zero
    (p i k : ℕ) (hi : 0 < i) :
    quintDiagonalCoeff p i k quintBase =
      quintBilateralTermCoeff false p i k 0 +
        quintBilateralTermCoeff true p i k 0 := by
  have hC0 : (PowerSeries.C (T (0 : ℤ)) :
      PowerSeries (LaurentPolynomial ℤ)) = X ^ 0 * PowerSeries.C (T (0 : ℤ)) := by simp
  have hCm1 : (PowerSeries.C (T (-1 : ℤ)) :
      PowerSeries (LaurentPolynomial ℤ)) = X ^ 0 * PowerSeries.C (T (-1 : ℤ)) := by simp
  rw [quintBase, hC0, hCm1, quintDiagonalCoeff_sub,
    quintDiagonalCoeff_monomial hi, quintDiagonalCoeff_monomial hi]
  simp only [quintBilateralTermCoeff, quintExp2, quintExpA2, quintExpB2,
    Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> omega

/-- **Bilateral side of the specialization bridge.**  The finite diagonal of
the formal quintuple theta is exactly Watson's signed two-branch coefficient. -/
theorem quintDiagonalCoeff_quintTheta_eq_bilateral
    (p i k : ℕ) (hi : 0 < i) (hp : 2 * i < p) :
    quintDiagonalCoeff p i k quintTheta = quintBilateralCoeff p i k := by
  rw [quintDiagonalCoeff_quintTheta_eq_finite, quintFiniteP,
    quintDiagonalCoeff_add, quintDiagonalCoeff_sum,
    quintDiagonalCoeff_quintBase_eq_bilateral_zero p i k hi]
  have hterms :
      (∑ m ∈ Finset.range (k + 1), quintDiagonalCoeff p i k (quintTermP m)) =
        ∑ m ∈ Finset.range (k + 1),
          ((quintBilateralTermCoeff false p i k ((m : ℤ) + 1) +
              quintBilateralTermCoeff true p i k ((m : ℤ) + 1)) +
            (quintBilateralTermCoeff false p i k (-((m : ℤ) + 1)) +
              quintBilateralTermCoeff true p i k (-((m : ℤ) + 1)))) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact quintDiagonalCoeff_quintTermP_eq_bilateral_pair p i k m hi hp
  rw [hterms, quintBilateralCoeff]
  norm_num [Nat.cast_add, Nat.cast_one]
  have hsum := sum_Icc_neg_nat_nat
    (fun n => quintBilateralTermCoeff false p i k n +
      quintBilateralTermCoeff true p i k n) (k + 1)
  norm_num [Nat.cast_add, Nat.cast_one] at hsum
  rw [hsum]

/-- The five formal factors on the left of the completed quintuple identity. -/
noncomputable def formalQuintupleProduct : PowerSeries (LaurentPolynomial ℤ) :=
  qfacInfL * qzProdAInf * (PowerSeries.map invertHom qzProdBInf) *
    jtp2ProdInf * (PowerSeries.map invertHom jtp2ProdInf)

/-- The completed formal quintuple identity remains valid on every finite
specialization diagonal.  No convergence or infinite rearrangement is used. -/
theorem quintDiagonalCoeff_formalProduct_eq_theta (p i k : ℕ) :
    quintDiagonalCoeff p i k formalQuintupleProduct =
      quintDiagonalCoeff p i k quintTheta := by
  apply quintDiagonalCoeff_congr
  exact formal_quintuple_product_identity

/-! ### Positive-cone transport to the one-variable Pochhammer product -/

/-- One summand in the finite specialization diagonal. -/
noncomputable def dterm (p i k : ℕ)
    (A : PowerSeries (LaurentPolynomial ℤ)) (n : ℕ) : ℤ :=
  if (i : ℤ) ∣ (p : ℤ) * n - k then
    coeff n A (((p : ℤ) * n - k) / (i : ℤ))
  else 0

/-- The positive weight cone for `q ↦ q^p`, `z ↦ q⁻ⁱ`: every supported
bivariate monomial has specialized weight at least its outer `q`-degree. -/
def wcone (p i : ℕ) (A : PowerSeries (LaurentPolynomial ℤ)) : Prop :=
  ∀ n d, (coeff n A : LaurentPolynomial ℤ) d ≠ 0 →
    (n : ℤ) ≤ (p : ℤ) * n - (i : ℤ) * d

lemma coeff_mul_bimonomial (A : PowerSeries (LaurentPolynomial ℤ))
    (a n : ℕ) (d e : ℤ) :
    (coeff n (A * (X ^ a * PowerSeries.C (T d))) : LaurentPolynomial ℤ) e =
      if a ≤ n then (coeff (n - a) A : LaurentPolynomial ℤ) (e - d) else 0 := by
  rw [show A * (X ^ a * PowerSeries.C (T d)) =
      X ^ a * A * PowerSeries.C (T d) by ring,
    PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [LaurentPolynomial.T, AddMonoidAlgebra.mul_single_apply, mul_one]
    congr 2
  · rw [zero_mul]
    rfl

lemma dterm_mul_bimonomial {p i a w : ℕ} {d : ℤ}
    (A : PowerSeries (LaurentPolynomial ℤ))
    (hi : 0 < i) (hcone : wcone p i A)
    (hw : (w : ℤ) = (p : ℤ) * a - (i : ℤ) * d)
    (k m : ℕ) :
    dterm p i k (A * (X ^ a * PowerSeries.C (T d))) (m + a) =
      if w ≤ k then dterm p i (k - w) A m else 0 := by
  rw [dterm, dterm]
  by_cases hwk : w ≤ k
  · simp only [hwk, if_true]
    norm_num [Nat.cast_add, Nat.cast_sub hwk]
    let L : ℤ := (p : ℤ) * ((m : ℤ) + a) - k
    let R : ℤ := (p : ℤ) * m - ((k : ℤ) - w)
    have hLR : L = R + (i : ℤ) * d := by
      dsimp [L, R]
      rw [hw]
      ring
    have hdiv : ((i : ℤ) ∣ L) ↔ ((i : ℤ) ∣ R) := by
      rw [hLR]
      simp
    by_cases hdv : (i : ℤ) ∣ L
    · have hdv' := hdiv.mp hdv
      rw [if_pos hdv, if_pos hdv', coeff_mul_bimonomial, if_pos (by omega)]
      simp only [Nat.add_sub_cancel_right]
      congr 2
      apply mul_left_cancel₀ (show (i : ℤ) ≠ 0 by omega)
      have hL := Int.ediv_mul_cancel hdv
      have hR := Int.ediv_mul_cancel hdv'
      rw [mul_sub, mul_comm (i : ℤ) (L / i), hL,
        mul_comm (i : ℤ) (R / i), hR]
      exact (sub_eq_iff_eq_add).2 hLR
    · rw [if_neg hdv, if_neg (mt hdiv.mpr hdv)]
  · rw [if_neg hwk]
    by_cases hdv : (i : ℤ) ∣ (p : ℤ) * ((m + a : ℕ) : ℤ) - k
    · rw [if_pos hdv]
      norm_num [Nat.cast_add] at hdv ⊢
      rw [coeff_mul_bimonomial, if_pos (by omega), Nat.add_sub_cancel_right]
      apply Classical.byContradiction
      intro hne
      have hc := hcone m
        (((p : ℤ) * ((m : ℤ) + a) - k) / (i : ℤ) - d) hne
      have hL := Int.ediv_mul_cancel hdv
      rw [mul_comm] at hL
      have hwkz : (k : ℤ) < w := by exact_mod_cast Nat.lt_of_not_ge hwk
      push_cast at hc hL
      nlinarith [hw, hwkz]
    · rw [if_neg hdv]

lemma wcone_one (p i : ℕ) : wcone p i 1 := by
  intro n d h
  by_cases hn : n = 0
  · subst n
    simp only [PowerSeries.coeff_zero_one] at h
    have hd : d = 0 := by
      by_contra hd
      change (LaurentPolynomial.C 1 : LaurentPolynomial ℤ) d ≠ 0 at h
      rw [LaurentPolynomial.C_apply, if_neg hd] at h
      exact h rfl
    subst d
    simp
  · rw [PowerSeries.coeff_one, if_neg hn] at h
    exact (h rfl).elim

lemma wcone_mul_factor {p i a w : ℕ} {d : ℤ}
    {A : PowerSeries (LaurentPolynomial ℤ)}
    (hcone : wcone p i A) (haw : a ≤ w)
    (hw : (w : ℤ) = (p : ℤ) * a - (i : ℤ) * d) :
    wcone p i (A * (1 - X ^ a * PowerSeries.C (T d))) := by
  intro n e hne
  rw [mul_sub, mul_one, map_sub] at hne
  change (coeff n A : LaurentPolynomial ℤ) e -
      (coeff n (A * (X ^ a * PowerSeries.C (T d))) : LaurentPolynomial ℤ) e ≠ 0 at hne
  rw [coeff_mul_bimonomial] at hne
  by_cases hA : (coeff n A : LaurentPolynomial ℤ) e ≠ 0
  · exact hcone n e hA
  · by_cases han : a ≤ n
    · rw [if_pos han] at hne
      have hAz : (coeff n A : LaurentPolynomial ℤ) e = 0 := not_ne_iff.mp hA
      have hshift : (coeff (n - a) A : LaurentPolynomial ℤ) (e - d) ≠ 0 := by
        intro hz
        rw [hz, hAz, sub_zero] at hne
        exact hne rfl
      have hc := hcone (n - a) (e - d) hshift
      have hawz : (a : ℤ) ≤ w := by exact_mod_cast haw
      norm_num [Nat.cast_sub han] at hc
      nlinarith [hw]
    · rw [if_neg han, sub_zero] at hne
      exact (hA hne).elim

lemma dterm_eq_zero_of_lt_degree {p i k n : ℕ}
    {A : PowerSeries (LaurentPolynomial ℤ)}
    (hcone : wcone p i A) (hkn : k < n) :
    dterm p i k A n = 0 := by
  rw [dterm]
  by_cases hdv : (i : ℤ) ∣ (p : ℤ) * n - k
  · rw [if_pos hdv]
    apply Classical.byContradiction
    intro hne
    have hc := hcone n (((p : ℤ) * n - k) / (i : ℤ)) hne
    have hdiv := Int.ediv_mul_cancel hdv
    rw [mul_comm] at hdiv
    push_cast at hc hdiv
    nlinarith
  · rw [if_neg hdv]

lemma dterm_mul_bimonomial_of_lt {p i k a : ℕ} {d : ℤ}
    (A : PowerSeries (LaurentPolynomial ℤ)) {n : ℕ} (hna : n < a) :
    dterm p i k (A * (X ^ a * PowerSeries.C (T d))) n = 0 := by
  rw [dterm]
  by_cases hdv : (i : ℤ) ∣ (p : ℤ) * n - k
  · rw [if_pos hdv, coeff_mul_bimonomial, if_neg (by omega)]
  · rw [if_neg hdv]

/-- Multiplication by one bivariate factor has exactly the same finite-diagonal
recurrence as multiplication by its specialized one-variable factor. -/
lemma quintDiagonalCoeff_mul_bimonomial {p i a w : ℕ} {d : ℤ}
    (A : PowerSeries (LaurentPolynomial ℤ))
    (hi : 0 < i) (hcone : wcone p i A) (haw : a ≤ w)
    (hw : (w : ℤ) = (p : ℤ) * a - (i : ℤ) * d) (k : ℕ) :
    quintDiagonalCoeff p i k (A * (X ^ a * PowerSeries.C (T d))) =
      if w ≤ k then quintDiagonalCoeff p i (k - w) A else 0 := by
  rw [quintDiagonalCoeff]
  change (∑ n ∈ Finset.range (k + 1),
      dterm p i k (A * (X ^ a * PowerSeries.C (T d))) n) = _
  by_cases hwk : w ≤ k
  · rw [if_pos hwk, quintDiagonalCoeff]
    let s := Finset.image (fun m : ℕ => m + a) (Finset.range (k - w + 1))
    have hs : s ⊆ Finset.range (k + 1) := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
      rw [Finset.mem_range] at hm ⊢
      omega
    have hout : ∀ n ∈ Finset.range (k + 1), n ∉ s →
        dterm p i k (A * (X ^ a * PowerSeries.C (T d))) n = 0 := by
      intro n hn hnout
      by_cases han : a ≤ n
      · have hrepr : n - a + a = n := Nat.sub_add_cancel han
        rw [← hrepr,
          show dterm p i k (A * (X ^ a * PowerSeries.C (T d))) ((n - a) + a) =
            dterm p i (k - w) A (n - a) from by
              simpa [hwk] using dterm_mul_bimonomial A hi hcone hw k (n - a)]
        apply dterm_eq_zero_of_lt_degree hcone
        have hmnot : n - a ∉ Finset.range (k - w + 1) := by
          intro hm
          apply hnout
          exact Finset.mem_image.mpr ⟨n - a, hm, hrepr⟩
        rw [Finset.mem_range] at hmnot
        omega
      · exact dterm_mul_bimonomial_of_lt A (by omega)
    calc
      ∑ n ∈ Finset.range (k + 1),
          dterm p i k (A * (X ^ a * PowerSeries.C (T d))) n =
          ∑ n ∈ s, dterm p i k (A * (X ^ a * PowerSeries.C (T d))) n := by
            symm
            exact Finset.sum_subset hs hout
      _ = ∑ m ∈ Finset.range (k - w + 1),
          dterm p i k (A * (X ^ a * PowerSeries.C (T d))) (m + a) := by
            apply Finset.sum_image
            intro x hx y hy hxy
            exact Nat.add_right_cancel hxy
      _ = ∑ m ∈ Finset.range (k - w + 1), dterm p i (k - w) A m := by
            apply Finset.sum_congr rfl
            intro m hm
            simpa [hwk] using dterm_mul_bimonomial A hi hcone hw k m
  · rw [if_neg hwk]
    apply Finset.sum_eq_zero
    intro n hn
    by_cases han : a ≤ n
    · have hrepr : n - a + a = n := Nat.sub_add_cancel han
      rw [← hrepr]
      simpa [hwk] using dterm_mul_bimonomial A hi hcone hw k (n - a)
    · exact dterm_mul_bimonomial_of_lt A (by omega)

/-- `A` and `B` are related by the coefficientwise specialization
`q ↦ q^p`, `z ↦ q⁻ⁱ`, with the positive cone carried as an invariant. -/
def diagonalSpecializes (p i : ℕ)
    (A : PowerSeries (LaurentPolynomial ℤ)) (B : PowerSeries ℤ) : Prop :=
  wcone p i A ∧ ∀ k, quintDiagonalCoeff p i k A = coeff k B

lemma diagonalSpecializes_one (p i : ℕ) (hi : 0 < i) :
    diagonalSpecializes p i 1 1 := by
  constructor
  · exact wcone_one p i
  · intro k
    have hone : (1 : PowerSeries (LaurentPolynomial ℤ)) =
        X ^ 0 * PowerSeries.C (T (0 : ℤ)) := by simp
    rw [hone, quintDiagonalCoeff_monomial hi]
    by_cases hk : k = 0
    · subst k
      simp
    · have hkz : (0 : ℤ) ≠ k := by exact_mod_cast Ne.symm hk
      simp [PowerSeries.coeff_one, hk, hkz]

lemma coeff_mul_one_sub_Xpow (B : PowerSeries ℤ) (w k : ℕ) :
    coeff k (B * (1 - X ^ w)) =
      coeff k B - if w ≤ k then coeff (k - w) B else 0 := by
  rw [mul_sub, mul_one, map_sub,
    show B * X ^ w = X ^ w * B by ring,
    PowerSeries.coeff_X_pow_mul']

lemma diagonalSpecializes_mul_factor {p i a w : ℕ} {d : ℤ}
    {A : PowerSeries (LaurentPolynomial ℤ)} {B : PowerSeries ℤ}
    (hi : 0 < i) (hAB : diagonalSpecializes p i A B) (haw : a ≤ w)
    (hw : (w : ℤ) = (p : ℤ) * a - (i : ℤ) * d) :
    diagonalSpecializes p i
      (A * (1 - X ^ a * PowerSeries.C (T d)))
      (B * (1 - X ^ w)) := by
  constructor
  · exact wcone_mul_factor hAB.1 haw hw
  · intro k
    rw [mul_sub, mul_one, quintDiagonalCoeff_sub,
      quintDiagonalCoeff_mul_bimonomial A hi hAB.1 haw hw,
      coeff_mul_one_sub_Xpow, hAB.2 k]
    by_cases hwk : w ≤ k
    · simp only [if_pos hwk]
      rw [hAB.2 (k - w)]
    · simp only [if_neg hwk, sub_zero]

/-- Finite products preserve exact coefficient specialization. -/
lemma diagonalSpecializes_mul_prod {p i : ℕ} {A : PowerSeries (LaurentPolynomial ℤ)}
    {B : PowerSeries ℤ} (hi : 0 < i) (hAB : diagonalSpecializes p i A B)
    {s : Finset ℕ} (a w : ℕ → ℕ) (d : ℕ → ℤ)
    (haw : ∀ r ∈ s, a r ≤ w r)
    (hw : ∀ r ∈ s, ((w r : ℕ) : ℤ) =
      (p : ℤ) * a r - (i : ℤ) * d r) :
    diagonalSpecializes p i
      (A * ∏ r ∈ s, (1 - X ^ (a r) * PowerSeries.C (T (d r))))
      (B * ∏ r ∈ s, (1 - X ^ (w r))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hAB
  | @insert r s hrs ih =>
      have hsaw : ∀ x ∈ s, a x ≤ w x := by
        intro x hx
        exact haw x (Finset.mem_insert_of_mem hx)
      have hsw : ∀ x ∈ s, ((w x : ℕ) : ℤ) =
          (p : ℤ) * a x - (i : ℤ) * d x := by
        intro x hx
        exact hw x (Finset.mem_insert_of_mem hx)
      have hrest := ih hsaw hsw
      have hadd := diagonalSpecializes_mul_factor hi hrest
        (haw r (Finset.mem_insert_self r s)) (hw r (Finset.mem_insert_self r s))
      rw [Finset.prod_insert hrs, Finset.prod_insert hrs]
      convert hadd using 1 <;> ring

/-- The five finite bivariate factors, written directly in their Laurent form. -/
noncomputable def bivariateQuintupleFinite (N : ℕ) :
    PowerSeries (LaurentPolynomial ℤ) :=
  (∏ r ∈ Finset.range N, (1 - X ^ (r + 1) * PowerSeries.C (T 0))) *
  (∏ r ∈ Finset.range N, (1 - X ^ (r + 1) * PowerSeries.C (T 1))) *
  (∏ r ∈ Finset.range N, (1 - X ^ r * PowerSeries.C (T (-1)))) *
  (∏ r ∈ Finset.range N, (1 - X ^ (2 * r + 1) * PowerSeries.C (T 2))) *
  (∏ r ∈ Finset.range N, (1 - X ^ (2 * r + 1) * PowerSeries.C (T (-2))))

/-- The corresponding five finite one-variable factors after specialization. -/
noncomputable def univariateQuintupleFinite (p i N : ℕ) : PowerSeries ℤ :=
  (∏ r ∈ Finset.range N, (1 - X ^ (p + p * r))) *
  (∏ r ∈ Finset.range N, (1 - X ^ (p - i + p * r))) *
  (∏ r ∈ Finset.range N, (1 - X ^ (i + p * r))) *
  (∏ r ∈ Finset.range N, (1 - X ^ (p - 2 * i + 2 * p * r))) *
  (∏ r ∈ Finset.range N, (1 - X ^ (p + 2 * i + 2 * p * r)))

theorem diagonalSpecializes_quintupleFinite (p i N : ℕ)
    (hi : 0 < i) (hp : 2 * i < p) :
    diagonalSpecializes p i (bivariateQuintupleFinite N)
      (univariateQuintupleFinite p i N) := by
  have hp1 : 1 ≤ p := by omega
  have hip : i ≤ p := by omega
  have h2ip : 2 * i ≤ p := by omega
  have h0 := diagonalSpecializes_one p i hi
  have h1 := diagonalSpecializes_mul_prod hi h0
    (fun r => r + 1) (fun r => p + p * r) (fun _ => 0)
    (s := Finset.range N) (by
      intro r hr
      dsimp
      have hrp : r ≤ p * r := Nat.le_mul_of_pos_left r hp1
      omega) (by
      intro r hr
      push_cast
      ring)
  have h2 := diagonalSpecializes_mul_prod hi h1
    (fun r => r + 1) (fun r => p - i + p * r) (fun _ => 1)
    (s := Finset.range N) (by
      intro r hr
      dsimp
      have hrp : r ≤ p * r := Nat.le_mul_of_pos_left r hp1
      omega) (by
      intro r hr
      norm_num [Nat.cast_sub hip]
      ring)
  have h3 := diagonalSpecializes_mul_prod hi h2
    (fun r => r) (fun r => i + p * r) (fun _ => -1)
    (s := Finset.range N) (by
      intro r hr
      dsimp
      have hrp : r ≤ p * r := Nat.le_mul_of_pos_left r hp1
      omega) (by
      intro r hr
      push_cast
      ring)
  have h4 := diagonalSpecializes_mul_prod hi h3
    (fun r => 2 * r + 1) (fun r => p - 2 * i + 2 * p * r) (fun _ => 2)
    (s := Finset.range N) (by
      intro r hr
      dsimp
      have hrp : r ≤ p * r := Nat.le_mul_of_pos_left r hp1
      have hrp2 : 2 * r ≤ 2 * (p * r) := Nat.mul_le_mul_left 2 hrp
      have hbase : 1 ≤ p - 2 * i := Nat.sub_pos_of_lt hp
      nlinarith) (by
      intro r hr
      norm_num [Nat.cast_sub h2ip]
      ring)
  have h5 := diagonalSpecializes_mul_prod hi h4
    (fun r => 2 * r + 1) (fun r => p + 2 * i + 2 * p * r) (fun _ => -2)
    (s := Finset.range N) (by
      intro r hr
      dsimp
      have hrp : r ≤ p * r := Nat.le_mul_of_pos_left r hp1
      have hrp2 : 2 * r ≤ 2 * (p * r) := Nat.mul_le_mul_left 2 hrp
      nlinarith) (by
      intro r hr
      push_cast
      ring)
  convert h5 using 1 <;> simp only [bivariateQuintupleFinite,
    univariateQuintupleFinite, one_mul]

/-- A common finite truncation of the five formal factors. -/
noncomputable def formalQuintupleFinite (N : ℕ) :
    PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.map LaurentPolynomial.C (qfac N) * qzProdA N *
    PowerSeries.map invertHom (qzProdB N) * jtp2Prod N *
    PowerSeries.map invertHom (jtp2Prod N)

private lemma invertHom_T_local (d : ℤ) : invertHom (T d) = T (-d) := by
  rw [LaurentPolynomial.T, invert_single]
  rfl

lemma bivariateQuintupleFinite_eq_formal (N : ℕ) :
    bivariateQuintupleFinite N = formalQuintupleFinite N := by
  simp [bivariateQuintupleFinite, formalQuintupleFinite, qfac, qzProdA,
    qzProdB, jtp2Prod, map_prod, map_sub, map_mul, map_pow, invertHom_T_local]

lemma univariateQuintupleFinite_eq_pochhammer (p i N : ℕ) :
    univariateQuintupleFinite p i N =
      pochhammerProductFinite
        [(i, p), (p - i, p), (p, p),
          (p + 2 * i, 2 * p), (p - 2 * i, 2 * p)] N := by
  simp [univariateQuintupleFinite, pochhammerProductFinite, pochhammerFinite]
  ring

theorem diagonalSpecializes_formalQuintupleFinite (p i N : ℕ)
    (hi : 0 < i) (hp : 2 * i < p) :
    diagonalSpecializes p i (formalQuintupleFinite N)
      (pochhammerProductFinite
        [(i, p), (p - i, p), (p, p),
          (p + 2 * i, 2 * p), (p - 2 * i, 2 * p)] N) := by
  rw [← bivariateQuintupleFinite_eq_formal,
    ← univariateQuintupleFinite_eq_pochhammer]
  exact diagonalSpecializes_quintupleFinite p i N hi hp

lemma coeff_mul_congr_upto {R : Type*} [CommRing R] {k : ℕ}
    {A A' B B' : PowerSeries R}
    (hA : ∀ j ≤ k, coeff j A = coeff j A')
    (hB : ∀ j ≤ k, coeff j B = coeff j B') :
    coeff k (A * B) = coeff k (A' * B') := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro pair hpair
  have hsum := Finset.mem_antidiagonal.mp hpair
  rw [hA pair.1 (by omega), hB pair.2 (by omega)]

lemma coeff_formalQuintupleProduct_eq_finite {k N : ℕ} (hN : k + 1 ≤ N) :
    coeff k formalQuintupleProduct = coeff k (formalQuintupleFinite N) := by
  have hqfac : ∀ j ≤ k, coeff j qfacInfL =
      coeff j (PowerSeries.map LaurentPolynomial.C (qfac N)) := by
    intro j hj
    simp only [qfacInfL, PowerSeries.coeff_map]
    rw [coeff_qfacInf (show j + 1 ≤ N by omega)]
  have hqzA : ∀ j ≤ k, coeff j qzProdAInf = coeff j (qzProdA N) := by
    intro j hj
    exact coeff_qzProdAInf (show j + 1 ≤ N by omega)
  have hqzB : ∀ j ≤ k,
      coeff j (PowerSeries.map invertHom qzProdBInf) =
        coeff j (PowerSeries.map invertHom (qzProdB N)) := by
    intro j hj
    simp only [PowerSeries.coeff_map]
    rw [coeff_qzProdBInf (show j + 1 ≤ N by omega)]
  have hjtp : ∀ j ≤ k, coeff j jtp2ProdInf = coeff j (jtp2Prod N) := by
    intro j hj
    exact coeff_jtp2ProdInf (show j + 1 ≤ N by omega)
  have hjtpInv : ∀ j ≤ k,
      coeff j (PowerSeries.map invertHom jtp2ProdInf) =
        coeff j (PowerSeries.map invertHom (jtp2Prod N)) := by
    intro j hj
    simp only [PowerSeries.coeff_map]
    rw [coeff_jtp2ProdInf (show j + 1 ≤ N by omega)]
  have h12 : ∀ j ≤ k, coeff j (qfacInfL * qzProdAInf) =
      coeff j (PowerSeries.map LaurentPolynomial.C (qfac N) * qzProdA N) := by
    intro j hj
    exact coeff_mul_congr_upto (fun x hx => hqfac x (hx.trans hj))
      (fun x hx => hqzA x (hx.trans hj))
  have h123 : ∀ j ≤ k,
      coeff j (qfacInfL * qzProdAInf * PowerSeries.map invertHom qzProdBInf) =
      coeff j (PowerSeries.map LaurentPolynomial.C (qfac N) * qzProdA N *
        PowerSeries.map invertHom (qzProdB N)) := by
    intro j hj
    exact coeff_mul_congr_upto (fun x hx => h12 x (hx.trans hj))
      (fun x hx => hqzB x (hx.trans hj))
  have h1234 : ∀ j ≤ k,
      coeff j (qfacInfL * qzProdAInf * PowerSeries.map invertHom qzProdBInf *
        jtp2ProdInf) =
      coeff j (PowerSeries.map LaurentPolynomial.C (qfac N) * qzProdA N *
        PowerSeries.map invertHom (qzProdB N) * jtp2Prod N) := by
    intro j hj
    exact coeff_mul_congr_upto (fun x hx => h123 x (hx.trans hj))
      (fun x hx => hjtp x (hx.trans hj))
  rw [formalQuintupleProduct, formalQuintupleFinite]
  exact coeff_mul_congr_upto (fun x hx => h1234 x hx) (fun x hx => hjtpInv x hx)

lemma quintDiagonalCoeff_formalProduct_eq_finite (p i k N : ℕ)
    (hN : k + 1 ≤ N) :
    quintDiagonalCoeff p i k formalQuintupleProduct =
      quintDiagonalCoeff p i k (formalQuintupleFinite N) := by
  rw [quintDiagonalCoeff]
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n + 1 ≤ N := by
    have := Finset.mem_range.mp hn
    omega
  by_cases hdv : (i : ℤ) ∣ (p : ℤ) * n - k
  · rw [if_pos hdv, if_pos hdv, coeff_formalQuintupleProduct_eq_finite hnle]
  · rw [if_neg hdv, if_neg hdv]

/-- The formal product diagonal is Watson's finite bilateral coefficient. -/
theorem quintDiagonalCoeff_formalProduct_eq_bilateral
    (p i k : ℕ) (hi : 0 < i) (hp : 2 * i < p) :
    quintDiagonalCoeff p i k formalQuintupleProduct = quintBilateralCoeff p i k := by
  rw [quintDiagonalCoeff_formalProduct_eq_theta,
    quintDiagonalCoeff_quintTheta_eq_bilateral p i k hi hp]

/-- **Complete coefficient specialization bridge.**  For `0 < i` and
`2i < p`, the actual stabilized five-Pochhammer product `Q(q^i,q^p)` has
exactly Watson's finite signed bilateral coefficient at every `q^k`. -/
theorem coeff_quintupleSpecialized_eq_bilateral
    (p i k : ℕ) (hi : 0 < i) (hp : 2 * i < p) :
    coeff k (quintupleSpecialized p i) = quintBilateralCoeff p i k := by
  let factors : List (ℕ × ℕ) :=
    [(i, p), (p - i, p), (p, p),
      (p + 2 * i, 2 * p), (p - 2 * i, 2 * p)]
  have hvalid : ∀ factor ∈ factors, 0 < factor.1 ∧ 0 < factor.2 := by
    intro factor hfactor
    simp only [factors, List.mem_cons, List.not_mem_nil, or_false] at hfactor
    rcases hfactor with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  have hspec := diagonalSpecializes_formalQuintupleFinite p i (k + 1) hi hp
  change diagonalSpecializes p i (formalQuintupleFinite (k + 1))
      (pochhammerProductFinite factors (k + 1)) at hspec
  calc
    coeff k (quintupleSpecialized p i) =
        coeff k (pochhammerProductFinite factors (k + 1)) := by
      rw [quintupleSpecialized]
      exact coeff_pochhammerProductInf hvalid (le_refl (k + 1))
    _ = quintDiagonalCoeff p i k (formalQuintupleFinite (k + 1)) :=
      (hspec.2 k).symm
    _ = quintDiagonalCoeff p i k formalQuintupleProduct :=
      (quintDiagonalCoeff_formalProduct_eq_finite p i k (k + 1) (le_refl (k + 1))).symm
    _ = quintBilateralCoeff p i k :=
      quintDiagonalCoeff_formalProduct_eq_bilateral p i k hi hp

end Ramanujan.MultiQuintuple
