import RamanujanTau.TheoremA.BinaryTheta
import Mathlib.Algebra.Polynomial.Homogenize

/-!
# Homogeneous Hasse divisibility

Homogenization transfers the proved affine-chart criterion to binary forms.
The Hasse polynomial takes value one at (1,0), so its chart has full degree:
no factor at infinity is lost. Consequently a homogeneous form is divisible
by Hasse exactly when its chart is, and theta introduces no Hasse factor
away from weights divisible by p.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open MvPolynomial

private theorem eval_homogenize_one_zero {F : Type*} [Field F]
    (f : Polynomial F) (n : ℕ) : eval ![1, 0] (f.homogenize n) = f.coeff n := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [Polynomial.homogenize_add, map_add, hf, hg, Polynomial.coeff_add]
  | monomial i c =>
    by_cases hi : i ≤ n
    · rw [Polynomial.homogenize_monomial hi, ModP.monomial_eq_two]
      by_cases he : i = n
      · subst i
        simp
      · have hni : n - i ≠ 0 := by omega
        simp [hni, Polynomial.coeff_monomial, he]
    · rw [Polynomial.homogenize_monomial_of_lt (by omega)]
      simp [Polynomial.coeff_monomial, show i ≠ n by omega]

theorem homogeneous_chartT_reconstruct {F : Type*} [Field F]
    {P : MvPolynomial (Fin 2) F} {k : ℕ} (hP : BinaryHomogeneous P k) :
    (Igusa.chartT P).homogenize k = P :=
  Polynomial.homogenize_eq_of_isHomogeneous hP rfl

theorem homogeneous_chartT_degree_le {F : Type*} [Field F]
    {P : MvPolynomial (Fin 2) F} {k : ℕ} (hP : BinaryHomogeneous P k) :
    (Igusa.chartT P).natDegree ≤ k := by
  apply Igusa.natDegree_chartT_le
  intro s hs
  have hw := hP (mem_support_iff.mp hs)
  rw [binary_weight] at hw
  omega

theorem homogeneous_chartT_top_coeff {F : Type*} [Field F]
    {P : MvPolynomial (Fin 2) F} {k : ℕ} (hP : BinaryHomogeneous P k) :
    (Igusa.chartT P).coeff k = eval ![1, 0] P := by
  rw [← eval_homogenize_one_zero, homogeneous_chartT_reconstruct hP]

theorem homogeneous_chartT_degree_eq {F : Type*} [Field F]
    {P : MvPolynomial (Fin 2) F} {k : ℕ} (hP : BinaryHomogeneous P k)
    (hTop : eval ![1, 0] P ≠ 0) : (Igusa.chartT P).natDegree = k := by
  apply le_antisymm (homogeneous_chartT_degree_le hP)
  apply Polynomial.le_natDegree_of_ne_zero
  rwa [homogeneous_chartT_top_coeff hP]

/-- A full-degree chart factor lifts to a homogeneous quotient of the expected weight. -/
theorem homogeneous_quotient_of_chartT_dvd {F : Type*} [Field F]
    {A P : MvPolynomial (Fin 2) F} {a k : ℕ}
    (hA : BinaryHomogeneous A a) (hP : BinaryHomogeneous P k)
    (hTop : eval ![1, 0] A ≠ 0) (hP0 : P ≠ 0)
    (hd : Igusa.chartT A ∣ Igusa.chartT P) :
    a ≤ k ∧ ∃ Q : MvPolynomial (Fin 2) F, BinaryHomogeneous Q (k - a) ∧ P = A * Q := by
  have hcP : Igusa.chartT P ≠ 0 := by
    intro h
    have he := homogeneous_chartT_reconstruct hP
    rw [h, Polynomial.homogenize_zero] at he
    exact hP0 he.symm
  obtain ⟨q, hq⟩ := hd
  have hcA : Igusa.chartT A ≠ 0 := left_ne_zero_of_mul (hq ▸ hcP)
  have hq0 : q ≠ 0 := right_ne_zero_of_mul (hq ▸ hcP)
  have he := Polynomial.natDegree_mul hcA hq0
  rw [← hq, homogeneous_chartT_degree_eq hA hTop] at he
  have hpdeg := homogeneous_chartT_degree_le hP
  have hak : a ≤ k := by omega
  have hqdeg : q.natDegree ≤ k - a := by omega
  refine ⟨hak, q.homogenize (k - a), Polynomial.isHomogeneous_homogenize q, ?_⟩
  calc
    P = (Igusa.chartT P).homogenize k := (homogeneous_chartT_reconstruct hP).symm
    _ = (Igusa.chartT A * q).homogenize (a + (k - a)) := by rw [← hq, Nat.add_sub_of_le hak]
    _ = (Igusa.chartT A).homogenize a * q.homogenize (k - a) :=
      Polynomial.homogenize_mul _ _ (homogeneous_chartT_degree_le hA) hqdeg
    _ = _ := by rw [homogeneous_chartT_reconstruct hA]

theorem homogeneous_dvd_iff_chartT_dvd {F : Type*} [Field F]
    {A P : MvPolynomial (Fin 2) F} {a k : ℕ}
    (hA : BinaryHomogeneous A a) (hP : BinaryHomogeneous P k)
    (hTop : eval ![1, 0] A ≠ 0) : A ∣ P ↔ Igusa.chartT A ∣ Igusa.chartT P := by
  constructor
  · exact map_dvd _
  · intro hd
    by_cases hP0 : P = 0
    · rw [hP0]
      exact dvd_zero _
    · obtain ⟨_, Q, _, hQ⟩ := homogeneous_quotient_of_chartT_dvd hA hP hTop hP0 hd
      exact ⟨Q, hQ⟩

variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]

theorem binaryHasse_at_infinity (hp5 : 5 ≤ p) :
    eval ![1, 0] (binaryHasse F p hp5) = 1 := by
  rw [binaryHasse, eval_binaryPullback, eval_binaryE4_zero_right]
  have h6 : eval ![1, 0] (binaryE6 F) = 1 := by simp [binaryE6_eq]
  rw [h6, one_pow]
  exact Igusa.eval_one_AF hp5

theorem hasse_dvd_iff_chartT_dvd (hp5 : 5 ≤ p)
    {P : MvPolynomial (Fin 2) F} {k : ℕ} (hP : BinaryHomogeneous P k) :
    binaryHasse F p hp5 ∣ P ↔
      Igusa.chartT (binaryHasse F p hp5) ∣ Igusa.chartT P :=
  homogeneous_dvd_iff_chartT_dvd (binaryHasse_homogeneous hp5) hP
    (by rw [binaryHasse_at_infinity]; exact one_ne_zero)

/-- The global homogeneous divisibility law needed for the non-dropping theta step. -/
theorem hasse_dvd_theta_iff (hp5 : 5 ≤ p) (n : ℕ)
    (P : MvPolynomial (Fin 2) F) (hP : BinaryHomogeneous P (2 * n))
    (hk : (2 * n : F) ≠ 0) :
    binaryHasse F p hp5 ∣ binaryThetaNumerator hp5 n P ↔ binaryHasse F p hp5 ∣ P := by
  rw [hasse_dvd_iff_chartT_dvd hp5 (binaryThetaNumerator_homogeneous hp5 n P hP),
    hasse_dvd_iff_chartT_dvd hp5 hP, chartT_hasse_dvd_theta_iff hp5 n P hk]

/-- A Hasse factor is exactly the ability to lower the weight by p−1 without
changing the complete q-expansion. -/
theorem hasse_dvd_iff_lower_expansion (hp5 : 5 ≤ p) (n : ℕ)
    (P : MvPolynomial (Fin 2) F) (hP : BinaryHomogeneous P (2 * n))
    (hk : p - 1 ≤ 2 * n) :
    binaryHasse F p hp5 ∣ P ↔
      ∃ Q : MvPolynomial (Fin 2) F, BinaryHomogeneous Q (2 * n - (p - 1)) ∧
        binaryEv F Q = binaryEv F P := by
  constructor
  · intro hd
    by_cases hP0 : P = 0
    · refine ⟨0, isWeightedHomogeneous_zero F _ _, ?_⟩
      rw [hP0]
    · obtain ⟨_, Q, hQ, he⟩ := homogeneous_quotient_of_chartT_dvd
        (binaryHasse_homogeneous hp5) hP
        (by rw [binaryHasse_at_infinity]; exact one_ne_zero) hP0 (map_dvd _ hd)
      refine ⟨Q, hQ, ?_⟩
      rw [he, map_mul, binaryEv_hasse, one_mul]
  · rintro ⟨Q, hQ, he⟩
    have hd := hasse_degree_even hp5
    have hlo : 2 * (n - (p - 1) / 2) = 2 * n - (p - 1) := by omega
    have hhi : 2 * (n - (p - 1) / 2) + 1 * (p - 1) = 2 * n := by omega
    have h := eq_binaryHasse_pow_mul hp5 (m := 1)
      (by rw [hlo]; exact hQ) (by rw [hhi]; exact hP) he
    exact ⟨Q, by simpa only [pow_one] using h⟩

end RamanujanTau.TheoremA
