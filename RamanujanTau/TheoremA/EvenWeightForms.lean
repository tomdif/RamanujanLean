import RamanujanTau.TheoremA.EtaQuotientQExpansion

/-!
# A uniform family of level-six forms in every even weight

For 0 ≤ i ≤ 2n the eta-squared exponent vector
(-3n+2i, 6n-4i, n-2i, -2n+4i) has weight 2n and order i at
infinity. Its other cusp orders are nonnegative. The resulting actual
modular forms have integral expansions with leading coefficient one.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open ModularForm CongruenceSubgroup PowerSeries
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm

lemma PhaseCertificate.linear {r s : Fin 4 → ℤ}
    (hr : PhaseCertificate r) (hs : PhaseCertificate s) (a b : ℤ) :
    PhaseCertificate (fun j => a * r j + b * s j) := by
  intro c i
  have he : (∑ j : Fin 4, wordExponent (generatorWord c i j) * (a * r j + b * s j)) =
      a * ∑ j, wordExponent (generatorWord c i j) * r j +
        b * ∑ j, wordExponent (generatorWord c i j) * s j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_right (hr c i) _) (dvd_mul_of_dvd_right (hs c i) _)

def evenExponent (n i : ℕ) (j : Fin 4) : ℤ :=
  ((n : ℤ) - i) * weightTwoExponent 0 j + (i : ℤ) * weightTwoExponent 1 j

theorem evenExponent_sum (n i : ℕ) : ∑ j : Fin 4, evenExponent n i j = (2 * n : ℕ) := by
  simp only [evenExponent, Finset.sum_add_distrib, ← Finset.mul_sum, weightTwoExponent_sum]
  push_cast
  ring

theorem evenExponent_weighted (n i : ℕ) :
    ∑ j : Fin 4, (dilation j : ℤ) * evenExponent n i j = 12 * (i : ℤ) := by
  norm_num [evenExponent, Fin.sum_univ_succ, dilation, weightTwoExponent]
  ring

theorem even_phase (n i : ℕ) : PhaseCertificate (evenExponent n i) :=
  (weightTwo_phase 0).linear (weightTwo_phase 1) ((n : ℤ) - i) i

lemma evenExponent_twice (n i : ℕ) (j : Fin 4) :
    2 * evenExponent n i j = (2 * (n : ℤ) - i) * weightTwoExponent 0 j +
      (i : ℤ) * weightTwoExponent 2 j := by
  have hr := congrFun weightTwoExponent_relation j
  simp only [Pi.add_apply] at hr
  have h : weightTwoExponent 2 j = 2 * weightTwoExponent 1 j - weightTwoExponent 0 j := by
    linarith
  rw [h, evenExponent]
  ring

theorem even_cusps (n i : ℕ) (hi : i ≤ 2 * n) : CuspCertificate (evenExponent n i) := by
  have hi' : (i : ℚ) ≤ 2 * n := by exact_mod_cast hi
  intro c
  have he : (2 : ℚ) * (∑ j : Fin 4, (evenExponent n i j : ℚ) * cuspA c j / cuspD c j) =
      (2 * (n : ℚ) - i) * (∑ j : Fin 4, (weightTwoExponent 0 j : ℚ) * cuspA c j / cuspD c j) +
        (i : ℚ) * (∑ j : Fin 4, (weightTwoExponent 2 j : ℚ) * cuspA c j / cuspD c j) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hj : (2 : ℚ) * evenExponent n i j =
        (2 * (n : ℚ) - i) * weightTwoExponent 0 j + (i : ℚ) * weightTwoExponent 2 j := by
      exact_mod_cast evenExponent_twice n i j
    calc
      _ = (2 * (evenExponent n i j : ℚ)) * (cuspA c j / cuspD c j) := by ring
      _ = _ := by rw [hj]; ring
  have hn := add_nonneg (mul_nonneg (sub_nonneg.mpr hi') (weightTwo_cusps 0 c))
    (mul_nonneg (Nat.cast_nonneg i : (0 : ℚ) ≤ i) (weightTwo_cusps 2 c))
  linarith

/-- The i-th actual eta quotient in weight 2n. -/
noncomputable def evenForm (n : ℕ) (i : Fin (2 * n + 1)) :
    ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) (2 * n : ℕ) :=
  quotientModularForm (evenExponent n i.val) (evenExponent_sum n i.val)
    (even_phase n i.val) (even_cusps n i.val (by omega))

@[simp] theorem evenForm_apply (n : ℕ) (i : Fin (2 * n + 1)) (z : ℍ) :
    evenForm n i z = quotientFunction (evenExponent n i.val) z := rfl

noncomputable def evenSeries (n i : ℕ) : PowerSeries ℤ := quotientSeries (evenExponent n i) i

theorem qExpansion_evenForm (n : ℕ) (i : Fin (2 * n + 1)) :
    qExpansion 1 (evenForm n i) = PowerSeries.map (Int.castRingHom ℂ) (evenSeries n i.val) :=
  qExpansion_quotientModularForm _ _ _ _ _ (evenExponent_weighted n i.val)

theorem evenSeries_coeff_lt (n i j : ℕ) (h : j < i) : (evenSeries n i).coeff j = 0 :=
  quotientSeries_coeff_lt _ _ _ h

theorem evenSeries_coeff_self (n i : ℕ) : (evenSeries n i).coeff i = 1 :=
  quotientSeries_coeff_self _ _

theorem evenForm_coeff_lt (n : ℕ) (i : Fin (2 * n + 1)) (j : ℕ) (h : j < i.val) :
    (qExpansion 1 (evenForm n i)).coeff j = 0 := by
  rw [qExpansion_evenForm, coeff_map, evenSeries_coeff_lt n i.val j h, map_zero]

theorem evenForm_coeff_self (n : ℕ) (i : Fin (2 * n + 1)) :
    (qExpansion 1 (evenForm n i)).coeff i.val = 1 := by
  rw [qExpansion_evenForm, coeff_map, evenSeries_coeff_self, map_one]

theorem evenExponent_add (n m i j : ℕ) :
    evenExponent (n + m) (i + j) = evenExponent n i + evenExponent m j := by
  ext a
  simp only [evenExponent, Pi.add_apply, Nat.cast_add]
  ring

end RamanujanTau.TheoremA.EtaSquared
