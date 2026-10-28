import RamanujanTau.Igusa.Charts

/-!
# The monomial complement meets `Ā · M` trivially (mod `p`)

`S p hp5 k` = weight-`k` monomials not divisible by the leading monomial `X₀^{dA} X₁^{eA}` of `Ā`.

* `eq_zero_of_support_S`: over any field `F` of characteristic `p`, if `x` is supported on
  `S p hp5 (m + (p−1))`, `y` is isobaric of weight `m`, and `x = Ā · y`, then `x = 0`
  (leading terms in the `t`-chart: `deg (Ā y)(t,1) = dA + deg y(t,1)`).
* `katz_independent_S`: hence the hypothesis of `ModP.katz_independent` holds for the pieces
  `B̄ i = {x | supp x ⊆ S p hp5 (k₀ + i(p−1))}`: q-expansions of such pieces are independent.
No use of `RamanujanODE`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Igusa
open MvPolynomial ModP

variable {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime] [CharP F p] (hp5 : 5 ≤ p)
include hp5

theorem eq_zero_of_support_S {m : ℕ} {x y : MvPolynomial (Fin 2) F}
    (hx : (x.support : Set (Fin 2 →₀ ℕ)) ⊆ S p hp5 (m + (p - 1))) (hy : Iso y m)
    (hxy : x = AF F p hp5 * y) : x = 0 := by
  by_contra hx0
  have hy0 : y ≠ 0 := by rintro rfl; rw [mul_zero] at hxy; exact hx0 hxy
  have hcy : chartT y ≠ 0 := by
    obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr ((not_congr support_eq_empty).mpr hy0)
    intro h
    have := coeff_chartT hy (weight_eq hy hs)
    rw [h, Polynomial.coeff_zero] at this
    exact mem_support_iff.mp hs this.symm
  set n := (chartT y).natDegree
  have hprod : chartT x = chartT (AF F p hp5) * chartT y := by rw [hxy, map_mul]
  have hdeg : (chartT x).natDegree = dA p hp5 + n := by
    rw [hprod, Polynomial.natDegree_mul (chartT_AF_ne_zero hp5) hcy, natDegree_chartT_AF hp5]
  have hcx : (chartT x).coeff (dA p hp5 + n) ≠ 0 := by
    rw [← hdeg, Polynomial.coeff_natDegree, Ne, Polynomial.leadingCoeff_eq_zero, hprod]
    exact mul_ne_zero (chartT_AF_ne_zero hp5) hcy
  have hcy' : (chartT y).coeff n ≠ 0 := by
    rw [Polynomial.coeff_natDegree, Ne, Polynomial.leadingCoeff_eq_zero]; exact hcy
  obtain ⟨s, hs, hs0⟩ : ∃ s ∈ x.support, s 0 = dA p hp5 + n := by
    by_contra h; push Not at h; exact hcx (coeff_chartT_eq_zero x h)
  obtain ⟨v, hv, hv0⟩ : ∃ v ∈ y.support, v 0 = n := by
    by_contra h; push Not at h; exact hcy' (coeff_chartT_eq_zero y h)
  have hSs := hx hs
  have wv := weight_eq hy hv
  have w0 := dA_eA (p := p) hp5
  have := hSs.1
  apply hSs.2
  constructor <;> omega

/-- The independence hypothesis of `ModP.katz_independent` for the monomial complement. -/
theorem katz_independent_S (k₀ : ℕ) :
    ∀ (n : ℕ) (P : ℕ → MvPolynomial (Fin 2) (ZMod p)), (∀ i ≤ n, Iso (P i) (k₀ + i * (p - 1))) →
      (∀ i ≤ n, ((P i).support : Set (Fin 2 →₀ ℕ)) ⊆ S p hp5 (k₀ + i * (p - 1))) →
      ∑ i ∈ Finset.range (n + 1), ev (ZMod p) (P i) = 0 → ∀ i ≤ n, P i = 0 := by
  refine katz_independent hp5 k₀ (fun i => {x | (x.support : Set (Fin 2 →₀ ℕ)) ⊆ S p hp5 (k₀ + i * (p - 1))}) ?_
  intro i hi x hx y hy hxy
  have hA : AF (ZMod p) p hp5 = hasseBar p hp5 := by
    rw [AF, ZMod.castHom_self, MvPolynomial.map_id]
  refine eq_zero_of_support_S (F := ZMod p) hp5 (m := k₀ + (i - 1) * (p - 1)) ?_ hy (by rw [hA]; exact hxy)
  have : k₀ + (i - 1) * (p - 1) + (p - 1) = k₀ + i * (p - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp [Nat.add_mul]; ring
  rw [this]; exact hx

end Igusa
