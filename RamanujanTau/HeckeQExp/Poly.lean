/-
# The Hecke operator `T_p` on isobaric polynomials in `(E₄, E₆)`

Level-one classical forms of weight `k` are the isobaric `P ∈ R[X₀,X₁]` of weight `k`, with q-expansion
`ev R P = P(E₄,E₆)` (`ModP`). Here `T_p` is constructed on them:

* `exists_hecke_C` — over `ℂ`: for isobaric `P` of weight `k` there is an isobaric `Q` of weight `k`
  with `Q(E₄,E₆) = T_p(P(E₄,E₆))`, `T_p = Tq p p^{k−1}` (`p^{k−1}` taken in `ℤ`-powers, so weight `0`
  gives `1 + 1/p`). Proof: realize monomials as modular forms (`ModP.exists_mono_form`), split
  `f = c·E_k + g` with `g` cuspidal, apply `Hecke.qExpansion_hecke` to `g` and `Tq_Eis` to `E_k`, and
  apply `ModP.exists_poly_qExpansion` to `T_p g`.
* `exists_hecke_Q` — the same over `ℚ` (descent `ModP.descend`).
* **`heckePoly p P`** — for every `ℚ`-algebra `R`, a definition of `T_p P ∈ R[X₀,X₁]`.
  * `iso_heckePoly`: it is isobaric of weight `k`;
  * `ev_heckePoly`: `ev R (heckePoly p P) = Tq p (p^{k−1}) (ev R P)`;
  * `heckePoly_unique`: it is the only isobaric polynomial of weight `k` with that q-expansion.
-/
import RamanujanTau.HeckeQExp.Tq
import RamanujanTau.ModP.Structure
import RamanujanTau.ModP.SwinnertonDyer
import RamanujanTau.HeckeQExp

set_option autoImplicit false

namespace HeckeQExp
open MvPolynomial ModularForm EisensteinSeries ModularFormClass UpperHalfPlane ModP
open scoped MatrixGroups

/-- The multiplier `p^{k−1}` (an integer power, so `p⁻¹` in weight `0`). -/
noncomputable def mulQ (p k : ℕ) : ℚ := (p : ℚ) ^ ((k : ℤ) - 1)

lemma mulQ_of_pos (p : ℕ) {k : ℕ} (hk : 1 ≤ k) : mulQ p k = (p : ℚ) ^ (k - 1) := by
  rw [mulQ, show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]

lemma Tq_C_mul {R : Type*} [CommRing R] (p : ℕ) (c a : R) (F : PowerSeries R) :
    Tq p c (PowerSeries.C a * F) = PowerSeries.C a * Tq p c F := by
  ext n; simp only [coeff_Tq, PowerSeries.coeff_C_mul]; split_ifs <;> ring

lemma Tq_add {R : Type*} [CommRing R] (p : ℕ) (c : R) (F G : PowerSeries R) :
    Tq p c (F + G) = Tq p c F + Tq p c G := (TqL p c).map_add F G

lemma Tq_zero {R : Type*} [CommRing R] (p : ℕ) (c : R) : Tq p c 0 = 0 := (TqL p c).map_zero

lemma Tq_sum {R : Type*} [CommRing R] (p : ℕ) (c : R) {ι : Type*} (s : Finset ι)
    (F : ι → PowerSeries R) : Tq p c (∑ i ∈ s, F i) = ∑ i ∈ s, Tq p c (F i) :=
  map_sum (TqL p c) F s

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Over `ℂ` -/

/-- `T_p` of a modular form of weight `n ≥ 3` (even) is again a polynomial in `E₄, E₆`. -/
theorem tq_form {n : ℕ} (hn : 3 ≤ n) (hn2 : Even n) (f : ModularForm 𝒮ℒ (n : ℤ)) :
    ∃ Q : MvPolynomial (Fin 2) ℂ, Iso Q n ∧
      ev ℂ Q = Tq p (Rat.castHom ℂ (mulQ p n)) (qExpansion 1 f) := by
  have hm : Rat.castHom ℂ (mulQ p n) = (p : ℂ) ^ ((n : ℤ) - 1) := by
    rw [mulQ, map_zpow₀, map_natCast]
  set c := (qExpansion 1 f).coeff 0 with hc
  set g : ModularForm 𝒮ℒ (n : ℤ) := f - c • E hn with hg
  have hqE : qExpansion 1 (E hn) = PowerSeries.map (Rat.castHom ℂ) (TateCurve.Eis n) :=
    qExpansion_E_eq_Eis hn hn2
  have hqg : qExpansion 1 g = qExpansion 1 f - c • qExpansion 1 (E hn) := by
    rw [hg, ModularForm.coe_sub, ModularFormClass.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      show ((c • E hn : ModularForm 𝒮ℒ (n : ℤ)) : ℍ → ℂ) = c • (E hn : ℍ → ℂ) from rfl,
      ModularFormClass.qExpansion_smul one_pos one_mem_strictPeriods_SL]
  have hg0 : (qExpansion 1 g).coeff 0 = 0 := by
    rw [hqg, map_sub, PowerSeries.coeff_smul, E_qExpansion_coeff_zero hn hn2, ← hc]; simp
  set gc := ModularForm.toCuspForm g hg0 with hgc
  have hqgc : qExpansion 1 gc = qExpansion 1 g := by
    congr 1
  set h := RamanujanTau.Hecke.heckeCusp p gc with hh
  have hqh : qExpansion 1 h = Tq p (Rat.castHom ℂ (mulQ p n)) (qExpansion 1 gc) := by
    ext m
    rw [coeff_Tq, hh, RamanujanTau.Hecke.qExpansion_hecke, hm]
  obtain ⟨Q1, hQ1, hQ1e⟩ := exists_poly_qExpansion (n + 1) (n : ℤ) (by omega)
    (CuspForm.toModularFormₗ h)
  rw [Int.toNat_natCast] at hQ1
  have hQ1e' : ev ℂ Q1 = qExpansion 1 h := hQ1e
  obtain ⟨PE, hPE, hPEe⟩ := exists_poly_Eis hn hn2
  refine ⟨C (c * (1 + (p : ℂ) ^ (n - 1))) * MvPolynomial.map (Rat.castHom ℂ) PE + Q1,
    (((iso_map _ hPE).C_mul _)).add hQ1, ?_⟩
  have hEis := congrArg (PowerSeries.map (Rat.castHom ℂ)) (Tq_Eis (p := p) hp.out (k := n))
  rw [map_Tq, map_mul, PowerSeries.map_C] at hEis
  have hm' : Rat.castHom ℂ ((p : ℚ) ^ (n - 1)) = Rat.castHom ℂ (mulQ p n) := by
    rw [mulQ_of_pos p (by omega)]
  rw [hm'] at hEis
  have hf : qExpansion 1 f = qExpansion 1 g + c • qExpansion 1 (E hn) := by rw [hqg]; ring
  rw [map_add, map_mul, ev_C, ← map_ev, hPEe, hQ1e', hqh, hqgc, hf, Tq_add,
    PowerSeries.smul_eq_C_mul, Tq_C_mul, hqE, hEis]
  simp only [map_mul, map_add, map_one, map_pow, map_natCast]
  ring

/-- `T_p` of a monomial `E₄^a E₆^b`, over `ℂ`. -/
theorem tq_mono (a b : ℕ) :
    ∃ Q : MvPolynomial (Fin 2) ℂ, Iso Q (4 * a + 6 * b) ∧
      ev ℂ Q = Tq p (Rat.castHom ℂ (mulQ p (4 * a + 6 * b))) (E4 ℂ ^ a * E6 ℂ ^ b) := by
  by_cases h0 : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h0
    refine ⟨C (1 + Rat.castHom ℂ (mulQ p 0)), isWeightedHomogeneous_C _ _, ?_⟩
    simp only [pow_zero, mul_one, Nat.mul_zero, Nat.add_zero]
    rw [ev_C]
    ext n
    rw [coeff_Tq, PowerSeries.coeff_C]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 : p * n ≠ 0 := Nat.mul_ne_zero hp.out.ne_zero hn.ne'
      rw [if_neg hn.ne', PowerSeries.coeff_one, if_neg h1]
      split_ifs with h
      · have : n / p ≠ 0 := by
          obtain ⟨m, rfl⟩ := h
          rw [Nat.mul_div_cancel_left _ hp.out.pos]; rintro rfl; simp at hn
        rw [PowerSeries.coeff_one, if_neg this]; ring
      · ring
  · have hn : 3 ≤ 4 * a + 6 * b := by omega
    have hn2 : Even (4 * a + 6 * b) := ⟨2 * a + 3 * b, by ring⟩
    obtain ⟨F, hF⟩ := exists_mono_form a b
    obtain ⟨Q, hQ, hQe⟩ := tq_form p hn hn2 F
    exact ⟨Q, hQ, by rw [hQe, hF]⟩

/-- **`T_p` on isobaric polynomials over `ℂ`.** -/
theorem exists_hecke_C {k : ℕ} {P : MvPolynomial (Fin 2) ℂ} (hP : Iso P k) :
    ∃ Q : MvPolynomial (Fin 2) ℂ, Iso Q k ∧ ev ℂ Q = Tq p (Rat.castHom ℂ (mulQ p k)) (ev ℂ P) := by
  classical
  rw [P.as_sum, map_sum, Tq_sum]
  refine Finset.sum_induction _ (fun F => ∃ Q : MvPolynomial (Fin 2) ℂ, Iso Q k ∧ ev ℂ Q = F)
    (fun F G ⟨Q, hQ, hQe⟩ ⟨Q', hQ', hQe'⟩ => ⟨Q + Q', hQ.add hQ', by rw [map_add, hQe, hQe']⟩)
    ⟨0, isWeightedHomogeneous_zero ℂ wt k, map_zero _⟩ fun d hd => ?_
  have hw : 4 * d 0 + 6 * d 1 = k := by rw [← weight_wt]; exact hP (mem_support_iff.mp hd)
  obtain ⟨Q, hQ, hQe⟩ := tq_mono p (d 0) (d 1)
  rw [hw] at hQ hQe
  refine ⟨C (coeff d P) * Q, hQ.C_mul _, ?_⟩
  rw [monomial_eq_two, map_mul, map_mul, ev_C, hQe, Tq_C_mul]
  simp [ev, evVec]

/-! ### Over `ℚ` -/

/-- **`T_p` on isobaric polynomials over `ℚ`.** -/
theorem exists_hecke_Q {k : ℕ} {P : MvPolynomial (Fin 2) ℚ} (hP : Iso P k) :
    ∃ Q : MvPolynomial (Fin 2) ℚ, Iso Q k ∧ ev ℚ Q = Tq p (mulQ p k) (ev ℚ P) := by
  have hinj : Function.Injective (Rat.castHom ℂ) := (Rat.castHom ℂ).injective
  obtain ⟨QC, hQC, hQCe⟩ := exists_hecke_C p (iso_map (Rat.castHom ℂ) hP)
  obtain ⟨Q, hQ, hQe⟩ := descend (Rat.castHom ℂ) hinj (isUnit_iff_ne_zero.mpr (by norm_num)) k QC hQC
    ⟨Tq p (mulQ p k) (ev ℚ P), by rw [map_Tq, hQCe, map_ev]⟩
  refine ⟨Q, hQ, PowerSeries.map_injective _ hinj ?_⟩
  rw [map_ev, hQe, hQCe, map_Tq, map_ev]

/-! ### Over any `ℚ`-algebra -/

/-- The `ℚ`-polynomial `T_p(E₄^a E₆^b)`, for a monomial `d = (a, b)`. -/
noncomputable def heckeMono (d : Fin 2 →₀ ℕ) : MvPolynomial (Fin 2) ℚ :=
  Classical.choose (exists_hecke_Q p (iso_mono (R := ℚ) (d 0) (d 1)))

lemma iso_heckeMono (d : Fin 2 →₀ ℕ) : Iso (heckeMono p d) (4 * d 0 + 6 * d 1) :=
  (Classical.choose_spec (exists_hecke_Q p (iso_mono (R := ℚ) (d 0) (d 1)))).1

lemma ev_heckeMono (d : Fin 2 →₀ ℕ) :
    ev ℚ (heckeMono p d) = Tq p (mulQ p (4 * d 0 + 6 * d 1)) (ev ℚ (X 0 ^ d 0 * X 1 ^ d 1)) :=
  (Classical.choose_spec (exists_hecke_Q p (iso_mono (R := ℚ) (d 0) (d 1)))).2

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- **The Hecke operator `T_p` on `R[X₀,X₁]`** (`R` a `ℚ`-algebra), defined monomialwise. -/
noncomputable def heckePoly (P : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  ∑ d ∈ P.support, C (coeff d P) * MvPolynomial.map (algebraMap ℚ R) (heckeMono p d)

theorem iso_heckePoly {k : ℕ} {P : MvPolynomial (Fin 2) R} (hP : Iso P k) :
    Iso (heckePoly p P) k := by
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have hw : 4 * d 0 + 6 * d 1 = k := by rw [← weight_wt]; exact hP (mem_support_iff.mp hd)
  exact (iso_of_eq (iso_map _ (iso_heckeMono p d)) hw).C_mul _

/-- **The q-expansion of `T_p P`**: `(T_p P)(E₄,E₆) = Σ a_{pn} qⁿ + p^{k−1} Σ a_n q^{pn}`. -/
theorem ev_heckePoly {k : ℕ} {P : MvPolynomial (Fin 2) R} (hP : Iso P k) :
    ev R (heckePoly p P) = Tq p (algebraMap ℚ R (mulQ p k)) (ev R P) := by
  classical
  conv_rhs => rw [P.as_sum, map_sum, ← TqL_apply, map_sum]
  rw [heckePoly, map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : 4 * d 0 + 6 * d 1 = k := by rw [← weight_wt]; exact hP (mem_support_iff.mp hd)
  have h1 := congrArg (PowerSeries.map (algebraMap ℚ R)) (ev_heckeMono p d)
  rw [map_Tq, map_ev, map_ev, hw] at h1
  rw [map_mul, ev_C, h1, monomial_eq_two, TqL_apply, map_mul (ev R) (C _) _, ev_C, Tq_C_mul]
  simp

lemma isUnit_1728 : IsUnit (1728 : R) := by
  have : (1728 : R) = algebraMap ℚ R 1728 := (map_ofNat _ _).symm
  rw [this]; exact (isUnit_iff_ne_zero.mpr (by norm_num : (1728 : ℚ) ≠ 0)).map _

/-- **Uniqueness**: an isobaric `Q` of weight `k` with `Q(E₄,E₆) = T_p(P(E₄,E₆))` is `heckePoly p P`. -/
theorem heckePoly_unique {k : ℕ} {P Q : MvPolynomial (Fin 2) R} (hP : Iso P k) (hQ : Iso Q k)
    (h : ev R Q = Tq p (algebraMap ℚ R (mulQ p k)) (ev R P)) : Q = heckePoly p P :=
  ev_injOn_iso isUnit_1728 hQ (iso_heckePoly p hP) (by rw [h, ev_heckePoly p hP])

end HeckeQExp
