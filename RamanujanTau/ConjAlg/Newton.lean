import RamanujanTau.SharpHQ.Final
import RamanujanTau.HeckeBridge.Final

/-!
# Newton's identities for the coefficients of the `Δ`-modular equation, as polynomials

Let `f : ℕ → Poly ℓ` be isobaric of weight `12k` with q-expansions `J(f_k) = e_k(ys Pdisc 12 ζ)`
(the shape of `VLayer.modular_equation` / `SharpHQ.HConj`). Then, in `ℚ_ℓ[X₀,X₁]`,

* **`f_zero`**: `f_0 = 1`;
* **`newton_poly`**: `k·f_k = (−1)^{k+1} Σ_{i+j=k, i<k} (−1)^i f_i · ℓ T_ℓ(Δ^j)`,

by injectivity of the q-expansion on each weight (`ModP.ev_injOn_iso`), `J`-injectivity, the Tate
power sums `VLayer.psum_ys` and Mathlib's `MvPolynomial.mul_esymm_eq_sum`.

* `map_heckePoly`: `heckePoly` commutes with ring maps between `ℚ`-algebras.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ConjAlg
open MvPolynomial ModP VLayer HeckeQExp AtkinOBrienFinal DBound

section Hecke
variable (p : ℕ) [Fact p.Prime]

/-- **`T_p` commutes with change of coefficients** (between `ℚ`-algebras). -/
theorem map_heckePoly {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
    (ψ : R →+* S) (P : MvPolynomial (Fin 2) R) :
    MvPolynomial.map ψ (heckePoly p P) = heckePoly p (MvPolynomial.map ψ P) := by
  classical
  have hψ : ψ.comp (algebraMap ℚ R) = algebraMap ℚ S := Subsingleton.elim _ _
  rw [heckePoly, heckePoly, map_sum]
  symm
  refine Finset.sum_subset (MvPolynomial.support_map_subset ψ P) ?_ |>.trans ?_
  · intro d _ hd
    rw [MvPolynomial.notMem_support_iff.mp hd, map_zero, zero_mul]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_mul, map_C, map_map, hψ, coeff_map]

end Hecke

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-- `Pdisc` over `ℚ_ℓ`. -/
lemma iso_Pdisc_pow (m : ℕ) : Iso (Pq (Pdisc hℓ) ^ m) (m * 12) :=
  iso_Pq_pow (iso_Pdisc hℓ) m

/-- The hypothesis on `f` in `SharpHQ.HConj`. -/
def IsModEqCoeffs (f : ℕ → Poly ℓ) (ζ : PadicAlgCl ℓ) : Prop :=
  ∀ k, J ℓ (PowerSeries.map (ιz ℓ) (ev ℤ_[ℓ] (f k))) =
    MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k)

variable {hℓ}

lemma J_ev_map {f : ℕ → Poly ℓ} {ζ : PadicAlgCl ℓ} (hJ : IsModEqCoeffs hℓ f ζ) (k : ℕ) :
    J ℓ (ev ℚ_[ℓ] (MvPolynomial.map (ιz ℓ) (f k))) =
      MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k) := by
  rw [← map_ev, hJ]

lemma iso_map_f {f : ℕ → Poly ℓ} (hf : ∀ k, Iso (f k) (k * 12)) (k : ℕ) :
    Iso (MvPolynomial.map (ιz ℓ) (f k)) (k * 12) := iso_map _ (hf k)

/-- **`f_0 = 1`** (over `ℚ_ℓ`). -/
theorem f_zero {f : ℕ → Poly ℓ} (hf : ∀ k, Iso (f k) (k * 12)) {ζ : PadicAlgCl ℓ}
    (hJ : IsModEqCoeffs hℓ f ζ) : MvPolynomial.map (ιz ℓ) (f 0) = 1 := by
  have h1 : Iso (1 : MvPolynomial (Fin 2) ℚ_[ℓ]) (0 * 12) := by
    simpa using (MvPolynomial.isWeightedHomogeneous_one ℚ_[ℓ] wt)
  refine ev_injOn_iso (isUnit_1728 (R := ℚ_[ℓ])) (iso_map_f hf 0) h1 (J_injective ℓ ?_)
  rw [J_ev_map hJ, map_one, map_one, MvPolynomial.esymm_zero, map_one]

/-- **Newton's identities for the `f_k`, as polynomials over `ℚ_ℓ`.** -/
theorem newton_poly {f : ℕ → Poly ℓ} (hf : ∀ k, Iso (f k) (k * 12)) {ζ : PadicAlgCl ℓ}
    (hζ : IsPrimitiveRoot ζ ℓ) (hJ : IsModEqCoeffs hℓ f ζ) (k : ℕ) :
    C (k : ℚ_[ℓ]) * MvPolynomial.map (ιz ℓ) (f k) =
      C ((-1 : ℚ_[ℓ]) ^ (k + 1)) * ∑ a ∈ Finset.antidiagonal k with a.1 < k,
        C ((-1 : ℚ_[ℓ]) ^ a.1) * MvPolynomial.map (ιz ℓ) (f a.1) * sigP (Pdisc hℓ) a.2 := by
  classical
  have hL : Iso (C (k : ℚ_[ℓ]) * MvPolynomial.map (ιz ℓ) (f k)) (k * 12) :=
    (iso_map_f hf k).C_mul _
  have hR : Iso (C ((-1 : ℚ_[ℓ]) ^ (k + 1)) * ∑ a ∈ Finset.antidiagonal k with a.1 < k,
      C ((-1 : ℚ_[ℓ]) ^ a.1) * MvPolynomial.map (ιz ℓ) (f a.1) * sigP (Pdisc hℓ) a.2) (k * 12) := by
    refine (MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun a ha => ?_).C_mul _
    obtain ⟨ha1, -⟩ := Finset.mem_filter.mp ha
    have hsum : a.1 + a.2 = k := Finset.mem_antidiagonal.mp ha1
    refine iso_of_eq (((MvPolynomial.isWeightedHomogeneous_C wt _).mul
      (iso_map_f hf a.1)).mul (iso_sigP (iso_Pdisc hℓ) a.2)) ?_
    rw [← hsum]; ring
  refine ev_injOn_iso (isUnit_1728 (R := ℚ_[ℓ])) hL hR (J_injective ℓ ?_)
  have hN := congrArg (MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ))
    (MvPolynomial.mul_esymm_eq_sum (Option (Fin ℓ)) ℤ k)
  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast] at hN
  rw [map_mul, map_mul, ev_C, J_C, J_ev_map hJ, map_mul, map_sum, map_mul, ev_C, J_C, map_sum]
  have hS : ∀ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
      J ℓ (ev ℚ_[ℓ] (C ((-1 : ℚ_[ℓ]) ^ a.1) * MvPolynomial.map (ιz ℓ) (f a.1) *
        sigP (Pdisc hℓ) a.2)) =
      (-1) ^ a.1 * MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ)
          (MvPolynomial.esymm (Option (Fin ℓ)) ℤ a.1) *
        MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.psum (Option (Fin ℓ)) ℤ a.2) := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    have hsum : a.1 + a.2 = k := Finset.mem_antidiagonal.mp ha1
    rw [map_mul, map_mul, map_mul, map_mul, ev_C, J_C, J_ev_map hJ, aeval_psum_ys,
      psum_ys (iso_Pdisc hℓ) (by norm_num) hζ (by omega)]
    simp
  rw [Finset.sum_congr rfl hS]
  simp only [map_pow, map_neg, map_one, map_natCast]
  exact hN

end ConjAlg
