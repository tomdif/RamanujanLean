/-
# The constant term of the Δ-modular equation: `∏_C Δ(W/C) = ℓ^12 Δ(W)^{ℓ+1}`

* `prod_ys`: `∏ᵢ yᵢ = X^{ℓ(ℓ+1)} · V` with `V(0) = ℓ^12` (conjugates of `Δ`, leading terms
  `ℓ^12 t^{ℓ²}` and `ζ^j t`, `∏ ζ^j = 1`).
* `f_last`: for the modular-equation coefficients `f` of `Δ`, `f_{ℓ+1} = Pdisc^{ℓ+1} · ℓ^12`
  (`X^{ℓ+1} ∣ f_{ℓ+1}` from `prod_ys`, then `VLayer.disc_pow_dvd`, weight `0` ⇒ constant).
* **`prodDelta`** (modulo `hKer`, via `ConjAlg.algebraicity_general` at `k = ℓ+1`), and
  **`prodDelta_C : ProdDelta ℓ ℂ_ℓ`** unconditionally (`TateAdd.tateKernels`).
* **`ordEBound_C' : QuotE.OrdEBound hℓ (SharpHQ.φC ℓ)`**, unconditionally.
-/
import RamanujanTau.OrdQuot.EBound
import RamanujanTau.VLayer.QB1
import RamanujanTau.TateAdd.Final

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OrdQuot
open PowerSeries ModP AtkinOBrienFinal AtkinOBrien DBound VLayer HeckeQExp

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

lemma esymm_card {σ R : Type*} [Fintype σ] [CommSemiring R] :
    MvPolynomial.esymm σ R (Fintype.card σ) = ∏ i, MvPolynomial.X i := by
  classical
  rw [MvPolynomial.esymm, ← Finset.card_univ, Finset.powersetCard_self, Finset.sum_singleton]

/-- **the product of the conjugates of `Δ`**. -/
theorem prod_ys {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) :
    ∃ V : PowerSeries (PadicAlgCl ℓ),
      MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ (ℓ + 1)) =
        X ^ (ℓ * (ℓ + 1)) * V ∧ constantCoeff V = (ℓ : PadicAlgCl ℓ) ^ 12 := by
  classical
  set G := map (Int.castRingHom (PadicAlgCl ℓ)) (MockTheta5.JTP.qfacInf ^ 24) with hG
  have hG0 : constantCoeff G = 1 := by
    rw [hG, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      map_pow, constantCoeff_qfacInf, one_pow, map_one]
  set v : Fin ℓ → PowerSeries (PadicAlgCl ℓ) := fun j =>
    C (ζ ^ (j : ℕ)) * rescale (ζ ^ (j : ℕ)) G with hv
  have hys : ∀ j : Fin ℓ, ys (Pdisc hℓ) 12 ζ (some j) = X * v j := by
    intro j
    simp only [ys, FK_disc, hv, map_mul, rescale_X, ← hG]
    ring
  set u : PowerSeries (PadicAlgCl ℓ) :=
    expand ℓ (ell_ne_zero' ℓ) (C ((ℓ : PadicAlgCl ℓ) ^ 12) * expand ℓ (ell_ne_zero' ℓ) G) with hu
  have hnone : ys (Pdisc hℓ) 12 ζ none = X ^ (ℓ * ℓ) * u := by
    simp only [ys, FK_disc, map_mul, map_pow, expand_X, ← hG, hu]
    ring
  have hcard : Fintype.card (Option (Fin ℓ)) = ℓ + 1 := by simp
  rw [← hcard, esymm_card, map_prod]
  simp only [MvPolynomial.aeval_X]
  rw [Fintype.prod_option, hnone]
  simp only [hys, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine ⟨u * ∏ j, v j, by rw [hcard]; ring, ?_⟩
  have hodd : Odd ℓ := Nat.odd_iff.mpr (odd_ell hℓ)
  have hcu : constantCoeff u = (ℓ : PadicAlgCl ℓ) ^ 12 := by
    rw [hu, ← coeff_zero_eq_constantCoeff_apply, coeff_expand, if_pos (dvd_zero _),
      Nat.zero_div, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_C,
      ← coeff_zero_eq_constantCoeff_apply, coeff_expand, if_pos (dvd_zero _), Nat.zero_div,
      coeff_zero_eq_constantCoeff_apply, hG0, mul_one]
  have hcv : ∀ j, constantCoeff (v j) = ζ ^ (j : ℕ) := by
    intro j
    rw [hv]
    simp only [map_mul, constantCoeff_C]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply, hG0, mul_one]
  rw [map_mul, map_prod, hcu]
  simp only [hcv]
  rw [prod_zeta hζ hodd, mul_one]

/-- **the last coefficient of the Δ-modular equation**: `f_{ℓ+1} = Pdisc^{ℓ+1} · ℓ^12`. -/
theorem f_last {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) {f : ℕ → Poly ℓ}
    (hf : ∀ k, Iso (f k) (k * 12))
    (hJ : ∀ k, J ℓ (map (ιz ℓ) (ev ℤ_[ℓ] (f k))) =
      MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k)) :
    f (ℓ + 1) = Pdisc hℓ ^ (ℓ + 1) * MvPolynomial.C ((ℓ : ℤ_[ℓ]) ^ 12) := by
  obtain ⟨V, hV, hV0⟩ := prod_ys hℓ hζ
  have hinj : Function.Injective ((ιq ℓ).comp (ιz ℓ)) :=
    (ιq ℓ).injective.comp Subtype.val_injective
  have hc : ∀ n, (ιq ℓ).comp (ιz ℓ) (coeff n (ev ℤ_[ℓ] (f (ℓ + 1)))) =
      coeff (ℓ * n) (X ^ (ℓ * (ℓ + 1)) * V) := by
    intro n; rw [← hV, ← hJ, coeff_J, coeff_map]; rfl
  have hlow : ∀ n < ℓ + 1, coeff n (ev ℤ_[ℓ] (f (ℓ + 1))) = 0 := by
    intro n hn
    apply hinj
    rw [hc, coeff_X_pow_mul', if_neg, map_zero]
    intro h
    have := Nat.le_of_mul_le_mul_left h hℓp.out.pos
    omega
  have hdvd : (X : PS ℓ) ^ (ℓ + 1) ∣ ev ℤ_[ℓ] (f (ℓ + 1)) := X_pow_dvd_iff.2 hlow
  obtain ⟨Q', hQ', hQ'e⟩ := disc_pow_dvd hℓ (ℓ + 1) 0 (f (ℓ + 1))
    (iso_of_eq (hf (ℓ + 1)) (by ring)) hdvd
  rw [iso_zero_eq_C hQ'] at hQ'e
  set c := MvPolynomial.eval one2 Q' with hcdef
  have hFc : coeff (ℓ + 1) (Dl ℓ ^ (ℓ + 1)) = 1 := by
    rw [Dl_eq, mul_pow, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, map_pow, map_pow]
    rw [Pl, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_qfacInf, map_one, one_pow, one_pow]
  have hevl : ev ℤ_[ℓ] (f (ℓ + 1)) = C c * Dl ℓ ^ (ℓ + 1) := by
    rw [hQ'e, map_mul, map_pow, ev_Pdisc, ev_C, mul_comm]
  have hcl : c = (ℓ : ℤ_[ℓ]) ^ 12 := by
    apply hinj
    have := hc (ℓ + 1)
    rw [hevl, coeff_C_mul, hFc, mul_one] at this
    rw [this, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply,
      hV0]
    simp
  rw [hQ'e, hcl]

/-! ### `ProdDelta` -/

section Curve
open ConjAlg SubgroupSum HeckeBridge

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]

include hℓ in
/-- **`∏_C Δ(Wₛ/C) = ℓ^12 Δ(W)^{ℓ+1}`** (modulo `hKer`). -/
theorem prodDelta (ψ : ℚ_[ℓ] →+* K) {ζK : K} (hζK : IsPrimitiveRoot ζK ℓ)
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] [DecidableEq L]
    (ι : PowerSeries K →+* L) (hι : Function.Injective ι) (hKer : TateKernels ℓ L ι ζK) :
    ProdDelta ℓ K := by
  classical
  intro W hW0 Z hZ
  obtain ⟨ζ, hζ⟩ := exists_zeta ℓ
  obtain ⟨f, hf, hJ, -⟩ := modular_equation hℓ (iso_Pdisc hℓ) (by norm_num : 1 ≤ 12) hζ
  obtain ⟨H₀, hH₀⟩ := subs_nonempty ℓ (shortModel_disc_ne hW0)
  obtain ⟨G, hmem, hinj, hsurj, -, hk⟩ :=
    algebraicity_general hℓ ψ hζK ι hι hKer hf hζ hJ W hW0 hH₀
  have h := hk (ℓ + 1)
  rw [f_last hℓ hζ hf hJ] at h
  rw [_root_.map_mul, _root_.map_pow, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    eval_Pdisc, MvPolynomial.map_C, MvPolynomial.eval_C] at h
  have hcard : Fintype.card (Option (Fin ℓ)) = ℓ + 1 := by simp
  have e : MvPolynomial.esymm (Option (Fin ℓ)) K (ℓ + 1) = ∏ i, MvPolynomial.X i := by
    rw [← hcard]; exact esymm_card
  rw [e, MvPolynomial.eval_prod, Fintype.prod_option] at h
  simp only [MvPolynomial.eval_X, Option.elim] at h
  have hZimg : Z = Finset.univ.image G := by
    ext C
    rw [← hZ C, Finset.mem_image]
    constructor
    · intro hC
      obtain ⟨c, hc⟩ := hsurj C hC
      exact ⟨c, Finset.mem_univ _, hc⟩
    · rintro ⟨c, -, rfl⟩
      exact hmem c
  rw [hZimg, Finset.prod_image (fun x _ y _ hxy => hinj hxy), Fin.prod_univ_succ, ← h]
  simp [map_pow, map_natCast]
  ring

end Curve

/-! ### Over `ℂ_ℓ` -/

section C
open Classical

include hℓ in
/-- **`ProdDelta` over `ℂ_ℓ`**, unconditionally. -/
theorem prodDelta_C : ProdDelta ℓ ℂ_[ℓ] := by
  have hℓ0 : ℓ ≠ 0 := hℓp.out.ne_zero
  haveI : NeZero (ℓ : ℂ_[ℓ]) := ⟨by
    have : (ℓ : ℂ_[ℓ]) = algebraMap ℚ_[ℓ] ℂ_[ℓ] (ℓ : ℚ_[ℓ]) := by simp
    rw [this]; exact (map_ne_zero _).mpr (by exact_mod_cast hℓ0)⟩
  obtain ⟨ζK, hζK⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[ℓ] ℓ
  set F := FractionRing (PowerSeries ℂ_[ℓ])
  set L := AlgebraicClosure F
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
  let ι : PowerSeries ℂ_[ℓ] →+* L := (algebraMap F L).comp (algebraMap (PowerSeries ℂ_[ℓ]) F)
  have hι : Function.Injective ι :=
    (algebraMap F L).injective.comp (IsFractionRing.injective (PowerSeries ℂ_[ℓ]) F)
  exact prodDelta hℓ (algebraMap ℚ_[ℓ] ℂ_[ℓ]) hζK ι hι (TateAdd.tateKernels hι hζK hℓ)

/-- **`QuotE.OrdEBound hℓ (SharpHQ.φC ℓ)`**, unconditionally. -/
theorem ordEBound_C' : QuotE.OrdEBound hℓ (SharpHQ.φC ℓ) :=
  ordEBound_C hℓ (prodDelta_C hℓ)

end C

end OrdQuot
