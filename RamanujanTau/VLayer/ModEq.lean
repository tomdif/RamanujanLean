import RamanujanTau.VLayer.GB
import RamanujanTau.HeckeQExp.Poly
import RamanujanTau.DBound.Decomp

/-!
# The modular equation of `E = E_{ℓ−1}` of level `ℓ`

Let `t = q^{1/ℓ}` and `ζ` a primitive `ℓ`-th root of unity. The `ℓ + 1` "conjugates"

  `x_∞ = ℓ^{ℓ−1} E(t^{ℓ²}) = ℓ^{ℓ−1} (V E)(q)`,   `x_j = E(ζ^j t)`  (`j < ℓ`)

are the values `E(Tate/C, ω_C)` over the `ℓ + 1` subgroups `C` of order `ℓ` (Vélu normalization; see
`HeckeQExp.tate_geom_sum`). Their power sums are `p_m = ℓ · T_ℓ(E^m)`, which are classical level-one
forms (`HeckeQExp.heckePoly`). By Newton's identities their elementary symmetric functions are
classical level-one forms `e_k` of weight `k(ℓ−1)` (over `ℚ_ℓ`); they are `ℓ`-integral because the
conjugates are (norms in `PadicAlgCl ℓ`), hence (`ModP.descend`) isobaric polynomials over `ℤ_ℓ`.
Since `x_∞` is a root of `∏_C (X − x_C)`:

**`modular_equation_E`**: there are isobaric `f_k ∈ ℤ_ℓ[E₄, E₆]` of weight `k(ℓ−1)` with

  `Σ_{k ≤ ℓ+1} (−1)^k f_k(E₄,E₆) · (ℓ^{ℓ−1} V E)^{ℓ+1−k} = 0`   in `ℤ_ℓ⟦q⟧`,

and `f_ℓ(E₄,E₆) ≡ 1 (mod ℓ)`.

No modular curve, Tate parametrization of quotients, or rigid geometry enters: only the q-series
identity `tate_geom_sum`, the Hecke operator on isobaric polynomials, and Newton's identities.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VLayer
open PowerSeries ModP AtkinOBrienFinal HeckeQExp

variable (ℓ : ℕ) [hℓp : Fact ℓ.Prime]

/-- `ℚ_ℓ → \bar{ℚ}_ℓ`. -/
noncomputable abbrev ιq : ℚ_[ℓ] →+* PadicAlgCl ℓ := algebraMap _ _
/-- `ℤ_ℓ → ℚ_ℓ`. -/
noncomputable abbrev ιz : ℤ_[ℓ] →+* ℚ_[ℓ] := PadicInt.Coe.ringHom

lemma ell_ne_zero' : ℓ ≠ 0 := hℓp.out.ne_zero

lemma norm_ιq (a : ℚ_[ℓ]) : ‖ιq ℓ a‖ = ‖a‖ := PadicAlgCl.norm_extends ℓ a

lemma norm_ell_K : ‖(ℓ : PadicAlgCl ℓ)‖ = (ℓ : ℝ)⁻¹ := by
  rw [show (ℓ : PadicAlgCl ℓ) = ιq ℓ (ℓ : ℚ_[ℓ]) from (map_natCast _ _).symm, norm_ιq,
    Padic.norm_p]

lemma ell_inv_le_one : (ℓ : ℝ)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by exact_mod_cast hℓp.out.one_lt.le)

lemma exists_zeta : ∃ ζ : PadicAlgCl ℓ, IsPrimitiveRoot ζ ℓ := by
  haveI : NeZero (ℓ : PadicAlgCl ℓ) := ⟨Nat.cast_ne_zero.mpr (ell_ne_zero' ℓ)⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic ℓ (PadicAlgCl ℓ))
    (Polynomial.degree_cyclotomic_pos ℓ _ hℓp.out.pos).ne'
  exact ⟨z, Polynomial.isRoot_cyclotomic_iff.mp hz⟩

lemma norm_zeta {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) : ‖ζ‖ = 1 := by
  have h := congrArg norm hζ.pow_eq_one
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (ell_ne_zero' ℓ)).mp h

variable (hℓ : 5 ≤ ℓ)

/-- `E ∈ ℚ_ℓ⟦q⟧`. -/
noncomputable def Eq : PowerSeries ℚ_[ℓ] := map (ιz ℓ) (E ℓ hℓ)
/-- `E ∈ \bar{ℚ}_ℓ⟦q⟧`. -/
noncomputable def EK : PowerSeries (PadicAlgCl ℓ) := map (ιq ℓ) (Eq ℓ hℓ)

/-- `F(q) ↦ F(t^ℓ)`, `ℚ_ℓ⟦q⟧ → \bar{ℚ}_ℓ⟦t⟧`. -/
noncomputable def J : PowerSeries ℚ_[ℓ] →+* PowerSeries (PadicAlgCl ℓ) :=
  (expand ℓ (ell_ne_zero' ℓ)).toRingHom.comp (map (ιq ℓ))

lemma J_apply (F : PowerSeries ℚ_[ℓ]) : J ℓ F = expand ℓ (ell_ne_zero' ℓ) (map (ιq ℓ) F) := rfl

lemma coeff_J (F : PowerSeries ℚ_[ℓ]) (n : ℕ) : coeff (ℓ * n) (J ℓ F) = ιq ℓ (coeff n F) := by
  rw [J_apply, coeff_expand, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hℓp.out.pos,
    coeff_map]

lemma J_injective : Function.Injective (J ℓ) := by
  intro F G h
  ext n
  have := congrArg (coeff (ℓ * n)) h
  rw [coeff_J, coeff_J] at this
  exact (ιq ℓ).injective this

lemma J_C (a : ℚ_[ℓ]) : J ℓ (C a) = C (ιq ℓ a) := by
  rw [J_apply, map_C, expand_C]

/-- a bound on `J F` gives the same bound on `F`. -/
lemma norm_coeff_of_GB {ρ : ℝ} {F : PowerSeries ℚ_[ℓ]} (h : GB ρ (J ℓ F)) (n : ℕ) :
    ‖coeff n F‖ ≤ ρ := by
  have := h (ℓ * n)
  rwa [coeff_J, norm_ιq] at this

/-- integral coefficients descend to `ℤ_ℓ`. -/
lemma exists_int_of_GB {F : PowerSeries ℚ_[ℓ]} (h : GB 1 (J ℓ F)) :
    ∃ g : PowerSeries ℤ_[ℓ], map (ιz ℓ) g = F := by
  refine ⟨mk fun n => ⟨coeff n F, norm_coeff_of_GB ℓ h n⟩, ?_⟩
  ext n
  rw [coeff_map, coeff_mk]; rfl

lemma norm_ιz_le (a : ℤ_[ℓ]) : ‖ιq ℓ (ιz ℓ a)‖ ≤ 1 := by
  rw [norm_ιq]; exact a.2

lemma GB_EK : GB 1 (EK ℓ hℓ) := fun n => by
  rw [EK, Eq, coeff_map, coeff_map]; exact norm_ιz_le ℓ _

lemma GB_EK_sub_one : GB (ℓ : ℝ)⁻¹ (EK ℓ hℓ - 1) := fun n => by
  obtain ⟨y, hy⟩ := PS_dvd_of_map (E ℓ hℓ - 1) (by rw [map_sub, map_E, map_one, sub_self])
  have : EK ℓ hℓ - 1 = map ((ιq ℓ).comp (ιz ℓ)) (E ℓ hℓ - 1) := by
    rw [EK, Eq, map_sub, map_one, psmap_map]
  rw [this, hy, coeff_map, coeff_smul, smul_eq_mul, map_mul, norm_mul, map_natCast,
    norm_ell_K]
  have h1 : ‖((ιq ℓ).comp (ιz ℓ)) (coeff n y)‖ ≤ 1 := norm_ιz_le ℓ _
  calc (ℓ : ℝ)⁻¹ * ‖((ιq ℓ).comp (ιz ℓ)) (coeff n y)‖ ≤ (ℓ : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := mul_one _

/-! ### the conjugates -/

variable {ℓ}

/-- `x_∞ = ℓ^{ℓ−1} E(t^{ℓ²})` and `x_j = E(ζ^j t)`. -/
noncomputable def xs (ζ : PadicAlgCl ℓ) : Option (Fin ℓ) → PowerSeries (PadicAlgCl ℓ)
  | none => expand ℓ (ell_ne_zero' ℓ) (C ((ℓ : PadicAlgCl ℓ) ^ (ℓ - 1)) *
      expand ℓ (ell_ne_zero' ℓ) (EK ℓ hℓ))
  | some j => rescale (ζ ^ (j : ℕ)) (EK ℓ hℓ)

lemma xs_none_eq (ζ : PadicAlgCl ℓ) :
    xs hℓ ζ none = J ℓ (C ((ℓ : ℚ_[ℓ]) ^ (ℓ - 1)) * expand ℓ (ell_ne_zero' ℓ) (Eq ℓ hℓ)) := by
  rw [xs, J_apply]; congr 1
  rw [map_mul, map_C, map_expand, EK]; congr 2; simp

lemma GB_xs_none (ζ : PadicAlgCl ℓ) : GB (ℓ : ℝ)⁻¹ (xs hℓ ζ none) := by
  rw [xs]
  refine GB_expand (by positivity) _ ?_
  have h := (GB_C (K := PadicAlgCl ℓ) (a := (ℓ : PadicAlgCl ℓ) ^ (ℓ - 1)) (ρ := (ℓ : ℝ)⁻¹) ?_
    (by positivity)).mul (GB_expand zero_le_one (ell_ne_zero' ℓ) (GB_EK ℓ hℓ)) (by positivity)
    zero_le_one
  · simpa using h
  · rw [norm_pow, norm_ell_K]
    have hl : 1 ≤ ℓ - 1 := by have := hℓp.out.two_le; omega
    calc ((ℓ : ℝ)⁻¹) ^ (ℓ - 1) ≤ ((ℓ : ℝ)⁻¹) ^ 1 :=
          pow_le_pow_of_le_one (by positivity) (ell_inv_le_one ℓ) hl
      _ = _ := pow_one _

lemma GB_xs_some {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) (j : Fin ℓ) :
    GB 1 (xs hℓ ζ (some j)) := by
  rw [xs]; exact GB_rescale (by rw [norm_pow, norm_zeta ℓ hζ, one_pow]) (GB_EK ℓ hℓ)

lemma GB_xs_some_sub_one {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) (j : Fin ℓ) :
    GB (ℓ : ℝ)⁻¹ (xs hℓ ζ (some j) - 1) := by
  rw [xs, show rescale (ζ ^ (j : ℕ)) (EK ℓ hℓ) - 1 = rescale (ζ ^ (j : ℕ)) (EK ℓ hℓ - 1) by
    rw [map_sub, map_one]]
  exact GB_rescale (by rw [norm_pow, norm_zeta ℓ hζ, one_pow]) (GB_EK_sub_one ℓ hℓ)

lemma GB_xs {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) (i : Option (Fin ℓ)) :
    GB 1 (xs hℓ ζ i) := by
  cases i with
  | none => exact (GB_xs_none hℓ ζ).mono (ell_inv_le_one ℓ)
  | some j => exact GB_xs_some hℓ hζ j

/-! ### the power sums are Hecke images -/

variable (ℓ) in
/-- the Hasse polynomial over `ℚ_ℓ` (`A(E₄,E₆) = E`). -/
noncomputable def Aq : MvPolynomial (Fin 2) ℚ_[ℓ] := MvPolynomial.map (ιz ℓ) (hasseA ℓ hℓ)

lemma ev_Aq : ev ℚ_[ℓ] (Aq ℓ hℓ) = Eq ℓ hℓ := by
  rw [Aq, ← map_ev, DBound.ev_hasseA_E hℓ]; rfl

lemma iso_Aq_pow (m : ℕ) : Iso (Aq ℓ hℓ ^ m) (m * (ℓ - 1)) :=
  iso_of_eq ((iso_map (ιz ℓ) (iso_hasseA hℓ)).pow m) (by rw [smul_eq_mul])

variable (ℓ) in
/-- `ℓ · T_ℓ(A^m)`: the `m`-th power sum of the conjugates. -/
noncomputable def sig (m : ℕ) : MvPolynomial (Fin 2) ℚ_[ℓ] :=
  MvPolynomial.C (ℓ : ℚ_[ℓ]) * heckePoly ℓ (Aq ℓ hℓ ^ m)

lemma iso_sig (m : ℕ) : Iso (sig ℓ hℓ m) (m * (ℓ - 1)) :=
  (iso_heckePoly ℓ (iso_Aq_pow hℓ m)).C_mul _

/-- **Power sums of the conjugates**: `Σ_C x_C^m = ℓ · (T_ℓ E^m)(t^ℓ)`. -/
lemma psum_xs {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) {m : ℕ} (hm : 1 ≤ m) :
    ∑ i, xs hℓ ζ i ^ m = J ℓ (ev ℚ_[ℓ] (sig ℓ hℓ m)) := by
  have hl : 1 ≤ ℓ - 1 := by have := hℓp.out.two_le; omega
  have hk : 1 ≤ m * (ℓ - 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hT := tate_geom_sum hℓp.out hζ hk (EK ℓ hℓ ^ m)
  have h2 : ∑ j : Fin ℓ, xs hℓ ζ (some j) ^ m =
      ∑ j ∈ Finset.range ℓ, rescale (ζ ^ j) (EK ℓ hℓ ^ m) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => rescale (ζ ^ j) (EK ℓ hℓ ^ m))]
    simp [xs, map_pow]
  have h1 : xs hℓ ζ none ^ m = expand ℓ (ell_ne_zero' ℓ)
      (C ((ℓ : PadicAlgCl ℓ) ^ (m * (ℓ - 1))) * expand ℓ (ell_ne_zero' ℓ) (EK ℓ hℓ ^ m)) := by
    rw [xs, ← map_pow, mul_pow, ← map_pow, ← map_pow, ← pow_mul, mul_comm (ℓ - 1) m]
  rw [Fintype.sum_option, h1, h2, hT]
  symm
  rw [sig, J_apply, map_mul (ev ℚ_[ℓ]), ev_C, ev_heckePoly ℓ (iso_Aq_pow hℓ m),
    map_mul (map (ιq ℓ)), map_C, map_Tq, map_pow, ev_Aq, mulQ_of_pos ℓ hk]
  congr 3 <;> first | rfl | simp [EK]

lemma aeval_psum (ζ : PadicAlgCl ℓ) (m : ℕ) :
    MvPolynomial.aeval (xs hℓ ζ) (MvPolynomial.psum (Option (Fin ℓ)) ℤ m) = ∑ i, xs hℓ ζ i ^ m := by
  simp [MvPolynomial.psum]

/-! ### Newton's identities: the elementary symmetric functions are classical -/

/-- **The `k`-th elementary symmetric function of the conjugates is a level-one form of weight
`k(ℓ−1)`** (over `ℚ_ℓ`). -/
theorem exists_esymm {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) (k : ℕ) :
    ∃ P : MvPolynomial (Fin 2) ℚ_[ℓ], Iso P (k * (ℓ - 1)) ∧
      J ℓ (ev ℚ_[ℓ] P) =
        MvPolynomial.aeval (xs hℓ ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k) := by
  classical
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, ?_, ?_⟩
    · simpa using (MvPolynomial.isWeightedHomogeneous_one ℚ_[ℓ] wt)
    · simp [MvPolynomial.esymm_zero]
  choose P hP hPe using fun j (hj : j < k) => ih j hj
  let Pf : ℕ → MvPolynomial (Fin 2) ℚ_[ℓ] := fun j => if h : j < k then P j h else 0
  have hPf : ∀ j, j < k → Iso (Pf j) (j * (ℓ - 1)) ∧
      J ℓ (ev ℚ_[ℓ] (Pf j)) =
        MvPolynomial.aeval (xs hℓ ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ j) := by
    intro j hj
    simp only [Pf, dif_pos hj]
    exact ⟨hP j hj, hPe j hj⟩
  let S : MvPolynomial (Fin 2) ℚ_[ℓ] := ∑ a ∈ Finset.antidiagonal k with a.1 < k,
      MvPolynomial.C ((-1 : ℚ_[ℓ]) ^ a.1) * Pf a.1 * sig ℓ hℓ a.2
  refine ⟨MvPolynomial.C ((k : ℚ_[ℓ])⁻¹ * (-1) ^ (k + 1)) * S, ?_, ?_⟩
  · refine (MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun a ha => ?_).C_mul _
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    have hsum : a.1 + a.2 = k := Finset.mem_antidiagonal.mp ha1
    refine iso_of_eq ((((MvPolynomial.isWeightedHomogeneous_C wt _).mul
      (hPf a.1 ha2).1)).mul (iso_sig hℓ a.2)) ?_
    rw [← hsum]; ring
  · have hN := congrArg (MvPolynomial.aeval (xs hℓ ζ))
      (MvPolynomial.mul_esymm_eq_sum (Option (Fin ℓ)) ℤ k)
    simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast] at hN
    have hS : J ℓ (ev ℚ_[ℓ] S) = ∑ a ∈ Finset.antidiagonal k with a.1 < k,
        (-1) ^ a.1 * MvPolynomial.aeval (xs hℓ ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ a.1) *
          MvPolynomial.aeval (xs hℓ ζ) (MvPolynomial.psum (Option (Fin ℓ)) ℤ a.2) := by
      simp only [S, map_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      have hsum : a.1 + a.2 = k := Finset.mem_antidiagonal.mp ha1
      rw [map_mul, map_mul, map_mul, map_mul, ev_C, J_C, (hPf a.1 ha2).2, aeval_psum,
        psum_xs hℓ hζ (by omega)]
      simp
    rw [map_mul, map_mul, ev_C, J_C, hS]
    have hk0 : (k : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    have e1 : C (ιq ℓ ((k : ℚ_[ℓ])⁻¹ * (-1) ^ (k + 1))) =
        C (ιq ℓ (k : ℚ_[ℓ])⁻¹) * (-1 : PowerSeries (PadicAlgCl ℓ)) ^ (k + 1) := by
      simp [map_mul]
    have e2 : C (ιq ℓ (k : ℚ_[ℓ])⁻¹) * (k : PowerSeries (PadicAlgCl ℓ)) = 1 := by
      rw [show (k : PowerSeries (PadicAlgCl ℓ)) = C (ιq ℓ (k : ℚ_[ℓ])) by simp, ← map_mul,
        ← map_mul, inv_mul_cancel₀ hk0, map_one, map_one]
    rw [e1, mul_assoc, ← hN, ← mul_assoc, e2, one_mul]

/-! ### `x_∞` is a root; integrality -/

/-- **`x_∞` is a root of `∏_C (X − x_C) = Σ_k (−1)^k e_k X^{ℓ+1−k}`.** -/
theorem root_identity (ζ : PadicAlgCl ℓ) :
    ∑ k ∈ Finset.range (ℓ + 2), (-1) ^ k *
      MvPolynomial.aeval (xs hℓ ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k) *
        xs hℓ ζ none ^ (ℓ + 1 - k) = 0 := by
  classical
  set s := (Finset.univ : Finset (Option (Fin ℓ))).val.map (xs hℓ ζ) with hs
  have hcard : Multiset.card s = ℓ + 1 := by simp [s]
  have h := congrArg (Polynomial.eval (xs hℓ ζ none)) (Multiset.prod_X_sub_X_eq_sum_esymm s)
  rw [Polynomial.eval_multiset_prod, Multiset.map_map] at h
  have h0 : (Multiset.map (Polynomial.eval (xs hℓ ζ none) ∘ fun t => Polynomial.X - Polynomial.C t)
      s).prod = 0 := by
    refine Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨xs hℓ ζ none, ?_, by simp⟩)
    exact Multiset.mem_map.mpr ⟨none, Finset.mem_univ_val _, rfl⟩
  rw [h0, Polynomial.eval_finsetSum, hcard] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  simp [mul_assoc, hs]

lemma GB_esymm {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) (k : ℕ) :
    GB 1 (MvPolynomial.aeval (xs hℓ ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k)) := by
  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.aeval_X]
  exact GB_sum zero_le_one _ _ fun t _ => GB_prod _ _ fun i _ => GB_xs hℓ hζ i

/-- **`e_ℓ ≡ 1 (mod ℓ)`**: `e_ℓ = ∏_j x_j + x_∞·(…)` and `x_j ≡ 1`, `x_∞ ≡ 0`. -/
lemma GB_esymm_ell {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) :
    GB (ℓ : ℝ)⁻¹ (MvPolynomial.aeval (xs hℓ ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ ℓ) - 1) := by
  classical
  have hρ : (0 : ℝ) ≤ (ℓ : ℝ)⁻¹ := by positivity
  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.aeval_X]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun t => none ∈ t)]
  have hsing : (Finset.powersetCard ℓ (Finset.univ : Finset (Option (Fin ℓ)))).filter
      (fun t => ¬ none ∈ t) = {Finset.univ.erase none} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨-, hc⟩, hn⟩
      refine Finset.eq_of_subset_of_card_le (fun i hi => Finset.mem_erase.mpr
        ⟨fun h => hn (h ▸ hi), Finset.mem_univ _⟩) ?_
      rw [hc, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_option,
        Fintype.card_fin, Nat.add_sub_cancel]
    · rintro rfl
      refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.notMem_erase _ _⟩
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_option,
        Fintype.card_fin, Nat.add_sub_cancel]
  rw [hsing, Finset.sum_singleton, add_sub_assoc]
  refine GB.add (GB_sum hρ _ _ fun t ht => ?_) ?_
  · have hn := (Finset.mem_filter.mp ht).2
    rw [← Finset.mul_prod_erase t _ hn]
    simpa using (GB_xs_none hℓ ζ).mul (GB_prod _ _ fun i _ => GB_xs hℓ hζ i) hρ zero_le_one
  · refine GB_prod_sub_one hρ _ _ (fun i _ => GB_xs hℓ hζ i) fun i hi => ?_
    cases i with
    | none => exact absurd rfl (Finset.mem_erase.mp hi).1
    | some j => exact GB_xs_some_sub_one hℓ hζ j

/-! ### the modular equation over `ℤ_ℓ` -/

/-- **The modular equation of `E_{ℓ−1}`.** There are isobaric `f_k ∈ ℤ_ℓ[X₀,X₁]` of weight
`k(ℓ−1)` (`X₀, X₁ ↦ E₄, E₆`) such that, with `Z = ℓ^{ℓ−1}·E(q^ℓ)`,

  `Σ_{k ≤ ℓ+1} (−1)^k f_k(E₄,E₆) Z^{ℓ+1−k} = 0`  in `ℤ_ℓ⟦q⟧`,

and `f_ℓ(E₄,E₆) ≡ 1 (mod ℓ)`. -/
theorem modular_equation_E :
    ∃ f : ℕ → Poly ℓ, (∀ k, Iso (f k) (k * (ℓ - 1))) ∧
      ∑ k ∈ Finset.range (ℓ + 2), (-1) ^ k * ev ℤ_[ℓ] (f k) *
        (C ((ℓ : ℤ_[ℓ]) ^ (ℓ - 1)) * expand ℓ (ell_ne_zero' ℓ) (E ℓ hℓ)) ^ (ℓ + 1 - k) = 0 ∧
      AtkinOBrien.Dvd (ℓ : ℤ_[ℓ]) 1 (ev ℤ_[ℓ] (f ℓ) - 1) := by
  obtain ⟨ζ, hζ⟩ := exists_zeta ℓ
  choose e he hJ using exists_esymm hℓ hζ
  have hint : ∀ k, ∃ f : Poly ℓ, Iso f (k * (ℓ - 1)) ∧ MvPolynomial.map (ιz ℓ) f = e k := by
    intro k
    obtain ⟨g, hg⟩ := exists_int_of_GB ℓ (F := ev ℚ_[ℓ] (e k)) (by rw [hJ]; exact GB_esymm hℓ hζ k)
    exact descend (ιz ℓ) Subtype.val_injective (isUnit_1728_Zp hℓ) _ _ (he k) ⟨g, hg⟩
  choose f hf hfe using hint
  have hev : ∀ k, map (ιz ℓ) (ev ℤ_[ℓ] (f k)) = ev ℚ_[ℓ] (e k) := fun k => by
    rw [map_ev, hfe]
  refine ⟨f, hf, ?_, ?_⟩
  · apply map_injective (ιz ℓ) Subtype.val_injective
    apply J_injective ℓ
    have hx : J ℓ (map (ιz ℓ) (C ((ℓ : ℤ_[ℓ]) ^ (ℓ - 1)) * expand ℓ (ell_ne_zero' ℓ) (E ℓ hℓ))) =
        xs hℓ ζ none := by
      rw [xs_none_eq, map_mul, map_C, map_expand]; simp [Eq]
    rw [map_zero, map_zero, ← root_identity hℓ ζ, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, map_pow, map_neg, map_one]
    rw [hev, hJ, ← hx]
    simp only [map_mul, map_pow]
  · -- coefficientwise: `‖coeff‖ ≤ ℓ⁻¹ < 1`
    have hb : GB (ℓ : ℝ)⁻¹ (J ℓ (ev ℚ_[ℓ] (e ℓ) - 1)) := by
      rw [map_sub, hJ, map_one]; exact GB_esymm_ell hℓ hζ
    have hc : ∀ n, (ℓ : ℤ_[ℓ]) ∣ coeff n (ev ℤ_[ℓ] (f ℓ) - 1) := by
      intro n
      rw [← PadicInt.norm_lt_one_iff_dvd]
      have h1 := norm_coeff_of_GB ℓ hb n
      rw [← hev, ← map_one (map (ιz ℓ)), ← map_sub, coeff_map] at h1
      have h2 : (ℓ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓp.out.one_lt)
      exact lt_of_le_of_lt (by simpa [PadicInt.norm_def] using h1) h2
    choose y hy using hc
    refine ⟨mk y, ?_⟩
    ext n
    rw [coeff_smul, coeff_mk, pow_one, smul_eq_mul, hy n]

end VLayer
