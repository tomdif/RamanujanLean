import RamanujanTau.VLayer.ModEq

/-!
# The level-`ℓ` modular equation of an arbitrary classical form

For an isobaric `P ∈ ℤ_ℓ[E₄, E₆]` of weight `w ≥ 1` with q-expansion `F`, the `ℓ + 1` conjugates

  `y_∞ = ℓ^w F(t^{ℓ²}) = ℓ^w (V F)(q)`,   `y_j = F(ζ^j t)`   (`t^ℓ = q`, `j < ℓ`)

have power sums `ℓ · T_ℓ(F^m)` (`HeckeQExp.tate_geom_sum`), hence (Newton) elementary symmetric
functions that are classical of weight `k w` and `ℓ`-integral.

**`modular_equation`**: there are isobaric `f_k ∈ ℤ_ℓ[X₀,X₁]` of weight `k w` with

  `Σ_{k ≤ ℓ+1} (−1)^k f_k(E₄,E₆) · (ℓ^w V F)^{ℓ+1−k} = 0`,

and `f_k(E₄,E₆)(t^ℓ) = e_k(y)` (so further properties of the `f_k` can be read off the conjugates).
This is the generalization of `VLayer.modular_equation_E` (`P = A`, `w = ℓ − 1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VLayer
open PowerSeries ModP AtkinOBrienFinal HeckeQExp

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (P : Poly ℓ) (w : ℕ)

/-- `F = P(E₄,E₆) ∈ ℚ_ℓ⟦q⟧`. -/
noncomputable def Fq : PowerSeries ℚ_[ℓ] := map (ιz ℓ) (ev ℤ_[ℓ] P)
/-- `F ∈ \bar{ℚ}_ℓ⟦t⟧`. -/
noncomputable def FK : PowerSeries (PadicAlgCl ℓ) := map (ιq ℓ) (Fq P)

/-- the conjugates `y_∞ = ℓ^w F(t^{ℓ²})`, `y_j = F(ζ^j t)`. -/
noncomputable def ys (ζ : PadicAlgCl ℓ) : Option (Fin ℓ) → PowerSeries (PadicAlgCl ℓ)
  | none => expand ℓ (ell_ne_zero' ℓ) (C ((ℓ : PadicAlgCl ℓ) ^ w) *
      expand ℓ (ell_ne_zero' ℓ) (FK P))
  | some j => rescale (ζ ^ (j : ℕ)) (FK P)

lemma ys_none_eq (ζ : PadicAlgCl ℓ) :
    ys P w ζ none = J ℓ (C ((ℓ : ℚ_[ℓ]) ^ w) * expand ℓ (ell_ne_zero' ℓ) (Fq P)) := by
  rw [ys, J_apply]; congr 1
  rw [map_mul, map_C, map_expand, FK]; congr 2; simp

lemma GB_FK : GB 1 (FK P) := fun n => by
  rw [FK, Fq, coeff_map, coeff_map]; exact norm_ιz_le ℓ _

lemma GB_ys {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) (i : Option (Fin ℓ)) :
    GB 1 (ys P w ζ i) := by
  cases i with
  | none =>
    rw [ys]
    refine GB_expand zero_le_one _ ?_
    have h := (GB_C (K := PadicAlgCl ℓ) (a := (ℓ : PadicAlgCl ℓ) ^ w) (ρ := 1) ?_
      zero_le_one).mul (GB_expand zero_le_one (ell_ne_zero' ℓ) (GB_FK P)) zero_le_one
      zero_le_one
    · simpa using h
    · rw [norm_pow, norm_ell_K]; exact pow_le_one₀ (by positivity) (ell_inv_le_one ℓ)
  | some j =>
    rw [ys]; exact GB_rescale (by rw [norm_pow, norm_zeta ℓ hζ, one_pow]) (GB_FK P)

/-- `P` over `ℚ_ℓ`. -/
noncomputable def Pq : MvPolynomial (Fin 2) ℚ_[ℓ] := MvPolynomial.map (ιz ℓ) P

lemma ev_Pq : ev ℚ_[ℓ] (Pq P) = Fq P := by rw [Pq, ← map_ev]; rfl

variable {P w}

lemma iso_Pq_pow (hP : Iso P w) (m : ℕ) : Iso (Pq P ^ m) (m * w) :=
  iso_of_eq ((iso_map (ιz ℓ) hP).pow m) (by rw [smul_eq_mul])

variable (P) in
/-- `ℓ · T_ℓ(P^m)`. -/
noncomputable def sigP (m : ℕ) : MvPolynomial (Fin 2) ℚ_[ℓ] :=
  MvPolynomial.C (ℓ : ℚ_[ℓ]) * heckePoly ℓ (Pq P ^ m)

lemma iso_sigP (hP : Iso P w) (m : ℕ) : Iso (sigP P m) (m * w) :=
  (iso_heckePoly ℓ (iso_Pq_pow hP m)).C_mul _

/-- **Power sums of the conjugates**: `Σ_C y_C^m = ℓ · (T_ℓ F^m)(t^ℓ)`. -/
lemma psum_ys (hP : Iso P w) (hw : 1 ≤ w) {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) {m : ℕ}
    (hm : 1 ≤ m) : ∑ i, ys P w ζ i ^ m = J ℓ (ev ℚ_[ℓ] (sigP P m)) := by
  have hk : 1 ≤ m * w := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hT := tate_geom_sum hℓp.out hζ hk (FK P ^ m)
  have h2 : ∑ j : Fin ℓ, ys P w ζ (some j) ^ m =
      ∑ j ∈ Finset.range ℓ, rescale (ζ ^ j) (FK P ^ m) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => rescale (ζ ^ j) (FK P ^ m))]
    simp [ys, map_pow]
  have h1 : ys P w ζ none ^ m = expand ℓ (ell_ne_zero' ℓ)
      (C ((ℓ : PadicAlgCl ℓ) ^ (m * w)) * expand ℓ (ell_ne_zero' ℓ) (FK P ^ m)) := by
    rw [ys, ← map_pow, mul_pow, ← map_pow, ← map_pow, ← pow_mul, mul_comm w m]
  rw [Fintype.sum_option, h1, h2, hT]
  symm
  rw [sigP, J_apply, map_mul (ev ℚ_[ℓ]), ev_C, ev_heckePoly ℓ (iso_Pq_pow hP m),
    map_mul (map (ιq ℓ)), map_C, map_Tq, map_pow, ev_Pq, mulQ_of_pos ℓ hk]
  congr 3 <;> first | rfl | simp [FK]

lemma aeval_psum_ys (ζ : PadicAlgCl ℓ) (m : ℕ) :
    MvPolynomial.aeval (ys P w ζ) (MvPolynomial.psum (Option (Fin ℓ)) ℤ m) =
      ∑ i, ys P w ζ i ^ m := by
  simp [MvPolynomial.psum]

/-- **Newton**: `e_k(y)` is the image of a classical form of weight `k w` over `ℚ_ℓ`. -/
theorem exists_esymm_gen (hP : Iso P w) (hw : 1 ≤ w) {ζ : PadicAlgCl ℓ}
    (hζ : IsPrimitiveRoot ζ ℓ) (k : ℕ) :
    ∃ Q : MvPolynomial (Fin 2) ℚ_[ℓ], Iso Q (k * w) ∧
      J ℓ (ev ℚ_[ℓ] Q) =
        MvPolynomial.aeval (ys P w ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k) := by
  classical
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, ?_, ?_⟩
    · simpa using (MvPolynomial.isWeightedHomogeneous_one ℚ_[ℓ] wt)
    · simp [MvPolynomial.esymm_zero]
  choose Q hQ hQe using fun j (hj : j < k) => ih j hj
  let Qf : ℕ → MvPolynomial (Fin 2) ℚ_[ℓ] := fun j => if h : j < k then Q j h else 0
  have hQf : ∀ j, j < k → Iso (Qf j) (j * w) ∧
      J ℓ (ev ℚ_[ℓ] (Qf j)) =
        MvPolynomial.aeval (ys P w ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ j) := by
    intro j hj
    simp only [Qf, dif_pos hj]
    exact ⟨hQ j hj, hQe j hj⟩
  let S : MvPolynomial (Fin 2) ℚ_[ℓ] := ∑ a ∈ Finset.antidiagonal k with a.1 < k,
      MvPolynomial.C ((-1 : ℚ_[ℓ]) ^ a.1) * Qf a.1 * sigP P a.2
  refine ⟨MvPolynomial.C ((k : ℚ_[ℓ])⁻¹ * (-1) ^ (k + 1)) * S, ?_, ?_⟩
  · refine (MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun a ha => ?_).C_mul _
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    have hsum : a.1 + a.2 = k := Finset.mem_antidiagonal.mp ha1
    refine iso_of_eq ((((MvPolynomial.isWeightedHomogeneous_C wt _).mul
      (hQf a.1 ha2).1)).mul (iso_sigP hP a.2)) ?_
    rw [← hsum]; ring
  · have hN := congrArg (MvPolynomial.aeval (ys P w ζ))
      (MvPolynomial.mul_esymm_eq_sum (Option (Fin ℓ)) ℤ k)
    simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast] at hN
    have hS : J ℓ (ev ℚ_[ℓ] S) = ∑ a ∈ Finset.antidiagonal k with a.1 < k,
        (-1) ^ a.1 * MvPolynomial.aeval (ys P w ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ a.1) *
          MvPolynomial.aeval (ys P w ζ) (MvPolynomial.psum (Option (Fin ℓ)) ℤ a.2) := by
      simp only [S, map_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      have hsum : a.1 + a.2 = k := Finset.mem_antidiagonal.mp ha1
      rw [map_mul, map_mul, map_mul, map_mul, ev_C, J_C, (hQf a.1 ha2).2, aeval_psum_ys,
        psum_ys hP hw hζ (by omega)]
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

variable (P w) in
/-- **`y_∞` is a root of `∏_C (X − y_C)`.** -/
theorem root_identity_gen (ζ : PadicAlgCl ℓ) :
    ∑ k ∈ Finset.range (ℓ + 2), (-1) ^ k *
      MvPolynomial.aeval (ys P w ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k) *
        ys P w ζ none ^ (ℓ + 1 - k) = 0 := by
  classical
  set s := (Finset.univ : Finset (Option (Fin ℓ))).val.map (ys P w ζ) with hs
  have hcard : Multiset.card s = ℓ + 1 := by simp [s]
  have h := congrArg (Polynomial.eval (ys P w ζ none)) (Multiset.prod_X_sub_X_eq_sum_esymm s)
  rw [Polynomial.eval_multiset_prod, Multiset.map_map] at h
  have h0 : (Multiset.map (Polynomial.eval (ys P w ζ none) ∘ fun t => Polynomial.X - Polynomial.C t)
      s).prod = 0 := by
    refine Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨ys P w ζ none, ?_, by simp⟩)
    exact Multiset.mem_map.mpr ⟨none, Finset.mem_univ_val _, rfl⟩
  rw [h0, Polynomial.eval_finsetSum, hcard] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  simp [mul_assoc, hs]

lemma GB_esymm_ys {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) (k : ℕ) :
    GB 1 (MvPolynomial.aeval (ys P w ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k)) := by
  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.aeval_X]
  exact GB_sum zero_le_one _ _ fun t _ => GB_prod _ _ fun i _ => GB_ys P w hζ i

/-- **The modular equation of `P`** (with the link to the conjugates). -/
theorem modular_equation (hℓ : 5 ≤ ℓ) (hP : Iso P w) (hw : 1 ≤ w) {ζ : PadicAlgCl ℓ}
    (hζ : IsPrimitiveRoot ζ ℓ) :
    ∃ f : ℕ → Poly ℓ, (∀ k, Iso (f k) (k * w)) ∧
      (∀ k, J ℓ (map (ιz ℓ) (ev ℤ_[ℓ] (f k))) =
        MvPolynomial.aeval (ys P w ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k)) ∧
      ∑ k ∈ Finset.range (ℓ + 2), (-1) ^ k * ev ℤ_[ℓ] (f k) *
        (C ((ℓ : ℤ_[ℓ]) ^ w) * expand ℓ (ell_ne_zero' ℓ) (ev ℤ_[ℓ] P)) ^ (ℓ + 1 - k) = 0 := by
  choose e he hJ using exists_esymm_gen hP hw hζ
  have hint : ∀ k, ∃ f : Poly ℓ, Iso f (k * w) ∧ MvPolynomial.map (ιz ℓ) f = e k := by
    intro k
    obtain ⟨g, hg⟩ := exists_int_of_GB ℓ (F := ev ℚ_[ℓ] (e k))
      (by rw [hJ]; exact GB_esymm_ys hζ k)
    exact descend (ιz ℓ) Subtype.val_injective (isUnit_1728_Zp hℓ) _ _ (he k) ⟨g, hg⟩
  choose f hf hfe using hint
  have hev : ∀ k, map (ιz ℓ) (ev ℤ_[ℓ] (f k)) = ev ℚ_[ℓ] (e k) := fun k => by
    rw [map_ev, hfe]
  refine ⟨f, hf, fun k => by rw [hev, hJ], ?_⟩
  apply map_injective (ιz ℓ) Subtype.val_injective
  apply J_injective ℓ
  have hx : J ℓ (map (ιz ℓ) (C ((ℓ : ℤ_[ℓ]) ^ w) * expand ℓ (ell_ne_zero' ℓ) (ev ℤ_[ℓ] P))) =
      ys P w ζ none := by
    rw [ys_none_eq, map_mul, map_C, map_expand]; simp [Fq]
  rw [map_zero, map_zero, ← root_identity_gen P w ζ, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_mul, map_pow, map_neg, map_one]
  rw [hev, hJ, ← hx]
  simp only [map_mul, map_pow]

end VLayer
