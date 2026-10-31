import RamanujanTau.BLBound.Modules

/-!
# The dimension of `V̄`

`dim V̄ = ⌊(ℓ+12)/24⌋`, which is the bound of Folsom–Kent–Ono. So `X̄` has rank exactly this number on `S̄`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BLBound
open MvPolynomial ModP BoylanWebb
open RamanujanTau.TheoremA.HalfIntegral

noncomputable section

variable {F : Type*} [Field F]

/-- The monomials of weight `k`. -/
def monoSet (k : ℕ) : Set (Fin 2 →₀ ℕ) := {d | Finsupp.weight wt d = k}

/-- The number of monomials of weight `k`. -/
def monoCount (k : ℕ) : ℕ := (k - 6 * ((k / 2) % 2)) / 12 + 1

/-- The monomials of weight `k` are indexed by a range. -/
def monoEquiv {k : ℕ} (hev : k % 2 = 0) (h2 : k ≠ 2) : Fin (monoCount k) ≃ monoSet k :=
  Equiv.ofBijective
    (fun i => ⟨Finsupp.equivFunOnFinite.symm
      ![(k - 6 * ((k / 2) % 2)) / 4 - 3 * (i : ℕ), (k / 2) % 2 + 2 * (i : ℕ)], by
        have hi := i.2
        unfold monoCount at hi
        change Finsupp.weight wt _ = k
        rw [weight_wt]
        simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
        omega⟩)
    (by
      constructor
      · intro i j hij
        have h1 := congrArg (fun x : monoSet k => (x : Fin 2 →₀ ℕ) 1) hij
        simp at h1
        exact Fin.ext h1
      · rintro ⟨d, hd⟩
        have hw : 4 * d 0 + 6 * d 1 = k := by
          have : Finsupp.weight wt d = k := hd
          rwa [weight_wt] at this
        refine ⟨⟨(d 1 - (k / 2) % 2) / 2, by unfold monoCount; omega⟩, ?_⟩
        apply Subtype.ext
        ext i
        fin_cases i
        · simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Matrix.cons_val_zero]
          simp
          omega
        · simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Matrix.cons_val_one]
          simp
          omega)

/-- The dimension of isobaric polynomials. -/
theorem finrank_W {k : ℕ} (hev : k % 2 = 0) (h2 : k ≠ 2) :
    Module.finrank F (weightedHomogeneousSubmodule F wt k) = monoCount k := by
  have e := monoEquiv hev h2
  haveI : Fintype (monoSet k) := Fintype.ofEquiv _ e
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  change Module.finrank F (Finsupp.supported F F (monoSet k)) = _
  have hl := (Finsupp.supportedEquivFinsupp (M := F) (R := F) (monoSet k))
  rw [hl.finrank_eq, Module.finrank_finsupp_self, Fintype.card_congr e.symm, Fintype.card_fin]

lemma finite_W {k : ℕ} (hev : k % 2 = 0) (h2 : k ≠ 2) :
    FiniteDimensional F (weightedHomogeneousSubmodule F wt k) := by
  have e := monoEquiv hev h2
  haveI : Fintype (monoSet k) := Fintype.ofEquiv _ e
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  change FiniteDimensional F (Finsupp.supported F F (monoSet k))
  exact Module.Finite.equiv (Finsupp.supportedEquivFinsupp (M := F) (R := F) (monoSet k)).symm

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- The constant-term functional on isobaric polynomials. -/
def constFun (k : ℕ) : weightedHomogeneousSubmodule (ZMod ℓ) wt k →ₗ[ZMod ℓ] ZMod ℓ where
  toFun P := eval one2 (P : MvPolynomial (Fin 2) (ZMod ℓ))
  map_add' P Q := by simp
  map_smul' c P := by simp

lemma constFun_apply (k : ℕ) (P : weightedHomogeneousSubmodule (ZMod ℓ) wt k) :
    constFun k P = PowerSeries.constantCoeff (ev (ZMod ℓ) (P : MvPolynomial (Fin 2) (ZMod ℓ))) :=
  (constantCoeff_ev _ _).symm

/-- The cusp part of the isobaric polynomials has one dimension less. -/
theorem finrank_ker_constFun {k : ℕ} (hev : k % 2 = 0) (h2 : k ≠ 2) (h4 : 4 ≤ k) :
    Module.finrank (ZMod ℓ) (LinearMap.ker (constFun (ℓ := ℓ) k)) + 1 = monoCount k := by
  haveI := finite_W (F := ZMod ℓ) hev h2
  have hn' : 4 * bexp0 k + 6 * bexp1 k = k := by
    unfold bexp0 bexp1
    omega
  have hbase : Iso (base k : MvPolynomial (Fin 2) (ZMod ℓ)) k := iso_base hn'
  have hsurj : Function.Surjective (constFun (ℓ := ℓ) k) := by
    intro c
    refine ⟨⟨C c * base k, hbase.C_mul c⟩, ?_⟩
    change eval one2 (C c * base k) = c
    rw [map_mul, eval_C, eval_base, mul_one]
  have hrk := LinearMap.finrank_range_add_finrank_ker (constFun (ℓ := ℓ) k)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, finrank_W hev h2] at hrk
  omega

lemma Psi_Dz_ne (t : ℕ) : Ψ ℓ (Dz ^ t) ≠ 0 := by
  rw [map_pow]
  refine pow_ne_zero t ?_
  rw [Dz, map_mul, map_pow, PowerSeries.map_X]
  refine mul_ne_zero PowerSeries.X_ne_zero (pow_ne_zero _ ?_)
  exact (MockTheta5.JTP.isUnit_qfacInf.map (Ψ ℓ)).ne_zero

/-- **`dim V̄ = ⌊(ℓ+12)/24⌋`.** -/
theorem finrank_Vbar (h13 : 13 ≤ ℓ) : Module.finrank (ZMod ℓ) (Vbar ℓ) = (ℓ + 12) / 24 := by
  have h5 : 5 ≤ ℓ := by omega
  have hd := ell_decomp (ℓ := ℓ)
  have hj := ell_mod h13
  obtain ⟨hk4, hkev⟩ := kprime_form (ℓ := ℓ) h13
  set k := (ℓ + jj ℓ - 2) / 2 with hk
  have hkev' : k % 2 = 0 := Nat.even_iff.mp hkev
  have hrk := finrank_ker_constFun (ℓ := ℓ) hkev' (by omega) hk4
  let f : LinearMap.ker (constFun (ℓ := ℓ) k) →ₗ[ZMod ℓ] Vbar ℓ :=
    { toFun := fun P => ⟨Ψ ℓ (Dz ^ tt ℓ) * ev (ZMod ℓ) ((P : weightedHomogeneousSubmodule (ZMod ℓ) wt k) :
          MvPolynomial (Fin 2) (ZMod ℓ)), by
        have h0 : PowerSeries.coeff 0 (ev (ZMod ℓ) ((P : weightedHomogeneousSubmodule (ZMod ℓ) wt k) :
            MvPolynomial (Fin 2) (ZMod ℓ))) = 0 := by
          rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, ← constFun_apply]
          exact P.2
        obtain ⟨a, ha, he⟩ := exists_lattice h13 ⟨_, (P : weightedHomogeneousSubmodule (ZMod ℓ) wt k).2, rfl⟩ h0
        exact ⟨a, ha, by rw [map_mul, he]⟩⟩
      map_add' := fun P Q => by
        apply Subtype.ext
        simp [mul_add]
      map_smul' := fun c P => by
        apply Subtype.ext
        simp }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    have h1 : Ψ ℓ (Dz ^ tt ℓ) * ev (ZMod ℓ) ((P : weightedHomogeneousSubmodule (ZMod ℓ) wt k) :
        MvPolynomial (Fin 2) (ZMod ℓ)) = 0 := congrArg Subtype.val hP
    have h2 := (mul_eq_zero.mp h1).resolve_left (Psi_Dz_ne _)
    have h3 := eq_zero_of_ev_eq_zero_modP h5 (P : weightedHomogeneousSubmodule (ZMod ℓ) wt k).2 h2
    apply Subtype.ext
    apply Subtype.ext
    exact h3
  have hsurj : Function.Surjective f := by
    rintro ⟨_, a, ha, rfl⟩
    obtain ⟨Q, hQ, hQe⟩ := formBar_of_intForm ℓ h5 (k + 1) k (by omega) a (intForm_of_lattice ha)
    have h0 : constFun (ℓ := ℓ) k ⟨Q, hQ⟩ = 0 := by
      rw [constFun_apply]
      change PowerSeries.constantCoeff (ev (ZMod ℓ) Q) = 0
      rw [hQe, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        coeff_zero_lattice ha, map_zero]
    refine ⟨⟨⟨Q, hQ⟩, h0⟩, Subtype.ext ?_⟩
    change Ψ ℓ (Dz ^ tt ℓ) * ev (ZMod ℓ) Q = Ψ ℓ (Dz ^ tt ℓ * a)
    rw [hQe, map_mul]
  have hfr := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq
  rw [← hfr]
  have hmc : monoCount k = (ℓ + 12) / 24 + 1 := by
    unfold monoCount
    rcases hj with h | h | h | h | h | h | h | h <;> omega
  omega

lemma ev_mem_Sbar (P : LinearMap.ker (constFun (ℓ := ℓ) (ℓ - 1))) :
    ev (ZMod ℓ) ((P : weightedHomogeneousSubmodule (ZMod ℓ) wt (ℓ - 1)) :
      MvPolynomial (Fin 2) (ZMod ℓ)) ∈ Sbar ℓ := by
  refine ⟨⟨_, (P : weightedHomogeneousSubmodule (ZMod ℓ) wt (ℓ - 1)).2, rfl⟩, ?_⟩
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, ← constFun_apply]
  exact P.2

/-- Evaluation on the cusp part of the isobaric polynomials. -/
def SbarMap : LinearMap.ker (constFun (ℓ := ℓ) (ℓ - 1)) →ₗ[ZMod ℓ] Sbar ℓ where
  toFun P := ⟨_, ev_mem_Sbar P⟩
  map_add' P Q := Subtype.ext (map_add (ev (ZMod ℓ)) _ _)
  map_smul' c P := Subtype.ext (by
    change ev (ZMod ℓ) (c • ((P : weightedHomogeneousSubmodule (ZMod ℓ) wt (ℓ - 1)) :
      MvPolynomial (Fin 2) (ZMod ℓ))) = c • ev (ZMod ℓ) _
    rw [MvPolynomial.smul_eq_C_mul, map_mul, ev_C, PowerSeries.smul_eq_C_mul])

/-- `S̄` is the cusp part of the isobaric polynomials of weight `ℓ - 1`. -/
def SbarEquiv (h5 : 5 ≤ ℓ) : LinearMap.ker (constFun (ℓ := ℓ) (ℓ - 1)) ≃ₗ[ZMod ℓ] Sbar ℓ :=
  LinearEquiv.ofBijective SbarMap
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro P hP
      have h2 : ev (ZMod ℓ) ((P : weightedHomogeneousSubmodule (ZMod ℓ) wt (ℓ - 1)) :
          MvPolynomial (Fin 2) (ZMod ℓ)) = 0 := congrArg Subtype.val hP
      have h3 := eq_zero_of_ev_eq_zero_modP h5 (P : weightedHomogeneousSubmodule (ZMod ℓ) wt (ℓ - 1)).2 h2
      apply Subtype.ext
      apply Subtype.ext
      exact h3,
     by
      rintro ⟨_, ⟨Q, hQ, rfl⟩, h0⟩
      refine ⟨⟨⟨Q, hQ⟩, ?_⟩, rfl⟩
      rw [LinearMap.mem_ker, constFun_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact h0⟩

/-- **The dimension of `S̄`.** -/
theorem finrank_Sbar (h13 : 13 ≤ ℓ) : Module.finrank (ZMod ℓ) (Sbar ℓ) + 1 = monoCount (ℓ - 1) := by
  have hodd : ℓ % 2 = 1 := Nat.odd_iff.mp (hℓ.out.odd_of_ne_two (by omega))
  rw [← (SbarEquiv (ℓ := ℓ) (by omega)).finrank_eq]
  exact finrank_ker_constFun (by omega) (by omega) (by omega)

instance finite_Sbar (h13 : 13 ≤ ℓ) : FiniteDimensional (ZMod ℓ) (Sbar ℓ) := by
  have hodd : ℓ % 2 = 1 := Nat.odd_iff.mp (hℓ.out.odd_of_ne_two (by omega))
  haveI := finite_W (F := ZMod ℓ) (k := ℓ - 1) (by omega) (by omega)
  exact Module.Finite.equiv (SbarEquiv (ℓ := ℓ) (by omega))

end

end RamanujanTau.BLBound
