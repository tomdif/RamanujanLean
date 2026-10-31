import RamanujanTau.BLBound.Image
import RamanujanTau.ThetaLift.Final

/-!
# The operator `X̄` on `V̄`

`V̄ = Ψ(Δ^t S_{k'})` is a finite-dimensional `𝔽_ℓ`-space, stable under `X̄ = D̄Ū` and with `X̄` injective on it.
So the characteristic polynomial of `X̄` on `V̄` is monic with nonzero constant term, and kills `V̄`.
-/

set_option autoImplicit false

namespace RamanujanTau.BLBound
open ModularForm UpperHalfPlane ModP BoylanWebb
open RamanujanTau.TheoremA.HalfIntegral RamanujanTau.TheoremA.SignLattice
open scoped MatrixGroups

noncomputable section

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- `Ū` as a linear map. -/
def Ubar : Module.End (ZMod ℓ) (PowerSeries (ZMod ℓ)) where
  toFun := U ℓ
  map_add' := U_add ℓ
  map_smul' c f := by
    simp only [RingHom.id_apply, PowerSeries.smul_eq_C_mul]
    exact U_C_mul ℓ c f

/-- `D̄` as a linear map. -/
def Dbar : Module.End (ZMod ℓ) (PowerSeries (ZMod ℓ)) :=
  Ubar ℓ ∘ₗ LinearMap.mulLeft (ZMod ℓ) (Ψ ℓ (Φ ℓ))

/-- `X̄ = D̄Ū`. -/
def Xbar : Module.End (ZMod ℓ) (PowerSeries (ZMod ℓ)) := Dbar ℓ ∘ₗ Ubar ℓ

lemma Xbar_apply (f : PowerSeries (ZMod ℓ)) : Xbar ℓ f = U ℓ (Ψ ℓ (Φ ℓ) * U ℓ f) := rfl

/-- The space `V̄`. -/
def Vbar : Submodule (ZMod ℓ) (PowerSeries (ZMod ℓ)) where
  carrier := {v | ∃ a ∈ intLattice ℓ, v = Ψ ℓ (Dz ^ tt ℓ * a)}
  zero_mem' := ⟨0, Submodule.zero_mem _, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, Submodule.add_mem _ ha hb, by rw [mul_add, map_add]⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
    refine ⟨n • a, Submodule.smul_mem _ n ha, ?_⟩
    rw [PowerSeries.smul_eq_C_mul, mul_smul_comm, map_zsmul, zsmul_eq_mul]
    congr 1
    simp

variable {ℓ}

/-- Elements of the lattice are integral forms. -/
lemma intForm_of_lattice {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ) :
    IntForm (kPrime ℓ) a := by
  obtain ⟨G, hG⟩ := ha
  exact ⟨(G : ModularForm 𝒮ℒ (kPrime ℓ)), by
    rw [hG]
    rfl⟩

/-- Elements of `V̄` have weight `ℓ - 1`. -/
lemma intForm_V (h13 : 13 ≤ ℓ) {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ) :
    IntForm ((ℓ - 1 : ℕ) : ℤ) (Dz ^ tt ℓ * a) := by
  have hd := ell_decomp (ℓ := ℓ)
  have hj := ell_mod h13
  refine ((IntForm.disc.pow (tt ℓ)).mul (intForm_of_lattice ha)).cast ?_
  unfold kPrime
  push_cast
  have e : (ℓ + jj ℓ - 2) / 2 + 12 * tt ℓ = ℓ - 1 := by omega
  rw [← e]
  push_cast
  ring

lemma coeff_zero_lattice {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ) : PowerSeries.coeff 0 a = 0 := by
  obtain ⟨G, hG⟩ := ha
  have hc : ModularForm.IsCuspForm (G : ModularForm 𝒮ℒ (kPrime ℓ)) :=
    ⟨G, CuspForm.toModularFormₗ_eq_coe _⟩
  have h := (ModularForm.isCuspForm_iff_coeffZero_eq_zero _).mp hc
  have h2 : (qExpansion 1 G).coeff 0 = 0 := h
  rw [← hG, PowerSeries.coeff_map, eq_intCast] at h2
  exact_mod_cast h2

lemma coeff_zero_V {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ) :
    PowerSeries.coeff 0 (Dz ^ tt ℓ * a) = 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply a, coeff_zero_lattice ha, mul_zero]

/-- `X̄` preserves `V̄`. -/
theorem Xbar_mem (h13 : 13 ≤ ℓ) {v : PowerSeries (ZMod ℓ)} (hv : v ∈ Vbar ℓ) : Xbar ℓ v ∈ Vbar ℓ := by
  obtain ⟨a, ha, rfl⟩ := hv
  have h5 : 5 ≤ ℓ := by omega
  have hy := intForm_V h13 ha
  have hy0 := coeff_zero_V ha
  have hT := hy.hecke ℓ (ℓ - 2) (by push_cast [Nat.cast_sub (show 2 ≤ ℓ by omega), Nat.cast_sub (show 1 ≤ ℓ by omega)]; ring) hy0
  have hU : FormBar ℓ (ℓ - 1) (U ℓ (Ψ ℓ (Dz ^ tt ℓ * a))) := by
    have h := formBar_of_intForm ℓ h5 ℓ (ℓ - 1) (by omega) _ hT
    rwa [Ψ_hecke ℓ (ℓ - 2) (by omega)] at h
  obtain ⟨b, hb, hbe⟩ := D_image h13 hU
  exact ⟨b, hb, hbe⟩

/-- `X̄` is injective on `V̄`, by Theorem A. -/
theorem Xbar_inj (h13 : 13 ≤ ℓ) {v : PowerSeries (ZMod ℓ)} (hv : v ∈ Vbar ℓ) (h0 : Xbar ℓ v = 0) : v = 0 := by
  obtain ⟨a, ha, rfl⟩ := hv
  have hX : Ψ ℓ (U ℓ (Φ ℓ * U ℓ (Dz ^ tt ℓ * a))) = 0 := by
    rw [map_U, map_mul, map_U]
    exact h0
  have ha0 := ThetaLift.X_injective_unconditional h13 ha hX
  rw [map_mul, ha0, mul_zero]

/-- The restriction of `X̄` to `V̄`. -/
def Tv (h13 : 13 ≤ ℓ) : Module.End (ZMod ℓ) (Vbar ℓ) :=
  (Xbar ℓ).restrict fun _ hv => Xbar_mem h13 hv

instance finite_Vbar (h13 : 13 ≤ ℓ) : FiniteDimensional (ZMod ℓ) (Vbar ℓ) := by
  have h5 : 5 ≤ ℓ := by omega
  let M := (ℓ - 1) / 12 + 1
  let f : Vbar ℓ →ₗ[ZMod ℓ] (Fin M → ZMod ℓ) :=
    { toFun := fun v i => PowerSeries.coeff (i : ℕ) (v : PowerSeries (ZMod ℓ))
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }
  refine FiniteDimensional.of_injective f ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨v, a, ha, rfl⟩ hv
  apply Subtype.ext
  change Ψ ℓ (Dz ^ tt ℓ * a) = 0
  refine sturm ℓ ℓ _ (by push_cast [Nat.cast_sub (show 1 ≤ ℓ by omega)]; omega) _ (intForm_V h13 ha) ?_
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [Int.toNat_natCast] at hm
  exact congrFun hv ⟨m, hm⟩

lemma aeval_restrict (h13 : 13 ≤ ℓ) (p : Polynomial (ZMod ℓ)) (v : Vbar ℓ) :
    Polynomial.aeval (Xbar ℓ) p (v : PowerSeries (ZMod ℓ)) =
      ((Polynomial.aeval (Tv h13) p v : Vbar ℓ) : PowerSeries (ZMod ℓ)) := by
  induction p using Polynomial.induction_on' generalizing v with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, Submodule.coe_add]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul]
    congr 1
    induction n generalizing v with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      exact ih (Tv h13 v)

/-- **The polynomial `χ`.** -/
theorem exists_chi (h13 : 13 ≤ ℓ) : ∃ χ : Polynomial ℤ, χ.Monic ∧ ¬ (ℓ : ℤ) ∣ χ.coeff 0 ∧
    ∀ v ∈ Vbar ℓ, Polynomial.aeval (Xbar ℓ) (χ.map (Int.castRingHom (ZMod ℓ))) v = 0 := by
  haveI := finite_Vbar (ℓ := ℓ) h13
  set T := Tv h13
  set c := LinearMap.charpoly T with hc
  have hmon : c.Monic := LinearMap.charpoly_monic T
  have hCH : Polynomial.aeval T c = 0 := LinearMap.aeval_self_charpoly T
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨v, hv⟩ h
    apply Subtype.ext
    exact Xbar_inj h13 hv (congrArg Subtype.val h)
  have hdet : IsUnit (LinearMap.det T) := by
    have := (LinearEquiv.ofInjectiveEndo T hinj).isUnit_det'
    simpa using this
  have hc0 : c.coeff 0 ≠ 0 := by
    intro h0
    have := LinearMap.det_eq_sign_charpoly_coeff T
    rw [← hc, h0, mul_zero] at this
    exact hdet.ne_zero this
  have hsurj : Function.Surjective (Int.castRingHom (ZMod ℓ)) := ZMod.intCast_surjective
  obtain ⟨q, hq⟩ := Polynomial.map_surjective _ hsurj c
  have hlift : c ∈ Polynomial.lifts (Int.castRingHom (ZMod ℓ)) :=
    (Polynomial.mem_lifts _).mpr ⟨q, hq⟩
  obtain ⟨χ, hχe, -, hχm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hmon
  refine ⟨χ, hχm, ?_, ?_⟩
  · intro hd
    apply hc0
    rw [← hχe, Polynomial.coeff_map]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  · intro v hv
    rw [hχe, aeval_restrict h13 c ⟨v, hv⟩, hCH]
    rfl

end

end RamanujanTau.BLBound
