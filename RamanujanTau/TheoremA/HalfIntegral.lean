import RamanujanTau.TheoremA.NewClass
import RamanujanTau.BoylanWebb.Series

/-!
# Theorem A on the half-integral-weight space

The space `S_{(ℓ-2)/2}(SL₂ℤ, ν_η^{-ℓ})` is `η^{-j} S_{k'}(SL₂ℤ)`, with `j = ℓ mod 24` and
`k' = (ℓ+j-2)/2`. A form `G/η^j` has exponents `(24m-j)/24`, and its coefficients are those of
the integer series `G·(q;q)_∞^{-j}`. On these coordinates Shimura's operator `T_{ℓ²}` has an
explicit formula.

`YangCorrespondence` records Yifan Yang's Hecke correspondence (Nagoya Math. J. 215 (2014),
Theorem 1) in the weak form used here: an injective map to `newClass ℓ` sending `T_{ℓ²}` to
`(12/ℓ) T_ℓ`. It is an explicit hypothesis: its trace-formula proof is not formalized. Everything
else in `theoremA` is proved. `scripts/frontier/pattern/shimura_check.py` and
`sign_class_coeff.gp` confirm the formula against PARI's newforms over ℤ for 13 ≤ ℓ ≤ 41.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.HalfIntegral
open ModularForm CongruenceSubgroup UpperHalfPlane PowerSeries MockTheta5.JTP
open scoped MatrixGroups ModularForm
open SignLattice

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- `j = ℓ mod 24`. -/
def jj (ℓ : ℕ) : ℕ := ℓ % 24

/-- The integral weight `k' = (ℓ+j-2)/2`. -/
def kPrime (ℓ : ℕ) : ℤ := (((ℓ + jj ℓ - 2) / 2 : ℕ) : ℤ)

/-- The half-integral coordinate `G ↦ G·(q;q)_∞^{-j}`. -/
noncomputable def coordOf {R : Type*} [CommRing R] (ℓ : ℕ) (G : PowerSeries R) : PowerSeries R :=
  G * PowerSeries.map (Int.castRingHom R) partitionGF ^ jj ℓ

/-- Shimura's `T_{ℓ²}` in the coordinate `A[m] = b(24m-j)`. With `n = 24m-j` it is
`b(ℓ²n) + (12/ℓ) ((-1)^λ n / ℓ) ℓ^(λ-1) b(n) + ℓ^(2λ-1) b(n/ℓ²)`, where `λ = (ℓ-3)/2`. -/
noncomputable def shimuraT {R : Type*} [CommRing R] (A : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun m =>
    A.coeff (ℓ ^ 2 * m - jj ℓ * BoylanWebb.δ ℓ) +
    ((legendreSym ℓ 3 * legendreSym ℓ ((-1) ^ halfWt ℓ * (24 * (m : ℤ) - jj ℓ)) : ℤ) : R) *
      (ℓ : R) ^ (halfWt ℓ - 1) * A.coeff m +
    (ℓ : R) ^ (2 * halfWt ℓ - 1) *
      (if ((ℓ : ℤ) ^ 2 ∣ 24 * (m : ℤ) - jj ℓ) then
        A.coeff ((((24 * (m : ℤ) - jj ℓ) / (ℓ : ℤ) ^ 2 + jj ℓ) / 24).toNat) else 0)

lemma coeff_shimuraT {R : Type*} [CommRing R] (A : PowerSeries R) (m : ℕ) :
    (shimuraT ℓ A).coeff m = A.coeff (ℓ ^ 2 * m - jj ℓ * BoylanWebb.δ ℓ) +
    ((legendreSym ℓ 3 * legendreSym ℓ ((-1) ^ halfWt ℓ * (24 * (m : ℤ) - jj ℓ)) : ℤ) : R) *
      (ℓ : R) ^ (halfWt ℓ - 1) * A.coeff m +
    (ℓ : R) ^ (2 * halfWt ℓ - 1) *
      (if ((ℓ : ℤ) ^ 2 ∣ 24 * (m : ℤ) - jj ℓ) then
        A.coeff (((24 * (m : ℤ) - jj ℓ) / (ℓ : ℤ) ^ 2 + jj ℓ) / 24).toNat else 0) :=
  PowerSeries.coeff_mk _ _

lemma map_shimuraT {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (A : PowerSeries R) :
    PowerSeries.map φ (shimuraT ℓ A) = shimuraT ℓ (PowerSeries.map φ A) := by
  ext m
  simp only [PowerSeries.coeff_map, coeff_shimuraT, map_add, map_mul, map_pow, map_natCast,
    map_intCast]
  split_ifs <;> simp

/-- **Yang's correspondence**, in the injective form used by the determinant argument. -/
structure YangCorrespondence (hℓ13 : 13 ≤ ℓ) where
  /-- Shimura's operator on the actual space. -/
  heckeS : Module.End ℂ (CuspForm 𝒮ℒ (kPrime ℓ))
  /-- It has the classical coefficient formula on half-integral coordinates. -/
  coord_heckeS : ∀ G, coordOf ℓ (qExpansion 1 (heckeS G)) =
    shimuraT ℓ (coordOf ℓ (qExpansion 1 G))
  /-- The Shimura correspondence, into the newform sign class. -/
  lift : CuspForm 𝒮ℒ (kPrime ℓ) →ₗ[ℂ] Forms ℓ
  lift_injective : Function.Injective lift
  lift_mem : ∀ G, lift G ∈ newClass ℓ
  /-- `T_{ℓ²} ↔ (12/ℓ) T_ℓ`. -/
  lift_hecke : ∀ G, lift (heckeS G) = ((legendreSym ℓ 3 : ℤ) : ℂ) • heckeL hℓ13 (lift G)

lemma map_coordOf {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (A : PowerSeries R) :
    PowerSeries.map φ (coordOf ℓ A) = coordOf ℓ (PowerSeries.map φ A) := by
  have h : (PowerSeries.map φ).comp (PowerSeries.map (Int.castRingHom R)) =
      PowerSeries.map (Int.castRingHom S) := by
    ext x n
    simp
  rw [coordOf, coordOf, map_mul, map_pow]
  congr 2
  exact congrArg (fun f : PowerSeries ℤ →+* PowerSeries S => f partitionGF) h

lemma qfac_pow_coord (A : PowerSeries ℤ) : coordOf ℓ A * qfacInf ^ jj ℓ = A := by
  have h : PowerSeries.map (Int.castRingHom ℤ) partitionGF = partitionGF := by
    ext n
    simp
  rw [coordOf, h, mul_assoc, ← mul_pow, mul_comm partitionGF, BoylanWebb.qfac_mul_pgf, one_pow,
    mul_one]

lemma qfac_pow_coord_C (A : PowerSeries ℂ) :
    coordOf ℓ A * PowerSeries.map (Int.castRingHom ℂ) qfacInf ^ jj ℓ = A := by
  rw [coordOf, mul_assoc, ← mul_pow, ← map_mul, mul_comm partitionGF, BoylanWebb.qfac_mul_pgf,
    map_one, one_pow, mul_one]

/-- The integer form of Shimura's operator on the level-one coordinate. -/
noncomputable def opS (a : PowerSeries ℤ) : PowerSeries ℤ :=
  shimuraT ℓ (coordOf ℓ a) * qfacInf ^ jj ℓ

variable {ℓ}

lemma shimuraT_add {R : Type*} [CommRing R] (A B : PowerSeries R) :
    shimuraT ℓ (A + B) = shimuraT ℓ A + shimuraT ℓ B := by
  ext m
  simp only [coeff_shimuraT, map_add]
  split_ifs <;> ring

lemma shimuraT_zsmul (r : ℤ) (A : PowerSeries ℤ) : shimuraT ℓ (r • A) = r • shimuraT ℓ A := by
  ext m
  simp only [coeff_shimuraT, map_zsmul, smul_eq_mul]
  split_ifs <;> ring

lemma opS_add (a b : PowerSeries ℤ) : opS ℓ (a + b) = opS ℓ a + opS ℓ b := by
  simp only [opS, coordOf, add_mul, shimuraT_add]

lemma opS_zsmul (r : ℤ) (a : PowerSeries ℤ) : opS ℓ (r • a) = r • opS ℓ a := by
  simp only [opS, coordOf, smul_mul_assoc, shimuraT_zsmul]

variable (ℓ) in
/-- Integer expansions of actual level-one cusp forms of weight `k'`. -/
def intLattice : Submodule ℤ (PowerSeries ℤ) where
  carrier := {a | ∃ G : CuspForm 𝒮ℒ (kPrime ℓ),
    PowerSeries.map (Int.castRingHom ℂ) a = qExpansion 1 G}
  add_mem' := by
    rintro a b ⟨F, hF⟩ ⟨G, hG⟩
    refine ⟨F + G, ?_⟩
    rw [map_add, hF, hG]
    exact (ModularFormClass.qExpansion_add one_pos one_mem_strictPeriods_SL F G).symm
  zero_mem' := ⟨0, by
    rw [map_zero]
    exact (qExpansion_zero 1).symm⟩
  smul_mem' r a := by
    rintro ⟨F, hF⟩
    refine ⟨(r : ℂ) • F, ?_⟩
    have := ModularFormClass.qExpansion_smul one_pos one_mem_strictPeriods_SL (r : ℂ) F
    refine Eq.trans ?_ this.symm
    rw [← hF]
    exact SignLattice.map_int_smul _ r a

/-- Equal expansions give equal level-one cusp forms. -/
lemma cusp_ext {F G : CuspForm 𝒮ℒ (kPrime ℓ)} (h : qExpansion 1 F = qExpansion 1 G) : F = G := by
  ext z
  have hs : ∀ K : CuspForm 𝒮ℒ (kPrime ℓ), HasSum
      (fun n => (qExpansion 1 K).coeff n * Function.Periodic.qParam 1 z ^ n) (K z) := by
    intro K
    have := hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex K one_mem_strictPeriods_SL)
      (ModularFormClass.holo K) (ModularFormClass.bdd_at_infty K) z
    simpa [smul_eq_mul] using this
  have hF := hs F
  rw [h] at hF
  exact hF.unique (hs G)

lemma opS_mem (h13 : 13 ≤ ℓ) (Y : YangCorrespondence ℓ h13) {a : PowerSeries ℤ}
    {G : CuspForm 𝒮ℒ (kPrime ℓ)} (hG : PowerSeries.map (Int.castRingHom ℂ) a = qExpansion 1 G) :
    PowerSeries.map (Int.castRingHom ℂ) (opS ℓ a) = qExpansion 1 (Y.heckeS G) := by
  rw [opS, map_mul, map_pow, map_shimuraT, map_coordOf, hG, ← Y.coord_heckeS, qfac_pow_coord_C]

/-- The Shimura operator on the integer lattice. -/
noncomputable def latticeS (h13 : 13 ≤ ℓ) (Y : YangCorrespondence ℓ h13) :
    intLattice ℓ →ₗ[ℤ] intLattice ℓ where
  toFun a := ⟨opS ℓ a.1, by
    obtain ⟨G, hG⟩ := a.2
    exact ⟨Y.heckeS G, opS_mem h13 Y hG⟩⟩
  map_add' a b := Subtype.ext (opS_add a.1 b.1)
  map_smul' r a := Subtype.ext (opS_zsmul r a.1)

lemma exists_form_intLattice {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ) :
    BoylanWebb.IntForm (kPrime ℓ) a := by
  obtain ⟨G, hG⟩ := ha
  exact ⟨{ G with
    bdd_at_cusps' := fun hc γ hγ => (CuspFormClass.zero_at_cusps G hc γ hγ).isBoundedAtImInfty },
    hG.symm⟩

/-- The first coefficients determine an element of the lattice. -/
lemma intLattice_eq_zero {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ)
    (h0 : ∀ m < (kPrime ℓ).toNat / 12 + 1, a.coeff m = 0) : a = 0 := by
  ext m
  rw [map_zero]
  by_contra hne
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes ((a.coeff m).natAbs + 1)
  haveI : Fact q.Prime := ⟨hqp⟩
  have hk : kPrime ℓ < 12 * (((kPrime ℓ).toNat + 1 : ℕ) : ℤ) := by
    have : 0 ≤ kPrime ℓ := Int.natCast_nonneg _
    push_cast
    omega
  have hs := BoylanWebb.sturm q _ _ hk a (exists_form_intLattice ha) (by
    rw [PowerSeries.X_pow_dvd_iff]
    intro i hi
    rw [BoylanWebb.Ψ, PowerSeries.coeff_map, h0 i hi, map_zero])
  have hc := congrArg (PowerSeries.coeff m) hs
  rw [BoylanWebb.Ψ, PowerSeries.coeff_map, map_zero] at hc
  have hd : (q : ℤ) ∣ a.coeff m := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
  have := Int.natAbs_dvd_natAbs.mpr hd
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (by simpa using this)
  omega

/-- Coefficient coordinates on the lattice. -/
noncomputable def firstCoeffs (ℓ : ℕ) :
    intLattice ℓ →ₗ[ℤ] (Fin ((kPrime ℓ).toNat / 12 + 1) → ℤ) where
  toFun a i := a.1.coeff i.val
  map_add' a b := by ext i; simp
  map_smul' r a := by
    ext i
    exact map_zsmul (PowerSeries.coeff i.val) r a.1

lemma firstCoeffs_injective : Function.Injective (firstCoeffs ℓ) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply Subtype.ext
  exact intLattice_eq_zero a.2 fun m hm => congrFun ha ⟨m, hm⟩

instance : Module.Finite ℤ (intLattice ℓ) :=
  Module.Finite.of_injective (firstCoeffs ℓ) firstCoeffs_injective

instance : Module.Free ℤ (intLattice ℓ) :=
  Module.Free.of_equiv (LinearEquiv.ofInjective (firstCoeffs ℓ) firstCoeffs_injective).symm

/-- Level-one expansion as a complex-linear map. -/
noncomputable def expL (ℓ : ℕ) : CuspForm 𝒮ℒ (kPrime ℓ) →ₗ[ℂ] PowerSeries ℂ where
  toFun G := qExpansion 1 G
  map_add' F G := ModularFormClass.qExpansion_add one_pos one_mem_strictPeriods_SL F G
  map_smul' c F := ModularFormClass.qExpansion_smul one_pos one_mem_strictPeriods_SL c F

lemma coeff_zero_det_of_matrix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (d : ℤ)
    (h : ¬ d ∣ B.charpoly.coeff 0) : ¬ d ∣ B.det := by
  intro hd
  apply h
  have he := Matrix.det_eq_sign_charpoly_coeff B
  rw [he] at hd
  rcases Int.units_eq_one_or (⟨(-1) ^ Fintype.card (Fin n), (-1) ^ Fintype.card (Fin n), by
    rw [← mul_pow]; simp, by rw [← mul_pow]; simp⟩ : ℤˣ) with hu | hu
  · have h1 : ((-1 : ℤ)) ^ Fintype.card (Fin n) = 1 := congrArg Units.val hu
    rwa [h1, one_mul] at hd
  · have h1 : ((-1 : ℤ)) ^ Fintype.card (Fin n) = -1 := congrArg Units.val hu
    rw [h1, neg_one_mul, dvd_neg] at hd
    exact hd

/-- **Determinant comparison.** Given Yang's correspondence, the integer determinant of
`T_{ℓ²}` is prime to ℓ. -/
theorem latticeS_det_not_dvd (h13 : 13 ≤ ℓ) (Y : YangCorrespondence ℓ h13) :
    ¬ (ℓ : ℤ) ∣ LinearMap.det (latticeS h13 Y) := by
  classical
  let ε : ℤ := legendreSym ℓ 3
  have hε : ε * ε = 1 := by
    have hs := legendreSym.sq_one ℓ (a := 3) (by
      simpa using int_cast_ne (ℓ := ℓ) h13 (p := 3) (Or.inr rfl))
    rw [sq] at hs
    exact hs
  let b := Module.finBasis ℤ (intLattice ℓ)
  let B := LinearMap.toMatrix b b (latticeS h13 Y)
  let e := LinearMap.charpoly (latticeTw h13 ε)
  have he : ¬ (ℓ : ℤ) ∣ e.coeff 0 := by
    have hTw := latticeT_det_not_dvd (ℓ := ℓ) h13
    let b' := Module.finBasis ℤ (signLattice ℓ)
    intro hd
    apply hTw
    have hdet : LinearMap.det (latticeTw h13 ε) =
        ε ^ Module.finrank ℤ (signLattice ℓ) * LinearMap.det (latticeT h13) := by
      rw [latticeTw, LinearMap.det_smul]
    have hd2 : (ℓ : ℤ) ∣ LinearMap.det (latticeTw h13 ε) := by
      rw [← LinearMap.det_toMatrix b' (latticeTw h13 ε)]
      rw [Matrix.det_eq_sign_charpoly_coeff, LinearMap.charpoly_toMatrix]
      exact hd.mul_left _
    rw [hdet] at hd2
    have hu : IsCoprime (ℓ : ℤ) (ε ^ Module.finrank ℤ (signLattice ℓ)) := by
      apply IsCoprime.pow_right
      exact ⟨0, ε, by rw [hε.symm]; ring⟩
    exact hu.dvd_of_dvd_mul_left hd2
  have hroot : ∀ α : ℂ, (B.charpoly.map (Int.castRingHom ℂ)).IsRoot α →
      (e.map (Int.castRingHom ℂ)).IsRoot α := by
    intro α hα
    let M : Matrix _ _ ℂ := B.map (Int.castRingHom ℂ)
    have hM : M.charpoly = B.charpoly.map (Int.castRingHom ℂ) := Matrix.charpoly_map B _
    let L : Module.End ℂ (Fin (Module.finrank ℤ (intLattice ℓ)) → ℂ) := Matrix.toLin' M
    have hL : LinearMap.charpoly L = M.charpoly := by
      rw [← LinearMap.charpoly_toMatrix L (Pi.basisFun ℂ _), LinearMap.toMatrix_eq_toMatrix',
        LinearMap.toMatrix'_toLin']
    have hev : Module.End.HasEigenvalue L α := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hL, hM]
      exact hα
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have hv0 := hv.2
    have hLv : M.mulVec v = α • v := by
      have := Module.End.mem_eigenspace_iff.mp hv.1
      simpa [L, Matrix.toLin'_apply] using this
    choose G hG using fun i => (b i).2
    have hB : ∀ i, (latticeS h13 Y (b i)).1 = ∑ j, B j i • (b j).1 := by
      intro i
      have hs := b.sum_repr (latticeS h13 Y (b i))
      have hval := congrArg Subtype.val hs
      rw [← hval, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul]
      congr 1
      exact (LinearMap.toMatrix_apply b b _ j i).symm
    have hH : ∀ i, Y.heckeS (G i) = ∑ j, (B j i : ℂ) • G j := by
      intro i
      apply cusp_ext (ℓ := ℓ)
      rw [← opS_mem h13 Y (hG i)]
      change PowerSeries.map _ (latticeS h13 Y (b i)).1 = expL ℓ _
      rw [hB, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(expL ℓ).map_smul, SignLattice.map_int_smul, hG]
      rfl
    let F : CuspForm 𝒮ℒ (kPrime ℓ) := ∑ i, v i • G i
    have hFH : Y.heckeS F = α • F := by
      simp only [F, map_sum, map_smul, hH, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj := congrFun hLv j
      simp only [M, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
        eq_intCast] at hj
      rw [← Finset.sum_smul]
      congr 1
      rw [← hj]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hF0 : F ≠ 0 := by
      intro hF
      apply hv0
      apply LatticeAlgebra.complex_independent (fun i => (b i).1)
        (b.linearIndependent.map' (intLattice ℓ).subtype (Submodule.ker_subtype _)) v
      have := congrArg (expL ℓ) hF
      rw [map_zero] at this
      simp only [F, map_sum, map_smul] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hG]
      rfl
    have hfne : Y.lift F ≠ 0 := fun h => hF0 (Y.lift_injective (by rw [h, map_zero]))
    have hT : ((ε : ℂ) • heckeL h13) (Y.lift F) = α • Y.lift F := by
      have := Y.lift_hecke F
      rw [hFH, map_smul] at this
      exact this.symm
    exact newClass_isRoot h13 ε (Y.lift_mem F) hfne α hT
  have hunit := LatticeAlgebra.not_dvd_coeff_zero_of_roots ℓ B.charpoly e
    (Matrix.charpoly_monic B) (LinearMap.charpoly_monic _) hroot he
  have hdet : LinearMap.det (latticeS h13 Y) = B.det := (LinearMap.det_toMatrix b _).symm
  rw [hdet]
  exact coeff_zero_det_of_matrix B _ hunit

/-- A multiple of `ℓ` in the lattice is `ℓ` times a lattice element. -/
lemma intLattice_saturated {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ)
    (h : ∀ m, (ℓ : ℤ) ∣ a.coeff m) : ∃ z : intLattice ℓ, a = (ℓ : ℤ) • z.1 := by
  choose c hc using h
  obtain ⟨G, hG⟩ := ha
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  let z : PowerSeries ℤ := PowerSeries.mk c
  have haz : a = (ℓ : ℤ) • z := by
    ext m
    rw [map_zsmul, smul_eq_mul, hc m, PowerSeries.coeff_mk]
  refine ⟨⟨z, (ℓ : ℂ)⁻¹ • G, ?_⟩, haz⟩
  have hexp := expL ℓ |>.map_smul (ℓ : ℂ)⁻¹ G
  change _ = expL ℓ _
  rw [hexp]
  change _ = (ℓ : ℂ)⁻¹ • qExpansion 1 G
  rw [← hG, haz, SignLattice.map_int_smul, smul_smul]
  have : (ℓ : ℂ)⁻¹ * (Int.castRingHom ℂ) (ℓ : ℤ) = 1 := by
    simp [hℓC]
  rw [this, one_smul]

/-- **Theorem A, half-integral form.** Given Yang's correspondence, `U_{ℓ²}` is injective modulo
`ℓ` on `S_{(ℓ-2)/2}(SL₂ℤ, ν_η^{-ℓ})`, written in the coordinates `A = G·(q;q)_∞^{-j}`. -/
theorem theoremA (h13 : 13 ≤ ℓ) (Y : YangCorrespondence ℓ h13) {a : PowerSeries ℤ}
    (ha : a ∈ intLattice ℓ)
    (hU : ∀ m, (ℓ : ℤ) ∣ (coordOf ℓ a).coeff (ℓ ^ 2 * m - jj ℓ * BoylanWebb.δ ℓ)) :
    ∀ m, (ℓ : ℤ) ∣ a.coeff m := by
  by_contra hne
  have hlam1 : halfWt ℓ - 1 ≠ 0 := by unfold halfWt; omega
  have hlam2 : 2 * halfWt ℓ - 1 ≠ 0 := by unfold halfWt; omega
  have hT : ∀ m, (ℓ : ℤ) ∣ (shimuraT ℓ (coordOf ℓ a)).coeff m := by
    intro m
    rw [coeff_shimuraT]
    refine dvd_add (dvd_add (hU m) ?_) ?_
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self _ hlam1) _) _
    · exact dvd_mul_of_dvd_left (dvd_pow_self _ hlam2) _
  have hop : ∀ m, (ℓ : ℤ) ∣ (opS ℓ a).coeff m := by
    choose c hc using hT
    have heq : shimuraT ℓ (coordOf ℓ a) = (ℓ : ℤ) • PowerSeries.mk c := by
      ext m
      rw [map_zsmul, smul_eq_mul, hc, PowerSeries.coeff_mk]
    intro m
    rw [opS, heq, smul_mul_assoc, map_zsmul, smul_eq_mul]
    exact dvd_mul_right _ _
  obtain ⟨y, hy⟩ := intLattice_saturated (ℓ := ℓ) (latticeS h13 Y ⟨a, ha⟩).2 hop
  apply latticeS_det_not_dvd h13 Y
  refine LatticeAlgebra.dvd_det_of_kernel ℓ _ ⟨a, ha⟩ y ?_ (Subtype.ext hy)
  rintro ⟨z, hz⟩
  apply hne
  intro m
  have := congrArg (fun u : intLattice ℓ => u.1.coeff m) hz
  simp only [Submodule.coe_smul, map_zsmul, smul_eq_mul] at this
  rw [this]
  exact dvd_mul_right _ _

end RamanujanTau.TheoremA.HalfIntegral
