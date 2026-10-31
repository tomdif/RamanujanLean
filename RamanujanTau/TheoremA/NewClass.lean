import RamanujanTau.TheoremA.SignLattice

/-!
# The newform sign class in weight ℓ−3 at level six

`newClass ℓ` is the space of actual cusp forms that are new at 2 and 3, with
Atkin–Lehner signs `(-(2/ℓ), -(3/ℓ))`. This file derives the two eigenvalue
formulas, proves that every normalized Hecke eigenform in the class has a unit
ℓ-th coefficient at every prime above ℓ, and places the whole class in the
complex span of the integer sign lattice.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.SignLattice
open ModularForm CongruenceSubgroup UpperHalfPlane PowerSeries
open scoped MatrixGroups ModularForm
open TraceCosets AtkinLehner BadPrime EtaSquared

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

instance : NeZero (3 * 2) := ⟨by norm_num⟩
instance : NeZero (2 * 3) := ⟨by norm_num⟩

variable (ℓ) in
/-- The Atkin–Lehner sign at 2 in the class. -/
noncomputable def sign2 : ℂ := -(legendreSym ℓ 2 : ℂ)

variable (ℓ) in
/-- The Atkin–Lehner sign at 3 in the class. -/
noncomputable def sign3 : ℂ := -(legendreSym ℓ 3 : ℂ)

/-- The explicit trace sum on functions. -/
noncomputable def traceSum {p M : ℕ} [Fact p.Prime] (D : CosetData p M) (k : ℤ) (h : ℍ → ℂ) :
    ℍ → ℂ :=
  h + ∑ j : ZMod p, h ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ (D.gam j)

lemma traceSum_add {p M : ℕ} [Fact p.Prime] (D : CosetData p M) (k : ℤ) (f g : ℍ → ℂ) :
    traceSum D k (f + g) = traceSum D k f + traceSum D k g := by
  simp only [traceSum, SlashAction.add_slash, Finset.sum_add_distrib]
  abel

lemma traceSum_smul {p M : ℕ} [Fact p.Prime] (D : CosetData p M) (k : ℤ) (c : ℂ) (f : ℍ → ℂ) :
    traceSum D k (c • f) = c • traceSum D k f := by
  have hs : ∀ γ : SL(2, ℤ), (c • f) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ =
      c • (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ) := by
    intro γ
    rw [ModularForm.smul_slash]
    congr 1
    simp [σ, Matrix.SpecialLinearGroup.det_mapGL]
  simp only [traceSum, hs, ← Finset.smul_sum, smul_add]

lemma W_det_pos {p M : ℕ} [hp : Fact p.Prime] (D : CosetData p M) : 0 < (W D).val.det := by
  have h := congrArg (Int.castRingHom ℝ) (matW_det D)
  rw [RingHom.map_det] at h
  have he : (W D).val.det = (p : ℝ) := by simpa [W] using h
  rw [he]
  exact_mod_cast hp.out.pos

lemma alOp_add {p M : ℕ} [Fact p.Prime] (D : CosetData p M) (k : ℤ) (f g : ℍ → ℂ) :
    alOp D k (f + g) = alOp D k f + alOp D k g := by
  simp [alOp, SlashAction.add_slash, smul_add]

lemma alOp_smul {p M : ℕ} [Fact p.Prime] (D : CosetData p M) (k : ℤ) (c : ℂ) (f : ℍ → ℂ) :
    alOp D k (c • f) = c • alOp D k f := by
  have hσ : σ (W D) c = c := by
    simp only [σ, Matrix.GeneralLinearGroup.val_det_apply, if_pos (W_det_pos D)]
    rfl
  simp only [alOp, ModularForm.smul_slash, hσ, smul_comm c]

variable (ℓ) in
/-- **The newform class** `S^new_{ℓ-3}(Γ₀(6))^{(-(2/ℓ), -(3/ℓ))}`. -/
def newClass : Submodule ℂ (Forms ℓ) where
  carrier := {f | (∃ g : CuspForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) ((2 * halfWt ℓ : ℕ) : ℤ),
      (g : ℍ → ℂ) = f) ∧
    IsNewSign (M := 3) (p := 2) data2 (sign2 ℓ) f ∧ IsNewSign (M := 2) (p := 3) data3 (sign3 ℓ) f}
  add_mem' {f g} hf hg := by
    obtain ⟨⟨a, ha⟩, f2, f3⟩ := hf
    obtain ⟨⟨b, hb⟩, g2, g3⟩ := hg
    have hc : ((f + g : Forms ℓ) : ℍ → ℂ) = (f : ℍ → ℂ) + g := rfl
    have t2 := data2.trace_eq (M := 3) f
    have u2 := data2.trace_eq (M := 3) g
    have t3 := data3.trace_eq (M := 2) f
    have u3 := data3.trace_eq (M := 2) g
    rw [f2.trace_zero] at t2
    rw [g2.trace_zero] at u2
    rw [f3.trace_zero] at t3
    rw [g3.trace_zero] at u3
    refine ⟨⟨a + b, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hc, ← ha, ← hb]; rfl
    · rw [hc, alOp_add, f2.eigen, g2.eigen, smul_add]
    · rw [data2.trace_eq (M := 3) (f + g)]
      change traceSum data2 _ ((f : ℍ → ℂ) + g) = 0
      rw [traceSum_add]
      change (0 : ℍ → ℂ) = traceSum data2 _ f at t2
      change (0 : ℍ → ℂ) = traceSum data2 _ g at u2
      rw [← t2, ← u2, add_zero]
    · rw [hc, alOp_add, f3.eigen, g3.eigen, smul_add]
    · rw [data3.trace_eq (M := 2) (f + g)]
      change traceSum data3 _ ((f : ℍ → ℂ) + g) = 0
      rw [traceSum_add]
      change (0 : ℍ → ℂ) = traceSum data3 _ f at t3
      change (0 : ℍ → ℂ) = traceSum data3 _ g at u3
      rw [← t3, ← u3, add_zero]
  zero_mem' := by
    have hz : ((0 : Forms ℓ) : ℍ → ℂ) = (0 : ℂ) • (0 : ℍ → ℂ) := by simp
    refine ⟨⟨0, rfl⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hz, alOp_smul]; simp
    · rw [data2.trace_eq (M := 3) (0 : Forms ℓ)]
      change traceSum data2 _ ((0 : Forms ℓ) : ℍ → ℂ) = 0
      rw [hz, traceSum_smul]; simp
    · rw [hz, alOp_smul]; simp
    · rw [data3.trace_eq (M := 2) (0 : Forms ℓ)]
      change traceSum data3 _ ((0 : Forms ℓ) : ℍ → ℂ) = 0
      rw [hz, traceSum_smul]; simp
  smul_mem' c f hf := by
    obtain ⟨⟨a, ha⟩, f2, f3⟩ := hf
    have hc : ((c • f : Forms ℓ) : ℍ → ℂ) = c • (f : ℍ → ℂ) := rfl
    have t2 := data2.trace_eq (M := 3) f
    have t3 := data3.trace_eq (M := 2) f
    rw [f2.trace_zero] at t2
    rw [f3.trace_zero] at t3
    refine ⟨⟨c • a, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hc, ← ha]; rfl
    · rw [hc, alOp_smul, f2.eigen, smul_comm]
    · rw [data2.trace_eq (M := 3) (c • f)]
      change traceSum data2 _ (c • (f : ℍ → ℂ)) = 0
      rw [traceSum_smul]
      change (0 : ℍ → ℂ) = traceSum data2 _ f at t2
      rw [← t2, smul_zero]
    · rw [hc, alOp_smul, f3.eigen, smul_comm]
    · rw [data3.trace_eq (M := 2) (c • f)]
      change traceSum data3 _ (c • (f : ℍ → ℂ)) = 0
      rw [traceSum_smul]
      change (0 : ℍ → ℂ) = traceSum data3 _ f at t3
      rw [← t3, smul_zero]

lemma sign_mul_self (a : ℤ) (h : (a : ZMod ℓ) ≠ 0) :
    (-(legendreSym ℓ a : ℂ)) * (-(legendreSym ℓ a : ℂ)) = 1 := by
  have hs := legendreSym.sq_one ℓ h
  have : ((legendreSym ℓ a ^ 2 : ℤ) : ℂ) = 1 := by rw [hs]; simp
  push_cast at this
  rw [neg_mul_neg, ← sq]
  exact this

lemma int_cast_ne (h13 : 13 ≤ ℓ) {p : ℕ} (hp : p = 2 ∨ p = 3) : (((p : ℕ) : ℤ) : ZMod ℓ) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro h
  exact coprime_ne h13 hp (by exact_mod_cast h)

lemma half_exponent (h13 : 13 ≤ ℓ) :
    (((2 * halfWt ℓ : ℕ) : ℤ) / 2 - 1) = (((ℓ - 5) / 2 : ℕ) : ℤ) := by
  have := (prime_ge h13).1
  unfold halfWt
  omega

/-- **The eigenvalue of `U₂` on the class is derived from the Atkin–Lehner sign.** -/
theorem newClass_U2 (h13 : 13 ≤ ℓ) {f : Forms ℓ} (hf : f ∈ newClass ℓ) :
    BoylanWebb.U 2 (qExpansion 1 f) = ((eig2 ℓ : ℤ) : ℂ) • qExpansion 1 f := by
  have h := hf.2.1.U_qExpansion (even_two_mul (halfWt ℓ) |>.natCast)
    (sign_mul_self 2 (by simpa using int_cast_ne h13 (p := 2) (Or.inl rfl)))
  convert h using 2
  rw [half_exponent h13, zpow_natCast]
  simp [eig2, sign2]

/-- **The eigenvalue of `U₃` on the class is derived from the Atkin–Lehner sign.** -/
theorem newClass_U3 (h13 : 13 ≤ ℓ) {f : Forms ℓ} (hf : f ∈ newClass ℓ) :
    BoylanWebb.U 3 (qExpansion 1 f) = ((eig3 ℓ : ℤ) : ℂ) • qExpansion 1 f := by
  have h := hf.2.2.U_qExpansion (even_two_mul (halfWt ℓ) |>.natCast)
    (sign_mul_self 3 (by simpa using int_cast_ne h13 (p := 3) (Or.inr rfl)))
  convert h using 2
  rw [half_exponent h13, zpow_natCast]
  simp [eig3, sign3]

/-- Descent of an eigenvalue relation along an injective embedding, then reduction. -/
lemma reduce_eigen {R F : Type*} [CommRing R] [Field F] (φ : R →+* ℂ)
    (hφ : Function.Injective φ) (ψ : R →+* F) (d : ℕ) (r : ℤ) (a : PowerSeries R)
    (h : BoylanWebb.U d (PowerSeries.map φ a) = (r : ℂ) • PowerSeries.map φ a) :
    BoylanWebb.U d (PowerSeries.map ψ a) = (r : F) • PowerSeries.map ψ a := by
  have hR : BoylanWebb.U d a = (r : R) • a := by
    apply PowerSeries.map_injective φ hφ
    rw [BoylanWebb.map_U, h]
    ext m
    simp
  rw [← BoylanWebb.map_U, hR]
  ext m
  simp

/-- **Target one, for Hecke eigenvectors.** An eigenvector of `T_ℓ` in the class with nonzero
reduction has eigenvalue nonzero modulo every prime above ℓ. -/
theorem newClass_eigenvalue_ne_zero (h13 : 13 ≤ ℓ) {R F : Type*} [CommRing R] [Field F] [CharP F ℓ]
    (φ : R →+* ℂ) (hφ : Function.Injective φ) (ψ : R →+* F) (a : PowerSeries R) {g : Forms ℓ}
    (hg : g ∈ newClass ℓ) (ha : PowerSeries.map φ a = qExpansion 1 g)
    (hf0 : PowerSeries.map ψ a ≠ 0) (α : R)
    (hα : qExpansion 1 (GoodHecke.heckeT (p := ℓ) (M := 6) g) = φ α • qExpansion 1 g) :
    ψ α ≠ 0 := by
  intro hz
  have hU2 := reduce_eigen φ hφ ψ 2 (eig2 ℓ) a (by rw [ha]; exact newClass_U2 h13 hg)
  have hU3 := reduce_eigen φ hφ ψ 3 (eig3 ℓ) a (by rw [ha]; exact newClass_U3 h13 hg)
  have hrep : BinaryRep (PowerSeries.map ψ a) ((ℓ - 3) / 2) :=
    binaryRep_of_reduced_modularForm φ hφ ψ (halfWt ℓ) a g ha
  have hcast2 : ((eig2 ℓ : ℤ) : F) = (legendreSym ℓ 2 : F) * (2 : F) ^ ((ℓ - 5) / 2) := by
    simp [eig2]
  have hcast3 : ((eig3 ℓ : ℤ) : F) = (legendreSym ℓ 3 : F) * (3 : F) ^ ((ℓ - 5) / 2) := by
    simp [eig3]
  rw [hcast2] at hU2
  rw [hcast3] at hU3
  apply U_ne_zero_of_binary_sign_eigenvalues ℓ h13 _ hrep hf0 hU2 hU3
  have hT := GoodHecke.qExpansion_heckeT (dataGood ℓ (six_dvd h13)) g
  rw [hα, ← ha, weight_sub_one h13] at hT
  ext m
  have hm := congrArg (PowerSeries.coeff m) hT
  simp only [PowerSeries.coeff_smul, PowerSeries.coeff_map, HeckeQExp.coeff_Tq, smul_eq_mul,
    zpow_natCast] at hm
  have hR : α * a.coeff m = a.coeff (ℓ * m) +
      (ℓ : R) ^ (ℓ - 4) * if ℓ ∣ m then a.coeff (m / ℓ) else 0 := by
    apply hφ
    rw [map_mul, hm, map_add, map_mul, map_pow, map_natCast]
    split_ifs <;> simp
  have hψ := congrArg ψ hR
  have hpos : ℓ - 4 ≠ 0 := by omega
  simp only [map_mul, map_add, map_pow, map_natCast, hz, zero_mul,
    CharP.cast_eq_zero F ℓ, zero_pow hpos, zero_add] at hψ
  rw [BoylanWebb.coeff_U, PowerSeries.coeff_map, map_zero]
  simpa using hψ.symm

/-- **Target one.** A normalized `T_ℓ`-eigenform in the class has ℓ-th coefficient nonzero under
every ring map to a field of characteristic ℓ, i.e. a unit at every prime above ℓ. -/
theorem newform_coeff_ell_ne_zero (h13 : 13 ≤ ℓ) {R F : Type*} [CommRing R] [Field F] [CharP F ℓ]
    (φ : R →+* ℂ) (hφ : Function.Injective φ) (ψ : R →+* F) (a : PowerSeries R) {g : Forms ℓ}
    (hg : g ∈ newClass ℓ) (ha : PowerSeries.map φ a = qExpansion 1 g)
    (h1 : a.coeff 1 = 1) (α : R)
    (hα : qExpansion 1 (GoodHecke.heckeT (p := ℓ) (M := 6) g) = φ α • qExpansion 1 g) :
    ψ (a.coeff ℓ) ≠ 0 := by
  have hf0 : PowerSeries.map ψ a ≠ 0 := by
    intro h
    have := congrArg (PowerSeries.coeff 1) h
    simp [h1] at this
  have hT := GoodHecke.qExpansion_heckeT (dataGood ℓ (six_dvd h13)) g
  rw [hα, ← ha] at hT
  have hm := congrArg (PowerSeries.coeff 1) hT
  have hnd : ¬ ℓ ∣ 1 := by
    intro h
    have := Nat.le_of_dvd one_pos h
    omega
  simp only [PowerSeries.coeff_smul, PowerSeries.coeff_map, HeckeQExp.coeff_Tq, smul_eq_mul,
    if_neg hnd, mul_zero, add_zero, h1, map_one, mul_one] at hm
  have hαe : α = a.coeff ℓ := hφ hm
  rw [← hαe]
  exact newClass_eigenvalue_ne_zero h13 φ hφ ψ a hg ha hf0 α hα

/-- `T_ℓ` as a complex-linear endomorphism of the actual weight `ℓ-3` space. -/
noncomputable def heckeL (h13 : 13 ≤ ℓ) : Module.End ℂ (Forms ℓ) where
  toFun := GoodHecke.heckeT (p := ℓ) (M := 6)
  map_add' f g := by
    apply modularExpansionLinear_injective (N := 6)
    rw [map_add]
    change qExpansion 1 _ = qExpansion 1 _ + qExpansion 1 _
    simp only [GoodHecke.qExpansion_heckeT (dataGood ℓ (six_dvd h13))]
    rw [show qExpansion 1 ((f + g : Forms ℓ) : ℍ → ℂ) = qExpansion 1 f + qExpansion 1 g from
      map_add (modularExpansionLinear 6 _) f g]
    ext m
    simp only [HeckeQExp.coeff_Tq, map_add]
    split_ifs <;> ring
  map_smul' c f := by
    apply modularExpansionLinear_injective (N := 6)
    rw [RingHom.id_apply, map_smul]
    change qExpansion 1 _ = c • qExpansion 1 _
    simp only [GoodHecke.qExpansion_heckeT (dataGood ℓ (six_dvd h13))]
    rw [show qExpansion 1 ((c • f : Forms ℓ) : ℍ → ℂ) = c • qExpansion 1 f from
      map_smul (modularExpansionLinear 6 _) c f]
    ext m
    simp only [HeckeQExp.coeff_Tq, PowerSeries.coeff_smul, smul_eq_mul]
    split_ifs <;> ring

@[simp] lemma heckeL_apply (h13 : 13 ≤ ℓ) (f : Forms ℓ) :
    heckeL h13 f = GoodHecke.heckeT (p := ℓ) (M := 6) f := rfl

variable (ℓ) in
/-- Coordinates to actual forms, as a complex-linear map. -/
noncomputable def formL : (Fin (2 * halfWt ℓ + 1) → ℂ) →ₗ[ℂ] Forms ℓ where
  toFun := formOf ℓ
  map_add' c d := by
    simp only [formOf, evenFormCombination, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [formOf, evenFormCombination, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply,
      Finset.smul_sum]

lemma formL_apply (c : Fin (2 * halfWt ℓ + 1) → ℂ) : formL ℓ c = formOf ℓ c := rfl

/-- The integer lattice inside the actual space. -/
noncomputable def formInt (c : Fin (2 * halfWt ℓ + 1) → ℤ) : Forms ℓ :=
  formL ℓ fun i => (c i : ℂ)

lemma qExpansion_formInt (c : Fin (2 * halfWt ℓ + 1) → ℤ) :
    qExpansion 1 (formInt c) = PowerSeries.map (Int.castRingHom ℂ) (ser ℓ c) := by
  rw [formInt, formL_apply]
  exact qExpansion_formOf ℓ c

lemma formInt_add (c d : Fin (2 * halfWt ℓ + 1) → ℤ) :
    formInt (c + d) = formInt c + formInt d := by
  rw [formInt, formInt, formInt, ← map_add]
  congr 1
  ext i
  simp

lemma formInt_smul (r : ℤ) (c : Fin (2 * halfWt ℓ + 1) → ℤ) :
    formInt (r • c) = (r : ℂ) • formInt c := by
  rw [formInt, formInt, ← map_smul]
  congr 1
  ext i
  simp

lemma heckeL_formInt (h13 : 13 ≤ ℓ) (c : Fin (2 * halfWt ℓ + 1) → ℤ) :
    heckeL h13 (formInt c) = formInt (tLat ℓ c) := by
  apply modularExpansionLinear_injective (N := 6)
  change qExpansion 1 _ = qExpansion 1 _
  rw [qExpansion_formInt, ser_tLat h13]
  exact (qExpansion_heckeT_int h13 (qExpansion_formInt c).symm).symm

/-- Every form in the class is a complex combination of sign-lattice forms. -/
theorem newClass_mem_span (h13 : 13 ≤ ℓ) {f : Forms ℓ} (hf : f ∈ newClass ℓ) :
    f ∈ Submodule.span ℂ (formInt '' (signLattice ℓ : Set (Fin (2 * halfWt ℓ + 1) → ℤ))) := by
  classical
  let n := halfWt ℓ
  let x : Fin (2 * n + 1) → ℂ :=
    evenCoordinates n (LevelSix.firstCoefficients (2 * n) f)
  have hfx : qExpansion 1 f = evenCombination n x := even_reconstruct_qExpansion n f
  have hser : ∀ m, (evenCombination n x).coeff m =
      ∑ i, (((evenSeries n i.val).coeff m : ℤ) : ℂ) * x i := by
    intro m
    simp [evenCombination, mul_comm]
  have hser' : ∀ (c : Fin (2 * n + 1) → ℤ) m, (ser ℓ c).coeff m =
      ∑ i, (evenSeries n i.val).coeff m * c i := by
    intro c m
    simp [ser, n, evenCombination, mul_comm]
  let r : (ℕ ⊕ ℕ) → Fin (2 * n + 1) → ℤ
    | .inl m, i => (evenSeries n i.val).coeff (2 * m) - eig2 ℓ * (evenSeries n i.val).coeff m
    | .inr m, i => (evenSeries n i.val).coeff (3 * m) - eig3 ℓ * (evenSeries n i.val).coeff m
  have hx : ∀ m, ∑ i, ((r m i : ℤ) : ℂ) * x i = 0 := by
    rintro (m | m)
    · have h := congrArg (PowerSeries.coeff m) (newClass_U2 h13 hf)
      rw [BoylanWebb.coeff_U, PowerSeries.coeff_smul, hfx, hser, hser, smul_eq_mul,
        Finset.mul_sum] at h
      simp only [r]
      push_cast
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc]
      rw [h, sub_self]
    · have h := congrArg (PowerSeries.coeff m) (newClass_U3 h13 hf)
      rw [BoylanWebb.coeff_U, PowerSeries.coeff_smul, hfx, hser, hser, smul_eq_mul,
        Finset.mul_sum] at h
      simp only [r]
      push_cast
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc]
      rw [h, sub_self]
  obtain ⟨s, c, w, hc, hsum⟩ := LatticeAlgebra.exists_integer_solutions r x hx
  have hmem : ∀ e, c e ∈ signLattice ℓ := by
    intro e
    refine ⟨?_, ?_⟩
    · ext m
      have := hc e (.inl m)
      simp only [r, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at this
      rw [BoylanWebb.coeff_U, map_zsmul, smul_eq_mul, hser', hser']
      linarith
    · ext m
      have := hc e (.inr m)
      simp only [r, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at this
      rw [BoylanWebb.coeff_U, map_zsmul, smul_eq_mul, hser', hser']
      linarith
  have hff : f = formL ℓ x := by
    apply modularExpansionLinear_injective (N := 6)
    change qExpansion 1 _ = qExpansion 1 _
    rw [hfx, formL_apply]
    exact (qExpansion_evenFormCombination n x).symm
  rw [hff, hsum, map_sum]
  refine Submodule.sum_mem _ fun e _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c e, hmem e, rfl⟩)

/-- `ε T_ℓ` on the sign lattice, for the quadratic twist `ε = (12/ℓ)`. -/
noncomputable def latticeTw (h13 : 13 ≤ ℓ) (ε : ℤ) : signLattice ℓ →ₗ[ℤ] signLattice ℓ :=
  ε • latticeT h13

lemma step_formInt (h13 : 13 ≤ ℓ) (ε : ℤ) (c : signLattice ℓ) :
    ((ε : ℂ) • heckeL h13) (formInt c.1) = formInt (latticeTw h13 ε c).1 := by
  have he : (latticeTw h13 ε c).1 = ε • tLat ℓ c.1 := rfl
  rw [he, formInt_smul, LinearMap.smul_apply, heckeL_formInt]

/-- `P` kills the class: polynomials in the integer operator act compatibly on forms. -/
lemma aeval_formInt (h13 : 13 ≤ ℓ) (ε : ℤ) (P : Polynomial ℤ) (c : signLattice ℓ) :
    Polynomial.aeval ((ε : ℂ) • heckeL h13) P (formInt c.1) =
      formInt (Polynomial.aeval (latticeTw h13 ε) P c).1 := by
  induction P using Polynomial.induction_on generalizing c with
  | C a =>
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    rw [Submodule.coe_smul, formInt_smul, Int.cast_smul_eq_zsmul]
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add, formInt_add, hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval ((ε : ℂ) • heckeL h13)),
      map_mul (Polynomial.aeval (latticeTw h13 ε)), Polynomial.aeval_X, Polynomial.aeval_X,
      Module.End.mul_apply, Module.End.mul_apply, step_formInt, ih]

/-- **Each eigenvalue of `ε T_ℓ` on the class is a root of the lattice characteristic polynomial.** -/
theorem newClass_isRoot (h13 : 13 ≤ ℓ) (ε : ℤ) {f : Forms ℓ} (hf : f ∈ newClass ℓ) (hf0 : f ≠ 0)
    (α : ℂ) (hT : ((ε : ℂ) • heckeL h13) f = α • f) :
    ((LinearMap.charpoly (latticeTw h13 ε)).map (Int.castRingHom ℂ)).IsRoot α := by
  let P := LinearMap.charpoly (latticeTw h13 ε)
  have hkill : Polynomial.aeval ((ε : ℂ) • heckeL h13) P f = 0 := by
    suffices hgen : ∀ x ∈ Submodule.span ℂ
        (formInt '' (signLattice ℓ : Set (Fin (2 * halfWt ℓ + 1) → ℤ))),
        Polynomial.aeval ((ε : ℂ) • heckeL h13) P x = 0 from hgen f (newClass_mem_span h13 hf)
    intro x hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      have := aeval_formInt h13 ε P ⟨c, hc⟩
      rw [this, LinearMap.aeval_self_charpoly]
      have h0 : formInt (0 : Fin (2 * halfWt ℓ + 1) → ℤ) = (0 : Forms ℓ) := by
        have := formInt_smul (ℓ := ℓ) 0 (0 : Fin (2 * halfWt ℓ + 1) → ℤ)
        simpa using this
      simpa using h0
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]
  have hev : Module.End.HasEigenvector ((ε : ℂ) • heckeL h13) α f :=
    ⟨Module.End.mem_eigenspace_iff.mpr hT, hf0⟩
  have heval := Module.End.aeval_apply_of_hasEigenvector hev
    (p := P.map (Int.castRingHom ℂ))
  have hmap : Polynomial.aeval ((ε : ℂ) • heckeL h13) (P.map (Int.castRingHom ℂ)) f = 0 := by
    have : P.map (Int.castRingHom ℂ) = P.map (algebraMap ℤ ℂ) := by congr 1
    rw [this, Polynomial.aeval_map_algebraMap, hkill]
  rw [hmap] at heval
  have := (smul_eq_zero.mp heval.symm).resolve_right hf0
  rw [Polynomial.IsRoot.def, ← Polynomial.coe_aeval_eq_eval]
  exact this

end RamanujanTau.TheoremA.SignLattice
