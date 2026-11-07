import RamanujanTau.TheoremA.GoodHecke
import RamanujanTau.TheoremA.LatticeAlgebra
import RamanujanTau.TheoremA.ReducedLevelSixOrdinarity

/-!
# The newform sign class and the integer sign lattice in weight ℓ−3

The Atkin–Lehner eigenvalue formula identifies the class with signs
`(-(2/ℓ), -(3/ℓ))` inside the prescribed `U₂, U₃` eigenspace. On the integer
lattice of that eigenspace, the Hecke operator `T_ℓ` has determinant prime to ℓ.
Its proof reduces to the all-prime ordinarity theorem, and uses no multiplicity-one
theorem, Deligne bound, or number-field integrality.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.SignLattice
open ModularForm CongruenceSubgroup UpperHalfPlane PowerSeries
open scoped MatrixGroups ModularForm
open TraceCosets AtkinLehner GoodHecke BadPrime

/-- Atkin–Lehner data at the prime 2 of level six. -/
def data2 : CosetData 2 3 := ⟨2, 1, 1, 1, by norm_num⟩

/-- Atkin–Lehner data at the prime 3 of level six. -/
def data3 : CosetData 3 2 := ⟨1, 1, 1, 1, by norm_num⟩

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Data for the Hecke coset representatives at a prime `ℓ` coprime to six. -/
def dataGood (ℓ : ℕ) (h : (6 : ℤ) ∣ (ℓ : ℤ) ^ 2 - 1) : CosetData ℓ 6 :=
  ⟨1, ((ℓ : ℤ) ^ 2 - 1) / 6, 1, ℓ, by
    have he := Int.mul_ediv_cancel' h
    push_cast
    linear_combination -he⟩

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- The half-weight `(ℓ-3)/2`. -/
def halfWt (ℓ : ℕ) : ℕ := (ℓ - 3) / 2

/-- Space of level-six forms in weight `ℓ-3`. -/
abbrev Forms : Type := ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) ((2 * halfWt ℓ : ℕ) : ℤ)

/-- The integer eigenvalue of `U₂` on the class. -/
def eig2 (ℓ : ℕ) [Fact ℓ.Prime] : ℤ := legendreSym ℓ 2 * 2 ^ ((ℓ - 5) / 2)

/-- The integer eigenvalue of `U₃` on the class. -/
def eig3 (ℓ : ℕ) [Fact ℓ.Prime] : ℤ := legendreSym ℓ 3 * 3 ^ ((ℓ - 5) / 2)

/-- The series attached to integer coordinates. -/
noncomputable abbrev ser (c : Fin (2 * halfWt ℓ + 1) → ℤ) : PowerSeries ℤ :=
  evenCombination (halfWt ℓ) c

/-- The actual form attached to integer coordinates. -/
noncomputable def formOf (c : Fin (2 * halfWt ℓ + 1) → ℂ) : Forms ℓ :=
  evenFormCombination (halfWt ℓ) c

lemma qExpansion_formOf (c : Fin (2 * halfWt ℓ + 1) → ℤ) :
    qExpansion 1 (formOf ℓ fun i => (c i : ℂ)) = PowerSeries.map (Int.castRingHom ℂ) (ser ℓ c) := by
  rw [formOf, qExpansion_evenFormCombination, evenCombination_map]
  rfl

/-- Integer coordinates of an integer series, read from its first coefficients. -/
noncomputable def lat (a : PowerSeries ℤ) : Fin (2 * halfWt ℓ + 1) → ℤ :=
  evenCoordinates (halfWt ℓ) fun i => a.coeff i.val

lemma ser_lat {a : PowerSeries ℤ} {g : Forms ℓ}
    (h : PowerSeries.map (Int.castRingHom ℂ) a = qExpansion 1 g) : ser ℓ (lat ℓ a) = a :=
  (even_expansion_descent (Int.castRingHom ℂ) (RingHom.injective_int _) (halfWt ℓ) a g h).symm

/-- Every integer-coordinate series is the expansion of an actual form. -/
lemma exists_form (c : Fin (2 * halfWt ℓ + 1) → ℤ) :
    ∃ g : Forms ℓ, PowerSeries.map (Int.castRingHom ℂ) (ser ℓ c) = qExpansion 1 g :=
  ⟨formOf ℓ fun i => (c i : ℂ), (qExpansion_formOf ℓ c).symm⟩

/-- The integer eigenspace of `U₂` and `U₃`. -/
def signLattice : Submodule ℤ (Fin (2 * halfWt ℓ + 1) → ℤ) where
  carrier := {c | BoylanWebb.U 2 (ser ℓ c) = eig2 ℓ • ser ℓ c ∧
    BoylanWebb.U 3 (ser ℓ c) = eig3 ℓ • ser ℓ c}
  add_mem' {c d} hc hd := by
    have hs : ser ℓ (c + d) = ser ℓ c + ser ℓ d := map_add (evenCombinationLinear (halfWt ℓ)) c d
    simp only [Set.mem_setOf_eq, hs, BoylanWebb.U_add, hc.1, hc.2, hd.1, hd.2, smul_add, and_self]
  zero_mem' := by
    have hs : ser ℓ 0 = 0 := map_zero (evenCombinationLinear (halfWt ℓ))
    simp only [Set.mem_setOf_eq, hs, smul_zero]
    constructor <;> (ext n; simp [BoylanWebb.coeff_U])
  smul_mem' r c hc := by
    have hs : ser ℓ (r • c) = r • ser ℓ c := map_smul (evenCombinationLinear (halfWt ℓ)) r c
    have hU : ∀ d (f : PowerSeries ℤ), BoylanWebb.U d (r • f) = r • BoylanWebb.U d f := by
      intro d f; ext n; rw [BoylanWebb.coeff_U, map_zsmul, map_zsmul, BoylanWebb.coeff_U]
    simp only [Set.mem_setOf_eq, hs, hU, hc.1, hc.2, smul_comm r, and_self]

/-- The integer Hecke series operator, with `ℓ^(ℓ-4)` in the `V` term. -/
noncomputable def tSeries (a : PowerSeries ℤ) : PowerSeries ℤ :=
  HeckeQExp.Tq ℓ ((ℓ : ℤ) ^ (ℓ - 4)) a

lemma coeff_tSeries (a : PowerSeries ℤ) (m : ℕ) :
    (tSeries ℓ a).coeff m = a.coeff (ℓ * m) +
      (ℓ : ℤ) ^ (ℓ - 4) * if ℓ ∣ m then a.coeff (m / ℓ) else 0 :=
  HeckeQExp.coeff_Tq _ _ _ _

lemma tSeries_add (a b : PowerSeries ℤ) : tSeries ℓ (a + b) = tSeries ℓ a + tSeries ℓ b := by
  ext m
  simp only [coeff_tSeries, map_add]
  split_ifs <;> ring

lemma tSeries_smul (r : ℤ) (a : PowerSeries ℤ) : tSeries ℓ (r • a) = r • tSeries ℓ a := by
  ext m
  simp only [coeff_tSeries, map_zsmul, smul_eq_mul]
  split_ifs <;> ring

variable {ℓ}

lemma prime_ge (h13 : 13 ≤ ℓ) : ℓ % 2 = 1 ∧ ℓ % 3 ≠ 0 := by
  have hp := hℓ.out
  constructor
  · exact hp.eq_two_or_odd.resolve_left (by omega)
  · intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)
    omega

lemma six_dvd (h13 : 13 ≤ ℓ) : (6 : ℤ) ∣ (ℓ : ℤ) ^ 2 - 1 := by
  obtain ⟨h2, h3⟩ := prime_ge h13
  have h6 : ℓ % 6 = 1 ∨ ℓ % 6 = 5 := by omega
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ℓ = 6 * m + ℓ % 6 := ⟨ℓ / 6, (Nat.div_add_mod ℓ 6).symm⟩
  rcases h6 with h | h <;> rw [h] at hm <;> rw [hm] <;> push_cast
  · exact ⟨6 * m ^ 2 + 2 * m, by ring⟩
  · exact ⟨6 * m ^ 2 + 10 * m + 4, by ring⟩

lemma coprime_ne (h13 : 13 ≤ ℓ) {p : ℕ} (hp : p = 2 ∨ p = 3) : ¬ ℓ ∣ p := by
  intro h
  have := Nat.le_of_dvd (by rcases hp with rfl | rfl <;> norm_num) h
  rcases hp with rfl | rfl <;> omega

lemma U_tSeries (h13 : 13 ≤ ℓ) {p : ℕ} (hp : p = 2 ∨ p = 3) (a : PowerSeries ℤ) :
    BoylanWebb.U p (tSeries ℓ a) = tSeries ℓ (BoylanWebb.U p a) := by
  have hpr : ℓ.Prime := hℓ.out
  have hp0 : 0 < ℓ := hpr.pos
  have hcop : Nat.Coprime ℓ p := (Nat.Prime.coprime_iff_not_dvd hpr).mpr (coprime_ne h13 hp)
  ext m
  rw [BoylanWebb.coeff_U, coeff_tSeries, coeff_tSeries, BoylanWebb.coeff_U, Nat.mul_left_comm]
  congr 1
  by_cases hm : ℓ ∣ m
  · have hpm : ℓ ∣ p * m := hm.mul_left p
    rw [if_pos hm, if_pos hpm, BoylanWebb.coeff_U, Nat.mul_div_assoc _ hm]
  · have hpm : ¬ ℓ ∣ p * m := fun h => hm (hcop.dvd_of_dvd_mul_left h)
    rw [if_neg hm, if_neg hpm]

instance [hℓ : Fact ℓ.Prime] : NeZero (6 * ℓ) := ⟨by have := hℓ.out.ne_zero; omega⟩

lemma weight_sub_one (h13 : 13 ≤ ℓ) : (((2 * halfWt ℓ : ℕ) : ℤ) - 1) = ((ℓ - 4 : ℕ) : ℤ) := by
  obtain ⟨h2, -⟩ := prime_ge h13
  unfold halfWt
  omega

/-- The analytic operator has expansion `tSeries`. -/
theorem qExpansion_heckeT_int (h13 : 13 ≤ ℓ) {a : PowerSeries ℤ} {g : Forms ℓ}
    (h : PowerSeries.map (Int.castRingHom ℂ) a = qExpansion 1 g) :
    PowerSeries.map (Int.castRingHom ℂ) (tSeries ℓ a) =
      qExpansion 1 (GoodHecke.heckeT (p := ℓ) (M := 6) g) := by
  rw [qExpansion_heckeT (dataGood ℓ (six_dvd h13)), ← h, weight_sub_one h13]
  ext m
  simp only [coeff_map, coeff_tSeries, HeckeQExp.coeff_Tq, map_add, map_mul, map_pow, map_natCast,
    zpow_natCast]
  split_ifs <;> simp

/-- The Hecke operator on integer coordinates. -/
noncomputable def tLat (ℓ : ℕ) [Fact ℓ.Prime] (c : Fin (2 * halfWt ℓ + 1) → ℤ) :
    Fin (2 * halfWt ℓ + 1) → ℤ :=
  lat ℓ (tSeries ℓ (ser ℓ c))

lemma ser_tLat (h13 : 13 ≤ ℓ) (c : Fin (2 * halfWt ℓ + 1) → ℤ) :
    ser ℓ (tLat ℓ c) = tSeries ℓ (ser ℓ c) := by
  obtain ⟨g, hg⟩ := exists_form ℓ c
  exact ser_lat ℓ (qExpansion_heckeT_int h13 hg)

lemma ser_injective : Function.Injective (ser ℓ) := evenCombination_injective _

/-- `T_ℓ` as a ℤ-linear endomorphism of the sign lattice. -/
noncomputable def latticeT (h13 : 13 ≤ ℓ) : signLattice ℓ →ₗ[ℤ] signLattice ℓ where
  toFun c := ⟨tLat ℓ c.1, by
    have hc := c.2
    refine ⟨?_, ?_⟩
    · rw [ser_tLat h13, U_tSeries h13 (Or.inl rfl), hc.1, tSeries_smul]
    · rw [ser_tLat h13, U_tSeries h13 (Or.inr rfl), hc.2, tSeries_smul]⟩
  map_add' c d := by
    apply Subtype.ext
    apply ser_injective
    change ser ℓ (tLat ℓ (c.1 + d.1)) = ser ℓ (tLat ℓ c.1 + tLat ℓ d.1)
    have hs : ∀ u v, ser ℓ (u + v) = ser ℓ u + ser ℓ v :=
      map_add (evenCombinationLinear (halfWt ℓ))
    rw [hs, ser_tLat h13, ser_tLat h13, ser_tLat h13, hs, tSeries_add]
  map_smul' r c := by
    apply Subtype.ext
    apply ser_injective
    change ser ℓ (tLat ℓ (r • c.1)) = ser ℓ (r • tLat ℓ c.1)
    have hs : ∀ (r : ℤ) u, ser ℓ (r • u) = r • ser ℓ u :=
      map_smul (evenCombinationLinear (halfWt ℓ))
    rw [hs, ser_tLat h13, ser_tLat h13, hs, tSeries_smul]

omit hℓ in
lemma map_int_smul {R : Type*} [CommRing R] (ψ : ℤ →+* R) (r : ℤ) (a : PowerSeries ℤ) :
    PowerSeries.map ψ (r • a) = ψ r • PowerSeries.map ψ a := by
  ext m
  simp only [PowerSeries.coeff_map, map_zsmul, PowerSeries.coeff_smul, smul_eq_mul]
  rw [zsmul_eq_mul]
  simp only [eq_intCast]

/-- **`T_ℓ` is invertible modulo ℓ on the integer sign lattice.** -/
theorem latticeT_det_not_dvd (h13 : 13 ≤ ℓ) : ¬ (ℓ : ℤ) ∣ LinearMap.det (latticeT h13) := by
  intro hdet
  obtain ⟨x, y, hx, hT⟩ := LatticeAlgebra.exists_kernel_of_dvd_det ℓ _ hdet
  let ψ : ℤ →+* ZMod ℓ := Int.castRingHom (ZMod ℓ)
  let f : PowerSeries (ZMod ℓ) := PowerSeries.map ψ (ser ℓ x.1)
  have hs : ∀ (r : ℤ) u, ser ℓ (r • u) = r • ser ℓ u :=
    map_smul (evenCombinationLinear (halfWt ℓ))
  have hf0 : f ≠ 0 := by
    intro hf
    apply hx
    have hc : ∀ i, (ℓ : ℤ) ∣ x.1 i := by
      have hz : (fun i => ψ (x.1 i)) = 0 := by
        apply evenCombination_injective (R := ZMod ℓ) (halfWt ℓ)
        rw [← evenCombination_map]
        change f = _
        rw [hf]
        ext m
        simp [evenCombination]
      intro i
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun hz i)
    choose z hz using hc
    have hxz : x.1 = (ℓ : ℤ) • z := funext hz
    have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
    have hcancel : ∀ a b : PowerSeries ℤ, (ℓ : ℤ) • a = (ℓ : ℤ) • b → a = b := by
      intro a b hab
      ext m
      have := congrArg (PowerSeries.coeff m) hab
      simp only [map_zsmul, smul_eq_mul] at this
      exact mul_left_cancel₀ hℓ0 this
    have hU : ∀ d (g : PowerSeries ℤ), BoylanWebb.U d ((ℓ : ℤ) • g) = (ℓ : ℤ) • BoylanWebb.U d g := by
      intro d g; ext n; rw [BoylanWebb.coeff_U, map_zsmul, map_zsmul, BoylanWebb.coeff_U]
    have hzm : z ∈ signLattice ℓ := by
      have h := x.2
      rw [hxz] at h
      refine ⟨hcancel _ _ ?_, hcancel _ _ ?_⟩
      · have := h.1
        rw [hs, hU] at this
        rw [this, smul_comm]
      · have := h.2
        rw [hs, hU] at this
        rw [this, smul_comm]
    exact ⟨⟨z, hzm⟩, Subtype.ext hxz⟩
  have hU2 : BoylanWebb.U 2 f = ((legendreSym ℓ 2 : ZMod ℓ) * (2 : ZMod ℓ) ^ ((ℓ - 5) / 2)) • f := by
    change BoylanWebb.U 2 (PowerSeries.map ψ _) = _
    rw [← BoylanWebb.map_U, x.2.1, map_int_smul]
    congr 1
    simp [eig2, ψ]
  have hU3 : BoylanWebb.U 3 f = ((legendreSym ℓ 3 : ZMod ℓ) * (3 : ZMod ℓ) ^ ((ℓ - 5) / 2)) • f := by
    change BoylanWebb.U 3 (PowerSeries.map ψ _) = _
    rw [← BoylanWebb.map_U, x.2.2, map_int_smul]
    congr 1
    simp [eig3, ψ]
  obtain ⟨g, hg⟩ := exists_form ℓ x.1
  have hrep : BinaryRep f ((ℓ - 3) / 2) :=
    binaryRep_of_reduced_modularForm (Int.castRingHom ℂ) (RingHom.injective_int _) ψ
      (halfWt ℓ) (ser ℓ x.1) g hg
  apply U_ne_zero_of_binary_sign_eigenvalues ℓ h13 f hrep hf0 hU2 hU3
  have hT' : tSeries ℓ (ser ℓ x.1) = (ℓ : ℤ) • ser ℓ y.1 := by
    rw [← ser_tLat h13, ← hs]
    exact congrArg (fun u : signLattice ℓ => ser ℓ u.1) hT
  have hpos : ℓ - 4 ≠ 0 := by omega
  ext m
  have hm := congrArg (fun a : PowerSeries ℤ => ψ (a.coeff m)) hT'
  simp only [coeff_tSeries, map_add, map_mul, map_pow, map_zsmul, smul_eq_mul, ψ, eq_intCast,
    Int.cast_natCast, CharP.cast_eq_zero (ZMod ℓ) ℓ, zero_pow hpos, zero_mul, add_zero] at hm
  rw [BoylanWebb.coeff_U]
  simpa [f, ψ, coeff_map] using hm

end RamanujanTau.TheoremA.SignLattice
