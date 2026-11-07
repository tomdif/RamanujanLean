/-
# Exact short-generator certificates for normalized projective lattices
-/
import RamanujanTau.MultiQuintupleIntegralSpan
import RamanujanTau.MultiQuintupleDualCharacter
import Mathlib.FieldTheory.Finite.Basic

namespace Ramanujan.MultiQuintuple

def shortSupportedDualSet (p : ℕ) (v : TernaryIntPoint) : Set TernaryIntPoint :=
  {x | x ∈ projectiveDualLattice p v ∧ 2*ternaryIntNorm x < (p : ℤ)^2 ∧
    ternaryCubicCharacter x ≠ 0}

def normalizedDualMap (p j k : ℕ) : TernaryIntPoint →ₗ[ℤ] TernaryIntPoint where
  toFun x := ((x.1.1,(j : ℤ)*x.1.1+(p : ℤ)*x.1.2),
    (k : ℤ)*x.1.1+(p : ℤ)*x.2)
  map_add' := by intros; ext <;> simp <;> ring
  map_smul' := by intros; ext <;> simp <;> ring

theorem normalizedDualMap_mem (p j k : ℕ) (x : TernaryIntPoint) :
    normalizedDualMap p j k x ∈ projectiveDualLattice p ((1,(j : ℤ)),(k : ℤ)) := by
  refine ⟨x.1.1,((0,x.1.2),x.2),?_⟩
  ext <;> simp [normalizedDualMap] <;> ring

theorem normalizedDualMap_surjective_on (p j k : ℕ) (x : TernaryIntPoint)
    (hx : x ∈ projectiveDualLattice p ((1,(j : ℤ)),(k : ℤ))) :
    ∃ y, normalizedDualMap p j k y = x := by
  obtain ⟨a,z,rfl⟩ := hx
  refine ⟨((a+(p : ℤ)*z.1.1,z.1.2-(j : ℤ)*z.1.1),z.2-(k : ℤ)*z.1.1),?_⟩
  ext <;> simp [normalizedDualMap] <;> ring

def NormalizedGeneratorCertificate (p j k : ℕ) (vs : List TernaryIntPoint) : Prop :=
  generatorDetGcd vs = 1 ∧ ∀ x ∈ vs,
    2*ternaryIntNorm (normalizedDualMap p j k x) < (p : ℤ)^2 ∧
      ternaryCubicCharacter (normalizedDualMap p j k x) ≠ 0

instance (p j k : ℕ) (vs : List TernaryIntPoint) :
    Decidable (NormalizedGeneratorCertificate p j k vs) := by
  unfold NormalizedGeneratorCertificate
  infer_instance

/-- The certificate checks integral coordinates in an explicit basis of the
actual projective lattice, not just the index of an unrelated sublattice. -/
theorem normalized_short_generation_of_certificate (p j k : ℕ)
    (vs : List TernaryIntPoint) (hc : NormalizedGeneratorCertificate p j k vs) :
    Submodule.span ℤ (shortSupportedDualSet p ((1,(j : ℤ)),(k : ℤ))) =
      projectiveDualLattice p ((1,(j : ℤ)),(k : ℤ)) := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun x hx => hx.1)
  · intro x hx
    obtain ⟨y,rfl⟩ := normalizedDualMap_surjective_on p j k x hx
    have htop := span_list_eq_top_of_generatorDetGcd vs hc.1
    have hsub : Submodule.span ℤ {a | a ∈ vs} ≤
        (Submodule.span ℤ (shortSupportedDualSet p ((1,(j : ℤ)),(k : ℤ)))).comap
          (normalizedDualMap p j k) := by
      apply Submodule.span_le.mpr
      intro a ha
      exact Submodule.subset_span ⟨normalizedDualMap_mem p j k a,hc.2 a ha⟩
    exact hsub (by rw [htop]; trivial)

/-- A row either certifies a quadratic nonresidue or supplies the unique
canonical square root and, when ordered distinctly, a short-generator list. -/
def NormalizedGeneratorRow (p j : ℕ) (row : Option (ℕ × List TernaryIntPoint)) : Prop :=
  match row with
  | none => (-(1 : ZMod p)-(j : ZMod p)^2)^((p-1)/2) = -1
  | some (k,vs) => 2*k < p ∧ (1 : ZMod p)+(j : ZMod p)^2+(k : ZMod p)^2 = 0 ∧
      (1 < j → j < k → p ≠ 13 → NormalizedGeneratorCertificate p j k vs)

instance (p j : ℕ) (row : Option (ℕ × List TernaryIntPoint)) :
    Decidable (NormalizedGeneratorRow p j row) := by
  cases row <;> unfold NormalizedGeneratorRow <;> infer_instance

theorem canonical_square_root_unique {p : ℕ} [Fact p.Prime]
    (k r : ℕ) (hk : 0 < k) (hkp : 2*k < p) (hrp : 2*r < p)
    (hsq : (k : ZMod p)^2 = (r : ZMod p)^2) : k = r := by
  have hh : ((k : ZMod p)-(r : ZMod p))*((k : ZMod p)+(r : ZMod p)) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hh with hh | hh
  · have hc := congrArg ZMod.val (sub_eq_zero.mp hh)
    simpa only [ZMod.val_natCast_of_lt (show k < p by omega),
      ZMod.val_natCast_of_lt (show r < p by omega)] using hc
  · have hd : p ∣ k+r := (ZMod.natCast_eq_zero_iff (k+r) p).mp (by simpa using hh)
    exact False.elim ((Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hd)

theorem normalized_row_yields_certificate {p : ℕ} [Fact p.Prime]
    (hp2 : 2 < p) (hp13 : p ≠ 13) (j k : ℕ) (hj : 1 < j) (hjk : j < k)
    (hkp : 2*k < p) (hiso : (1 : ZMod p)+(j : ZMod p)^2+(k : ZMod p)^2 = 0)
    (row : Option (ℕ × List TernaryIntPoint)) (hr : NormalizedGeneratorRow p j row) :
    ∃ vs, NormalizedGeneratorCertificate p j k vs := by
  cases row with
  | none =>
      have htwo : (2 : ZMod p) ≠ 0 :=
        (ZMod.natCast_eq_zero_iff 2 p).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hp2)
      have hk0 : (k : ZMod p) ≠ 0 :=
        (ZMod.natCast_eq_zero_iff k p).not.mpr
          (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
      have he : 2*((p-1)/2) = p-1 := by
        obtain ⟨a,ha⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
        omega
      have hsq : (k : ZMod p)^2 = -1-(j : ZMod p)^2 := by
        linear_combination hiso
      have hpow : ((k : ZMod p)^2)^((p-1)/2) = 1 := by
        rw [← pow_mul,he]
        exact ZMod.pow_card_sub_one_eq_one hk0
      change (-(1 : ZMod p)-(j : ZMod p)^2)^((p-1)/2) = -1 at hr
      rw [← hsq,hpow] at hr
      exact False.elim (htwo (by linear_combination hr))
  | some data =>
      obtain ⟨r,vs⟩ := data
      obtain ⟨hrp,hiso',hvs⟩ := hr
      have hkr : k = r := canonical_square_root_unique k r (by omega) hkp hrp (by
        linear_combination hiso - hiso')
      subst r
      exact ⟨vs,hvs hj hjk hp13⟩

theorem normalized_generation_of_checked_rows {p : ℕ} [Fact p.Prime]
    (hp2 : 2 < p) (hp13 : p ≠ 13)
    (rows : ℕ → Option (ℕ × List TernaryIntPoint))
    (hrows : ∀ j : Fin ((p+1)/2), NormalizedGeneratorRow p j.val (rows j.val))
    (j k : ℕ) (hj : 1 < j) (hjk : j < k) (hkp : 2*k < p)
    (hiso : (1 : ZMod p)+(j : ZMod p)^2+(k : ZMod p)^2 = 0) :
    Submodule.span ℤ (shortSupportedDualSet p ((1,(j : ℤ)),(k : ℤ))) =
      projectiveDualLattice p ((1,(j : ℤ)),(k : ℤ)) := by
  obtain ⟨vs,hvs⟩ := normalized_row_yields_certificate hp2 hp13 j k hj hjk hkp hiso
    (rows j) (hrows ⟨j,by omega⟩)
  exact normalized_short_generation_of_certificate p j k vs hvs

end Ramanujan.MultiQuintuple
