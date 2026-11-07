/-
# The universal admissible sparse triple Root–Vanishing equivalence
-/
import RamanujanTau.MultiQuintupleUniversalShortGeneration
import RamanujanTau.MultiQuintupleDualShellPartners
import RamanujanTau.MultiQuintupleShortDualConverse
import RamanujanTau.MultiQuintupleConverseThirteen

namespace Ramanujan.MultiQuintuple

noncomputable def projectiveDualLiftOfMem (p : ℕ) (v x : TernaryIntPoint)
    (hx : x ∈ projectiveDualLattice p v) : ProjectiveDualLift p v where
  point := x
  scalar := Classical.choose hx
  remainder := Classical.choose (Classical.choose_spec hx)
  point_eq := Classical.choose_spec (Classical.choose_spec hx)

/-- The converse for every admissible prime and every canonical residue.
Both short generation and the analytic opposite-partner input are proved
upstream; neither is assumed in this theorem. -/
theorem admissible_root_vanishing_converse {p i j k R : ℕ}
    (ha : AdmissibleSparseTriple p i j k) (hR : R < p)
    (hz : PersistentTripleVanishing p i j k R) : HasProjectiveRootTarget p i j k R := by
  classical
  by_cases hp13 : p=13
  · subst p
    exact admissible_root_vanishing_converse_thirteen i j k R ha hR hz
  letI : Fact p.Prime := ⟨ha.1⟩
  have hp3 : (p : ZMod 3) ≠ 0 := admissible_modulus_ne_zero_zmod3 ha
  letI : NeZero (p : ZMod 3) := ⟨hp3⟩
  have h3 : (3 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 3 p).not.mpr
    intro hd
    have hh := (Nat.prime_dvd_prime_iff_eq ha.1 (by decide : Nat.Prime 3)).mp hd
    exact ha.2.1 hh
  have hi : (i : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff i p).not.mpr
    apply Nat.not_dvd_of_pos_of_lt ha.2.2.1
    rcases ha with ⟨_,_,hi,hij,hjk,hk,_⟩
    omega
  have hk : (k : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff k p).not.mpr
    apply Nat.not_dvd_of_pos_of_lt
    · rcases ha with ⟨_,_,hi,hij,hjk,hk,_⟩; omega
    · rcases ha with ⟨_,_,hi,hij,hjk,hk,_⟩; omega
  let q : ℤ := (((3 : ZMod p)*(k : ZMod p))⁻¹).val
  have hq : (3 : ZMod p)*q*(k : ZMod p)=1 := by
    dsimp [q]
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val]
    calc
      _ = ((3 : ZMod p)*k)*((3 : ZMod p)*k)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ (mul_ne_zero h3 hk)
  let v : TernaryIntPoint := (((i : ℤ),(j : ℤ)),(k : ℤ))
  let S := shortSupportedDualSet p v
  let lifts (a : S) := projectiveDualLiftOfMem p v a.val a.property.1
  let signs (a : S) := canonicalDualSigns p hp3 a.val a.property.2.2
  apply root_target_of_short_dual_generation_and_cancellation ha q hq lifts signs
  · intro a
    exact a.property.2.1
  · have he : Set.range (fun a : S => (lifts a).point)=S := by
      change Set.range (fun a : S => a.val)=S
      exact Subtype.range_coe_subtype
    rw [he]
    exact admissible_short_dual_generation ha hp13
  · intro a
    obtain ⟨y,sy,hyN,hyn,hyp⟩ := persistent_vanishing_projective_shell_partner ha hR hz q hq h3 hi
      a.val a.property.1 (signs a)
    let b : S := ⟨y,hyN,by rw [hyn]; exact a.property.2.1,sy.cubicCharacter_ne_zero hp3⟩
    refine ⟨b,hyn,?_⟩
    have he : signs b=sy := Subsingleton.elim _ _
    change (6*(p : ℤ)) ∣ dualLatticeCompressedPhase p v q R y (signs b)-
      dualLatticeCompressedPhase p v q R a.val (signs a)-3*p
    rw [he]
    exact hyp

/-- Persistent vanishing is exactly the existence of a projective root
certificate, for all admissible sparse triples and canonical residues. -/
theorem admissible_root_vanishing_equivalence {p i j k R : ℕ}
    (ha : AdmissibleSparseTriple p i j k) (hR : R < p) :
    HasProjectiveRootTarget p i j k R ↔ PersistentTripleVanishing p i j k R := by
  constructor
  · have hpodd : Odd (p : ℤ) := by
      exact_mod_cast ha.1.odd_of_ne_two (by rcases ha with ⟨_,_,hi,hij,hjk,hk,_⟩; omega)
    rcases ha with ⟨_,_,hi,hij,hjk,hpk,_⟩
    exact hasProjectiveRootTarget_implies_persistentTripleVanishing p i j k R
      hi (by omega) (by omega) (by omega) (by omega) hpk hpodd
  · exact admissible_root_vanishing_converse ha hR

/-- The corrected rigidity proposition from the original research interface
is now discharged without an additional geometric or analytic hypothesis. -/
theorem admissibleRootVanishingRigidity_proved (p i j k R : ℕ) :
    AdmissibleRootVanishingRigidity p i j k R := by
  intro ha hR
  exact ((admissibleRootVanishingEquivalence_iff_rigidity p i j k R ha hR).mp
    (admissible_root_vanishing_equivalence ha hR)) ha hR

end Ramanujan.MultiQuintuple
