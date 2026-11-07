/-
# Extracting the exact root target from a dual lattice involution

This closes the arithmetic passage from an involution preserving the full
integral projective lattice and its linear phase to the root certificate.
A single supported cubic-character reversal selects the required sign.
-/
import RamanujanTau.MultiQuintupleLatticeConverse
import RamanujanTau.MultiQuintupleDualLatticePhase
import RamanujanTau.MultiQuintupleDualCharacter

namespace Ramanujan.MultiQuintuple

set_option maxHeartbeats 1000000 in
theorem hasProjectiveRootTarget_of_dual_lattice_involution
    {p i j k R : ℕ} [Fact p.Prime]
    (ha : AdmissibleSparseTriple p i j k)
    (c0 : ZMod p) (hc0 : 3*c0 = 2*(R : ZMod p)-((i : ZMod p)+j+k))
    (T : RationalTernaryOrthogonalInvolution)
    (hphase : ∀ x ∈ projectiveDualLattice p (((i : ℤ),(j : ℤ)),(k : ℤ)),
      ∃ y ∈ projectiveDualLattice p (((i : ℤ),(j : ℤ)),(k : ℤ)),
        T.linear (ternaryIntIndexToRat x) = ternaryIntIndexToRat y ∧
        dualLatticePhase p (((i : ℤ),(j : ℤ)),(k : ℤ)) c0 y =
          dualLatticePhase p (((i : ℤ),(j : ℤ)),(k : ℤ)) c0 x)
    (hflip : ∃ x y : TernaryIntPoint, ternaryCubicCharacter x ≠ 0 ∧
      T.linear (ternaryIntIndexToRat x) = ternaryIntIndexToRat y ∧
      ternaryCubicCharacter y = -ternaryCubicCharacter x) :
    HasProjectiveRootTarget p i j k R := by
  let v : TernaryIntPoint := (((i : ℤ),(j : ℤ)),(k : ℤ))
  let N := projectiveDualLattice p v
  let phi := dualLatticePhase p v c0
  have hp : p.Prime := ha.1
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp0
  have hip : 0 < i ∧ i < p := by
    rcases ha with ⟨_,_,hi,hij,hjk,hk,_⟩
    omega
  have hi0 : (i : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff i p).not.mpr (Nat.not_dvd_of_pos_of_lt hip.1 hip.2)
  have h2 : (2 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 2 p).not.mpr
    apply Nat.not_dvd_of_pos_of_lt (by decide)
    rcases ha with ⟨_,_,hi,hij,hjk,hk,_⟩
    omega
  have hvdiv : (p : ℤ) ∣ ternaryIntNorm v := ha.2.2.2.2.2.2
  obtain ⟨h,hv⟩ := hvdiv
  have hvdiv : (p : ℤ) ∣ ternaryIntNorm v := ⟨h,hv⟩
  have hN : ∀ x ∈ N, ∃ y ∈ N,
      T.linear (ternaryIntIndexToRat x) = ternaryIntIndexToRat y := by
    intro x hx
    obtain ⟨y,hy,hmap,_⟩ := hphase x hx
    exact ⟨y,hy,hmap⟩
  have hpres : ∀ x ∈ N, ∀ y,
      T.linear (ternaryIntIndexToRat x) = ternaryIntIndexToRat y → phi y = phi x := by
    intro x hx y hy
    obtain ⟨z,hz,hmap,hph⟩ := hphase x hx
    have heq : y = z := ternaryIntIndexToRat_injective (hy.symm.trans hmap)
    simpa only [heq] using hph
  let TL := CongruenceLatticeInvolution.ofProjective p i j k hp0 T hN
  obtain ⟨w,hw,b1,b2,b3,e,lambda,a1,a2,a3,hprimitive,he,hroot,hw1,hw2,hw3,hT⟩ :=
    TL.exists_primitive_short_projective_householder ha
  have hwN : w ∈ N := by
    refine ⟨lambda,((a1,a2),a3),?_⟩
    exact Prod.ext (Prod.ext hw1 hw2) hw3
  let W : ProjectiveDualLift p v := {
    point := w
    scalar := lambda
    remainder := ((a1,a2),a3)
    point_eq := Prod.ext (Prod.ext hw1 hw2) hw3
  }
  let u : ℤ := W.pairing
  have hvw : ternaryDot i j k w.1.1 w.1.2 w.2 = (p : ℤ)*u := by
    change ternaryIntDot v W.point = (p : ℤ)*W.pairing
    rw [W.pairing_eq hp0 h hv]
    exact W.dot_base h hv
  obtain ⟨c,hce⟩ : ∃ c : ℤ, c*e = 2 := by
    rcases he with rfl | rfl
    · exact ⟨2,by norm_num⟩
    · exact ⟨1,by norm_num⟩
  have hn3 : (ternaryIntNorm w : ZMod 3) ≠ 0 := by
    change ((ternaryNorm w.1.1 w.1.2 w.2 : ℤ) : ZMod 3) ≠ 0
    rw [hroot,Int.cast_mul]
    apply mul_ne_zero
    · rcases he with rfl | rfl <;> decide
    · exact admissible_modulus_ne_zero_zmod3 ha
  have hwq : ternaryIntIndexToRat w ≠ 0 := by
    intro hz
    apply hw
    apply ternaryIntIndexToRat_injective
    simpa [ternaryIntIndexToRat] using hz
  have hw1p : (w.1.1 : ZMod p) = (lambda : ZMod p)*(i : ZMod p) := by
    rw [hw1]; simp
  have hw2p : (w.1.2 : ZMod p) = (lambda : ZMod p)*(j : ZMod p) := by
    rw [hw2]; simp
  have hw3p : (w.2 : ZMod p) = (lambda : ZMod p)*(k : ZMod p) := by
    rw [hw3]; simp
  let base : ℤ := 2*lambda*R-(w.1.1+w.1.2+w.2)+6*u
  have hbase : (base : ZMod p) = 3*phi w := by
    have hph : phi w = W.phase c0 :=
      (W.phase_eq_dualLatticePhase c0 (by simpa [v] using hi0)).symm
    rw [hph]
    change ((2*lambda*R-(w.1.1+w.1.2+w.2)+6*u : ℤ) : ZMod p) =
      3*(2*(u : ZMod p)+c0*(lambda : ZMod p))
    push_cast
    rw [hw1p,hw2p,hw3p]
    linear_combination -(lambda : ZMod p)*hc0
  obtain ⟨x,y,hxchar,hxy,hxychar⟩ := hflip
  refine ⟨{
    lambda := lambda
    e := e
    c := c
    w1 := w.1.1
    w2 := w.1.2
    w3 := w.2
    a1 := a1
    a2 := a2
    a3 := a3
    u := u
    he := he
    hw1 := hw1
    hw2 := hw2
    hw3 := hw3
    hvw := hvw
    hroot := hroot
    hcoefficient := hce
    hcase := ?_
  }⟩
  rcases hT with hpositive | hnegative
  · have hHxy : ternaryRatHouseholder (ternaryIntIndexToRat w)
        (ternaryIntIndexToRat x) = ternaryIntIndexToRat y :=
      (hpositive _).symm.trans hxy
    have hchar := householder_integral_cubic_character w x y hw hn3 hHxy
    have hn1 : (ternaryIntNorm w : ZMod 3) = 1 := by
      apply mul_right_cancel₀ hxchar
      linear_combination hchar - hxychar
    have hTw : T.linear (ternaryIntIndexToRat w) = ternaryIntIndexToRat (-w) := by
      change TL.linear _ = _
      rw [hpositive,ternaryRatHouseholder_normal _ hwq,ternaryIntIndexToRat_neg]
    have hph := hpres w hwN (-w) hTw
    have hneg := dualLatticePhase_smul hp0 hvdiv c0 (-1) w hwN
    simp only [neg_one_smul] at hneg
    have hz : phi w = 0 := by
      apply (mul_eq_zero.mp (show (2 : ZMod p)*phi w = 0 by
        linear_combination -hph + hneg)).resolve_left h2
    have hb0 : (base : ZMod p) = 0 := by rw [hbase,hz]; ring
    obtain ⟨a,ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd base p).mp hb0
    left
    refine ⟨?_,a,?_⟩
    · simpa only [ternaryIntNorm,hroot] using hn1
    · dsimp [base] at ha
      linarith
  · have hHxy : ternaryRatHouseholder (ternaryIntIndexToRat w)
        (ternaryIntIndexToRat x) = ternaryIntIndexToRat (-y) := by
      have hh := congrArg Neg.neg ((hnegative _).symm.trans hxy)
      simpa only [neg_neg,ternaryIntIndexToRat_neg] using hh
    have hchar := householder_integral_cubic_character w x (-y) hw hn3 hHxy
    rw [ternaryCubicCharacter_neg,hxychar,neg_neg] at hchar
    have hn2 : (ternaryIntNorm w : ZMod 3) = 2 := by
      have hn : (ternaryIntNorm w : ZMod 3) = -1 := by
        apply mul_right_cancel₀ hxchar
        linear_combination hchar
      simpa using hn
    let z : TernaryIntPoint := (p : ℤ) • thetaIndexBasis1
    have hzN : z ∈ N := projectiveDualLattice_mul p v thetaIndexBasis1
    have hHz : ternaryRatHouseholder (ternaryIntIndexToRat w) (ternaryIntIndexToRat z) =
        ternaryIntIndexToRat (z - (c*w.1.1) • w) := by
      have hh := ternaryRatHouseholder_int_eq_shortRootReflect p e c w.1.1 w z hpz hroot
        (by simp [z,thetaIndexBasis1,ternaryDot]) hce
      simpa [shortRootReflectCoord] using hh
    have hTz : T.linear (ternaryIntIndexToRat z) =
        ternaryIntIndexToRat (-z + (c*w.1.1) • w) := by
      change TL.linear _ = _
      rw [hnegative,hHz,← ternaryIntIndexToRat_neg]
      congr 1
      module
    have hph := hpres z hzN (-z+(c*w.1.1) • w) hTz
    have hneg := dualLatticePhase_smul hp0 hvdiv c0 (-1) z hzN
    simp only [neg_one_smul] at hneg
    have hval : phi z = 2*(i : ZMod p) := by
      simpa [phi,z,v] using dualLatticePhase_p_basis1 hp0 v c0
    change dualLatticePhase p v c0 (-z+(c*w.1.1) • w) = phi z at hph
    rw [dualLatticePhase_add hp0 hvdiv c0 _ _ (N.neg_mem hzN) (N.smul_mem _ hwN),
      dualLatticePhase_smul hp0 hvdiv c0 _ w hwN,hneg] at hph
    change -phi z + (c*w.1.1) • phi w = phi z at hph
    rw [hval,zsmul_eq_mul,Int.cast_mul,hw1p] at hph
    have hfour : (c : ZMod p)*(lambda : ZMod p)*phi w = 4 := by
      apply mul_left_cancel₀ hi0
      linear_combination hph
    have htarget : ((c*lambda*base-12 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [hbase]
      linear_combination 3*hfour
    obtain ⟨a,ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (c*lambda*base-12) p).mp htarget
    right
    refine ⟨?_,base,a,rfl,?_⟩
    · simpa only [ternaryIntNorm,hroot] using hn2
    · linarith

end Ramanujan.MultiQuintuple
