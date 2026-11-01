/-
# The complete arithmetic converse from short dual generation and cancellation

This theorem discharges the symmetry construction, preservation of both
integer lattices, phase transport, sign selection, and exact root target.
The remaining inputs are generation and opposite-phase partners on the
short supported dual vectors; neither input is asserted here for all primes.
-/
import RamanujanTau.MultiQuintupleDualRootTarget
import RamanujanTau.MultiQuintupleDualPhaseParity

namespace Ramanujan.MultiQuintuple

set_option maxHeartbeats 1000000 in
theorem root_target_of_short_dual_generation_and_cancellation
    {ι : Type*} {p i j k R : ℕ} [Fact p.Prime]
    (ha : AdmissibleSparseTriple p i j k)
    (q : ℤ) (hq : (3 : ZMod p)*q*(k : ZMod p) = 1)
    (x : ι → ProjectiveDualLift p (((i : ℤ),(j : ℤ)),(k : ℤ)))
    (signs : ∀ a, CompressedDualSigns p (x a).point)
    (hshort : ∀ a, 2*ternaryIntNorm (x a).point < (p : ℤ)^2)
    (hspan : Submodule.span ℤ (Set.range (fun a => (x a).point)) =
      projectiveDualLattice p (((i : ℤ),(j : ℤ)),(k : ℤ)))
    (hpartners : ∀ a, ∃ b,
      ternaryIntNorm (x b).point = ternaryIntNorm (x a).point ∧
      (6*(p : ℤ)) ∣ (x b).compressedPhase q R (signs b).count -
        (x a).compressedPhase q R (signs a).count - 3*p) :
    HasProjectiveRootTarget p i j k R := by
  classical
  let v : TernaryIntPoint := (((i : ℤ),(j : ℤ)),(k : ℤ))
  let S := Set.range (fun a => (x a).point)
  let N := projectiveDualLattice p v
  let c0 : ZMod p := ((q*(k : ℤ)*(2*(R : ℤ)-((i : ℤ)+j+k)) : ℤ) : ZMod p)
  have hp : p.Prime := ha.1
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp2 : 2 < p := by rcases ha with ⟨_,_,hi,hij,hjk,hk,_⟩; omega
  have hpodd : Odd (p : ℤ) := by
    exact_mod_cast hp.odd_of_ne_two (by omega)
  have hvi : (v.1.1 : ZMod p) ≠ 0 := by
    have hi0 : (i : ZMod p) ≠ 0 := by
      apply (ZMod.natCast_eq_zero_iff i p).not.mpr
      apply Nat.not_dvd_of_pos_of_lt
      · exact ha.2.2.1
      · rcases ha with ⟨_,_,hi,hij,hjk,hk,_⟩; omega
    simpa [v] using hi0
  have htwo : (2 : ZMod p) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff 2 p).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hp2)
  have hp3 : (p : ZMod 3) ≠ 0 := by
    simpa using admissible_modulus_ne_zero_zmod3 ha
  have hvdiv : (p : ℤ) ∣ ternaryIntNorm v := ha.2.2.2.2.2.2
  obtain ⟨h,hv⟩ := hvdiv
  have hvdiv : (p : ℤ) ∣ ternaryIntNorm v := ⟨h,hv⟩
  have hc0 : (3 : ZMod p)*c0 = 2*(R : ZMod p)-((i : ZMod p)+j+k) := by
    dsimp [c0]
    push_cast
    linear_combination (2*(R : ZMod p)-((i : ZMod p)+j+k))*hq
  have hproperties : ∀ a b,
      ternaryIntNorm (x b).point = ternaryIntNorm (x a).point →
      (6*(p : ℤ)) ∣ (x b).compressedPhase q R (signs b).count -
        (x a).compressedPhase q R (signs a).count - 3*p →
      (x b).point ≠ (x a).point ∧ (x b).phase c0 = (x a).phase c0 ∧
        ternaryCubicCharacter (x b).point = -ternaryCubicCharacter (x a).point := by
    intro a b hn hc
    have hchar := opposite_compressed_phase_reverses_cubic p hpodd
      (x a).point (x b).point (signs a) (signs b) q R
      (x a).pairing (x b).pairing hn hc
    have hne : (x b).point ≠ (x a).point := by
      intro heq
      rw [heq] at hchar
      have hz : (2 : ZMod 3)*ternaryCubicCharacter (x a).point = 0 := by
        linear_combination hchar
      exact (signs a).cubicCharacter_ne_zero hp3
        ((mul_eq_zero.mp hz).resolve_left (by decide : (2 : ZMod 3) ≠ 0))
    have hd : (p : ℤ) ∣ (x b).compressedPhase q R (signs b).count -
        (x a).compressedPhase q R (signs a).count := by
      obtain ⟨d,hd⟩ := hc
      refine ⟨6*d+3,?_⟩
      linear_combination hd
    have hph := (x a).phase_eq_of_compressed_congruent (x b) ha.2.1 q R
      (signs a).count (signs b).count (by simpa using hq) hd
    exact ⟨hne,hph,hchar⟩
  have hs : ∀ a, (x a).point ∈ N := by
    intro a
    change (x a).point ∈ projectiveDualLattice p (((i : ℤ),(j : ℤ)),(k : ℤ))
    rw [← hspan]
    exact Submodule.subset_span ⟨a,rfl⟩
  have hspanQ : Submodule.span ℚ (Set.range (fun a => ternaryIntIndexToRat (x a).point)) = ⊤ := by
    have himage : ternaryIntIndexToRat '' S =
        Set.range (fun a => ternaryIntIndexToRat (x a).point) := by
      ext z
      constructor
      · rintro ⟨w,⟨a,rfl⟩,rfl⟩
        exact ⟨a,rfl⟩
      · rintro ⟨a,rfl⟩
        exact ⟨(x a).point,⟨a,rfl⟩,rfl⟩
    simpa only [himage] using projective_integral_generators_span_rat p hp0 v S hspan
  have hnphase : ∃ a, (x a).phase c0 ≠ 0 := by
    obtain ⟨z,⟨a,rfl⟩,hz⟩ := exists_nonzero_dual_phase_generator hp0 hvdiv c0 S hspan
      (mul_ne_zero htwo hvi)
    exact ⟨a,by rwa [(x a).phase_eq_dualLatticePhase c0 hvi]⟩
  obtain ⟨T,hT⟩ := short_phase_partners_yield_orthogonal_involution x hpodd hvi h hv c0
    hshort hspanQ (by
      intro a
      obtain ⟨b,hn,hc⟩ := hpartners a
      obtain ⟨hne,hph,_⟩ := hproperties a b hn hc
      exact ⟨b,hn,hne,hph⟩) hnphase
  apply hasProjectiveRootTarget_of_dual_lattice_involution ha c0 hc0 T
  · apply phase_preserved_of_integral_generators hp0 hvdiv c0 S hspan T.linear
    rintro z ⟨a,rfl⟩
    obtain ⟨b,hTb,hn,hne,hph⟩ := hT a
    refine ⟨(x b).point,hs b,hTb,?_⟩
    simpa only [(x a).phase_eq_dualLatticePhase c0 hvi,
      (x b).phase_eq_dualLatticePhase c0 hvi] using hph
  · obtain ⟨a,ha⟩ := hnphase
    obtain ⟨b0,hn0,hc0'⟩ := hpartners a
    obtain ⟨hne0,hph0,hchar0⟩ := hproperties a b0 hn0 hc0'
    obtain ⟨b1,hTb,hn1,hne1,hph1⟩ := hT a
    have heq := (x a).short_phase_partner_unique (x b1) (x b0) hpodd h hv c0
      hn1 hn0 (hshort a) hne1 hne0 hph1 hph0
    refine ⟨(x a).point,(x b0).point,(signs a).cubicCharacter_ne_zero hp3,?_,hchar0⟩
    rwa [heq] at hTb

end Ramanujan.MultiQuintuple
