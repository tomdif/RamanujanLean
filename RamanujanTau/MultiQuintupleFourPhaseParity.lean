import RamanujanTau.MultiQuintupleFourShellPartners

/-! Opposite phases on an equal-norm four-factor shell reverse the quartic
cubic character. This is a consequence of the phase formula, not an assumption. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 2000000

private theorem four_mod_two_mul_self : ∀ a : ZMod 2, a*a=a := by decide +kernel

private theorem four_opposite_count_signs :
    ∀ a b : Fin 4 → Bool, (fourSignCount b : ZMod 2)-(fourSignCount a : ZMod 2)=1 →
      (∏ i, dualCubicSign (b i))= -(∏ i, dualCubicSign (a i)) := by decide +kernel

theorem four_opposite_phase_reverses_character {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (v : Fin 4 → ℤ) (R : ℤ)
    (x y : ZMod p × (Fin 4 → ℤ))
    (hx : fourCubicCharacter x.2 ≠ 0) (hy : fourCubicCharacter y.2 ≠ 0)
    (hn : fourDualNorm p v y=fourDualNorm p v x)
    (hphase : fourCanonicalPhase p v R y=fourCanonicalPhase p v R x+p) :
    fourCubicCharacter y.2= -fourCubicCharacter x.2 := by
  let bx := fourCanonicalSigns x.2
  let byy := fourCanonicalSigns y.2
  have hbx := fourCanonicalSigns_spec x.2 hx
  have hby := fourCanonicalSigns_spec y.2 hy
  have hdx := Int.mul_ediv_cancel' (four_compressed_numerator_dvd p v R x bx hbx)
  have hdy := Int.mul_ediv_cancel' (four_compressed_numerator_dvd p v R y byy hby)
  have hdiv : (2*(p : ℤ)) ∣ fourCompressedNumerator p v R y byy/3-
      fourCompressedNumerator p v R x bx/3-(p : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2*p)).mp
    push_cast
    change fourCanonicalPhase p v R y-fourCanonicalPhase p v R x-p=0
    rw [hphase]
    ring
  obtain ⟨a,ha⟩ := hdiv
  have hfull : fourCompressedNumerator p v R y byy-fourCompressedNumerator p v R x bx-
      3*p=6*(p : ℤ)*a := by linear_combination 3*ha-hdy+hdx
  have hpmod2 : (p : ZMod 2)=1 := by
    have hpodd := (Fact.out : p.Prime).odd_of_ne_two hp2
    obtain ⟨k,hk⟩ := hpodd
    have hh := congrArg (fun n : ℕ => (n : ZMod 2)) hk
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
      show (2 : ZMod 2)=0 by decide,zero_mul,zero_add] using hh
  have hsum : (∑ i, (fourDualPoint p v y i : ZMod 2))=
      ∑ i, (fourDualPoint p v x i : ZMod 2) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod 2)) hn
    simpa only [fourDualNorm,Int.cast_sum,Int.cast_mul,four_mod_two_mul_self] using hh
  have hh := congrArg (fun z : ℤ => (z : ZMod 2)) hfull
  have hcount : (fourSignCount byy : ZMod 2)-(fourSignCount bx : ZMod 2)=1 := by
    simp only [fourCompressedNumerator,fourRawPhase,Int.cast_add,Int.cast_sub,
      Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,Int.cast_sum,hpmod2,
      show (6 : ZMod 2)=0 by decide,show (3 : ZMod 2)=1 by decide,
      zero_mul,zero_sub,sub_zero,one_mul,mul_one] at hh
    linear_combination hh+hsum
  simpa only [fourCubicCharacter,hbx,hby] using four_opposite_count_signs bx byy hcount

/-- An actual coefficient-vanishing hypothesis yields a same-norm partner
with reversed cubic character, on every nonzero short dual shell. -/
theorem four_persistent_vanishing_character_partner {p R : ℕ} [Fact p.Prime]
    {v : Fin 4 → ℕ} (hp2 : p ≠ 2) (h3 : (3 : ZMod p) ≠ 0)
    (hc : fourCanonical p v) (hR : R<p) (hz : PersistentFourVanishing p v R)
    (H : ℤ) (hv : (∑ i, (v i : ℤ)*(v i : ℤ))=(p : ℤ)*H)
    (hvi : (v 0 : ZMod p) ≠ 0) (x : ZMod p × (Fin 4 → ℤ))
    (hx : fourCubicCharacter x.2 ≠ 0)
    (hpos : 0<fourDualNorm p (fun i => (v i : ℤ)) x)
    (hshort : 2*fourDualNorm p (fun i => (v i : ℤ)) x<(p : ℤ)^2) :
    ∃ y : ZMod p × (Fin 4 → ℤ), fourCubicCharacter y.2 ≠ 0 ∧
      fourDualNorm p (fun i => (v i : ℤ)) y=fourDualNorm p (fun i => (v i : ℤ)) x ∧
      fourCanonicalPhase p (fun i => (v i : ℤ)) R y=
        fourCanonicalPhase p (fun i => (v i : ℤ)) R x+p ∧
      fourCubicCharacter y.2= -fourCubicCharacter x.2 := by
  obtain ⟨y,hy,hn,hphase⟩ := four_persistent_vanishing_short_partner
    hp2 h3 hc hR hz H hv hvi x hx hpos hshort
  exact ⟨y,hy,hn,hphase,four_opposite_phase_reverses_character hp2 _ R x y hx hy hn hphase⟩

end Ramanujan.MultiQuintuple
