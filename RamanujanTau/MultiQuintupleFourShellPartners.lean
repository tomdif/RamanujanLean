import RamanujanTau.MultiQuintupleFourDualIndex
import RamanujanTau.MultiQuintupleSupportedShellPartners

/-! Actual persistent four-factor vanishing produces opposite partners on
nonzero short Fourier shells. No lattice symmetry is assumed here. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 2000000

noncomputable def fourCanonicalSigns (z : Fin 4 → ℤ) : Fin 4 → Bool :=
  if h : fourCubicCharacter z ≠ 0 then Classical.choose (exists_four_signs z h) else fun _ => false

theorem fourCanonicalSigns_spec (z : Fin 4 → ℤ) (hz : fourCubicCharacter z ≠ 0) :
    ∀ i, (z i : ZMod 3)=dualCubicSign (fourCanonicalSigns z i) := by
  simp only [fourCanonicalSigns,dif_pos hz]
  exact Classical.choose_spec (exists_four_signs z hz)

noncomputable def fourCanonicalPhase (p : ℕ) (v : Fin 4 → ℤ) (R : ℤ)
    (x : ZMod p × (Fin 4 → ℤ)) : ZMod (2*p) :=
  (fourCompressedNumerator p v R x (fourCanonicalSigns x.2)/3 : ℤ)

theorem fourRawAmplitude_canonical (p : ℕ) [NeZero p] (v : Fin 4 → ℤ) (R : ℤ)
    (x : ZMod p × (Fin 4 → ℤ)) (hx : fourCubicCharacter x.2 ≠ 0) :
    fourRawAmplitude p v R x=fourCommonFactor p*
      (watsonPhaseRoot p)^(fourCanonicalPhase p v R x).val := by
  rw [fourRawAmplitude_compressed p v R x _ (fourCanonicalSigns_spec x.2 hx),
    watsonAddChar_eq_root_power]
  rfl

/-- The analytic and cyclotomic parts of the four-factor necessity argument,
for actual coefficients and every supported vector below the short-shell bound. -/
theorem four_persistent_vanishing_short_partner {p R : ℕ} [Fact p.Prime]
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
        fourCanonicalPhase p (fun i => (v i : ℤ)) R x+p := by
  classical
  let vv : Fin 4 → ℤ := fun i => (v i : ℤ)
  let d := fourNormDegree p vv x
  let I := (fourNormDegree p vv) ⁻¹' {d}
  letI : Finite I := four_norm_degree_finite vv h3 (by simpa [vv] using hvi) d
  letI := Fintype.ofFinite I
  let P (w : I) := fourCubicCharacter w.val.2 ≠ 0
  let phase (w : I) := fourCanonicalPhase p vv R w.val
  let A (w : I) := fourRawAmplitude p vv R w.val
  let xx : I := ⟨x,rfl⟩
  have hnorm (w : I) : fourDualNorm p vv w.val=fourDualNorm p vv x :=
    (fourNormDegree_norm p vv d w).trans (fourNormDegree_norm p vv d xx).symm
  have hzero : (∑ w : I, A w)=0 := by
    simpa only [tsum_fintype] using
      four_persistent_vanishing_fourier_shells hp2 hc hR hz H hv d
  have hs : (∑' w : {w : I // P w}, fourCommonFactor p*(watsonPhaseRoot p)^(phase w).val)=0 := by
    change (∑' w : ↑(setOf P), fourCommonFactor p*(watsonPhaseRoot p)^(phase w.val).val)=0
    rw [tsum_subtype (setOf P) (fun w => fourCommonFactor p*(watsonPhaseRoot p)^(phase w).val)]
    have hf : (setOf P).indicator (fun w => fourCommonFactor p*(watsonPhaseRoot p)^(phase w).val)=A := by
      funext w
      by_cases hw : P w
      · simp only [Set.indicator_apply,Set.mem_setOf_eq,if_pos hw]
        exact (fourRawAmplitude_canonical p vv R w.val hw).symm
      · simp only [Set.indicator_apply,Set.mem_setOf_eq,if_neg hw]
        exact (fourRawAmplitude_zero_of_unsupported p vv R w.val (not_ne_iff.mp hw)).symm
    rw [hf,tsum_fintype,hzero]
  rw [tsum_mul_left] at hs
  have hzphase : (∑ w : {w : I // P w}, (watsonPhaseRoot p)^(phase w).val)=0 := by
    simpa only [tsum_fintype] using (mul_eq_zero.mp hs).resolve_left (fourCommonFactor_ne_zero p)
  have he : ((fourDualNorm p vv x/p : ℤ) : ZMod p) ≠ 0 :=
    four_short_norm_quotient_nonzero vv H hv x hpos hshort
  have hn (w : {w : I // P w}) :
      (-3*w.val.val.1)*ZMod.castHom (dvd_mul_left p 2) (ZMod p) (phase w)-
        ((H : ZMod p)+((2*(R : ℤ)-(∑ i, vv i) : ℤ) : ZMod p)/3)*(-3*w.val.val.1)^2=
          ((fourDualNorm p vv x/p : ℤ) : ZMod p) := by
    change (-3*w.val.val.1)*ZMod.castHom (dvd_mul_left p 2) (ZMod p)
      ((fourCompressedNumerator p vv R w.val.val (fourCanonicalSigns w.val.val.2)/3 : ℤ) : ZMod (2*p))-
      _ = _
    rw [map_intCast]
    rw [← hnorm w.val]
    exact four_phase_projective_norm h3 vv R H hv w.val.val _
      (fourCanonicalSigns_spec w.val.val.2 w.property)
  have hpartners := opposite_phase_partner_of_projective_norm hp2 (watsonPhaseRoot p)
    (watsonPhaseRoot_half_turn p) (watsonPhaseRoot_square_primitive p)
    (fun w : {w : I // P w} => phase w) (fun w => -3*w.val.val.1)
    ((H : ZMod p)+((2*(R : ℤ)-(∑ i, vv i) : ℤ) : ZMod p)/3)
    ((fourDualNorm p vv x/p : ℤ) : ZMod p) he hn hzphase
  obtain ⟨y,hy⟩ := hpartners ⟨xx,hx⟩
  exact ⟨y.val.val,y.property,hnorm y.val,hy⟩

end Ramanujan.MultiQuintuple
