/-
# Actual coefficient vanishing produces opposite supported lattice partners
-/
import RamanujanTau.MultiQuintupleDualGaussianCancellation
import RamanujanTau.MultiQuintupleCanonicalPhaseCharacter
import RamanujanTau.MultiQuintupleSupportedShellPartners

namespace Ramanujan.MultiQuintuple
open scoped BigOperators

def projectiveNormShell (p : ℕ) (v : TernaryIntPoint) (d : ℕ) :=
  {w : projectiveDualLattice p v // (ternaryIntNorm w.val).toNat=d}

theorem ternaryIntNorm_neg (w : TernaryIntPoint) : ternaryIntNorm (-w)=ternaryIntNorm w := by
  simp [ternaryIntNorm,ternaryNorm]

theorem projectiveNormShell_norm {p : ℕ} {v : TernaryIntPoint} {d : ℕ}
    (w : projectiveNormShell p v d) : ternaryIntNorm w.val.val=(d : ℤ) := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) w.property
  simpa only [Int.toNat_of_nonneg (ternaryIntNorm_nonneg _)] using h

instance projectiveNormShell_finite (p : ℕ) (v : TernaryIntPoint) (d : ℕ) :
    Finite (projectiveNormShell p v d) := by
  letI := (ternary_norm_shell_finite d).fintype
  apply Finite.of_injective (fun w : projectiveNormShell p v d =>
    (⟨w.val.val,projectiveNormShell_norm w⟩ : {w : TernaryIntPoint | ternaryIntNorm w=(d : ℤ)}))
  intro x y h
  have he : x.val.val=y.val.val := congrArg
    (fun z : {w : TernaryIntPoint | ternaryIntNorm w=(d : ℤ)} => z.val) h
  exact Subtype.ext (Subtype.ext he)

def projectiveNormShell_antipode (p : ℕ) (v : TernaryIntPoint) (d : ℕ) :
    projectiveNormShell p v d ≃ projectiveNormShell p v d where
  toFun w := ⟨⟨-w.val.val,(projectiveDualLattice p v).neg_mem w.val.property⟩,
    by simpa only [ternaryIntNorm_neg] using w.property⟩
  invFun w := ⟨⟨-w.val.val,(projectiveDualLattice p v).neg_mem w.val.property⟩,
    by simpa only [ternaryIntNorm_neg] using w.property⟩
  left_inv w := Subtype.ext (Subtype.ext (neg_neg _))
  right_inv w := Subtype.ext (Subtype.ext (neg_neg _))

noncomputable def fourierNormShellEquiv {p : ℕ} [Fact p.Prime]
    (v : TernaryIntPoint) (h3 : (3 : ZMod p) ≠ 0) (hvi : (v.1.1 : ZMod p) ≠ 0) (d : ℕ) :
    (fourierNormDegree p v) ⁻¹' {d} ≃ projectiveNormShell p v d :=
  (dualFourierEquiv v h3 hvi).subtypeEquiv (fun _ => Iff.rfl)

theorem persistent_vanishing_projective_shell_partner {p i j k R : ℕ} [Fact p.Prime]
    (ha : AdmissibleSparseTriple p i j k) (hR : R < p)
    (hz : PersistentTripleVanishing p i j k R) (q : ℤ)
    (hq : (3 : ZMod p)*q*(k : ZMod p)=1)
    (h3 : (3 : ZMod p) ≠ 0) (hi : (i : ZMod p) ≠ 0)
    (x : TernaryIntPoint) (hx : x ∈ projectiveDualLattice p (((i : ℤ),(j : ℤ)),(k : ℤ)))
    (sx : CompressedDualSigns p x) :
    ∃ y : TernaryIntPoint, ∃ sy : CompressedDualSigns p y,
      y ∈ projectiveDualLattice p (((i : ℤ),(j : ℤ)),(k : ℤ)) ∧
      ternaryIntNorm y=ternaryIntNorm x ∧
      (6*(p : ℤ)) ∣ dualLatticeCompressedPhase p (((i : ℤ),(j : ℤ)),(k : ℤ)) q R y sy -
        dualLatticeCompressedPhase p (((i : ℤ),(j : ℤ)),(k : ℤ)) q R x sx - 3*p := by
  classical
  let v : TernaryIntPoint := (((i : ℤ),(j : ℤ)),(k : ℤ))
  have hp3 : (p : ZMod 3) ≠ 0 := admissible_modulus_ne_zero_zmod3 ha
  let d := (ternaryIntNorm x).toNat
  letI := Fintype.ofFinite (projectiveNormShell p v d)
  let E := dualFourierEquiv v h3 (by simpa [v] using hi)
  let e := fourierNormShellEquiv v h3 (by simpa [v] using hi) d
  let A (w : projectiveNormShell p v d) : ℂ := rawFourierAmplitude p v R (E.symm w.val)
  let phase (w : projectiveNormShell p v d) := canonicalDualPhase p hp3 v q R w.val.val
  let P (w : projectiveNormShell p v d) := ternaryCubicCharacter w.val.val ≠ 0
  have hw (w : projectiveNormShell p v d) : fourierDualPoint p v (E.symm w.val)=w.val.val :=
    congrArg Subtype.val (E.apply_symm_apply w.val)
  have hzero : (∑ w : projectiveNormShell p v d, A w)=0 := by
    have hh := (e.symm.tsum_eq (fun z => rawFourierAmplitude p v R z.val)).trans
      (persistent_vanishing_fourier_shells ha hR hz d)
    simpa only [tsum_fintype] using hh
  have hpart := supported_opposite_partner_of_finite_shell ha.1 (by
      rcases ha with ⟨_,_,hi,hij,hjk,hk,_⟩; omega)
    (watsonPhaseRoot p) watsonCommonFactor watsonCommonFactor_ne_zero
    (watsonPhaseRoot_half_turn p) (watsonPhaseRoot_square_primitive p)
    P phase (projectiveNormShell_antipode p v d)
    (by intro w; change ternaryCubicCharacter (-w.val.val) ≠ 0 ↔ _; simp [P])
    (by
      intro w hs
      exact canonicalDualPhase_neg (v := v) (x := w.val.val) hp3 ha.2.2.2.2.2.2 w.val.property hs q R)
    A (by
      intro w hs
      have hh := rawFourierAmplitude_canonical hp3 v q R (by simpa [v] using hq)
        (E.symm w.val) (by rwa [hw])
      simpa only [hw] using hh)
    (by
      intro w hs
      have hh := rawFourierAmplitude_zero_of_unsupported p hp3 v R (E.symm w.val)
        (by rw [hw]; exact not_ne_iff.mp hs)
      exact hh) hzero
  let xx : projectiveNormShell p v d := ⟨⟨x,hx⟩,rfl⟩
  obtain ⟨yy,hy,hphase⟩ := hpart xx (sx.cubicCharacter_ne_zero hp3)
  let sy := canonicalDualSigns p hp3 yy.val.val hy
  refine ⟨yy.val.val,sy,yy.val.property,?_,?_⟩
  · exact (projectiveNormShell_norm yy).trans (projectiveNormShell_norm xx).symm
  · change canonicalDualPhase p hp3 v q R yy.val.val=canonicalDualPhase p hp3 v q R x+p at hphase
    rw [canonicalDualPhase_eq p hp3 v q R _ sy,canonicalDualPhase_eq p hp3 v q R _ sx] at hphase
    have hd : (2*(p : ℤ)) ∣ dualLatticeCompressedPhase p v q R yy.val.val sy/3 -
        dualLatticeCompressedPhase p v q R x sx/3 - (p : ℤ) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2*p)).mp
      push_cast
      linear_combination hphase
    obtain ⟨a,hd⟩ := hd
    have hx3 := Int.mul_ediv_cancel' (sx.three_dvd_phase v q R)
    have hy3 := Int.mul_ediv_cancel' (sy.three_dvd_phase v q R)
    refine ⟨a,?_⟩
    change dualLatticeCompressedPhase p v q R yy.val.val sy-
      dualLatticeCompressedPhase p v q R x sx-3*p=6*(p : ℤ)*a
    linear_combination 3*hd - hy3 + hx3

end Ramanujan.MultiQuintuple
