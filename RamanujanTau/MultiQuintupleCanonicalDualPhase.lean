/-
# Canonical compressed phases on supported projective dual vectors
-/
import RamanujanTau.MultiQuintupleDualPhaseParity
import RamanujanTau.MultiQuintupleDualLatticePhase

namespace Ramanujan.MultiQuintuple

private theorem dualCubicSign_injective : Function.Injective dualCubicSign := by
  intro a b h
  cases a <;> cases b <;> first | rfl | contradiction

instance compressedDualSigns_subsingleton {p : ℕ} {x : TernaryIntPoint}
    [NeZero (p : ZMod 3)] : Subsingleton (CompressedDualSigns p x) where
  allEq a b := by
    have h1 := dualCubicSign_injective (mul_left_cancel₀ (NeZero.ne (p : ZMod 3)) (a.h1.symm.trans b.h1))
    have h2 := dualCubicSign_injective (mul_left_cancel₀ (NeZero.ne (p : ZMod 3)) (a.h2.symm.trans b.h2))
    have h3 := dualCubicSign_injective (mul_left_cancel₀ (NeZero.ne (p : ZMod 3)) (a.h3.symm.trans b.h3))
    cases a
    cases b
    simp_all

def CompressedDualSigns.neg {p : ℕ} {x : TernaryIntPoint}
    (s : CompressedDualSigns p x) : CompressedDualSigns p (-x) where
  b1 := !s.b1
  b2 := !s.b2
  b3 := !s.b3
  h1 := by
    change ((-x.1.1 : ℤ) : ZMod 3) = _
    rw [Int.cast_neg,s.h1]
    cases s.b1 <;> simp [dualCubicSign]
  h2 := by
    change ((-x.1.2 : ℤ) : ZMod 3) = _
    rw [Int.cast_neg,s.h2]
    cases s.b2 <;> simp [dualCubicSign]
  h3 := by
    change ((-x.2 : ℤ) : ZMod 3) = _
    rw [Int.cast_neg,s.h3]
    cases s.b3 <;> simp [dualCubicSign]

theorem CompressedDualSigns.count_neg {p : ℕ} {x : TernaryIntPoint}
    (s : CompressedDualSigns p x) : ((s.neg.count : ℕ) : ℤ)=3-(s.count : ℤ) := by
  rcases s with ⟨a,b,c,_,_,_⟩
  cases a <;> cases b <;> cases c <;> norm_num [neg,count,cubicWatsonConjugateCount]

def dualLatticeBasePhase (p : ℕ) (v : TernaryIntPoint) (q R : ℤ) (x : TernaryIntPoint) : ℤ :=
  dualWatsonBasePhase q R (ternaryIntDot v x / p) x.1.1 x.1.2 x.2

def dualLatticeCompressedPhase (p : ℕ) (v : TernaryIntPoint) (q R : ℤ)
    (x : TernaryIntPoint) (s : CompressedDualSigns p x) : ℤ :=
  dualWatsonCompressedPhase p (dualLatticeBasePhase p v q R x) s.count

theorem CompressedDualSigns.three_dvd_phase {p : ℕ} {x : TernaryIntPoint}
    (s : CompressedDualSigns p x) (v : TernaryIntPoint) (q R : ℤ) :
    (3 : ℤ) ∣ dualLatticeCompressedPhase p v q R x s := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
  simp only [dualLatticeCompressedPhase,dualLatticeBasePhase,dualWatsonCompressedPhase,
    dualWatsonBasePhase,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,
    show (6 : ZMod 3)=0 by decide,zero_mul,zero_add,s.h1,s.h2,s.h3]
  rcases s with ⟨a,b,c,_,_,_⟩
  cases a <;> cases b <;> cases c <;>
    norm_num [CompressedDualSigns.count,cubicWatsonConjugateCount,dualCubicSign] <;>
    ring_nf <;> simp [show (3 : ZMod 3)=0 by decide,show (6 : ZMod 3)=0 by decide]

theorem dualLatticeBasePhase_neg {p : ℕ} [Fact p.Prime] {v x : TernaryIntPoint}
    (hv : (p : ℤ) ∣ ternaryIntNorm v) (hx : x ∈ projectiveDualLattice p v) (q R : ℤ) :
    dualLatticeBasePhase p v q R (-x) = -dualLatticeBasePhase p v q R x := by
  have hd := projectiveDualLattice_pairing_dvd hv hx
  have he : ternaryIntDot v (-x) = -ternaryIntDot v x := by
    simp [ternaryIntDot,ternaryDot]; ring
  simp only [dualLatticeBasePhase,he,Int.neg_ediv_of_dvd hd,Prod.fst_neg,Prod.snd_neg]
  exact dualWatsonBasePhase_neg q R _ _ _ _

theorem dualLatticeCompressedPhase_neg {p : ℕ} [Fact p.Prime] {v x : TernaryIntPoint}
    (hv : (p : ℤ) ∣ ternaryIntNorm v) (hx : x ∈ projectiveDualLattice p v)
    (q R : ℤ) (s : CompressedDualSigns p x) :
    dualLatticeCompressedPhase p v q R (-x) s.neg =
      3*(p : ℤ)-dualLatticeCompressedPhase p v q R x s := by
  rw [dualLatticeCompressedPhase,dualLatticeBasePhase_neg hv hx,s.count_neg]
  exact dualWatsonCompressedPhase_antipodal _ _ _

end Ramanujan.MultiQuintuple
