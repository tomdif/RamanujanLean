/-
# Integral ternary forms and unimodular changes of coordinates
-/
import RamanujanTau.MultiQuintupleIntegralSpan
import Mathlib.Algebra.Order.Round

namespace Ramanujan.MultiQuintuple

@[ext] structure IntegralTernaryGram where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ

namespace IntegralTernaryGram

def dot (G : IntegralTernaryGram) (x y : TernaryIntPoint) : ℤ :=
  G.a*x.1.1*y.1.1+G.b*x.1.2*y.1.2+G.c*x.2*y.2+
  G.d*(x.1.1*y.1.2+x.1.2*y.1.1)+G.e*(x.1.1*y.2+x.2*y.1.1)+
  G.f*(x.1.2*y.2+x.2*y.1.2)

def norm (G : IntegralTernaryGram) (x : TernaryIntPoint) : ℤ := G.dot x x

def det (G : IntegralTernaryGram) : ℤ :=
  G.a*G.b*G.c+2*G.d*G.e*G.f-G.a*G.f^2-G.b*G.e^2-G.c*G.d^2

def minor (G : IntegralTernaryGram) : ℤ := G.a*G.b-G.d^2

def Positive (G : IntegralTernaryGram) : Prop := ∀ x : TernaryIntPoint, x ≠ 0 → 0 < G.norm x

theorem norm_zero (G : IntegralTernaryGram) : G.norm 0 = 0 := by simp [norm,dot]

theorem a_pos {G : IntegralTernaryGram} (hG : G.Positive) : 0 < G.a := by
  simpa [norm,dot,thetaIndexBasis1] using hG thetaIndexBasis1 (by decide)

theorem minor_pos {G : IntegralTernaryGram} (hG : G.Positive) : 0 < G.minor := by
  have ha := a_pos hG
  have hx : (((-G.d,G.a),0) : TernaryIntPoint) ≠ 0 := by
    intro hh
    have he := congrArg (fun x : TernaryIntPoint => x.1.2) hh
    change G.a=0 at he
    omega
  have hp := hG ((-G.d,G.a),0) hx
  have he : G.norm ((-G.d,G.a),0) = G.a*G.minor := by simp [norm,dot,minor]; ring
  rw [he] at hp
  exact (mul_pos_iff_of_pos_left ha).mp hp

end IntegralTernaryGram

structure TernaryUnimodularBasis where
  x : TernaryIntPoint
  y : TernaryIntPoint
  z : TernaryIntPoint
  det_unit : ternaryPointDet x y z = 1 ∨ ternaryPointDet x y z = -1

namespace TernaryUnimodularBasis

def standard : TernaryUnimodularBasis where
  x := ((1,0),0)
  y := ((0,1),0)
  z := ((0,0),1)
  det_unit := by left; rfl

def map (B : TernaryUnimodularBasis) : TernaryIntPoint →ₗ[ℤ] TernaryIntPoint where
  toFun u := u.1.1 • B.x+u.1.2 • B.y+u.2 • B.z
  map_add' := by intros; simp only [Prod.fst_add,Prod.snd_add,add_smul]; module
  map_smul' := by intros; simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,smul_add,smul_smul]; module

theorem map_injective (B : TernaryUnimodularBasis) : Function.Injective B.map := by
  apply (injective_iff_map_eq_zero B.map).mpr
  intro u hu
  have h1 : ternaryPointDet (B.map u) B.y B.z = u.1.1*ternaryPointDet B.x B.y B.z := by
    simp [map,ternaryPointDet,ternaryDet]; ring
  have h2 : ternaryPointDet B.x (B.map u) B.z = u.1.2*ternaryPointDet B.x B.y B.z := by
    simp [map,ternaryPointDet,ternaryDet]; ring
  have h3 : ternaryPointDet B.x B.y (B.map u) = u.2*ternaryPointDet B.x B.y B.z := by
    simp [map,ternaryPointDet,ternaryDet]; ring
  rw [hu] at h1 h2 h3
  have hd : ternaryPointDet B.x B.y B.z ≠ 0 := by rcases B.det_unit with h | h <;> omega
  have hz1 : u.1.1=0 := (mul_eq_zero.mp (by simpa [ternaryPointDet,ternaryDet] using h1.symm)).resolve_right hd
  have hz2 : u.1.2=0 := (mul_eq_zero.mp (by simpa [ternaryPointDet,ternaryDet] using h2.symm)).resolve_right hd
  have hz3 : u.2=0 := (mul_eq_zero.mp (by simpa [ternaryPointDet,ternaryDet] using h3.symm)).resolve_right hd
  exact Prod.ext (Prod.ext hz1 hz2) hz3

theorem map_surjective (B : TernaryUnimodularBasis) : Function.Surjective B.map := by
  intro u
  have hh := ternaryPointDet_smul B.x B.y B.z u
  rcases B.det_unit with hd | hd
  · refine ⟨((ternaryPointDet u B.y B.z,ternaryPointDet B.x u B.z),ternaryPointDet B.x B.y u),?_⟩
    simpa [map,hd] using hh.symm
  · refine ⟨((-ternaryPointDet u B.y B.z,-ternaryPointDet B.x u B.z),-ternaryPointDet B.x B.y u),?_⟩
    have hneg := congrArg Neg.neg hh
    simpa [map,hd,neg_add,neg_smul,add_comm,add_left_comm,add_assoc] using hneg.symm

def gram (B : TernaryUnimodularBasis) (G : IntegralTernaryGram) : IntegralTernaryGram where
  a := G.norm B.x
  b := G.norm B.y
  c := G.norm B.z
  d := G.dot B.x B.y
  e := G.dot B.x B.z
  f := G.dot B.y B.z

set_option maxHeartbeats 0 in
theorem gram_norm (B : TernaryUnimodularBasis) (G : IntegralTernaryGram) (u : TernaryIntPoint) :
    (B.gram G).norm u = G.norm (B.map u) := by
  simp [gram,map,IntegralTernaryGram.norm,IntegralTernaryGram.dot]
  ring

theorem gram_positive (B : TernaryUnimodularBasis) (G : IntegralTernaryGram) (hG : G.Positive) :
    (B.gram G).Positive := by
  intro u hu
  rw [gram_norm]
  apply hG
  intro hz
  exact hu (B.map_injective (by simpa using hz))

set_option maxHeartbeats 0 in
theorem gram_det (B : TernaryUnimodularBasis) (G : IntegralTernaryGram) :
    (B.gram G).det = G.det := by
  have hid : (B.gram G).det = (ternaryPointDet B.x B.y B.z)^2*G.det := by
    simp [gram,IntegralTernaryGram.det,IntegralTernaryGram.norm,IntegralTernaryGram.dot,
      ternaryPointDet,ternaryDet]
    ring
  rw [hid]
  rcases B.det_unit with h | h <;> simp [h]

end TernaryUnimodularBasis
end Ramanujan.MultiQuintuple
