import RamanujanTau.MultiQuintupleFourCancellation

/-! Integer Watson coordinates for four-factor cancellation. -/
namespace Ramanujan.MultiQuintuple
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

abbrev QuadIntPoint := Fin 4 → ℤ
def branchZ (x : QuintBranchIndex) : ℤ := 3*x.2+if x.1 then 1 else 0
def quadZ (x : QuadQuintBranchIndex) : QuadIntPoint :=
  ![branchZ x.1.1.1,branchZ x.1.1.2,branchZ x.1.2,branchZ x.2]
def quadBits (x : QuadQuintBranchIndex) : Fin 4 → Bool :=
  ![x.1.1.1.1,x.1.1.2.1,x.1.2.1,x.2.1]
def quadAssemble (b : Fin 4 → Bool) (z : QuadIntPoint) : QuadQuintBranchIndex :=
  ((((b 0,z 0),(b 1,z 1)),(b 2,z 2)),(b 3,z 3))

lemma branchZ_injective : Function.Injective branchZ := by
  rintro ⟨b,n⟩ ⟨c,m⟩ h
  cases b <;> cases c <;> simp [branchZ] at h ⊢ <;> omega

lemma quadZ_injective : Function.Injective quadZ := by
  rintro ⟨⟨⟨a,b⟩,c⟩,d⟩ ⟨⟨⟨a',b'⟩,c'⟩,d'⟩ h
  have ha : a=a' := branchZ_injective (congrFun h 0)
  have hb : b=b' := branchZ_injective (congrFun h 1)
  have hc : c=c' := branchZ_injective (congrFun h 2)
  have hd : d=d' := branchZ_injective (congrFun h 3)
  rw [ha,hb,hc,hd]

def fourDot {R : Type*} [CommRing R] (v z : Fin 4 → R) : R :=
  v 0*z 0+v 1*z 1+v 2*z 2+v 3*z 3
def fourSum {R : Type*} [CommRing R] (z : Fin 4 → R) : R := z 0+z 1+z 2+z 3
def fourEnergy {R : Type*} [CommRing R] (p : R) (v z : Fin 4 → R) : R :=
  p*(fourDot z z-fourSum z)+6*fourDot v z
def fourEnergyTriple {R : Type*} [CommRing R] (p : R) (v z : Fin 4 → R) : R :=
  p*fourDot z z-3*p*fourSum z+18*fourDot v z

lemma fourEnergyTriple_scale (p : ℤ) (v z : QuadIntPoint) :
    fourEnergyTriple p v (fun i => 3*z i)=9*fourEnergy p v z := by
  simp only [fourEnergyTriple,fourEnergy,fourDot,fourSum]
  ring

/-- The actual Watson exponent is a single quadratic polynomial in `3n+b`. -/
lemma quadExp2_energy (p i j k l : ℕ) (x : QuadQuintBranchIndex) :
    3*quadExp2 p i j k l x =
      fourEnergy (p : ℤ) ![(i : ℤ),(j : ℤ),(k : ℤ),(l : ℤ)] (quadZ x) := by
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    norm_num [quadExp2,pointTripleExp2,tripleQuintExp2,quintExp2,quintExpA2,quintExpB2,
      quadB4,quadN4,pointB1,pointB2,pointB3,pointN1,pointN2,pointN3,
      fourEnergy,fourDot,fourSum,quadZ,branchZ,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] <;> ring

end Ramanujan.MultiQuintuple
