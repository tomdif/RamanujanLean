import RamanujanTau.MultiQuintupleFourReflectionCriterion

/-! A second quadratic norm family: `p=2m²+n²`, with a denominator-five reflection. -/
namespace Ramanujan.MultiQuintuple
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def fourBinaryV {R : Type*} [CommRing R] (m n : R) : Fin 4 → R := ![2*m,4*m,n,3*n]
def fourBinaryW {R : Type*} [CommRing R] (m n : R) : Fin 4 → R := ![n,2*n,-m,-3*m]

def fourBinaryNum {R : Type*} [CommRing R] (m n : R) (r : Bool) (z : Fin 4 → R) : R :=
  if r then 3*n-4*m-2*fourDot (fourBinaryW m n) z
  else 3*m+2*n-30-fourDot (fourBinaryV m n) z

def fourBinaryRaw {R : Type*} [CommRing R] (m n : R) (r : Bool)
    (z : Fin 4 → R) (k : R) : Fin 4 → R :=
  if r then fun i => 5*z i-(![0,0,-3,1] i)*(fourDot ![0,0,-3,1] z+1)+fourBinaryW m n i*k
  else fun i => 5*z i-(![-2,1,0,0] i)*(2*fourDot ![-2,1,0,0] z+1)+fourBinaryV m n i*k

def fourBinaryRule {R : Type*} [CommRing R] (r : Bool) (z : Fin 4 → R) : Fin 4 → R :=
  if r then ![z 1,z 0,z 2,1-z 3] else ![1-z 1,1-z 0,1-z 2,z 3]
def fourBinaryBits (r : Bool) (b : Fin 4 → Bool) : Fin 4 → Bool :=
  if r then ![b 1,b 0,b 2,!b 3] else ![!b 1,!b 0,!b 2,b 3]

def fourEnergyFive {R : Type*} [CommRing R] (p : R) (v z : Fin 4 → R) : R :=
  p*fourDot z z-5*p*fourSum z+30*fourDot v z

lemma fourEnergyFive_scale (p : ℤ) (v z : QuadIntPoint) :
    fourEnergyFive p v (fun i => 5*z i)=25*fourEnergy p v z := by
  simp only [fourEnergyFive,fourEnergy,fourDot,fourSum]
  ring

lemma fourBinary_energy_raw (m n : ℤ) (r : Bool) (z : QuadIntPoint) (k : ℤ)
    (hk : (2*m^2+n^2)*k=fourBinaryNum m n r z) :
    fourEnergyFive (2*m^2+n^2) (fourBinaryV m n) (fourBinaryRaw m n r z k)=
      25*fourEnergy (2*m^2+n^2) (fourBinaryV m n) z := by
  cases r <;> dsimp [fourBinaryRaw,fourBinaryNum,fourBinaryV,fourBinaryW,
    fourEnergyFive,fourEnergy,fourDot,fourSum] at hk ⊢
  · linear_combination 10*(2*m^2+n^2)*k*hk
  · linear_combination 5*(2*m^2+n^2)*k*hk

lemma fourBinary_raw_involutive (m n : ℤ) (r : Bool) (z z' : QuadIntPoint) (k : ℤ)
    (hz : ∀ i, 5*z' i=fourBinaryRaw m n r z k i) :
    ∀ i, fourBinaryRaw m n r z' (-k) i=5*z i := by
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  have h3 := hz 3
  intro i
  cases r <;> fin_cases i <;>
    dsimp [fourBinaryRaw,fourBinaryV,fourBinaryW,fourDot] at h0 h1 h2 h3 ⊢ <;> nlinarith

lemma fourBinary_num_next (m n : ℤ) (r : Bool) (z z' : QuadIntPoint) (k : ℤ)
    (hk : (2*m^2+n^2)*k=fourBinaryNum m n r z)
    (hz : ∀ i, 5*z' i=fourBinaryRaw m n r z k i) :
    fourBinaryNum m n r z'=(2*m^2+n^2)*(-k) := by
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  have h3 := hz 3
  suffices hh : 5*fourBinaryNum m n r z'=5*((2*m^2+n^2)*(-k)) by omega
  cases r <;> dsimp [fourBinaryRaw,fourBinaryNum,fourBinaryV,fourBinaryW,fourDot]
    at hk h0 h1 h2 h3 ⊢
  · linear_combination -5*hk-2*m*h0-4*m*h1-n*h2-3*n*h3
  · linear_combination -5*hk-2*n*h0-4*n*h1+2*m*h2+6*m*h3

lemma fourBinary_mod_fifteen_identity (a b : ZMod 15) (r : Bool)
    (z : Fin 4 → ZMod 15) (k : ZMod 15) (i : Fin 4) :
    (2*(3*a)^2+(5*b)^2)*fourBinaryRaw (3*a) (5*b) r z k i=
      (2*(3*a)^2+(5*b)^2)*(5*fourBinaryRule r z i)+
      (if r then fourBinaryW (3*a) (5*b) i else fourBinaryV (3*a) (5*b) i)*
        ((2*(3*a)^2+(5*b)^2)*k-fourBinaryNum (3*a) (5*b) r z) := by
  cases r <;> fin_cases i <;>
    dsimp [fourBinaryRaw,fourBinaryRule,fourBinaryNum,fourBinaryV,fourBinaryW,fourDot] <;>
    ring_nf <;> reduce_mod_char <;> ring_nf <;> reduce_mod_char

lemma fourBinary_raw_mod_fifteen (m n : ZMod 15) (r : Bool)
    (hm : ∃ a, m=3*a) (hn : ∃ b, n=5*b) (hp : IsUnit (2*m^2+n^2))
    (z : Fin 4 → ZMod 15) (k : ZMod 15) (hk : (2*m^2+n^2)*k=fourBinaryNum m n r z)
    (i : Fin 4) : fourBinaryRaw m n r z k i=5*fourBinaryRule r z i := by
  obtain ⟨a,rfl⟩ := hm
  obtain ⟨b,rfl⟩ := hn
  apply hp.mul_left_cancel
  simpa only [hk,sub_self,mul_zero,add_zero] using
    fourBinary_mod_fifteen_identity a b r z k i

lemma fourBinary_bits_weight (r : Bool) (x : QuadQuintBranchIndex) (z : QuadIntPoint) :
    quadWeight (quadAssemble (fourBinaryBits r (quadBits x)) z) = -quadWeight x := by
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  cases r <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    norm_num [quadAssemble,fourBinaryBits,quadBits,quadWeight,pointBranchWeight,
      quadB4,pointB1,pointB2,pointB3,branchSign,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]

lemma fourBinary_rule_branch (r : Bool) (x : QuadQuintBranchIndex) (i : Fin 4) :
    (15 : ℤ) ∣ 5*fourBinaryRule r (quadZ x) i-5*(if fourBinaryBits r (quadBits x) i then 1 else 0) := by
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  cases r <;> fin_cases i <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    norm_num [fourBinaryRule,fourBinaryBits,quadBits,quadZ,branchZ,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] <;> omega

/-- The two residue criteria avoid division modulo the modulus. -/
def fourBinaryResidue {R : Type*} [CommRing R] (m n a : R) (r : Bool) : R :=
  if r then 3*m+2*n-a else 3*m+2*n-30-a

lemma fourBinary_num_zero {R : Type*} [CommRing R] (m n a : R) (r : Bool)
    (z : Fin 4 → R) (hm : IsUnit m) (hp : 2*m^2+n^2=0)
    (hz : fourDot (fourBinaryV m n) z=a) (ha : fourBinaryResidue m n a r=0) :
    fourBinaryNum m n r z=0 := by
  cases r <;> dsimp [fourBinaryNum,fourBinaryResidue,fourBinaryV,fourBinaryW,fourDot] at hz ha ⊢
  · linear_combination ha-hz
  · apply hm.mul_left_cancel
    linear_combination n*ha-n*hz+(z 2+3*z 3-2)*hp

lemma fourBinaryNum_cast (q : ℕ) (m n : ℤ) (r : Bool) (z : QuadIntPoint) :
    ((fourBinaryNum m n r z : ℤ) : ZMod q)=
      fourBinaryNum (m : ZMod q) (n : ZMod q) r (fun i => (z i : ZMod q)) := by
  cases r <;> dsimp [fourBinaryNum,fourBinaryV,fourBinaryW,fourDot] <;> push_cast <;> ring

lemma fourBinaryRaw_cast (q : ℕ) (m n : ℤ) (r : Bool) (z : QuadIntPoint) (k : ℤ) (i : Fin 4) :
    ((fourBinaryRaw m n r z k i : ℤ) : ZMod q)=
      fourBinaryRaw (m : ZMod q) (n : ZMod q) r (fun j => (z j : ZMod q)) (k : ZMod q) i := by
  cases r <;> fin_cases i <;> dsimp [fourBinaryRaw,fourBinaryV,fourBinaryW,fourDot] <;> push_cast <;> ring

lemma fourBinaryRule_cast (q : ℕ) (r : Bool) (z : QuadIntPoint) (i : Fin 4) :
    ((fourBinaryRule r z i : ℤ) : ZMod q)=fourBinaryRule r (fun j => (z j : ZMod q)) i := by
  cases r <;> fin_cases i <;> dsimp [fourBinaryRule] <;> push_cast <;> ring

lemma fourBinaryResidue_cast (q : ℕ) (m n a : ℤ) (r : Bool) :
    ((fourBinaryResidue m n a r : ℤ) : ZMod q)=
      fourBinaryResidue (m : ZMod q) (n : ZMod q) (a : ZMod q) r := by
  cases r <;> simp [fourBinaryResidue]

end Ramanujan.MultiQuintuple
