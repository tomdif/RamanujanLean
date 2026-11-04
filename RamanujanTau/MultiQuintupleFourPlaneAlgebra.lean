import RamanujanTau.MultiQuintupleFourPlaneCoordinates
import Mathlib.Tactic.ReduceModChar

/-! Four short plane reflections, uniform in two integer parameters. -/
namespace Ramanujan.MultiQuintuple
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def fourV {R : Type*} [CommRing R] (m n : R) : Fin 4 → R := ![m-n,n,m,m+n]

def fourPlaneNum {R : Type*} [CommRing R] (m n : R) (r : Fin 4) (z : Fin 4 → R) : R :=
  match r.val with
  | 0 => 3*m+n-18-2*fourDot (fourV m n) z
  | 1 => m+2*n-9-fourDot ![2*m,n-m,m+n,2*n] z
  | 2 => 2*m-n-9-fourDot ![-2*n,m+n,m-n,2*m] z
  | _ => 2*fourDot (fourV m n) z-3*m-n

def fourPlaneRaw {R : Type*} [CommRing R] (m n : R) (r : Fin 4)
    (z : Fin 4 → R) (k : R) : Fin 4 → R :=
  match r.val with
  | 0 => fun i => 3*z i+(![1,1,-1,0] i)*(1-2*(z 0+z 1-z 2))+fourV m n i*k
  | 1 => fun i => 3*z i+(![1,2,0,-1] i)*(1-(z 0+2*z 1-z 3))+
      (![2*m,n-m,m+n,2*n] i)*k
  | 2 => fun i => 3*z i-(![1,0,-2,1] i)*(z 0-2*z 2+z 3)+
      (![-2*n,m+n,m-n,2*m] i)*k
  | _ => fun i => 3*(1-z i)+(![1,1,-1,0] i)*(2*(z 0+z 1-z 2)-1)+fourV m n i*k

def fourPlaneBits (r : Fin 4) (b : Fin 4 → Bool) : Fin 4 → Bool :=
  match r.val with
  | 0 => ![!b 0,b 2,b 1,b 3]
  | 1 => ![b 3,!b 1,b 2,b 0]
  | 2 => ![!b 3,b 1,!b 2,!b 0]
  | _ => ![b 0,!b 2,!b 1,!b 3]

def fourPlaneZRule {R : Type*} [CommRing R] (r : Fin 4) (z : Fin 4 → R) : Fin 4 → R :=
  match r.val with
  | 0 => ![1-z 0,z 2,z 1,z 3]
  | 1 => ![z 3,1-z 1,z 2,z 0]
  | 2 => ![1-z 3,z 1,1-z 2,1-z 0]
  | _ => ![z 0,1-z 2,1-z 1,1-z 3]

def fourPlaneNextK {R : Type*} [CommRing R] (r : Fin 4) (k : R) : R :=
  if r.val=3 then k else -k

lemma fourPlane_energy_raw (m n : ℤ) (r : Fin 4) (z : QuadIntPoint) (k : ℤ)
    (hk : (m^2+n^2)*k=fourPlaneNum m n r z) :
    fourEnergyTriple (m^2+n^2) (fourV m n) (fourPlaneRaw m n r z k)=
      9*fourEnergy (m^2+n^2) (fourV m n) z := by
  fin_cases r <;>
    norm_num [fourPlaneRaw,fourPlaneNum,fourV,fourDot,fourSum,fourEnergyTriple,fourEnergy,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at hk ⊢
  · linear_combination 3*(m^2+n^2)*k*hk
  · linear_combination 6*(m^2+n^2)*k*hk
  · linear_combination 6*(m^2+n^2)*k*hk
  · linear_combination (3*(m^2+n^2)*k+54)*hk

lemma fourPlane_raw_involutive (m n : ℤ) (r : Fin 4) (z z' : QuadIntPoint) (k : ℤ)
    (hz : ∀ i, 3*z' i=fourPlaneRaw m n r z k i) :
    ∀ i, fourPlaneRaw m n r z' (fourPlaneNextK r k) i=3*z i := by
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  have h3 := hz 3
  intro i
  fin_cases r <;> fin_cases i <;>
    dsimp [fourPlaneRaw,fourPlaneNextK,fourV] at h0 h1 h2 h3 ⊢ <;> nlinarith

lemma fourPlane_num_next (m n : ℤ) (r : Fin 4) (z z' : QuadIntPoint) (k : ℤ)
    (hk : (m^2+n^2)*k=fourPlaneNum m n r z)
    (hz : ∀ i, 3*z' i=fourPlaneRaw m n r z k i) :
    fourPlaneNum m n r z'=(m^2+n^2)*fourPlaneNextK r k := by
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  have h3 := hz 3
  suffices hh : 3*fourPlaneNum m n r z'=3*((m^2+n^2)*fourPlaneNextK r k) by omega
  fin_cases r <;>
    dsimp [fourPlaneRaw,fourPlaneNum,fourPlaneNextK,fourV,fourDot] at hk h0 h1 h2 h3 ⊢
  · linear_combination (-3*hk-2*(m-n)*h0-2*n*h1-2*m*h2-2*(m+n)*h3)
  · linear_combination (-3*hk-2*m*h0-(n-m)*h1-(m+n)*h2-2*n*h3)
  · linear_combination (-3*hk+2*n*h0-(m+n)*h1-(m-n)*h2-2*m*h3)
  · linear_combination (3*hk+2*(m-n)*h0+2*n*h1+2*m*h2+2*(m+n)*h3)

/-- The congruence modulo nine makes all four maps respect the signed Watson branches. -/
lemma fourPlane_raw_mod_nine (m n : ZMod 9) (hn : IsUnit n) (hs : m+n=0)
    (r : Fin 4) (z : Fin 4 → ZMod 9) (k : ZMod 9)
    (hk : (m^2+n^2)*k=fourPlaneNum m n r z) (i : Fin 4) :
    fourPlaneRaw m n r z k i=3*fourPlaneZRule r z i := by
  have hm : m=-n := by linear_combination hs
  have htwo : IsUnit (2 : ZMod 9) := (ZMod.isUnit_iff_coprime 2 9).mpr (by decide)
  rw [hm] at hk ⊢
  apply (htwo.mul hn).mul_left_cancel
  fin_cases r <;> fin_cases i <;>
    dsimp [fourPlaneRaw,fourPlaneZRule,fourPlaneNum,fourV,fourDot] at hk ⊢ <;>
    first | (linear_combination (norm := (ring_nf <;> reduce_mod_char <;> ring)) -2*hk; done) |
      (linear_combination (norm := (ring_nf <;> reduce_mod_char <;> ring)) -hk; done) |
      (linear_combination (norm := (ring_nf <;> reduce_mod_char <;> ring)) hk; done) |
      (linear_combination (norm := (ring_nf <;> reduce_mod_char <;> ring)) 2*hk; done) | ring

lemma fourPlane_bits_weight (r : Fin 4) (x : QuadQuintBranchIndex) (z : QuadIntPoint) :
    quadWeight (quadAssemble (fourPlaneBits r (quadBits x)) z) = -quadWeight x := by
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  fin_cases r <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    norm_num [quadAssemble,fourPlaneBits,quadBits,quadWeight,pointBranchWeight,
      quadB4,pointB1,pointB2,pointB3,branchSign,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]

lemma fourPlane_rule_branch (r : Fin 4) (x : QuadQuintBranchIndex) (i : Fin 4) :
    (9 : ℤ) ∣ 3*fourPlaneZRule r (quadZ x) i-
      3*(if fourPlaneBits r (quadBits x) i then 1 else 0) := by
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  fin_cases r <;> fin_cases i <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    norm_num [fourPlaneZRule,fourPlaneBits,quadBits,quadZ,branchZ,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] <;> omega


/-- A residue polynomial avoiding division modulo the modulus. -/
def fourPlaneResidueNum {R : Type*} [CommRing R] (m n a : R) (r : Fin 4) : R :=
  match r.val with
  | 0 => 3*m+n-18-2*a
  | 1 => n*(m+2*n-9)-(n-m)*a
  | 2 => n*(2*m-n-9)-(m+n)*a
  | _ => 2*a-3*m-n

lemma fourPlane_num_zero {R : Type*} [CommRing R] (m n a : R) (r : Fin 4)
    (z : Fin 4 → R) (hn : IsUnit n) (hp : m^2+n^2=0)
    (hz : fourDot (fourV m n) z=a) (ha : fourPlaneResidueNum m n a r=0) :
    fourPlaneNum m n r z=0 := by
  fin_cases r <;>
    simp only [fourPlaneNum,fourPlaneResidueNum,fourV,fourDot,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.head_cons,Matrix.tail_cons] at hz ha ⊢
  · linear_combination ha-2*hz
  · apply hn.mul_left_cancel
    linear_combination ha-(n-m)*hz-(z 0+z 2+z 3)*hp
  · apply hn.mul_left_cancel
    linear_combination ha-(m+n)*hz+(z 0+z 2+z 3)*hp
  · linear_combination ha+2*hz

lemma fourPlaneNum_cast (q : ℕ) (m n : ℤ) (r : Fin 4) (z : QuadIntPoint) :
    ((fourPlaneNum m n r z : ℤ) : ZMod q)=
      fourPlaneNum (m : ZMod q) (n : ZMod q) r (fun i => (z i : ZMod q)) := by
  fin_cases r <;> simp [fourPlaneNum,fourV,fourDot,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]

lemma fourPlaneRaw_cast (q : ℕ) (m n : ℤ) (r : Fin 4) (z : QuadIntPoint) (k : ℤ)
    (i : Fin 4) :
    ((fourPlaneRaw m n r z k i : ℤ) : ZMod q)=
      fourPlaneRaw (m : ZMod q) (n : ZMod q) r (fun j => (z j : ZMod q)) (k : ZMod q) i := by
  fin_cases r <;> fin_cases i <;> simp [fourPlaneRaw,fourV,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]

lemma fourPlaneZRule_cast (q : ℕ) (r : Fin 4) (z : QuadIntPoint) (i : Fin 4) :
    ((fourPlaneZRule r z i : ℤ) : ZMod q)=fourPlaneZRule r (fun j => (z j : ZMod q)) i := by
  fin_cases r <;> fin_cases i <;> simp [fourPlaneZRule,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]

lemma fourPlaneResidueNum_cast (q : ℕ) (m n a : ℤ) (r : Fin 4) :
    ((fourPlaneResidueNum m n a r : ℤ) : ZMod q)=
      fourPlaneResidueNum (m : ZMod q) (n : ZMod q) (a : ZMod q) r := by
  fin_cases r <;> simp [fourPlaneResidueNum]

end Ramanujan.MultiQuintuple
