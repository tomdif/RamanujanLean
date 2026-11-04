import RamanujanTau.MultiQuintupleFourPlane

/-! Sixteen plane reflections from four short directions and four long directions. -/
namespace Ramanujan.MultiQuintuple
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

def fourShort {R : Type*} [CommRing R] (a : Fin 4) : Fin 4 → R :=
  match a.val with
  | 0 => ![1,1,-1,0]
  | 1 => ![0,-1,-1,1]
  | 2 => ![1,2,0,-1]
  | _ => ![1,0,-2,1]

def fourLong {R : Type*} [CommRing R] (m n : R) (b : Fin 4) : Fin 4 → R :=
  match b.val with
  | 0 => fourV m n
  | 1 => ![-m-n,m,-n,m-n]
  | 2 => ![2*m,n-m,m+n,2*n]
  | _ => ![-2*n,m+n,m-n,2*m]

def fourShortNum {R : Type*} [CommRing R] (a : Fin 4) (z : Fin 4 → R) : R :=
  match a.val with
  | 0 => 1-2*fourDot (fourShort a) z
  | 1 => -1-2*fourDot (fourShort a) z
  | 2 => 1-fourDot (fourShort a) z
  | _ => -fourDot (fourShort a) z

def fourLongNum {R : Type*} [CommRing R] (m n : R) (b : Fin 4) (z : Fin 4 → R) : R :=
  match b.val with
  | 0 => 3*m+n-18-2*fourDot (fourLong m n b) z
  | 1 => m-3*n-2*fourDot (fourLong m n b) z
  | 2 => m+2*n-9-fourDot (fourLong m n b) z
  | _ => 2*m-n-9-fourDot (fourLong m n b) z

def fourReflectionRaw {R : Type*} [CommRing R] (m n : R) (a b : Fin 4)
    (z : Fin 4 → R) (k : R) : Fin 4 → R :=
  fun i => 3*z i+fourShort a i*fourShortNum a z+fourLong m n b i*k

def fourReflectionBranch (a : Fin 4) : Fin 4 :=
  match a.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2

/-- The congruence needed by each pairing of short and long directions. -/
def fourReflectionCondition {R : Type*} [CommRing R] (m n : R) (a b : Fin 4) : R :=
  match a.val,b.val with
  | 0,0 | 1,1 | 2,2 | 3,3 => m+n
  | 0,1 | 1,0 | 2,3 | 3,2 => m-n
  | 0,2 | 1,3 | 2,1 | 3,0 => n
  | _,_ => m

def fourReflectionResidue {R : Type*} [CommRing R] (m n r : R) (b : Fin 4) : R :=
  match b.val with
  | 0 => 3*m+n-18-2*r
  | 1 => 2*r-3*m-n
  | 2 => n*(m+2*n-9)-(n-m)*r
  | _ => n*(2*m-n-9)-(m+n)*r

lemma fourReflection_energy_raw (m n : ℤ) (a b : Fin 4) (z : QuadIntPoint) (k : ℤ)
    (hk : (m^2+n^2)*k=fourLongNum m n b z) :
    fourEnergyTriple (m^2+n^2) (fourV m n) (fourReflectionRaw m n a b z k)=
      9*fourEnergy (m^2+n^2) (fourV m n) z := by
  fin_cases a <;> fin_cases b <;>
    dsimp [fourReflectionRaw,fourShortNum,fourLongNum,fourShort,fourLong,
      fourV,fourDot,fourSum,fourEnergyTriple,fourEnergy] at hk ⊢ <;>
    first | (linear_combination 3*(m^2+n^2)*k*hk) |
      (linear_combination 6*(m^2+n^2)*k*hk)

lemma fourReflection_raw_involutive (m n : ℤ) (a b : Fin 4) (z z' : QuadIntPoint) (k : ℤ)
    (hz : ∀ i, 3*z' i=fourReflectionRaw m n a b z k i) :
    ∀ i, fourReflectionRaw m n a b z' (-k) i=3*z i := by
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  have h3 := hz 3
  intro i
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    dsimp [fourReflectionRaw,fourShortNum,fourShort,fourLong,fourV,fourDot]
      at h0 h1 h2 h3 ⊢ <;> nlinarith

lemma fourReflection_num_next (m n : ℤ) (a b : Fin 4) (z z' : QuadIntPoint) (k : ℤ)
    (hk : (m^2+n^2)*k=fourLongNum m n b z)
    (hz : ∀ i, 3*z' i=fourReflectionRaw m n a b z k i) :
    fourLongNum m n b z'=(m^2+n^2)*(-k) := by
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  have h3 := hz 3
  suffices hh : 3*fourLongNum m n b z'=3*((m^2+n^2)*(-k)) by omega
  fin_cases a <;> fin_cases b <;>
    dsimp [fourReflectionRaw,fourLongNum,fourShortNum,fourShort,fourLong,fourV,fourDot]
      at hk h0 h1 h2 h3 ⊢
  all_goals first
    | (linear_combination -3*hk-2*(m-n)*h0-2*n*h1-2*m*h2-2*(m+n)*h3)
    | (linear_combination -3*hk+2*(m+n)*h0-2*m*h1+2*n*h2-2*(m-n)*h3)
    | (linear_combination -3*hk-2*m*h0-(n-m)*h1-(m+n)*h2-2*n*h3)
    | (linear_combination -3*hk+2*n*h0-(m+n)*h1-(m-n)*h2-2*m*h3)

lemma fourReflection_mod_nine_identity (m n : ZMod 9) (a b : Fin 4)
    (hs : fourReflectionCondition m n a b=0) (z : Fin 4 → ZMod 9) (k : ZMod 9) (i : Fin 4) :
    (m^2+n^2)*fourReflectionRaw m n a b z k i=
      (m^2+n^2)*(3*fourPlaneZRule (fourReflectionBranch a) z i)+
      fourLong m n b i*((m^2+n^2)*k-fourLongNum m n b z) := by
  fin_cases a <;> fin_cases b <;>
    dsimp [fourReflectionCondition] at hs
  all_goals first
    | (have hm : m=-n := by linear_combination hs
       rw [hm]
       fin_cases i <;>
         dsimp [fourReflectionRaw,fourShortNum,fourLongNum,fourShort,fourLong,
           fourReflectionBranch,fourPlaneZRule,fourV,fourDot] <;>
         ring_nf <;> reduce_mod_char)
    | (have hm : m=n := by linear_combination hs
       rw [hm]
       fin_cases i <;>
         dsimp [fourReflectionRaw,fourShortNum,fourLongNum,fourShort,fourLong,
           fourReflectionBranch,fourPlaneZRule,fourV,fourDot] <;>
         ring_nf <;> reduce_mod_char)
    | (have hm : m=0 := by linear_combination hs
       rw [hm]
       fin_cases i <;>
         dsimp [fourReflectionRaw,fourShortNum,fourLongNum,fourShort,fourLong,
           fourReflectionBranch,fourPlaneZRule,fourV,fourDot] <;>
         ring_nf <;> reduce_mod_char)
    | (have hn : n=0 := by linear_combination hs
       rw [hn]
       fin_cases i <;>
         dsimp [fourReflectionRaw,fourShortNum,fourLongNum,fourShort,fourLong,
           fourReflectionBranch,fourPlaneZRule,fourV,fourDot] <;>
         ring_nf <;> reduce_mod_char)

lemma fourReflection_raw_mod_nine (m n : ZMod 9) (a b : Fin 4)
    (hp : IsUnit (m^2+n^2)) (hs : fourReflectionCondition m n a b=0)
    (z : Fin 4 → ZMod 9) (k : ZMod 9) (hk : (m^2+n^2)*k=fourLongNum m n b z)
    (i : Fin 4) :
    fourReflectionRaw m n a b z k i=3*fourPlaneZRule (fourReflectionBranch a) z i := by
  apply hp.mul_left_cancel
  simpa only [hk,sub_self,mul_zero,add_zero] using
    fourReflection_mod_nine_identity m n a b hs z k i

lemma fourReflection_num_zero {R : Type*} [CommRing R] (m n r : R) (b : Fin 4)
    (z : Fin 4 → R) (hn : IsUnit n) (hp : m^2+n^2=0)
    (hz : fourDot (fourV m n) z=r) (hr : fourReflectionResidue m n r b=0) :
    fourLongNum m n b z=0 := by
  fin_cases b <;>
    dsimp [fourReflectionResidue,fourLongNum,fourLong,fourV,fourDot] at hz hr ⊢
  · linear_combination hr-2*hz
  · apply hn.mul_left_cancel
    linear_combination -m*hr-2*m*hz+(2*(z 0+z 2+z 3)-3)*hp
  · apply hn.mul_left_cancel
    linear_combination hr-(n-m)*hz-(z 0+z 2+z 3)*hp
  · apply hn.mul_left_cancel
    linear_combination hr-(m+n)*hz+(z 0+z 2+z 3)*hp


lemma fourLongNum_cast (q : ℕ) (m n : ℤ) (b : Fin 4) (z : QuadIntPoint) :
    ((fourLongNum m n b z : ℤ) : ZMod q)=
      fourLongNum (m : ZMod q) (n : ZMod q) b (fun i => (z i : ZMod q)) := by
  fin_cases b <;> dsimp [fourLongNum,fourLong,fourV,fourDot] <;> push_cast <;> ring

lemma fourReflectionRaw_cast (q : ℕ) (m n : ℤ) (a b : Fin 4)
    (z : QuadIntPoint) (k : ℤ) (i : Fin 4) :
    ((fourReflectionRaw m n a b z k i : ℤ) : ZMod q)=
      fourReflectionRaw (m : ZMod q) (n : ZMod q) a b
        (fun j => (z j : ZMod q)) (k : ZMod q) i := by
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    dsimp [fourReflectionRaw,fourShortNum,fourShort,fourLong,fourV,fourDot] <;> push_cast <;> ring

lemma fourReflectionCondition_cast (q : ℕ) (m n : ℤ) (a b : Fin 4) :
    ((fourReflectionCondition m n a b : ℤ) : ZMod q)=
      fourReflectionCondition (m : ZMod q) (n : ZMod q) a b := by
  fin_cases a <;> fin_cases b <;> simp [fourReflectionCondition]

lemma fourReflectionResidue_cast (q : ℕ) (m n r : ℤ) (b : Fin 4) :
    ((fourReflectionResidue m n r b : ℤ) : ZMod q)=
      fourReflectionResidue (m : ZMod q) (n : ZMod q) (r : ZMod q) b := by
  fin_cases b <;> simp [fourReflectionResidue]

end Ramanujan.MultiQuintuple
