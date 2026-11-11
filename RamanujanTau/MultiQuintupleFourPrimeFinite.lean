import RamanujanTau.MultiQuintupleFourPrimeGeneratorData

/-!
# Kernel checks of short generators and possible symmetries

The points below have perpendicular coordinate (1,0) or (0,1), long
coordinate norm at most 50, and nonzero quartic character. Their integer
coordinates generate the entire abstract rank-four lattice. Among the 36
pairs of involutive signed permutations, only four long-plane reflections
can reverse the character on these points. Availability is exactly the
modulo-nine condition already used by the forward theorem.

These finite statements do not assert the analytic coefficient converse.
-/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fourPrimeNumerator (m n : ℤ) (z : Fin 4 → ℤ) : Fin 4 → ℤ :=
  let p := m*m+n*n
  let x := m*z 0-n*z 1
  let y := n*z 0+m*z 1
  ![x-y+p*z 2,y+p*z 2-p*z 3,x-p*z 2-p*z 3,x+y+p*z 3]

def fourPrimeTrit (x : ℤ) : ℤ := if x%9=3 then 1 else if x%9=6 then -1 else 0

def fourPrimeCharacter (m n : ℤ) (z : Fin 4 → ℤ) : ℤ :=
  ∏ i, fourPrimeTrit (fourPrimeNumerator m n z i)

def fourPrimeBase (m n : ℤ) : Fin 2 → Fin 2 → ℤ :=
  ![![(m-n+1)%3-1,(-m-n+1)%3-1],![(m+n+1)%3-1,(m-n+1)%3-1]]

def fourPrimeCoordinates (m n : ℤ) (z : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![(z 0-z 2*fourPrimeBase m n 0 0-z 3*fourPrimeBase m n 1 0)/3,
    (z 1-z 2*fourPrimeBase m n 0 1-z 3*fourPrimeBase m n 1 1)/3,z 2,z 3]

/-- The four reflections, followed by the two scalar involutions. -/
def fourPrimePlaneInvolution (a : Fin 6) (x y : ℤ) : Fin 2 → ℤ :=
  ![![-x,y],![x,-y],![y,x],![-y,-x],![x,y],![-x,-y]] a

def fourPrimeImage (a b : Fin 6) (z : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![fourPrimePlaneInvolution a (z 0) (z 1) 0,
    fourPrimePlaneInvolution a (z 0) (z 1) 1,
    fourPrimePlaneInvolution b (z 2) (z 3) 0,
    fourPrimePlaneInvolution b (z 2) (z 3) 1]

def FourPrimeFiniteCompatible (m n : Fin 9) (a b : Fin 6) : Prop :=
  ∀ j : Fin 12,
    fourPrimeCharacter m.val n.val (fourPrimeImage a b ((fourPrimeGeneratorData m n).points j)) =
      -fourPrimeCharacter m.val n.val ((fourPrimeGeneratorData m n).points j)

instance (m n : Fin 9) (a b : Fin 6) : Decidable (FourPrimeFiniteCompatible m n a b) := by
  unfold FourPrimeFiniteCompatible
  infer_instance

/-- Explicit integer linear combinations recover all four coordinate vectors. -/
theorem fourPrime_generators_finite :
    ∀ m n : Fin 9, (m.val*m.val+n.val*n.val)%3 ≠ 0 →
      (∀ j : Fin 12, let z := (fourPrimeGeneratorData m n).points j
        (z 2=1 ∧ z 3=0 ∨ z 2=0 ∧ z 3=1) ∧
        z 0*z 0+z 1*z 1 ≤ 50 ∧
        fourPrimeCharacter m.val n.val z ≠ 0 ∧
        (z 0-z 2*fourPrimeBase m.val n.val 0 0-z 3*fourPrimeBase m.val n.val 1 0)%3=0 ∧
        (z 1-z 2*fourPrimeBase m.val n.val 0 1-z 3*fourPrimeBase m.val n.val 1 1)%3=0) ∧
      (∀ i k : Fin 4, ∑ j : Fin 12,
        (fourPrimeGeneratorData m n).inverse i j *
          fourPrimeCoordinates m.val n.val ((fourPrimeGeneratorData m n).points j) k =
            if i=k then 1 else 0) := by
  decide +kernel

/-- All character-reversing possibilities have a nonscalar long-plane reflection. -/
theorem fourPrime_symmetry_finite :
    ∀ m n : Fin 9, (m.val*m.val+n.val*n.val)%3 ≠ 0 →
      (∀ a b : Fin 6, FourPrimeFiniteCompatible m n a b → a.val < 4) ∧
      ((∃ a b : Fin 6, FourPrimeFiniteCompatible m n a b) ↔
        m.val=0 ∨ n.val=0 ∨ m=n ∨ (m.val+n.val)%9=0) := by
  decide +kernel

end Ramanujan.MultiQuintuple
