import RamanujanTau.MultiQuintupleFourCancellation

/-! Exact plane-flipping cancellation of all four reported progressions at 41. -/
namespace Ramanujan.MultiQuintuple
open PowerSeries
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def quadResidue (i j k l : ℕ) (x : QuadQuintBranchIndex) : ℤ :=
  i*(3*quadN1 x + if quadB1 x then 1 else 0) +
  j*(3*quadN2 x + if quadB2 x then 1 else 0) +
  k*(3*quadN3 x + if quadB3 x then 1 else 0) +
  l*(3*quadN4 x + if quadB4 x then 1 else 0)

lemma quadExp2_residue (p i j k l : ℕ) (x : QuadQuintBranchIndex) :
    ∃ u : ℤ, quadExp2 p i j k l x = 2*quadResidue i j k l x + p*u := by
  refine ⟨quadN1 x*(3*quadN1 x + if quadB1 x then 1 else -1) +
    quadN2 x*(3*quadN2 x + if quadB2 x then 1 else -1) +
    quadN3 x*(3*quadN3 x + if quadB3 x then 1 else -1) +
    quadN4 x*(3*quadN4 x + if quadB4 x then 1 else -1), ?_⟩
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    simp [quadExp2, quadResidue, quadB1,quadB2,quadB3,quadB4,quadN1,quadN2,quadN3,quadN4,
      pointTripleExp2, pointB1,pointB2,pointB3,pointN1,pointN2,pointN3,
      tripleQuintExp2,quintExp2,quintExpA2,quintExpB2] <;> ring

def four41Residue (r : Fin 4) : ℕ :=
  match r.val with
  | 0 => 21
  | 1 => 25
  | 2 => 26
  | _ => 30

def four41BitSum (b1 b2 b3 b4 : Bool) : ℤ :=
  (if b1 then 1 else 0) + 4*(if b2 then 1 else 0) +
    5*(if b3 then 1 else 0) + 9*(if b4 then 1 else 0)

def four41C0 (r : Fin 4) (b1 b2 b3 b4 : Bool) : ℤ :=
  (38*((four41Residue r : ℤ)-four41BitSum b1 b2 b3 b4)) % 41

def four41Q0 (r : Fin 4) (b1 b2 b3 b4 : Bool) : ℤ :=
  (four41BitSum b1 b2 b3 b4 + 27*four41C0 r b1 b2 b3 b4-four41Residue r)/41

lemma four41_branch_constant (r : Fin 4) (b1 b2 b3 b4 : Bool) :
    four41BitSum b1 b2 b3 b4 + 27*four41C0 r b1 b2 b3 b4 =
      four41Residue r + 41*four41Q0 r b1 b2 b3 b4 := by
  fin_cases r <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    norm_num [four41BitSum,four41C0,four41Q0,four41Residue]

def four41FiberZ (r : Fin 4) (x : QuadQuintBranchIndex) : ℤ :=
  (quadN4 x - 9*quadN1 x - 36*quadN2 x - 4*quadN3 x -
    four41C0 r (quadB1 x) (quadB2 x) (quadB3 x) (quadB4 x))/41

def four41FiberPoint (r : Fin 4) (b1 b2 b3 b4 : Bool) (n1 n2 n3 z : ℤ) :
    QuadQuintBranchIndex :=
  ((((b1,n1),(b2,n2)),(b3,n3)),
    (b4,9*n1+36*n2+4*n3+four41C0 r b1 b2 b3 b4+41*z))

lemma four41_fiber_representation (r : Fin 4) (x : QuadQuintBranchIndex) (q : ℤ)
    (hres : quadResidue 1 4 5 9 x = four41Residue r + 41*q) :
    x = four41FiberPoint r (quadB1 x) (quadB2 x) (quadB3 x) (quadB4 x)
      (quadN1 x) (quadN2 x) (quadN3 x) (four41FiberZ r x) := by
  let d := quadN4 x-9*quadN1 x-36*quadN2 x-4*quadN3 x-
    four41C0 r (quadB1 x) (quadB2 x) (quadB3 x) (quadB4 x)
  let a := q-four41Q0 r (quadB1 x) (quadB2 x) (quadB3 x) (quadB4 x)-
    6*quadN1 x-24*quadN2 x-3*quadN3 x
  have he : 27*d=41*a := by
    have hc := four41_branch_constant r (quadB1 x) (quadB2 x) (quadB3 x) (quadB4 x)
    dsimp [quadResidue] at hres
    dsimp [four41BitSum] at hc
    dsimp [d,a]
    linear_combination hres-hc
  have hd : (41 : ℤ) ∣ d := by
    refine ⟨38*a-25*d,?_⟩
    linear_combination 38*he
  obtain ⟨z,hz⟩ := hd
  have hq : four41FiberZ r x=z := by
    change d/41=z
    rw [hz]; norm_num
  have hlast : quadN4 x=9*quadN1 x+36*quadN2 x+4*quadN3 x+
      four41C0 r (quadB1 x) (quadB2 x) (quadB3 x) (quadB4 x)+41*four41FiberZ r x := by
    rw [hq]; dsimp [d] at hz; linarith
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  simpa [four41FiberPoint,quadB1,quadB2,quadB3,quadB4,quadN1,quadN2,quadN3,quadN4,
    pointB1,pointB2,pointB3,pointN1,pointN2,pointN3] using hlast

@[simp] lemma four41FiberZ_fiberPoint (r : Fin 4) (b1 b2 b3 b4 : Bool) (n1 n2 n3 z : ℤ) :
    four41FiberZ r (four41FiberPoint r b1 b2 b3 b4 n1 n2 n3 z)=z := by
  simp only [four41FiberZ,four41FiberPoint,quadB1,quadB2,quadB3,quadB4,
    quadN1,quadN2,quadN3,quadN4,pointB1,pointB2,pointB3,pointN1,pointN2,pointN3]
  ring_nf
  simp

def four41PartnerFiber0 (b1 b2 b3 b4 : Bool) (n1 n2 n3 z : ℤ) : QuadQuintBranchIndex :=
  match b1,b2,b3,b4 with
  | false, false, false, false => four41FiberPoint 0 true false false false (-3 + (-1)*n1 + (-6)*n2 + (-6)*z) (-11 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-14 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (11 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)
  | false, false, false, true => four41FiberPoint 0 true false false true (-1 + (-1)*n1 + (-6)*n2 + (-6)*z) (-3 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-4 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (3 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)
  | false, false, true, false => four41FiberPoint 0 true true false false (-5 + (-1)*n1 + (-6)*n2 + (-6)*z) (-20 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-25 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (20 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)
  | false, false, true, true => four41FiberPoint 0 true true false true (-3 + (-1)*n1 + (-6)*n2 + (-6)*z) (-12 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-15 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (12 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)
  | false, true, false, false => four41FiberPoint 0 true false true false (-5 + (-1)*n1 + (-6)*n2 + (-6)*z) (-18 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-23 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (18 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)
  | false, true, false, true => four41FiberPoint 0 true false true true (-3 + (-1)*n1 + (-6)*n2 + (-6)*z) (-10 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-13 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (10 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)
  | false, true, true, false => four41FiberPoint 0 true true true false (-1 + (-1)*n1 + (-6)*n2 + (-6)*z) (-3 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-4 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (3 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)
  | false, true, true, true => four41FiberPoint 0 true true true true (-5 + (-1)*n1 + (-6)*n2 + (-6)*z) (-19 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-24 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (19 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)
  | true, false, false, false => four41FiberPoint 0 false false false false (-3 + (-1)*n1 + (-6)*n2 + (-6)*z) (-13 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-16 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (13 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)
  | true, false, false, true => four41FiberPoint 0 false false false true (-1 + (-1)*n1 + (-6)*n2 + (-6)*z) (-5 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-6 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (5 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)
  | true, false, true, false => four41FiberPoint 0 false true false false (-5 + (-1)*n1 + (-6)*n2 + (-6)*z) (-22 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-27 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (22 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)
  | true, false, true, true => four41FiberPoint 0 false true false true (-3 + (-1)*n1 + (-6)*n2 + (-6)*z) (-14 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-17 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (14 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)
  | true, true, false, false => four41FiberPoint 0 false false true false (-5 + (-1)*n1 + (-6)*n2 + (-6)*z) (-20 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-25 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (20 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)
  | true, true, false, true => four41FiberPoint 0 false false true true (-3 + (-1)*n1 + (-6)*n2 + (-6)*z) (-12 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-15 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (12 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)
  | true, true, true, false => four41FiberPoint 0 false true true false (-1 + (-1)*n1 + (-6)*n2 + (-6)*z) (-5 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-6 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (5 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)
  | true, true, true, true => four41FiberPoint 0 false true true true (-5 + (-1)*n1 + (-6)*n2 + (-6)*z) (-21 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-26 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (21 + (6)*n1 + (22)*n2 + (2)*n3 + (25)*z)

def four41PartnerFiber1 (b1 b2 b3 b4 : Bool) (n1 n2 n3 z : ℤ) : QuadQuintBranchIndex :=
  match b1,b2,b3,b4 with
  | false, false, false, false => four41FiberPoint 1 false true false false (-2 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (5 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-4 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-4 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)
  | false, false, false, true => four41FiberPoint 1 true true false false (-11 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (25 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-20 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-18 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)
  | false, false, true, false => four41FiberPoint 1 false true true false (-7 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (16 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-13 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-12 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)
  | false, false, true, true => four41FiberPoint 1 true true true false (-3 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (6 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-5 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-5 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)
  | false, true, false, false => four41FiberPoint 1 false false false false (-6 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (14 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-11 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-10 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)
  | false, true, false, true => four41FiberPoint 1 true false false false (-2 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (4 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-3 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-3 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)
  | false, true, true, false => four41FiberPoint 1 false false true false (-11 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (25 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-20 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-18 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)
  | false, true, true, true => four41FiberPoint 1 true false true false (-7 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (15 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-12 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-11 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)
  | true, false, false, false => four41FiberPoint 1 false true false true (-3 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (7 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-6 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-5 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)
  | true, false, false, true => four41FiberPoint 1 true true false true (-12 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (27 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-22 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-19 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)
  | true, false, true, false => four41FiberPoint 1 false true true true (-8 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (18 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-15 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-13 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)
  | true, false, true, true => four41FiberPoint 1 true true true true (-4 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (8 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-7 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-6 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)
  | true, true, false, false => four41FiberPoint 1 false false false true (-7 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (16 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-13 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-12 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)
  | true, true, false, true => four41FiberPoint 1 true false false true (-3 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (6 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-5 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-5 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)
  | true, true, true, false => four41FiberPoint 1 false false true true (-12 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (27 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-22 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-19 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)
  | true, true, true, true => four41FiberPoint 1 true false true true (-8 + (-3)*n1 + (-12)*n2 + (-2)*n3 + (-13)*z) (17 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-14 + (-6)*n1 + (-21)*n2 + (-2)*n3 + (-24)*z) (-12 + (-4)*n1 + (-18)*n2 + (-2)*n3 + (-21)*z)

def four41PartnerFiber2 (b1 b2 b3 b4 : Bool) (n1 n2 n3 z : ℤ) : QuadQuintBranchIndex :=
  match b1,b2,b3,b4 with
  | false, false, false, false => four41FiberPoint 2 true false true true (1 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-3 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (2 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (2 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)
  | false, false, false, true => four41FiberPoint 2 false false true true (10 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-23 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (18 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (16 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)
  | false, false, true, false => four41FiberPoint 2 true false false true (6 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-14 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (11 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (9 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)
  | false, false, true, true => four41FiberPoint 2 false false false true (2 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-4 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (3 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (2 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)
  | false, true, false, false => four41FiberPoint 2 true true true true (5 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-12 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (9 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (8 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)
  | false, true, false, true => four41FiberPoint 2 false true true true (1 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-2 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (1 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (1 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)
  | false, true, true, false => four41FiberPoint 2 true true false true (10 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-23 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (18 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (16 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)
  | false, true, true, true => four41FiberPoint 2 false true false true (6 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-13 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (10 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (9 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)
  | true, false, false, false => four41FiberPoint 2 true false true false (2 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-5 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (4 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (3 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)
  | true, false, false, true => four41FiberPoint 2 false false true false (11 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-25 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (20 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (17 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)
  | true, false, true, false => four41FiberPoint 2 true false false false (7 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-16 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (13 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (11 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)
  | true, false, true, true => four41FiberPoint 2 false false false false (3 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-6 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (5 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (4 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)
  | true, true, false, false => four41FiberPoint 2 true true true false (6 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-14 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (11 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (9 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)
  | true, true, false, true => four41FiberPoint 2 false true true false (2 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-4 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (3 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (2 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)
  | true, true, true, false => four41FiberPoint 2 true true false false (11 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-25 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (20 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (17 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)
  | true, true, true, true => four41FiberPoint 2 false true false false (7 + (3)*n1 + (12)*n2 + (2)*n3 + (13)*z) (-15 + (-6)*n1 + (-26)*n2 + (-3)*n3 + (-30)*z) (12 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (10 + (4)*n1 + (18)*n2 + (2)*n3 + (21)*z)

def four41PartnerFiber3 (b1 b2 b3 b4 : Bool) (n1 n2 n3 z : ℤ) : QuadQuintBranchIndex :=
  match b1,b2,b3,b4 with
  | false, false, false, false => four41FiberPoint 3 false true true true (5 + (1)*n1 + (6)*n2 + (6)*z) (19 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (24 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-20 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)
  | false, false, false, true => four41FiberPoint 3 false true true false (3 + (1)*n1 + (6)*n2 + (6)*z) (11 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (14 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-12 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)
  | false, false, true, false => four41FiberPoint 3 false false true true (1 + (1)*n1 + (6)*n2 + (6)*z) (4 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (5 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-5 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)
  | false, false, true, true => four41FiberPoint 3 false false true false (5 + (1)*n1 + (6)*n2 + (6)*z) (20 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (25 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-21 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)
  | false, true, false, false => four41FiberPoint 3 false true false true (1 + (1)*n1 + (6)*n2 + (6)*z) (2 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (3 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-3 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)
  | false, true, false, true => four41FiberPoint 3 false true false false (5 + (1)*n1 + (6)*n2 + (6)*z) (18 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (23 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-19 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)
  | false, true, true, false => four41FiberPoint 3 false false false true (3 + (1)*n1 + (6)*n2 + (6)*z) (11 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (14 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-12 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)
  | false, true, true, true => four41FiberPoint 3 false false false false (1 + (1)*n1 + (6)*n2 + (6)*z) (3 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (4 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-4 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)
  | true, false, false, false => four41FiberPoint 3 true true true true (5 + (1)*n1 + (6)*n2 + (6)*z) (21 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (26 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-22 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)
  | true, false, false, true => four41FiberPoint 3 true true true false (3 + (1)*n1 + (6)*n2 + (6)*z) (13 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (16 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-14 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)
  | true, false, true, false => four41FiberPoint 3 true false true true (1 + (1)*n1 + (6)*n2 + (6)*z) (6 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (7 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-7 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)
  | true, false, true, true => four41FiberPoint 3 true false true false (5 + (1)*n1 + (6)*n2 + (6)*z) (22 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (27 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-23 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)
  | true, true, false, false => four41FiberPoint 3 true true false true (1 + (1)*n1 + (6)*n2 + (6)*z) (4 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (5 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-5 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)
  | true, true, false, true => four41FiberPoint 3 true true false false (5 + (1)*n1 + (6)*n2 + (6)*z) (20 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (25 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-21 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)
  | true, true, true, false => four41FiberPoint 3 true false false true (3 + (1)*n1 + (6)*n2 + (6)*z) (13 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (16 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-14 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)
  | true, true, true, true => four41FiberPoint 3 true false false false (1 + (1)*n1 + (6)*n2 + (6)*z) (5 + (6)*n1 + (21)*n2 + (2)*n3 + (24)*z) (6 + (6)*n1 + (26)*n2 + (3)*n3 + (30)*z) (-6 + (-6)*n1 + (-22)*n2 + (-2)*n3 + (-25)*z)

def four41PartnerFiber (r : Fin 4) (b1 b2 b3 b4 : Bool) (n1 n2 n3 z : ℤ) : QuadQuintBranchIndex :=
  match r.val with
  | 0 => four41PartnerFiber0 b1 b2 b3 b4 n1 n2 n3 z
  | 1 => four41PartnerFiber1 b1 b2 b3 b4 n1 n2 n3 z
  | 2 => four41PartnerFiber2 b1 b2 b3 b4 n1 n2 n3 z
  | _ => four41PartnerFiber3 b1 b2 b3 b4 n1 n2 n3 z

def four41Partner (r : Fin 4) (x : QuadQuintBranchIndex) : QuadQuintBranchIndex :=
  four41PartnerFiber r (quadB1 x) (quadB2 x) (quadB3 x) (quadB4 x)
    (quadN1 x) (quadN2 x) (quadN3 x) (four41FiberZ r x)

@[simp] lemma four41Partner_fiberPoint (r : Fin 4) (b1 b2 b3 b4 : Bool) (n1 n2 n3 z : ℤ) :
    four41Partner r (four41FiberPoint r b1 b2 b3 b4 n1 n2 n3 z) =
    four41PartnerFiber r b1 b2 b3 b4 n1 n2 n3 z := by
  unfold four41Partner
  rw [four41FiberZ_fiberPoint]
  rfl

lemma four41Partner_weight (r : Fin 4) (x : QuadQuintBranchIndex) :
    quadWeight (four41Partner r x) = -quadWeight x := by
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  fin_cases r <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    norm_num [four41Partner,four41PartnerFiber,four41PartnerFiber0,four41PartnerFiber1,
      four41PartnerFiber2,four41PartnerFiber3,four41FiberPoint,
      quadWeight,pointBranchWeight,branchSign,quadB1,quadB2,quadB3,quadB4,
      pointB1,pointB2,pointB3]

lemma four41Partner_exponent (r : Fin 4) (b1 b2 b3 b4 : Bool) (n1 n2 n3 z : ℤ) :
    quadExp2 41 1 4 5 9 (four41Partner r (four41FiberPoint r b1 b2 b3 b4 n1 n2 n3 z)) =
    quadExp2 41 1 4 5 9 (four41FiberPoint r b1 b2 b3 b4 n1 n2 n3 z) := by
  rw [four41Partner_fiberPoint]
  fin_cases r <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    norm_num [four41PartnerFiber,four41PartnerFiber0,four41PartnerFiber1,
      four41PartnerFiber2,four41PartnerFiber3,four41FiberPoint,four41C0,four41BitSum,
      four41Residue,quadExp2,pointTripleExp2,tripleQuintExp2,quintExp2,quintExpA2,quintExpB2,
      quadB4,quadN4,pointB1,pointB2,pointB3,pointN1,pointN2,pointN3] <;> ring

lemma four41Partner_involutive (r : Fin 4) (b1 b2 b3 b4 : Bool) (n1 n2 n3 z : ℤ) :
    four41Partner r (four41Partner r (four41FiberPoint r b1 b2 b3 b4 n1 n2 n3 z)) =
    four41FiberPoint r b1 b2 b3 b4 n1 n2 n3 z := by
  fin_cases r <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    simp [four41PartnerFiber,four41PartnerFiber0,four41PartnerFiber1,
      four41PartnerFiber2,four41PartnerFiber3] <;>
    simp [four41FiberPoint] <;> ring_nf <;> try simp

lemma four41_target_has_residue (r : Fin 4) (N : ℕ) (x : QuadQuintBranchIndex)
    (hexp : quadExp2 41 1 4 5 9 x=2*((41*N+four41Residue r : ℕ):ℤ)) :
    ∃ q : ℤ, quadResidue 1 4 5 9 x = four41Residue r+41*q := by
  obtain ⟨u,hu⟩ := quadExp2_residue 41 1 4 5 9 x
  have hueven : Even u := by
    have hc := congrArg (fun z : ℤ => (z : ZMod 2)) (hexp.symm.trans hu)
    have htwo : (2 : ZMod 2) = 0 := by decide
    have h41 : (41 : ZMod 2) = 1 := by decide
    have hz : (u : ZMod 2)=0 := by
      push_cast at hc
      simpa only [htwo,h41,zero_mul,zero_add,one_mul] using hc.symm
    exact even_iff_two_dvd.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd u 2).mp hz)
  obtain ⟨w,hw⟩ := hueven
  refine ⟨(N : ℤ)-w,?_⟩
  rw [hw] at hu
  norm_num only [Nat.cast_ofNat] at hu
  push_cast at hexp
  nlinarith

/-- All four progressions reported for the actual four-factor product at 41 vanish forever. -/
theorem coeff_four_quintuple_p41_zero (r : Fin 4) (N : ℕ) :
    coeff (41*N+four41Residue r) (quintupleSpecialized 41 1 * quintupleSpecialized 41 4 *
      quintupleSpecialized 41 5 * quintupleSpecialized 41 9)=0 := by
  apply coeff_quad_eq_zero_of_expInvolution 41 1 4 5 9 (41*N+four41Residue r) (four41Partner r)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro x _; exact four41Partner_weight r x
  · intro x hx
    obtain ⟨q,hq⟩ := four41_target_has_residue r N x hx
    rw [four41_fiber_representation r x q hq]
    exact four41Partner_exponent _ _ _ _ _ _ _ _ _
  · intro x hx
    obtain ⟨q,hq⟩ := four41_target_has_residue r N x hx
    rw [four41_fiber_representation r x q hq]
    exact four41Partner_involutive _ _ _ _ _ _ _ _ _

end Ramanujan.MultiQuintuple
