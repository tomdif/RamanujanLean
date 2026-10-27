/-
# Exact arithmetic in `span{J_ν}` and in `span{J}[Y]` modulo the modular equation

An element of `span{J_ν}` is stored as five dense `Int[z]`-coefficient lists, one for each of the
residues `1, g₂, g₃, g₄, g₆` (`J_{5b+r} = z^b g_r`). Products use Atkin's multiplication table `gtab`.
Polynomials in `Y` (low degree first) have such coefficients. `redP` reduces modulo the modular
equation `Y¹¹ = Σ_j (−1)^j e_{j+1} Y^{10−j}`. All functions are structurally recursive, so the
kernel evaluates them under `decide +kernel`.
-/

set_option autoImplicit false

namespace Atkin11Seed

/-! ### `Int[z]` -/

def addZ : List Int → List Int → List Int
  | [], g => g
  | f, [] => f
  | a :: f, b :: g => (a + b) :: addZ f g

def smulZ (c : Int) (f : List Int) : List Int := f.map (c * ·)

def mulZ : List Int → List Int → List Int
  | [], _ => []
  | a :: f, g => addZ (smulZ a g) (0 :: mulZ f g)

def shiftZ (k : Nat) (f : List Int) : List Int := List.replicate k 0 ++ f

def zeroZ (f : List Int) : Bool := f.all (· == 0)

/-! ### `span{J}` -/

structure JE where
  c0 : List Int
  c1 : List Int
  c2 : List Int
  c3 : List Int
  c4 : List Int

namespace JE

def zero : JE := ⟨[], [], [], [], []⟩

def add (f g : JE) : JE := ⟨addZ f.c0 g.c0, addZ f.c1 g.c1, addZ f.c2 g.c2, addZ f.c3 g.c3, addZ f.c4 g.c4⟩

def smul (c : Int) (f : JE) : JE := ⟨smulZ c f.c0, smulZ c f.c1, smulZ c f.c2, smulZ c f.c3, smulZ c f.c4⟩

def zmul (p : List Int) (f : JE) : JE := ⟨mulZ p f.c0, mulZ p f.c1, mulZ p f.c2, mulZ p f.c3, mulZ p f.c4⟩

def comp (f : JE) : Nat → List Int
  | 0 => f.c0
  | 1 => f.c1
  | 2 => f.c2
  | 3 => f.c3
  | _ => f.c4

/-- the element `p(z)·g_d` -/
def single : Nat → List Int → JE
  | 0, p => ⟨p, [], [], [], []⟩
  | 1, p => ⟨[], p, [], [], []⟩
  | 2, p => ⟨[], [], p, [], []⟩
  | 3, p => ⟨[], [], [], p, []⟩
  | _, p => ⟨[], [], [], [], p⟩

def isZero (f : JE) : Bool := zeroZ f.c0 && zeroZ f.c1 && zeroZ f.c2 && zeroZ f.c3 && zeroZ f.c4

end JE

/-- `g_i g_r = Σ s J_d`. -/
def gtab : Nat → Nat → List (Nat × Int)
  | 0, r => [(r, 1)]
  | i, 0 => [(i, 1)]
  | 1, 1 => [(2, 1), (3, 1)]
  | 1, 2 => [(3, 1), (5, 11)]
  | 1, 3 => [(4, 1)]
  | 1, 4 => [(5, 1), (6, 12), (7, 11)]
  | 2, 1 => [(3, 1), (5, 11)]
  | 2, 2 => [(4, 1), (5, -1)]
  | 2, 3 => [(5, 1), (6, 11)]
  | 2, 4 => [(6, 1), (7, 11), (8, 11)]
  | 3, 1 => [(4, 1)]
  | 3, 2 => [(5, 1), (6, 11)]
  | 3, 3 => [(6, 1), (7, 11)]
  | 3, 4 => [(7, 1), (8, 12), (10, 121)]
  | 4, 1 => [(5, 1), (6, 12), (7, 11)]
  | 4, 2 => [(6, 1), (7, 11), (8, 11)]
  | 4, 3 => [(7, 1), (8, 12), (10, 121)]
  | 4, 4 => [(8, 1), (9, 12), (10, 11), (11, 121)]
  | _, _ => []

/-- `g_i · (p(z) g_r)`. -/
def mulGr (i r : Nat) (p : List Int) : JE :=
  (gtab i r).foldr (fun q acc => JE.add (JE.single (q.1 % 5) (smulZ q.2 (shiftZ (q.1 / 5) p))) acc) JE.zero

/-- `g_i · f`. -/
def mulG (i : Nat) (f : JE) : JE :=
  JE.add (mulGr i 0 f.c0) (JE.add (mulGr i 1 f.c1) (JE.add (mulGr i 2 f.c2) (JE.add (mulGr i 3 f.c3) (mulGr i 4 f.c4))))

/-- `f · g`. -/
def mulJ (f g : JE) : JE :=
  JE.add (JE.zmul g.c0 f) (JE.add (JE.zmul g.c1 (mulG 1 f)) (JE.add (JE.zmul g.c2 (mulG 2 f))
    (JE.add (JE.zmul g.c3 (mulG 3 f)) (JE.zmul g.c4 (mulG 4 f)))))

/-! ### `span{J}[Y]` -/

abbrev PY := List JE

def addY : PY → PY → PY
  | [], g => g
  | f, [] => f
  | a :: f, b :: g => JE.add a b :: addY f g

def smulY (c : Int) (f : PY) : PY := f.map (JE.smul c)

/-- multiply every coefficient by `e ∈ span{J}` (on the right, `e` small). -/
def jmulY (e : JE) (f : PY) : PY := f.map (fun a => mulJ a e)

def mulY : PY → PY → PY
  | [], _ => []
  | a :: f, g => addY (g.map (mulJ a)) (JE.zero :: mulY f g)

def isZeroY (f : PY) : Bool := f.all JE.isZero

/-- the coefficients `e_j` of the modular equation. -/
def eJ : Nat → JE
  | 1 => ⟨[0, 161051], [121], [2662], [14641], []⟩
  | 2 => ⟨[0, 161051], [-11], [968], [11979], []⟩
  | 3 => ⟨[0, 73205], [], [242], [5324], []⟩
  | 4 => ⟨[0, 14641], [], [22], [1452], []⟩
  | 5 => ⟨[0, -1331], [], [], [242], []⟩
  | 6 => ⟨[0, -1331], [], [], [22], []⟩
  | 7 => ⟨[0, -121], [], [], [], []⟩
  | 8 => ⟨[0, 121], [], [], [], []⟩
  | 9 => ⟨[0, 55], [], [], [], []⟩
  | 10 => ⟨[0, 11], [], [], [], []⟩
  | 11 => ⟨[0, 1], [], [], [], []⟩
  | _ => JE.zero

/-- the reduction step on a high-degree-first list `t :: rest` (`t` the coefficient of `Y^{n}`, `n ≥ 11`):
`rest[j] += (−1)^j e_{j+1} t`. -/
def stepH (t : JE) : Nat → List JE → List JE
  | _, [] => []
  | j, a :: rest => (if j < 11 then JE.add a (mulJ t (JE.smul ((-1) ^ j) (eJ (j + 1)))) else a) :: stepH t (j + 1) rest

def redH : Nat → List JE → List JE
  | 0, h => h
  | _ + 1, [] => []
  | n + 1, t :: rest => if rest.length < 11 then t :: rest else redH n (stepH t 0 rest)

/-- reduction modulo `P`. -/
def redP (f : PY) : PY := (redH f.length f.reverse).reverse

/-- `P'(Y) = 11 Y^10 − Σ_{j<10} (−1)^j (10 − j) e_{j+1} Y^{9−j}`. -/
def dP : PY := ((List.range 10).map fun (m : Nat) => JE.smul (-((-1) ^ (9 - m)) * ((m : Int) + 1)) (eJ (10 - m))) ++
  [JE.single 0 [11]]

/-! ### helpers for the checks -/

def shiftY (k : Nat) (f : PY) : PY := List.replicate k JE.zero ++ f

def subY (f g : PY) : PY := addY f (smulY (-1) g)

/-- `f = g` as elements of `span{J}[Y]`. -/
def ckEq (f g : PY) : Bool := isZeroY (subY f g)

/-- `z` (that is, `J₅`). -/
def zJ : JE := JE.single 0 [0, 1]

/-- `Y¹²`. -/
def y12 : PY := shiftY 12 [JE.single 0 [1]]

/-- `F, Y F, Y² F, …` reduced modulo `P`. -/
def iterF : Nat → PY → List PY
  | 0, F => [F]
  | n + 1, F => F :: iterF n (redP (JE.zero :: F))

/-- a `span{J}` element from `(ν, c)` pairs. -/
def ofPairs (l : List (Nat × Int)) : JE :=
  l.foldr (fun p acc => JE.add (JE.single (p.1 % 5) (shiftZ (p.1 / 5) [p.2])) acc) JE.zero

end Atkin11Seed
