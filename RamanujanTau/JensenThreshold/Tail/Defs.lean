/-
# Computable definitions for the Jensen tail certificate (light imports, no real analysis)

Fixed-point intervals `Iv` (denoting `[lo/S, hi/S]`, `S = 2^192`), the integer `(u,w)`-polynomial data `Pz m`
of the derivatives of `log Mmain`, and the box checker `checkBox`. Soundness: `Interval.lean`, `Model.lean`,
`Box.lean`.
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Batteries.Data.Nat.Basic

set_option autoImplicit false

namespace JensenThreshold.Tail

/-- the scale `2^192`. -/
def S : ℤ := 2 ^ 192

structure Iv where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

/-- floor and ceiling division by `S`. -/
def fdS (a : ℤ) : ℤ := a / S
def cdS (a : ℤ) : ℤ := -((-a) / S)

/-- general floor/ceiling division by a positive integer. -/
def fdv (a b : ℤ) : ℤ := a / b
def cdv (a b : ℤ) : ℤ := -((-a) / b)

namespace Iv

def add (I J : Iv) : Iv := ⟨I.lo + J.lo, I.hi + J.hi⟩
def neg (I : Iv) : Iv := ⟨-I.hi, -I.lo⟩
def sub (I J : Iv) : Iv := add I (neg J)

def mul (I J : Iv) : Iv :=
  let a := I.lo * J.lo
  let b := I.lo * J.hi
  let c := I.hi * J.lo
  let d := I.hi * J.hi
  ⟨fdS (min (min a b) (min c d)), cdS (max (max a b) (max c d))⟩

/-- the rational `p/q` (`q > 0`). -/
def ofFrac (p : ℤ) (q : ℤ) : Iv := ⟨fdv (p * S) q, cdv (p * S) q⟩

def ofInt (p : ℤ) : Iv := ⟨p * S, p * S⟩

/-- `1/x` (meaningful when `0 < lo`). -/
def inv (I : Iv) : Iv := ⟨fdv (S * S) I.hi, cdv (S * S) I.lo⟩

/-- `√x` (meaningful when `0 ≤ lo`). -/
def sqrt (I : Iv) : Iv := ⟨(Nat.sqrt (I.lo.toNat * S.toNat) : ℤ), (Nat.sqrt (I.hi.toNat * S.toNat) : ℤ) + 1⟩

def pow (I : Iv) : ℕ → Iv
  | 0 => ofInt 1
  | k + 1 => mul (pow I k) I

def hull (I J : Iv) : Iv := ⟨min I.lo J.lo, max I.hi J.hi⟩

/-- `[−r, r]` for the absolute bound of `I`. -/
def absHi (I : Iv) : ℤ := max (-I.lo) I.hi
def symm (r : ℤ) : Iv := ⟨-r, r⟩

instance : Add Iv := ⟨add⟩
instance : Mul Iv := ⟨mul⟩
instance : Neg Iv := ⟨neg⟩
instance : Sub Iv := ⟨sub⟩

end Iv

/-- integer `(u, w)`-polynomials: `Σ c · U^{-p} (U−1)^{-q}`. -/
abbrev UWZ := List (ℕ × ℕ × ℤ)

/-- `2·U·d/dU` on monomials (the factor `a/2` per derivative is kept outside). -/
def dZ (P : UWZ) : UWZ :=
  P.flatMap fun m => [(m.1 + 2, m.2.1, -(m.1 : ℤ) * m.2.2), (m.1 + 1, m.2.1 + 1, -(m.2.1 : ℤ) * m.2.2)]

def insZ (m : ℕ × ℕ × ℤ) : UWZ → UWZ
  | [] => [m]
  | x :: xs => if x.1 = m.1 ∧ x.2.1 = m.2.1 then (x.1, x.2.1, x.2.2 + m.2.2) :: xs else x :: insZ m xs

def normZ (P : UWZ) : UWZ := P.foldr insZ []

def P1 : UWZ := [(1, 0, 1), (1, 1, 1), (2, 0, -3)]

/-- `Pz m` : the data of `E_m`, `f^{(m)} = (a/2)^m E_m(U)`. -/
def Pz : ℕ → UWZ
  | 0 => []
  | 1 => P1
  | m + 2 => normZ (dZ (Pz (m + 1)))

def toQ (m : ℕ) (P : UWZ) : UWZ := P.map fun x => (x.1 + x.2.1 - (2 * m - 1), x.2.1, x.2.2)

def okQ (m : ℕ) (P : UWZ) : Bool := P.all fun x => decide (2 * m - 1 ≤ x.1 + x.2.1)

open Iv

def zeroI : Iv := ofInt 0
def oneI : Iv := ofInt 1

/-- `Σ c uᵉ ωᵠ` in intervals. -/
def evalQIv (Q : UWZ) (Iu Iω : Iv) : Iv :=
  Q.foldr (fun x acc => ofInt x.2.2 * Iu.pow x.1 * Iω.pow x.2.1 + acc) zeroI

/-- interval sums over `range n`. -/
def sumIv (n : ℕ) (f : ℕ → Iv) : Iv := (List.range n).foldr (fun i acc => f i + acc) zeroI

/-- the Leibniz recurrence `g_{k+1} = Σ_{i≤k} C(k,i) g_{k−i} Φ_{i+1}` on interval lists. -/
def recStep (Φ : List Iv) (L : List Iv) (k : ℕ) : Iv :=
  sumIv (k + 1) fun i => ofInt (k.choose i) * L.getD (k - i) zeroI * Φ.getD (i + 1) zeroI

def recIv (Φ : List Iv) (E0 : Iv) : ℕ → List Iv
  | 0 => [E0]
  | k + 1 => let L := recIv Φ E0 k; L ++ [recStep Φ L k]

/-- `aC = 2π²/3` from `π ∈ (3.14159265358979323846, 3.14159265358979323847)`. -/
def Ia : Iv :=
  ⟨(ofFrac (2 * 314159265358979323846 ^ 2) (3 * 10 ^ 40)).lo,
   (ofFrac (2 * 314159265358979323847 ^ 2) (3 * 10 ^ 40)).hi⟩

def Ia2 : Iv := Ia * ofFrac 1 2

def Qd (m : ℕ) : UWZ := toQ m (Pz m)

/-- `Δ^k j^i (0) = Σ_j (−1)^{k−j} C(k,j) j^i`. -/
def Dki (k i : ℕ) : ℤ := ((List.range (k + 1)).map fun j => (-1 : ℤ) ^ (k - j) * (k.choose j) * (j : ℤ) ^ i).sum

/-- `Σ_j C(k,j) j^K`. -/
def CjK (k K : ℕ) : ℤ := ((List.range (k + 1)).map fun j => (k.choose j : ℤ) * (j : ℤ) ^ K).sum

/-- `x^i / i!` as a product of `i` factors `x/(j+1)` (keeps precision for large `i`). -/
def powFact (x : Iv) : ℕ → Iv
  | 0 => oneI
  | i + 1 => powFact x i * x * ofFrac 1 (i + 1)

/-- `Π_{j=1}^{N} (2j·t²)` = `2^N N! t^{2N}`. -/
def prodT (It : Iv) : ℕ → Iv
  | 0 => oneI
  | j + 1 => prodT It j * (ofInt (2 * (j + 1)) * It.pow 2)

structure BoxD where
  tlp : ℤ
  tlq : ℤ
  thp : ℤ
  thq : ℤ
  pts : List (ℤ × ℤ)
  deriving Repr

def c2powI (c2 sq : Iv) (m : ℕ) : Iv := c2.pow (m / 2) * (if m % 2 = 1 then sq else oneI)

/-! ### the intervals of one box (each a separate definition, for the soundness proofs) -/

section box
variable (d K N : ℕ) (B : BoxD)

def bIt : Iv := ⟨(ofFrac B.tlp B.tlq).lo, (ofFrac B.thp B.thq).hi⟩
def bIu0 : Iv := (bIt B).pow 2
def bIom0 : Iv := (oneI - bIu0 B).inv
def bc2 : Iv := evalQIv (Qd 2) (bIu0 B) (bIom0 B) * ofFrac (-1) 2
def bsq : Iv := (bc2 B).sqrt
def bdel : Iv := Ia2 * (bIt B).pow 3 * bsq B
def bPhi0 : List Iv := [zeroI, zeroI, ofInt (-2)] ++
  (List.range (K - 2)).map fun i =>
    evalQIv (Qd (i + 3)) (bIu0 B) (bIom0 B) * (bIt B).pow (i + 1) * (c2powI (bc2 B) (bsq B) (i + 3)).inv
def bg0 : List Iv := recIv (bPhi0 K B) oneI K
def bIrho : Iv := (⟨S, (oneI + Ia * ofInt d * (bIt B).pow 4).hi⟩ : Iv).sqrt
def bIratio : Iv := ⟨(bIrho d B).inv.lo, S⟩
def bIus : Iv := bIu0 B * bIratio d B
def bIoms : Iv := (oneI - bIus d B).inv
def bQ2s : Iv := evalQIv (Qd 2) (bIus d B) (bIoms d B)
def bIf2 : Iv := Ia2.pow 2 * (bIus d B).pow 3 * bQ2s d B
def bsint : Iv := ⟨0, d * S⟩
def bJ1 : Iv := Ia2 * (bIratio d B).pow 3 * (bIt B).pow 3 * bQ2s d B * (bsq B).inv
def bPhis : List Iv := [((bsint d).pow 2 * ofFrac 1 2) * bIf2 d B, bsint d * bJ1 d B] ++
  (List.range (K - 1)).map fun i =>
    (bIratio d B).pow (2 * (i + 2) - 1) * (bIt B).pow i * evalQIv (Qd (i + 2)) (bIus d B) (bIoms d B) *
      (c2powI (bc2 B) (bsq B) (i + 2)).inv
def bE0s : Iv := ⟨((bPhis d K B).getD 0 zeroI).lo + S, S⟩
def bgs : List Iv := recIv (bPhis d K B) (bE0s d K B) K
def bMK : ℤ := absHi ((bgs d K B).getD K zeroI)
def bIU0 : Iv := (bIu0 B).inv
def bIexps : Iv := sumIv N fun i => powFact (bIU0 B * ofFrac 1 2) i
def bepsF : Iv := ofInt 2 * (bIU0 B * bIrho d B).pow 3 * (bIU0 B - oneI).inv * (bIexps N B).inv
def bEk (k : ℕ) : ℤ := if 0 < B.tlp then (ofInt (2 ^ k) * bepsF d N B * (bdel B).inv.pow k).hi
  else (ofInt (2 ^ k * 4) * prodT (ofFrac B.thp B.thq) N * (ofFrac B.thq B.thp).pow (4 + 3 * k) *
    ((Ia2 * bsq B).inv).pow k).hi
def bmain (k : ℕ) : Iv := sumIv (K - k) fun i' =>
  ofFrac (Dki k (k + i')) ((k + i').factorial) * (bdel B).pow i' * (bg0 K B).getD (k + i') zeroI
def bremM (k : ℕ) : ℤ :=
  (ofFrac (CjK k K) (K.factorial) * (bdel B).pow (K - k) * (⟨bMK d K B, bMK d K B⟩ : Iv)).hi
def bgam (k : ℕ) : Iv := bmain K B k + symm (bremM d K B k) + symm (bEk d N B k)
def bG (x : ℤ × ℤ) : Iv :=
  sumIv (d + 1) fun k => ofInt (d.choose k) * bgam d K N B k * (ofFrac x.1 x.2).pow (d - k) *
    (bdel B * ofFrac x.1 x.2 - oneI).pow k

end box

/-- sign of `G` at the `i`-th point must be `(−1)^{d−i}`. -/
def signOK (d i : ℕ) (I : Iv) : Bool := if (d - i) % 2 = 0 then decide (0 < I.lo) else decide (I.hi < 0)

def checkBox (d K N : ℕ) (B : BoxD) : Bool :=
  decide (0 < B.tlq) && decide (0 < B.thq) && decide (0 ≤ B.tlp) && decide (0 < B.thp) &&
  decide (2 * B.thp ≤ B.thq) && decide (B.tlp * B.thq ≤ B.thp * B.tlq) &&
  decide (0 < (oneI - bIu0 B).lo) && decide (0 < (bc2 B).lo) && decide (0 < (bsq B).lo) &&
  decide (0 < (oneI - bIus d B).lo) && decide (0 < (bIrho d B).lo) &&
  (List.range (K + 1)).all (fun m => decide (0 < (c2powI (bc2 B) (bsq B) m).lo)) &&
  decide (((bPhis d K B).getD 0 zeroI).hi ≤ 0) && decide ((bIf2 d B).hi ≤ 0) &&
  (List.range (K + 1)).all (fun m => okQ m (Pz m)) &&
  decide (3 ≤ K) && decide (d + 1 ≤ K) && decide (3 * d + 4 ≤ 2 * N) && decide (0 < (Ia2 * bsq B).lo) &&
  (List.range (d + 1)).all (fun k => (List.range k).all fun i => decide (Dki k i = 0)) &&
  decide (B.pts.length = d + 1) &&
  (List.range d).all (fun i => decide ((B.pts.getD i (0, 1)).1 * (B.pts.getD (i + 1) (0, 1)).2 <
      (B.pts.getD (i + 1) (0, 1)).1 * (B.pts.getD i (0, 1)).2)) &&
  B.pts.all (fun x => decide (0 < x.2)) &&
  (List.range (d + 1)).all (fun i => signOK d i (bG d K N B (B.pts.getD i (0, 1)))) &&
  (if 0 < B.tlp then decide (0 < (bIU0 B - oneI).lo) && decide (0 < (bIexps N B).lo) &&
    decide (0 < (bdel B).lo) && decide (0 < (bIu0 B).lo) else true)

/-- the boxes are contiguous from `t_max = p/q` down to `0`. -/
def coverOK : List BoxD → ℤ × ℤ → Bool
  | [], _ => false
  | B :: Bs, (p, q) => decide (0 < B.thq) && decide (0 < B.tlq) && decide (0 ≤ B.tlp) &&
      decide (B.thp * q = p * B.thq) && (if B.tlp = 0 then true else coverOK Bs (B.tlp, B.tlq))

end JensenThreshold.Tail
