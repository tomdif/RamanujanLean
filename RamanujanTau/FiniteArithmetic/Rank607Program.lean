import RamanujanTau.FiniteArithmetic.PackedSeries

/-! # The prime-607 kernel program

Computes packed prefixes of the series behind the 25-by-25 rank witness.
This file only computes; correctness of each step is proved separately. -/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.Rank607Program
open Packed

abbrev p : ℕ := 607
abbrev Q : ℕ := 607 ^ 2
abbrev N : ℕ := 61308
def mu : ℕ := 2 ^ 40 / Q
/-- `(p^2 - 1) / 24`. -/
def delta : ℕ := 15352

abbrev mulQ (a b : ℕ) : Option ℕ := mulR Q N mu a b
abbrev addQ (a b : ℕ) : Option ℕ := addR Q N mu a b

/-- Generalized pentagonal exponents for `k = j + 1`. -/
def pentLow (j : ℕ) : ℕ := (j + 1) * (3 * (j + 1) - 1) / 2
def pentHigh (j : ℕ) : ℕ := (j + 1) * (3 * (j + 1) + 1) / 2
/-- Sign of the `j`-th pentagonal pair, as a residue. -/
def pentSign (j : ℕ) : ℕ := if j % 2 = 0 then Q - 1 else 1

/-- `1 + Σ_{j<J} (-1)^(j+1) (q^low + q^high)`, reduced. -/
def pentFold : ℕ → Option ℕ
  | 0 => some 1
  | j + 1 => do
    let a ← pentFold j
    let b ← addQ a (shiftR N (pentLow j) (pentSign j))
    addQ b (shiftR N (pentHigh j) (pentSign j))

/-- Number of pentagonal pairs meeting the prefix. -/
def pentCount : ℕ := 202

/-- Untrusted Newton iteration for an inverse. Certified afterwards by `invOk`. -/
def newton (u : ℕ) : ℕ → ℕ → ℕ
  | 0, b => b
  | n + 1, b =>
    let v := (reduceRaw Q N mu ((u * b) % x ^ N)).1
    let w := fastMask (16 * Q) N - v + 2
    newton u n (reduceRaw Q N mu ((b * w) % x ^ N)).1

/-- Canonical lanes, for an inverse with lanes below `2^22`. -/
def inverse (u : ℕ) : ℕ := newton u 17 1

/-- Multiply by the lane index. -/
def thetaLane (i v : ℕ) : ℕ := i * v % Q

/-- The denominator lane: `4 p · (v c m^(p-2) mod p)`, with `c = (-24)⁻¹ mod p`
and `m` the prime-to-`p` part of `i`. -/
def cInv : ℕ := 177
def sigmaLane (i v : ℕ) : ℕ :=
  let m := if i % p = 0 then i / p else i
  4 * p * ((v * cInv * m ^ (p - 2)) % p) % Q

/-- The prefix map applied through `laneMap`. -/
def mapQ (h : ℕ → ℕ → ℕ) (a : ℕ) : ℕ := laneMap h 16 0 a % x ^ N

/-- Binary power by a list of squarings. -/
def powQ (a : ℕ) : ℕ → Option ℕ
  | 0 => some 1
  | n + 1 => do
    let b ← powQ a n
    mulQ b a

/-- Lanes `0, stride, 2 stride, ...` of `a`, packed into `2^l` lanes. -/
def sparse (stride : ℕ) : ℕ → ℕ → ℕ
  | 0, a => a % x
  | l + 1, a =>
    sparse stride l (a % x ^ (stride * 2 ^ l)) +
      sparse stride l (a >>> (64 * (stride * 2 ^ l))) <<< (64 * 2 ^ l)

/-- The row of `U_p` values: lanes `607 j`, for `j ≤ 101`. -/
def rowOf (a : ℕ) : ℕ := sparse p 7 a % x ^ 102

/-- A certified inverse, or failure. -/
def invert (u : ℕ) : Option ℕ :=
  if invOk Q N mu u (inverse u) then some (inverse u) else none

/-- The series reachable from the pentagonal prefix, up to the basis loop. -/
structure Prelude where
  /-- The prefix of `(q;q)⁻¹`. -/
  pgf : ℕ
  /-- The prefix of `E₄`. -/
  e4 : ℕ
  /-- The prefix of `E₄^303 (1 + 4 p S)`. -/
  b0 : ℕ
  /-- The prefix of `Δ E₄⁻³`. -/
  g : ℕ

/-- All series needed by the basis loop. -/
def prelude : Option Prelude := do
  let P ← pentFold pentCount
  let Pi ← invert P
  let P2 ← mulQ P P
  let P3 ← mulQ P2 P
  let P6 ← mulQ P3 P3
  let P12 ← mulQ P6 P6
  let W ← mulQ P12 P12
  let Pi2 ← mulQ Pi Pi
  let Pi3 ← mulQ Pi2 Pi
  let Pi6 ← mulQ Pi3 Pi3
  let Pi12 ← mulQ Pi6 Pi6
  let Wi ← mulQ Pi12 Pi12
  let e2a ← mulQ (mapQ thetaLane W) Wi
  let E2 ← addQ e2a 1
  let sq ← mulQ E2 E2
  let sc ← mulQ (mapQ thetaLane E2) (Q - 12)
  let E4 ← addQ sq sc
  let Eis ← addQ 1 (mapQ sigmaLane E2)
  let E4s ← mulQ E4 E4
  let E4c ← mulQ E4 E4s
  let E303 ← powQ E4c 101
  let E4ci ← invert E4c
  let g ← mulQ (shiftR N 1 W) E4ci
  let B0 ← mulQ E303 Eis
  return ⟨Pi, E4, B0, g⟩

/-- The three families of 102-lane rows, one entry per basis series. -/
structure Rows where
  /-- Low coefficients. -/
  ls : List ℕ
  /-- `U` values. -/
  us : List ℕ
  /-- `U(Φ ·)` values. -/
  ds : List ℕ

/-- Rows for `c` basis series, starting from `b`. -/
def basisRows (g phi : ℕ) : ℕ → ℕ → Option Rows
  | 0, _ => some ⟨[], [], []⟩
  | c + 1, b => do
    let next ← mulQ b g
    let d ← reduceR Q 102 mu (rowOf ((b * phi) % x ^ N))
    let rest ← basisRows g phi c next
    return ⟨(b % x ^ 102) :: rest.ls, rowOf b :: rest.us, d :: rest.ds⟩

/-- All rows, with the row of `Φ` itself. -/
def rows : Option (Rows × ℕ) := do
  let pr ← prelude
  let rs ← basisRows pr.g (shiftR N delta pr.pgf) 102 pr.b0
  return (rs, rowOf (shiftR N delta pr.pgf))

end RamanujanTau.FiniteArithmetic.Rank607Program
