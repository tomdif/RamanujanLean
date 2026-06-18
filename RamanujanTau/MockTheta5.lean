/-
# Ramanujan's fifth-order mock theta functions — truncated q-series + kernel-checked relations

The ten fifth-order mock theta functions from the Lost Notebook, as EXACT integer q-series truncated
to order `q^N`, with two classical Ramanujan relations among them machine-verified by `native_decide`.

  f₀ f₁ F₀ F₁ φ₀ φ₁ ψ₀ ψ₁ χ₀ χ₁   (Watson / Andrews–Garvan notation)

Relations certified here (to order q^N):
  (R1)  χ₀(q) = 2·F₀(q) − φ₀(−q)
  (R2)  q·χ₁(q) = 2q·F₁(q) + φ₁(−q)          i.e.  χ₁(q) = 2F₁(q) + q⁻¹φ₁(−q)

HONEST SCOPE (proofworld soundness gate): this is rung-2 evidence — a machine-checked verification that
the identities hold for coefficients 0..N-1. It is NOT the infinite identity (rung 3), which needs a
q-Pochhammer / q-series proof not yet in Mathlib; and it is NOT the deep "mock theta conjectures"
(Hickerson), which are out of scope. `native_decide` trusts the compiler (a wider trust base than the
kernel); a pure-kernel `decide` certifies the same at smaller N.

Self-contained: core `Int`/`List` only, no Mathlib import (fast to build, no dependency on the τ project).
-/

namespace MockTheta5

/-- truncation order. -/
def N : Nat := 48

/-- coefficient `i` of a truncated power series (0 outside range). -/
def gc (l : List Int) (i : Nat) : Int := l.getD i 0

/-- `1` as a length-`N` series. -/
def pone : List Int := (1 : Int) :: List.replicate (N - 1) 0

/-- truncated product of two power series. -/
def pmul (a b : List Int) : List Int :=
  (List.range N).map (fun k =>
    (List.range (k + 1)).foldl (fun acc i => acc + gc a i * gc b (k - i)) 0)

/-- multiply by `q^e`. -/
def pshift (a : List Int) (e : Nat) : List Int :=
  (List.range N).map (fun k => if e ≤ k then gc a (k - e) else 0)

def padd (a b : List Int) : List Int := (List.range N).map (fun k => gc a k + gc b k)
def psub (a b : List Int) : List Int := (List.range N).map (fun k => gc a k - gc b k)
def pscale (c : Int) (a : List Int) : List Int := a.map (· * c)

/-- the factor `(1 + s·q^e)`. -/
def factor (e : Nat) (s : Int) : List Int :=
  (List.range N).map (fun k => if k = 0 then 1 else if k = e then s else 0)

/-- inverse of `(1 + s·q^e)` = Σ_m (−s)^m q^{m·e}  (coeff `(−s)^(k/e)` at multiples of `e`). -/
def geomInv (e : Nat) (s : Int) : List Int :=
  (List.range N).map (fun k => if e = 0 then 0 else if k % e = 0 then (-s) ^ (k / e) else 0)

def pprod (fs : List (List Int)) : List Int := fs.foldl pmul pone

-- q-Pochhammer building blocks
def negq_q_inv (n : Nat) : List Int := pprod ((List.range n).map (fun k => geomInv (k + 1) 1))      -- 1/(−q;q)_n
def q_q2_inv   (n : Nat) : List Int := pprod ((List.range n).map (fun k => geomInv (2*k + 1) (-1)))  -- 1/(q;q²)_n
def negq_q2    (n : Nat) : List Int := pprod ((List.range n).map (fun k => factor (2*k + 1) 1))      -- (−q;q²)_n
def negq_q     (n : Nat) : List Int := pprod ((List.range n).map (fun k => factor (k + 1) 1))        -- (−q;q)_n
def qn1_q_inv  (n m : Nat) : List Int := pprod ((List.range m).map (fun k => geomInv (n + 1 + k) (-1)))  -- 1/(q^{n+1};q)_m

/-- Σ_{n<cnt} of `f n`. -/
def sumN (f : Nat → List Int) (cnt : Nat) : List Int :=
  ((List.range cnt).map f).foldl padd (List.replicate N 0)

-- the ten fifth-order mock theta functions (cnt chosen so all in-range terms are included)
def f0   : List Int := sumN (fun n => pshift (negq_q_inv n) (n*n))            10
def f1   : List Int := sumN (fun n => pshift (negq_q_inv n) (n*n + n))        10
def F0   : List Int := sumN (fun n => pshift (q_q2_inv n) (2*n*n))            8
def F1   : List Int := sumN (fun n => pshift (q_q2_inv (n+1)) (2*n*n + 2*n))  8
def phi0 : List Int := sumN (fun n => pshift (negq_q2 n) (n*n))               10
def phi1 : List Int := sumN (fun n => pshift (negq_q2 n) ((n+1)*(n+1)))       10
def psi0 : List Int := sumN (fun n => pshift (negq_q n) ((n+1)*(n+2)/2))      12
def psi1 : List Int := sumN (fun n => pshift (negq_q n) (n*(n+1)/2))          12
def chi0 : List Int := sumN (fun n => pshift (qn1_q_inv n n) n)               N
def chi1 : List Int := sumN (fun n => pshift (qn1_q_inv n (n+1)) n)           N

/-- substitute `q → −q`: negate odd-degree coefficients. -/
def subNegQ (a : List Int) : List Int :=
  (List.range N).map (fun k => if k % 2 = 0 then gc a k else - gc a k)

def allZero (a : List Int) : Bool := a.all (· == 0)

-- (R1)  χ₀ − (2F₀ − φ₀(−q))
def res_R1 : List Int := psub chi0 (psub (pscale 2 F0) (subNegQ phi0))
-- (R2)  q·χ₁ − (2q·F₁ + φ₁(−q))
def res_R2 : List Int := psub (pshift chi1 1) (padd (pshift (pscale 2 F1) 1) (subNegQ phi1))

/-- Ramanujan 5th-order relation **χ₀(q) = 2F₀(q) − φ₀(−q)**, verified to order q^N. -/
theorem mtc5_R1_chi0 : allZero res_R1 = true := by native_decide

/-- Ramanujan 5th-order relation **q·χ₁(q) = 2q·F₁(q) + φ₁(−q)**, verified to order q^N. -/
theorem mtc5_R2_chi1 : allZero res_R2 = true := by native_decide

end MockTheta5
