import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Vélu's formulas: definitions

Short Weierstrass curve `E : y² = x³ + A x + B` over a field `K`, a finite subgroup `G ⊂ E(K)`
without `2`-torsion (e.g. of odd order), and a set `S` of representatives of `(G ∖ {0}) / ±`.

For `Q ∈ S` put `t_Q = 6 x_Q² + 2A`, `u_Q = 4 y_Q²`, `t = Σ t_Q`, `w = Σ (u_Q + x_Q t_Q)`.
The Vélu curve is `E' : y² = x³ + (A - 5t) x + (B - 7w)` and the Vélu maps are
`X(x) = x + Σ (t_Q/(x - x_Q) + u_Q/(x - x_Q)²)`,
`Y(x,y) = y - Σ (u_Q 2y/(x - x_Q)³ + t_Q y/(x - x_Q)²)`  (Washington, Thm 12.16).
-/

namespace Velu

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K]

/-- The short Weierstrass curve `y² = x³ + A x + B`. -/
def short (A B : K) : WeierstrassCurve.Affine K :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }

@[simp] lemma short_a₁ (A B : K) : (short A B).a₁ = 0 := rfl
@[simp] lemma short_a₂ (A B : K) : (short A B).a₂ = 0 := rfl
@[simp] lemma short_a₃ (A B : K) : (short A B).a₃ = 0 := rfl
@[simp] lemma short_a₄ (A B : K) : (short A B).a₄ = A := rfl
@[simp] lemma short_a₆ (A B : K) : (short A B).a₆ = B := rfl

lemma short_equation_iff (A B x y : K) :
    (short A B).Equation x y ↔ y ^ 2 = x ^ 3 + A * x + B := by
  rw [Affine.equation_iff]; simp

lemma short_Δ (A B : K) : (short A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, short_a₁, short_a₂, short_a₃, short_a₄, short_a₆]
  ring

variable {A B : K}

/-- `x`-coordinate of a point (junk value `0` at infinity). -/
def xc : (short A B).Point → K
  | .zero => 0
  | .some x _ _ => x

/-- `y`-coordinate of a point (junk value `0` at infinity). -/
def yc : (short A B).Point → K
  | .zero => 0
  | .some _ y _ => y

@[simp] lemma xc_zero : xc (0 : (short A B).Point) = 0 := rfl
@[simp] lemma yc_zero : yc (0 : (short A B).Point) = 0 := rfl
@[simp] lemma xc_some {x y : K} (h : (short A B).Nonsingular x y) : xc (.some x y h) = x := rfl
@[simp] lemma yc_some {x y : K} (h : (short A B).Nonsingular x y) : yc (.some x y h) = y := rfl

@[simp] lemma xc_neg (P : (short A B).Point) : xc (-P) = xc P := by
  cases P <;> rfl

@[simp] lemma yc_neg (P : (short A B).Point) : yc (-P) = -yc P := by
  cases P with
  | zero => show (0:K) = -0; simp
  | some x y h =>
    change (short A B).negY x y = -y
    simp [Affine.negY]

lemma equation_xc_yc {P : (short A B).Point} (hP : P ≠ 0) :
    yc P ^ 2 = xc P ^ 3 + A * xc P + B := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => simpa [short_equation_iff] using h.1

lemma eq_some_of_ne_zero {P : (short A B).Point} (hP : P ≠ 0) :
    ∃ h, P = .some (xc P) (yc P) h := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact ⟨h, rfl⟩

variable [DecidableEq K]

/-- Coordinates of a sum of two affine points with distinct `x`-coordinates. -/
lemma add_coords_of_xc_ne {P Q : (short A B).Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : xc P ≠ xc Q) :
    xc (P + Q) = ((yc P - yc Q) / (xc P - xc Q)) ^ 2 - xc P - xc Q ∧
    yc (P + Q) = -(((yc P - yc Q) / (xc P - xc Q)) *
      (xc (P + Q) - xc P) + yc P) := by
  obtain ⟨hP', eP⟩ := eq_some_of_ne_zero hP
  obtain ⟨hQ', eQ⟩ := eq_some_of_ne_zero hQ
  rw [eP, eQ, Affine.Point.add_of_X_ne hx]
  simp [Affine.slope_of_X_ne hx, Affine.negY]

/-- Coordinates of the double of an affine point with nonzero `y`-coordinate. -/
lemma double_coords {P : (short A B).Point} (hP : P ≠ 0) (hy : yc P ≠ 0) (h2 : (2 : K) ≠ 0) :
    xc (P + P) = ((3 * xc P ^ 2 + A) / (2 * yc P)) ^ 2 - 2 * xc P ∧
    yc (P + P) = -(((3 * xc P ^ 2 + A) / (2 * yc P)) * (xc (P + P) - xc P) + yc P) := by
  obtain ⟨hP', eP⟩ := eq_some_of_ne_zero hP
  have hne : yc P ≠ (short A B).negY (xc P) (yc P) := by
    simp only [Affine.negY, short_a₁, short_a₃, zero_mul, sub_zero]
    intro h; apply hy
    have : 2 * yc P = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' h2
    · exact h'
  have hs : (short A B).slope (xc P) (xc P) (yc P) (yc P) = (3 * xc P ^ 2 + A) / (2 * yc P) := by
    rw [Affine.slope_of_Y_ne rfl hne]
    simp [Affine.negY]; ring
  rw [eP, Affine.Point.add_self_of_Y_ne hne]
  simp only [xc_some, yc_some, Affine.addY, Affine.addX, Affine.negAddY, hs, Affine.negY,
    short_a₁, short_a₂, short_a₃]
  constructor <;> ring

/-! ## Kernel data -/

/-- A finite subgroup `G` of `E(K)` without `2`-torsion, together with a set `S` of
representatives of `(G ∖ {0})/±`. (Any finite subgroup of odd order admits such data.) -/
structure Kernel (A B : K) where
  G : Finset (short A B).Point
  S : Finset (short A B).Point
  zero_mem : 0 ∈ G
  add_mem : ∀ P ∈ G, ∀ Q ∈ G, P + Q ∈ G
  neg_mem : ∀ P ∈ G, -P ∈ G
  no_two_torsion : ∀ P ∈ G, P + P = 0 → P = 0
  S_sub : S ⊆ G
  zero_not_mem_S : (0 : (short A B).Point) ∉ S
  neg_not_mem_S : ∀ Q ∈ S, -Q ∉ S
  cover : ∀ P ∈ G, P ≠ 0 → P ∈ S ∨ -P ∈ S

namespace Kernel

variable (κ : Kernel A B)

/-- `t_Q = 6 x_Q² + 2A`. -/
def tQ (Q : (short A B).Point) : K := 6 * xc Q ^ 2 + 2 * A

/-- `u_Q = 4 y_Q²`. -/
def uQ (Q : (short A B).Point) : K := 4 * yc Q ^ 2

/-- `t = Σ_{Q∈S} t_Q`. -/
def t : K := ∑ Q ∈ κ.S, tQ (A := A) (B := B) Q

/-- `w = Σ_{Q∈S} (u_Q + x_Q t_Q)`. -/
def w : K := ∑ Q ∈ κ.S, (uQ (A := A) (B := B) Q + xc Q * tQ (A := A) (B := B) Q)

/-- Coefficient `A' = A - 5t` of the Vélu curve. -/
def A' : K := A - 5 * κ.t

/-- Coefficient `B' = B - 7w` of the Vélu curve. -/
def B' : K := B - 7 * κ.w

/-- The Vélu curve `E/G : y² = x³ + A' x + B'`. -/
def curve : WeierstrassCurve.Affine K := short κ.A' κ.B'

/-- Vélu's `X`. -/
def X (x : K) : K := x + ∑ Q ∈ κ.S, (tQ (A := A) (B := B) Q / (x - xc Q) +
  uQ (A := A) (B := B) Q / (x - xc Q) ^ 2)

/-- The `x`-derivative of Vélu's `X`. -/
def Xd (x : K) : K := 1 - ∑ Q ∈ κ.S, (tQ (A := A) (B := B) Q / (x - xc Q) ^ 2 +
  2 * uQ (A := A) (B := B) Q / (x - xc Q) ^ 3)

/-- Vélu's `Y`. -/
def Y (x y : K) : K := y - ∑ Q ∈ κ.S, (uQ (A := A) (B := B) Q * (2 * y) / (x - xc Q) ^ 3 +
  tQ (A := A) (B := B) Q * y / (x - xc Q) ^ 2)

/-- `Y = y · dX/dx`; hence `dX / (2Y) = dx / (2y)` (the invariant differential is preserved). -/
lemma Y_eq (x y : K) : κ.Y x y = y * κ.Xd x := by
  simp only [Y, Xd, mul_sub, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun Q _ => ?_
  ring

lemma curve_Δ : κ.curve.Δ = -16 * (4 * (A - 5 * κ.t) ^ 3 + 27 * (B - 7 * κ.w) ^ 2) :=
  short_Δ _ _

end Kernel

end Velu
