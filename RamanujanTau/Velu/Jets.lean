import RamanujanTau.Velu.Defs

/-!
# Vélu: pointwise jet identities

For `Q₀ = (x₀, y₀)` and `Q = (x_Q, y_Q)` on `E` with `x₀ ≠ x_Q`, `y₀ ≠ 0`, the Taylor
coefficients at `x = x₀` of `φ_Q(x) = t_Q/(x - x_Q) + u_Q/(x - x_Q)²` are expressed through the
coordinates of `Q₀ ± Q`. With `D = d/dx` along the curve (`D x(P+T) = y(P+T)/y(P)`) one has
`(D^k/k!) x(P+T)|_{P=Q₀} = c_k(Q₀+T)` with the explicit `c_k` below, and
`φ_Q = x(P+Q) + x(P-Q) - 2x_Q`; hence `jet_k(φ_Q) = c_k(Q₀+Q) + c_k(Q₀-Q) - 2 x_Q [k=0]`.
-/

set_option linter.unusedSimpArgs false

namespace Velu

variable {K : Type*} [Field K]

/-- The `k`-th Taylor coefficient of `t/(δ+s) + u/(δ+s)²` at `s = 0`. -/
def jet (k : ℕ) (δ t u : K) : K := (-1) ^ k * (t / δ ^ (k + 1) + (k + 1) * u / δ ^ (k + 2))

/-- `c_k(V)`: Taylor coefficient of order `k` of `x(P+T)` at `P = Q₀ = (x₀,y₀)`, `V = Q₀+T`. -/
def cj (A x0 y0 : K) : ℕ → K → K → K
  | 0, X, _ => X
  | 1, _, Y => Y / y0
  | 2, X, Y => (3 * X ^ 2 + A) / (4 * y0 ^ 2) - Y * (3 * x0 ^ 2 + A) / (4 * y0 ^ 3)
  | 3, X, Y => X * Y / (2 * y0 ^ 3) - (3 * X ^ 2 + A) * (3 * x0 ^ 2 + A) / (8 * y0 ^ 4)
      - Y * x0 / (2 * y0 ^ 3) + Y * (3 * x0 ^ 2 + A) ^ 2 / (8 * y0 ^ 5)
  | _, _, _ => 0

/-- The algebraic jet identity, with the sum/difference points given by the chord formulas. -/
theorem jet_alg (A B x0 y0 xq yq : K) (h0 : y0 ^ 2 = x0 ^ 3 + A * x0 + B)
    (hq : yq ^ 2 = xq ^ 3 + A * xq + B) (hx : x0 ≠ xq) (hy : y0 ≠ 0) (h2 : (2 : K) ≠ 0)
    (k : ℕ) (hk : k ≤ 3) :
    jet k (x0 - xq) (6 * xq ^ 2 + 2 * A) (4 * yq ^ 2) =
      cj A x0 y0 k (((y0 - yq) / (x0 - xq)) ^ 2 - x0 - xq)
          (-(((y0 - yq) / (x0 - xq)) * ((((y0 - yq) / (x0 - xq)) ^ 2 - x0 - xq) - x0) + y0)) +
        cj A x0 y0 k (((y0 + yq) / (x0 - xq)) ^ 2 - x0 - xq)
          (-(((y0 + yq) / (x0 - xq)) * ((((y0 + yq) / (x0 - xq)) ^ 2 - x0 - xq) - x0) + y0)) -
        (if k = 0 then 2 * xq else 0) := by
  have hd : x0 - xq ≠ 0 := sub_ne_zero.2 hx
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have h8 : (8 : K) ≠ 0 := by
    have : (8 : K) = 2 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h2 h4
  have hB : B = y0 ^ 2 - x0 ^ 3 - A * x0 := by linear_combination -h0
  subst hB
  have hA : A = (y0 ^ 2 - yq ^ 2 - x0 ^ 3 + xq ^ 3) / (x0 - xq) := by
    field_simp; linear_combination hq
  subst hA
  interval_cases k <;>
  · simp only [jet, cj, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_add, Nat.reduceAdd,
      pow_zero, pow_one, one_mul, if_true, if_false, OfNat.ofNat_ne_zero, one_ne_zero,
      Nat.succ_ne_zero, ↓reduceIte]
    field_simp
    ring

variable {A B : K} [DecidableEq K]

/-- Jet identity for points: the `k`-th Taylor coefficient of `φ_Q` at `x(Q₀)` is
`c_k(Q₀ + Q) + c_k(Q₀ - Q) - 2 x_Q [k = 0]`. -/
theorem jet_point {Q0 Q : (short A B).Point} (h0 : Q0 ≠ 0) (hQ : Q ≠ 0) (hx : xc Q0 ≠ xc Q)
    (hy : yc Q0 ≠ 0) (h2 : (2 : K) ≠ 0) (k : ℕ) (hk : k ≤ 3) :
    jet k (xc Q0 - xc Q) (Kernel.tQ Q) (Kernel.uQ Q) =
      cj A (xc Q0) (yc Q0) k (xc (Q0 + Q)) (yc (Q0 + Q)) +
        cj A (xc Q0) (yc Q0) k (xc (Q0 + -Q)) (yc (Q0 + -Q)) -
        (if k = 0 then 2 * xc Q else 0) := by
  have hQ' : -Q ≠ 0 := neg_ne_zero.2 hQ
  have hx' : xc Q0 ≠ xc (-Q) := by rwa [xc_neg]
  obtain ⟨e1, e2⟩ := add_coords_of_xc_ne h0 hQ hx
  obtain ⟨e3, e4⟩ := add_coords_of_xc_ne h0 hQ' hx'
  rw [e2, e4, e1, e3]
  simp only [xc_neg, yc_neg, sub_neg_eq_add, Kernel.tQ, Kernel.uQ]
  exact jet_alg A B (xc Q0) (yc Q0) (xc Q) (yc Q) (equation_xc_yc h0) (equation_xc_yc hQ) hx hy
    h2 k hk

end Velu
