/-
# Level-21 theta atoms and normalized Weierstrass instances

With `q = t^N`, `N = 21 d`, put `Q = t^d` and `J a = θ(Q^a; Q^{21})`. Every `θ(Q^e)` normalizes to
`± Q^m J_r` with `0 ≤ r ≤ 10` (quasi-periodicity + reflection), so each Weierstrass instance becomes a
polynomial relation among `J 1, …, J 10` and `Q`. Theta identities of level 21 are then proved by
`linear_combination` of such instances (certificates found offline).
-/
import RamanujanTau.ALTheta
import RamanujanTau.ALSplitM

set_option autoImplicit false

namespace ALz
open HahnSeries

section ThetaCore
variable {N : ℕ} (hN : 1 ≤ N) {d : ℕ} (hd : N = 21 * d)
include hN hd

/-- `J a = θ(Q^a; Q^{21})`. -/
noncomputable def Jt (_hd : N = 21 * d) (a : ℤ) : L := θ hN (d * a) 1

/-- `Q = t^d`. -/
noncomputable def Qt (_hd : N = 21 * d) : L := mono d 1

omit hN in
lemma Qt_zpow (m : ℤ) : (Qt hd) ^ m = mono (d * m) 1 := by
  rw [Qt, mono_zpow, one_zpow, mul_comm]

omit hN in
lemma Qt_ne : Qt hd ≠ 0 := by
  rw [Qt, Ne, mono, single_eq_zero_iff]; exact one_ne_zero

lemma d_pos : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; omega
  · exact h

/-- quasi-periodicity in `Q`-units. -/
theorem Jt_shift (a j : ℤ) :
    θ hN (d * (a + 21 * j)) 1 = (-1) ^ j * (Qt hd) ^ (-(21 * c2 (j + 1)) - a * j + 21 * j) * Jt hN hd a := by
  have h := θ_qshift hN (d * a) (one_ne_zero) j
  rw [show (d : ℤ) * (a + 21 * j) = d * a + N * j by rw [hd]; push_cast; ring, h, Qt_zpow, Jt, one_zpow,
    mul_one]
  congr 1
  rw [show (-1 : L) ^ j = mono 0 ((-1 : ℂ) ^ j) by
    rw [show (-1 : L) = mono 0 (-1) by rw [mono]; exact (single_neg _ _).symm]
    rw [mono_zpow, mul_zero]]
  rw [mono_mul, zero_add, mul_one]
  congr 1; rw [hd]; push_cast; ring

/-- reflection `θ(Q^{21-a}) = θ(Q^a)`. -/
theorem Jt_refl (a : ℤ) : θ hN (d * (21 - a)) 1 = Jt hN hd a := by
  have h := θ_reflect hN (d * a) (one_ne_zero (α := ℂ))
  rw [inv_one] at h
  rw [Jt, ← h]; congr 1; rw [hd]; push_cast; ring

omit hd in
theorem Jt_zero : θ hN (d * 0) 1 = 0 := by
  rw [mul_zero]; exact θ_one hN

theorem Jt_ne {a : ℤ} (h0 : 0 < a) (h1 : a < 21) : Jt hN hd a ≠ 0 := by
  have := d_pos hN hd
  refine θ_ne hN ?_ ?_ 1
  · positivity
  · rw [hd]; push_cast; nlinarith

/-- Weierstrass in `Q`-units. -/
theorem weierQ {x y u v : ℤ} (h1 : 0 < u) (h12 : u < v) (h2 : 2 * v < 21) :
    θ hN (d * (x + y)) 1 * θ hN (d * (x - y)) 1 * θ hN (d * (u + v)) 1 * θ hN (d * (u - v)) 1
      - θ hN (d * (x + v)) 1 * θ hN (d * (x - v)) 1 * θ hN (d * (u + y)) 1 * θ hN (d * (u - y)) 1
      = (Qt hd) ^ (u - y) * θ hN (d * (y + v)) 1 * θ hN (d * (y - v)) 1 *
          θ hN (d * (x + u)) 1 * θ hN (d * (x - u)) 1 := by
  have hd0 := d_pos hN hd
  have h := weierstrass hN (by' := d * y) (bu := d * u) (bv := d * v) (bx := d * x) one_ne_zero one_ne_zero
    one_ne_zero one_ne_zero (by positivity) (by nlinarith) (by rw [hd]; push_cast; nlinarith)
  simp only [mul_one, inv_one] at h
  rw [Qt_zpow]
  simp only [mul_add, mul_sub]
  exact h

/-- normal form of `θ(Q^e)`: `e = r + 21 j`, `r = 21 - R` (or `r = R`). -/
theorem Jt_norm (e r j m R : ℤ) (s : L) (h1 : e = r + 21 * j) (h2 : m = -(21 * c2 (j + 1)) - r * j + 21 * j)
    (h3 : r = R ∨ r = 21 - R) (hs : (-1 : L) ^ j = s) :
    θ hN (d * e) 1 = s * (Qt hd) ^ m * Jt hN hd R := by
  subst h1 h2
  rw [Jt_shift hN hd, hs]
  rcases h3 with h | h
  · rw [h]
  · rw [Jt, h, Jt_refl hN hd]

theorem Jt_norm0 (e j : ℤ) (h1 : e = 21 * j) : θ hN (d * e) 1 = 0 := by
  subst h1
  rw [show (d : ℤ) * (21 * j) = N * j by rw [hd]; push_cast; ring]
  exact θ_qpow hN j

end ThetaCore
end ALz
