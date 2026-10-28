/-
# The series `w(z)` of a Weierstrass curve (Silverman, AEC IV.1)

In the coordinates `z = -x/y`, `w = -1/y` the Weierstrass equation becomes `G(z, w) = 0` with
  `G(z, w) = z³ + a₁ z w + a₂ z² w + a₃ w² + a₄ z w² + a₆ w³ - w`.
Over any commutative ring `R` we construct `w(z) ∈ R⟦z⟧` with `w = z³ + a₁ z w + … + a₆ w³`, prove it
is the unique solution with zero constant term (even in any multivariable power series ring, and
for any power series `z` without constant term), that `z³ ∣ w` and the first coefficients
`w = z³ + a₁ z⁴ + (a₁² + a₂) z⁵ + …`, and that it commutes with base change.
-/
import Mathlib

set_option autoImplicit false

namespace EllipticFormal

open PowerSeries

variable {R : Type*} [CommRing R]

/-- the Weierstrass equation in `(z, w)`-coordinates. -/
def G {S : Type*} [CommRing S] (W : WeierstrassCurve S) (z w : S) : S :=
  z ^ 3 + W.a₁ * z * w + W.a₂ * z ^ 2 * w + W.a₃ * w ^ 2 + W.a₄ * z * w ^ 2 + W.a₆ * w ^ 3 - w

lemma map_G {S : Type*} [CommRing S] (f : R →+* S) (W : WeierstrassCurve R) (z w : R) :
    f (G W z w) = G (W.map f) (f z) (f w) := by
  simp [G]

/-! ## Uniqueness, in any multivariable power series ring -/

section Unique
variable {σ : Type*}

/-- **uniqueness**: for `z, w₁, w₂` without constant term, `G(z, w₁) = G(z, w₂) = 0` forces
`w₁ = w₂` (the derivative of `G` in `w` is a unit `≡ -1`). -/
theorem G_unique (W : WeierstrassCurve (MvPowerSeries σ R)) {z w₁ w₂ : MvPowerSeries σ R}
    (hz : MvPowerSeries.constantCoeff z = 0) (h₁ : MvPowerSeries.constantCoeff w₁ = 0)
    (h₂ : MvPowerSeries.constantCoeff w₂ = 0) (e₁ : G W z w₁ = 0) (e₂ : G W z w₂ = 0) :
    w₁ = w₂ := by
  set U := W.a₁ * z + W.a₂ * z ^ 2 + W.a₃ * (w₁ + w₂) + W.a₄ * z * (w₁ + w₂) +
    W.a₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2) - 1 with hU
  have hfac : G W z w₁ - G W z w₂ = (w₁ - w₂) * U := by rw [hU]; simp only [G]; ring
  have hu : IsUnit U := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, hU]
    simp [hz, h₁, h₂]
  rw [e₁, e₂, sub_zero, eq_comm] at hfac
  have := (hu.mul_left_eq_zero).1 hfac
  exact sub_eq_zero.1 this

end Unique

/-! ## Existence: iteration of the contraction `Φ` -/

section Exist
variable (W : WeierstrassCurve R)

/-- the curve with coefficients viewed as constant power series. -/
noncomputable abbrev WC : WeierstrassCurve R⟦X⟧ := W.map (C (R := R))

/-- `Φ(f) = z³ + a₁ z f + a₂ z² f + a₃ f² + a₄ z f² + a₆ f³`. -/
noncomputable def Φ (f : R⟦X⟧) : R⟦X⟧ := f + G (WC W) X f

lemma Φ_eq (f : R⟦X⟧) : Φ W f = X ^ 3 + C W.a₁ * X * f + C W.a₂ * X ^ 2 * f + C W.a₃ * f ^ 2 +
    C W.a₄ * X * f ^ 2 + C W.a₆ * f ^ 3 := by
  simp only [Φ, G, WC, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]; ring

lemma cc_Φ {f : R⟦X⟧} (hf : constantCoeff f = 0) : constantCoeff (Φ W f) = 0 := by
  rw [Φ_eq]; simp [hf]

/-- the contraction estimate: `X^k ∣ f - g ⇒ X^(k+1) ∣ Φ f - Φ g`. -/
lemma Φ_sub_dvd {f g : R⟦X⟧} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) {k : ℕ}
    (h : X ^ k ∣ f - g) : X ^ (k + 1) ∣ Φ W f - Φ W g := by
  have e : Φ W f - Φ W g = (f - g) * (C W.a₁ * X + C W.a₂ * X ^ 2 + C W.a₃ * (f + g) +
      C W.a₄ * X * (f + g) + C W.a₆ * (f ^ 2 + f * g + g ^ 2)) := by rw [Φ_eq, Φ_eq]; ring
  rw [e, pow_succ]
  apply mul_dvd_mul h
  rw [X_dvd_iff]; simp [hf, hg]

/-- the iterates `Φ^[n] 0`. -/
noncomputable def u (n : ℕ) : R⟦X⟧ := (Φ W)^[n] 0

lemma u_succ (n : ℕ) : u W (n + 1) = Φ W (u W n) := Function.iterate_succ_apply' _ _ _

lemma cc_u (n : ℕ) : constantCoeff (u W n) = 0 := by
  induction n with
  | zero => simp [u]
  | succ n ih => rw [u_succ]; exact cc_Φ W ih

lemma u_dvd_succ (n : ℕ) : X ^ n ∣ u W (n + 1) - u W n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := Φ_sub_dvd W (cc_u W _) (cc_u W _) ih
    rwa [← u_succ, ← u_succ] at this

lemma u_dvd (n m : ℕ) (h : n ≤ m) : X ^ n ∣ u W m - u W n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have : u W (m + 1) - u W n = (u W (m + 1) - u W m) + (u W m - u W n) := by ring
    rw [this]
    exact dvd_add ((pow_dvd_pow X hm).trans (u_dvd_succ W m)) ih

/-- **the series `w(z)`**. -/
noncomputable def w : R⟦X⟧ := PowerSeries.mk fun n => coeff n (u W (n + 1))

lemma w_sub_u_dvd (N : ℕ) : X ^ N ∣ w W - u W N := by
  rw [X_pow_dvd_iff]
  intro m hm
  have h := u_dvd W (m + 1) N hm
  rw [X_pow_dvd_iff] at h
  have := h m (Nat.lt_succ_self m)
  rw [map_sub, sub_eq_zero] at this
  simp [w, this]

lemma cc_w : constantCoeff (w W) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, w, coeff_mk, coeff_zero_eq_constantCoeff_apply,
    cc_u]

/-- **the defining equation** `w = z³ + a₁ z w + a₂ z² w + a₃ w² + a₄ z w² + a₆ w³`. -/
theorem w_fixed : Φ W (w W) = w W := by
  rw [← sub_eq_zero]
  ext N
  have h1 := Φ_sub_dvd W (cc_w W) (cc_u W N) (w_sub_u_dvd W N)
  have h2 := w_sub_u_dvd W (N + 1)
  rw [← u_succ] at h1
  have : Φ W (w W) - w W = (Φ W (w W) - u W (N + 1)) - (w W - u W (N + 1)) := by ring
  rw [this]
  have h := dvd_sub h1 h2
  rw [X_pow_dvd_iff] at h
  simpa using h N (Nat.lt_succ_self N)

theorem G_w : G (WC W) X (w W) = 0 := by
  have := w_fixed W
  rw [Φ] at this
  linear_combination this

theorem w_eq : w W = X ^ 3 + C W.a₁ * X * w W + C W.a₂ * X ^ 2 * w W + C W.a₃ * w W ^ 2 +
    C W.a₄ * X * w W ^ 2 + C W.a₆ * w W ^ 3 := by
  conv_lhs => rw [← w_fixed W]
  exact Φ_eq W _

/-- uniqueness of `w` among series without constant term. -/
theorem w_unique {f : R⟦X⟧} (hf : constantCoeff f = 0) (h : G (WC W) X f = 0) : f = w W :=
  G_unique (σ := Unit) (WC W) (z := X) (PowerSeries.constantCoeff_X (R := R)) hf (cc_w W) h (G_w W)

lemma X3_dvd_u (n : ℕ) : X ^ 3 ∣ u W n := by
  induction n with
  | zero => simp [u]
  | succ n ih =>
    rw [u_succ, Φ_eq]
    obtain ⟨g, hg⟩ := ih
    rw [hg]
    exact ⟨1 + C W.a₁ * X * g + C W.a₂ * X ^ 2 * g + C W.a₃ * X ^ 3 * g ^ 2 +
      C W.a₄ * X ^ 4 * g ^ 2 + C W.a₆ * X ^ 6 * g ^ 3, by ring⟩

/-- `z³ ∣ w`. -/
theorem X3_dvd_w : X ^ 3 ∣ w W := by
  have h := w_sub_u_dvd W 3
  have : w W = (w W - u W 3) + u W 3 := by ring
  rw [this]; exact dvd_add h (X3_dvd_u W 3)

/-- `w = z³ · v` with `v` a unit series `1 + …`. -/
noncomputable def v : R⟦X⟧ := (X3_dvd_w W).choose

theorem w_eq_X3_mul_v : w W = X ^ 3 * v W := (X3_dvd_w W).choose_spec

lemma coeff_w_of_lt {n : ℕ} (hn : n < 3) : coeff n (w W) = 0 := by
  have := X3_dvd_w W
  rw [X_pow_dvd_iff] at this
  exact this n hn

lemma coeff_w_sq_of_lt {n : ℕ} (hn : n < 6) : coeff n (w W ^ 2) = 0 := by
  have h : X ^ 6 ∣ w W ^ 2 := by
    rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul]; exact pow_dvd_pow_of_dvd (X3_dvd_w W) 2
  rw [X_pow_dvd_iff] at h
  exact h n hn

lemma coeff_w_cube_of_lt {n : ℕ} (hn : n < 9) : coeff n (w W ^ 3) = 0 := by
  have h : X ^ 9 ∣ w W ^ 3 := by
    rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul]; exact pow_dvd_pow_of_dvd (X3_dvd_w W) 3
  rw [X_pow_dvd_iff] at h
  exact h n hn

/-- the coefficient recursion for `n < 6`, where the quadratic and cubic terms do not contribute. -/
lemma coeff_w_small (n : ℕ) (hn : n < 4) : coeff (n + 2) (w W) =
    coeff (n + 2) (X ^ 3 : R⟦X⟧) + W.a₁ * coeff (n + 1) (w W) + W.a₂ * coeff n (w W) := by
  conv_lhs => rw [w_eq W]
  have e1 : C W.a₁ * X * w W = C W.a₁ * (X * w W) := by ring
  have e2 : C W.a₂ * X ^ 2 * w W = C W.a₂ * (X * (X * w W)) := by ring
  have e3 : C W.a₄ * X * w W ^ 2 = C W.a₄ * (X * w W ^ 2) := by ring
  rw [e1, e2, e3]
  simp only [map_add, coeff_C_mul, coeff_succ_X_mul]
  rw [coeff_w_sq_of_lt W (n := n + 2) (by omega), coeff_w_cube_of_lt W (n := n + 2) (by omega)]
  have : coeff (n + 1) (w W ^ 2) = 0 := coeff_w_sq_of_lt W (n := n + 1) (by omega)
  rw [this]; ring

theorem coeff_three_w : coeff 3 (w W) = 1 := by
  rw [coeff_w_small W 1 (by norm_num), coeff_w_of_lt W (by norm_num),
    coeff_w_of_lt W (by norm_num), coeff_X_pow]; simp

theorem coeff_four_w : coeff 4 (w W) = W.a₁ := by
  rw [coeff_w_small W 2 (by norm_num), coeff_three_w, coeff_w_of_lt W (by norm_num), coeff_X_pow]
  simp

theorem coeff_five_w : coeff 5 (w W) = W.a₁ ^ 2 + W.a₂ := by
  rw [coeff_w_small W 3 (by norm_num), coeff_four_w, coeff_three_w, coeff_X_pow]; simp; ring

theorem cc_v : constantCoeff (v W) = 1 := by
  have h := coeff_three_w W
  rw [w_eq_X3_mul_v, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    coeff_zero_eq_constantCoeff_apply] at h
  exact h

/-! ## Base change -/

theorem map_w {S : Type*} [CommRing S] (f : R →+* S) : PowerSeries.map f (w W) = w (W.map f) := by
  apply w_unique
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, cc_w,
      map_zero]
  · have := congrArg (PowerSeries.map f) (G_w W)
    rw [map_G, map_zero] at this
    convert this using 2
    · simp only [WC, WeierstrassCurve.map_map]
      congr 1
      ext r : 1
      simp
    · simp

end Exist

end EllipticFormal
