import RamanujanTau.ThetaLift.ChiTheta

/-!
# Poisson summation in the third lattice variable

The lattice side of the Shimura kernel, with `Q^λ` replaced by a generating exponential, is Gaussian
in the variable `c`. Mathlib's quadratic Poisson formula evaluates this sum as a sum over the dual
variable `m`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex
open scoped Real

noncomputable section

/-- **Poisson summation in `c`.** -/
theorem poisson_c {κ : ℝ} (hκ : 0 < κ) (τ₁ τ₂ : ℝ) (s Y : ℂ) :
    ∑' c : ℤ, cexp (s * (c + τ₁ + I * τ₂) - κ * (((c : ℂ) + τ₁) ^ 2 + τ₂ ^ 2) - 2 * π * I * c * Y) =
      ((√(π / κ) : ℝ) : ℂ) * ∑' m : ℤ, cexp (s * I * τ₂ - κ * τ₂ ^ 2 + 2 * π * I * τ₁ * (Y + m) +
        s ^ 2 / (4 * κ) - π * I * s * (Y + m) / κ - π ^ 2 * (Y + m) ^ 2 / κ) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hκC : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  let A : ℂ := (κ : ℂ) / π
  have hA : 0 < A.re := by
    have : A = ((κ / π : ℝ) : ℂ) := by simp [A]
    rw [this, Complex.ofReal_re]
    positivity
  let B : ℂ := (s - 2 * κ * τ₁ - 2 * π * I * Y) / (2 * π)
  let C : ℂ := s * (τ₁ + I * τ₂) - κ * (τ₁ ^ 2 + τ₂ ^ 2)
  have hP := Complex.tsum_exp_neg_quadratic hA B
  have hL : ∀ c : ℤ, cexp (s * (c + τ₁ + I * τ₂) - κ * (((c : ℂ) + τ₁) ^ 2 + τ₂ ^ 2) -
      2 * π * I * c * Y) = cexp C * cexp (-π * A * c ^ 2 + 2 * π * B * c) := by
    intro c
    rw [← Complex.exp_add]
    congr 1
    simp only [A, B, C]
    field_simp
    ring
  have hR : ∀ m : ℤ, cexp (s * I * τ₂ - κ * τ₂ ^ 2 + 2 * π * I * τ₁ * (Y + m) +
      s ^ 2 / (4 * κ) - π * I * s * (Y + m) / κ - π ^ 2 * (Y + m) ^ 2 / κ) =
      cexp C * cexp (-π / A * (m + I * B) ^ 2) := by
    intro m
    let X : ℂ := (s - 2 * κ * τ₁) / (2 * π)
    let W : ℂ := Y + m
    have hB : B = X - I * Y := by
      simp only [B, X]
      field_simp
    have hIB : (m : ℂ) + I * B = W + I * X := by
      rw [hB]
      simp only [W]
      linear_combination (-Y) * Complex.I_sq
    have hsq : (W + I * X) ^ 2 = W ^ 2 + 2 * I * X * W - X ^ 2 := by
      linear_combination X ^ 2 * Complex.I_sq
    rw [← Complex.exp_add]
    congr 1
    rw [hIB, hsq]
    simp only [A, C, X, W]
    field_simp
    ring
  simp_rw [hL, hR]
  rw [tsum_mul_left, tsum_mul_left, hP]
  have hsq : 1 / A ^ (1 / 2 : ℂ) = ((√(π / κ) : ℝ) : ℂ) := by
    have hApos : (0 : ℝ) < κ / π := by positivity
    have hAe : A = ((κ / π : ℝ) : ℂ) := by simp [A]
    have h12 : ((κ / π : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (((κ / π) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hApos.le]
      norm_num
    rw [hAe, h12, show (π / κ : ℝ) = (κ / π)⁻¹ by field_simp, Real.sqrt_inv, Real.sqrt_eq_rpow]
    push_cast
    rw [one_div]
  rw [hsq]
  ring

/-- **The exponent identity.** The dual exponent with `b = 0`, together with the factor from
inverting `Θ`, is the exponent of the Poincaré term. It reduces to `z - z̄ = 2iv`, power by power
in `σ`. Here `n = Nm`, `L = nz - a`, and `Lb = n z̄ - a`. -/
theorem exponent_identity {z zb v ξ y σ a n N p : ℂ} (hz : z ≠ 0) (hzb : zb ≠ 0) (hv0 : v ≠ 0)
    (hy : y ≠ 0) (hN : N ≠ 0) (hp : p ≠ 0) (hv : z - zb = 2 * I * v)
    (hL : n * z - a ≠ 0) :
    let L := n * z - a
    let Lb := n * zb - a
    let κ := p * v / (6 * N ^ 2 * y ^ 2 * z * zb)
    let s := I * σ / (N * z * y)
    let W := Lb / (N * zb)
    let τ₁ := 6 * N * a * (ξ ^ 2 - y ^ 2)
    let τ₂ := -12 * N * a * y * ξ
    let ζ₀ := ξ * L + σ / (2 * p * I)
    s * I * τ₂ - κ * τ₂ ^ 2 + 2 * p * I * τ₁ * W + s ^ 2 / (4 * κ) - p * I * s * W / κ -
        p ^ 2 * W ^ 2 / κ + 2 * p * I * (6 * ζ₀ ^ 2 / z) =
      6 * y * σ * Lb / v - 3 * σ ^ 2 * Lb / (2 * p * L * v) - 6 * p * y ^ 2 * L * Lb / v +
        2 * p * I * (6 * n * ζ₀ ^ 2 / L) := by
  intro L Lb κ s W τ₁ τ₂ ζ₀
  have hI2 : I * I = -1 := Complex.I_mul_I
  have hL0 : L ≠ 0 := hL
  have hzbe : zb = z - 2 * I * v := by rw [← hv]; ring
  have hLe : Lb = L - 2 * I * v * n := by
    simp only [L, Lb, hzbe]
    ring
  -- the three powers of σ
  have p1 : s * I * τ₂ = 12 * a * ξ * σ / z := by
    simp only [s, τ₂]
    field_simp
    linear_combination (-(a * ξ * σ)) * hI2
  have p2 : κ * τ₂ ^ 2 = 24 * p * v * a ^ 2 * ξ ^ 2 / (z * zb) := by
    simp only [κ, τ₂]
    field_simp
    ring
  have p3 : 2 * p * I * τ₁ * W = 12 * p * I * a * (ξ ^ 2 - y ^ 2) * Lb / zb := by
    simp only [τ₁, W]
    field_simp
    ring
  have hκ0 : κ ≠ 0 := by
    simp only [κ]
    exact div_ne_zero (mul_ne_zero hp hv0) (by simp [hN, hy, hz, hzb])
  have hIne : I ≠ 0 := Complex.I_ne_zero
  have p4 : s ^ 2 / (4 * κ) = -(3 * σ ^ 2 * zb / (2 * p * v * z)) := by
    have hs2 : s ^ 2 = -(σ ^ 2 / (N * z * y) ^ 2) := by
      simp only [s, div_pow, mul_pow, Complex.I_sq]
      ring
    rw [hs2]
    simp only [κ]
    field_simp
    ring
  have p5 : p * I * s * W / κ = -(6 * y * σ * Lb / v) := by
    have hIs : I * s = -(σ / (N * z * y)) := by
      simp only [s]
      rw [← mul_div_assoc, ← mul_assoc, hI2]
      ring
    rw [show p * I * s * W / κ = p * (I * s) * W / κ by ring, hIs]
    simp only [κ, W]
    field_simp
  have p6 : p ^ 2 * W ^ 2 / κ = 6 * p * y ^ 2 * Lb ^ 2 * z / (v * zb) := by
    simp only [κ, W]
    field_simp
  have hζ : ∀ B : ℂ, 2 * p * I * (6 * B * ζ₀ ^ 2) = 12 * p * I * ξ ^ 2 * L ^ 2 * B +
      12 * ξ * L * σ * B - 3 * I * σ ^ 2 * B / p := by
    intro B
    have hd : (2 * p * I) * (σ / (2 * p * I)) = σ := by field_simp
    have hd2 : (2 * p * I) * (σ / (2 * p * I)) ^ 2 = -(I * σ ^ 2 / (2 * p)) := by
      rw [div_pow, sq σ, sq (2 * p * I)]
      field_simp
      linear_combination (σ ^ 2) * hI2
    simp only [ζ₀]
    calc 2 * p * I * (6 * B * (ξ * L + σ / (2 * p * I)) ^ 2)
        = 12 * p * I * ξ ^ 2 * L ^ 2 * B + 12 * ξ * L * B * ((2 * p * I) * (σ / (2 * p * I))) +
          6 * B * ((2 * p * I) * (σ / (2 * p * I)) ^ 2) := by ring
      _ = _ := by
        rw [hd, hd2]
        field_simp
        ring
  have hA : zb / (v * z) + 2 * I / z = 1 / v := by
    field_simp
    linear_combination -hv
  have hB : Lb / (L * v) + 2 * I * n / L = 1 / v := by
    field_simp
    rw [hLe]
    ring
  have q1 : -(3 * σ ^ 2 * zb / (2 * p * v * z)) - 3 * I * σ ^ 2 / (p * z) =
      -(3 * σ ^ 2 * Lb / (2 * p * L * v)) - 3 * I * σ ^ 2 * n / (p * L) := by
    have e1 : -(3 * σ ^ 2 * zb / (2 * p * v * z)) - 3 * I * σ ^ 2 / (p * z) =
        -(3 * σ ^ 2 / (2 * p)) * (zb / (v * z) + 2 * I / z) := by
      field_simp
      ring
    have e2 : -(3 * σ ^ 2 * Lb / (2 * p * L * v)) - 3 * I * σ ^ 2 * n / (p * L) =
        -(3 * σ ^ 2 / (2 * p)) * (Lb / (L * v) + 2 * I * n / L) := by
      field_simp
      ring
    rw [e1, e2, hA, hB]
  have q2 : 12 * a * ξ * σ / z + 12 * ξ * L * σ / z = 12 * ξ * σ * n := by
    simp only [L]
    field_simp
    ring
  have hh : 2 * I * a * v + Lb * z = L * zb := by
    simp only [L, Lb]
    linear_combination (-a) * hv
  have q3 : -(12 * p * I * a * y ^ 2 * Lb / zb) - 6 * p * y ^ 2 * Lb ^ 2 * z / (v * zb) =
      -(6 * p * y ^ 2 * L * Lb / v) := by
    have e : -(12 * p * I * a * y ^ 2 * Lb / zb) - 6 * p * y ^ 2 * Lb ^ 2 * z / (v * zb) =
        -(6 * p * y ^ 2 * Lb / (v * zb)) * (2 * I * a * v + Lb * z) := by
      field_simp
      ring
    rw [e, hh]
    field_simp
  have q4 : -(24 * p * v * a ^ 2 * ξ ^ 2 / (z * zb)) + 12 * p * I * a * ξ ^ 2 * Lb / zb +
      12 * p * I * ξ ^ 2 * L ^ 2 / z = 12 * p * I * ξ ^ 2 * (n * L) := by
    have hneg : -(24 * p * v) = 12 * p * I * (z - zb) := by
      rw [hv]
      linear_combination (-(24 * p * v)) * hI2
    have inner : (z - zb) * a ^ 2 / (z * zb) + a * Lb / zb + L ^ 2 / z = n * L := by
      simp only [L, Lb]
      field_simp
      ring
    rw [← inner]
    calc -(24 * p * v * a ^ 2 * ξ ^ 2 / (z * zb)) + 12 * p * I * a * ξ ^ 2 * Lb / zb +
          12 * p * I * ξ ^ 2 * L ^ 2 / z
        = (-(24 * p * v)) * (a ^ 2 * ξ ^ 2 / (z * zb)) + 12 * p * I * a * ξ ^ 2 * Lb / zb +
          12 * p * I * ξ ^ 2 * L ^ 2 / z := by ring
      _ = _ := by rw [hneg]; ring
  have hLn : 6 * n * ζ₀ ^ 2 / L = (6 * (n / L) * ζ₀ ^ 2) := by ring
  have hzn : 6 * ζ₀ ^ 2 / z = (6 * (1 / z) * ζ₀ ^ 2) := by ring
  have hLL : L ^ 2 * (n / L) = n * L := by field_simp
  have hLL2 : L * (n / L) = n := by field_simp
  rw [p1, p2, p3, p4, p5, p6, hzn, hLn, hζ, hζ]
  rw [show 12 * p * I * ξ ^ 2 * L ^ 2 * (n / L) = 12 * p * I * ξ ^ 2 * (L ^ 2 * (n / L)) by ring, hLL,
    show 12 * ξ * L * σ * (n / L) = 12 * ξ * σ * (L * (n / L)) by ring, hLL2]
  have h3 : 3 * I * σ ^ 2 * n / (p * L) = 3 * I * σ ^ 2 * (n / L) / p := by
    field_simp
  rw [h3] at q1
  simp only [τ₁] at p3 ⊢
  linear_combination q1 + q2 + q3 + q4

end

end RamanujanTau.ThetaLift
