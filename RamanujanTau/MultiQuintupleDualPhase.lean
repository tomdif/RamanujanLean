/-
# The antipodal phase law for Poisson-dual Watson amplitudes

For a projective dual vector `w`, write

  u = ((i,j,k) dot w) / p.

The eight branch phases factor as `zeta^C * product_s (1-zeta^delta_s)`.
Replacing `w` by `-w` conjugates this expression.  Once the three support
factors are nonzero, the antipodal pair cancels precisely when

  2*C + delta_1 + delta_2 + delta_3 = 0  (mod 6p).

The main result below reduces that condition to one linear congruence modulo
`p`:

  2*u + q*w3*(2*R-i-j-k) = 0  (mod p).

This is the phase hyperplane behind the long collinear and coplanar false
prefixes in fixed dual-shell scans.  The proof here is entirely integral; a
future analytic Poisson bridge only has to connect this finite phase law to
the corresponding root-of-unity amplitudes.
-/
import RamanujanTau.MultiQuintupleDualSpanning

namespace Ramanujan.MultiQuintuple

/-- The branch-independent phase in one factored dual amplitude. -/
def dualWatsonBasePhase
    (q R u w1 w2 w3 : ℤ) : ℤ :=
  6 * w3 * q * R + 6 * u - (w1 + w2 + w3)

/-- The exponent comparing the amplitudes of `w` and `-w`. -/
def dualWatsonAntipodalPhase
    (q i j k R u w1 w2 w3 : ℤ) : ℤ :=
  2 * dualWatsonBasePhase q R u w1 w2 w3 +
    dualWatsonDelta q i w3 w1 +
    dualWatsonDelta q j w3 w2 +
    dualWatsonDelta q k w3 w3

/-- The reduced linear phase functional modulo `p`. -/
def dualWatsonPairLinear
    (q i j k R u w3 : ℤ) : ℤ :=
  2 * u + w3 * q * (2 * R - (i + j + k))

/-- All dependence on `w1+w2+w3` cancels from the antipodal comparison. -/
theorem dualWatsonAntipodalPhase_eq_six_mul_pairLinear
    (q i j k R u w1 w2 w3 : ℤ) :
    dualWatsonAntipodalPhase q i j k R u w1 w2 w3 =
      6 * dualWatsonPairLinear q i j k R u w3 := by
  simp only [dualWatsonAntipodalPhase, dualWatsonBasePhase,
    dualWatsonDelta, dualWatsonPairLinear]
  ring

/-- Cancelling the common factor six converts the `6p` phase condition into
one congruence modulo `p`. -/
theorem six_mul_dvd_six_mul_iff (p x : ℤ) :
    6 * p ∣ 6 * x ↔ p ∣ x := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply mul_left_cancel₀ (by norm_num : (6 : ℤ) ≠ 0)
    nlinarith
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    ring

/-- **Exact antipodal phase law.**

The phase comparison for `w` and `-w` vanishes modulo `6p` exactly when the
reduced linear functional vanishes modulo `p`. -/
theorem dualWatsonAntipodalPhase_dvd_iff
    (p q i j k R u w1 w2 w3 : ℤ) :
    6 * p ∣ dualWatsonAntipodalPhase q i j k R u w1 w2 w3 ↔
      p ∣ dualWatsonPairLinear q i j k R u w3 := by
  rw [dualWatsonAntipodalPhase_eq_six_mul_pairLinear,
    six_mul_dvd_six_mul_iff]

/-- The quotient `u` of the projective pairing is forced by a projective lift
and isotropy. -/
theorem projectiveDual_pairingQuotient
    (p lambda i j k w1 w2 w3 z1 z2 z3 h u : ℤ)
    (hp : p ≠ 0)
    (hw1 : w1 = lambda * i + p * z1)
    (hw2 : w2 = lambda * j + p * z2)
    (hw3 : w3 = lambda * k + p * z3)
    (hisotropic : ternaryNorm i j k = p * h)
    (hpairing : ternaryDot i j k w1 w2 w3 = p * u) :
    u = lambda * h + ternaryDot i j k z1 z2 z3 := by
  have hlift := projectiveLift_dot
    p lambda i j k w1 w2 w3 z1 z2 z3 i j k hw1 hw2 hw3
  have hself : ternaryDot i j k i j k = p * h := by
    simpa only [ternaryDot, ternaryNorm, pow_two] using hisotropic
  have hmul :
      p * u = p * (lambda * h + ternaryDot i j k z1 z2 z3) := by
    calc
      p * u = ternaryDot i j k w1 w2 w3 := hpairing.symm
      _ = lambda * ternaryDot i j k i j k +
          p * ternaryDot i j k z1 z2 z3 := hlift
      _ = p * (lambda * h + ternaryDot i j k z1 z2 z3) := by
        rw [hself]
        ring
  exact mul_left_cancel₀ hp hmul

/-- In centered projective-lift coordinates, the pair law is an affine linear
hyperplane plus an explicit multiple of `p`. -/
theorem dualWatsonPairLinear_projectiveLift
    (p q i j k R lambda h z1 z2 z3 u w3 : ℤ)
    (hu : u = lambda * h + ternaryDot i j k z1 z2 z3)
    (hw3 : w3 = lambda * k + p * z3) :
    dualWatsonPairLinear q i j k R u w3 =
      (2 * lambda * h + 2 * ternaryDot i j k z1 z2 z3 +
        lambda * k * q * (2 * R - (i + j + k))) +
      p * (z3 * q * (2 * R - (i + j + k))) := by
  simp only [dualWatsonPairLinear]
  rw [hu, hw3]
  ring

/-- Therefore divisibility of the pair phase depends only on the displayed
projective-lift hyperplane modulo `p`. -/
theorem dualWatsonPairLinear_projectiveLift_dvd_iff
    (p q i j k R lambda h z1 z2 z3 u w3 : ℤ)
    (hu : u = lambda * h + ternaryDot i j k z1 z2 z3)
    (hw3 : w3 = lambda * k + p * z3) :
    p ∣ dualWatsonPairLinear q i j k R u w3 ↔
      p ∣ 2 * lambda * h + 2 * ternaryDot i j k z1 z2 z3 +
        lambda * k * q * (2 * R - (i + j + k)) := by
  rw [dualWatsonPairLinear_projectiveLift
    p q i j k R lambda h z1 z2 z3 u w3 hu hw3]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c - z3 * q * (2 * R - (i + j + k)), ?_⟩
    nlinarith
  · rintro ⟨c, hc⟩
    refine ⟨c + z3 * q * (2 * R - (i + j + k)), ?_⟩
    nlinarith

end Ramanujan.MultiQuintuple
