import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Vélu: truncated inverses modulo `s⁶`

In a commutative ring with `s⁶ = 0` and `e d = 1`, `e + s` is invertible with inverse the
truncated geometric series `ivt d s`, and the partial fractions `t/(e+s) + u/(e+s)²` (and their
derivatives) agree with their `4`-jets after multiplication by `s²` (resp. `s³`).
-/

namespace Velu

/-- `d (1 - sd + (sd)² - … - (sd)⁵)`, the inverse of `e + s` modulo `s⁶` when `ed = 1`. -/
def ivt {𝔸 : Type*} [CommRing 𝔸] (d s : 𝔸) : 𝔸 :=
  d * (1 - s * d + (s * d) ^ 2 - (s * d) ^ 3 + (s * d) ^ 4 - (s * d) ^ 5)

variable {𝔸 : Type*} [CommRing 𝔸]

theorem ivt_spec (e d s : 𝔸) (hed : e * d = 1) (hs : s ^ 6 = 0) : (e + s) * ivt d s = 1 := by
  unfold ivt
  linear_combination (-d^5*s^5 + d^4*s^4 - d^3*s^3 + d^2*s^2 - d*s + 1) * hed + (-d^6) * hs

theorem N_term (a b e d s E : 𝔸) (hed : e * d = 1) (hs : s ^ 6 = 0) :
    (a * (e + s) + b) * (ivt d s * s * E) ^ 2 =
      E ^ 2 * s ^ 2 * ((a * d + b * d ^ 2) + (-(a * d ^ 2 + 2 * b * d ^ 3)) * s +
        (a * d ^ 3 + 3 * b * d ^ 4) * s ^ 2 + (-(a * d ^ 4 + 4 * b * d ^ 5)) * s ^ 3) := by
  unfold ivt
  linear_combination (E^2*a*d^11*s^12 - 2*E^2*a*d^10*s^11 + 3*E^2*a*d^9*s^10 - 4*E^2*a*d^8*s^9 + 5*E^2*a*d^7*s^8 - 6*E^2*a*d^6*s^7 + 5*E^2*a*d^5*s^6 - 4*E^2*a*d^4*s^5 + 3*E^2*a*d^3*s^4 - 2*E^2*a*d^2*s^3 + E^2*a*d*s^2) * hed + (E^2*a*d^12*s^7 - E^2*a*d^11*s^6 + E^2*a*d^10*s^5 - E^2*a*d^9*s^4 + E^2*a*d^8*s^3 - E^2*a*d^7*s^2 - E^2*a*d^6*s + E^2*a*d^5 + E^2*b*d^12*s^6 - 2*E^2*b*d^11*s^5 + 3*E^2*b*d^10*s^4 - 4*E^2*b*d^9*s^3 + 5*E^2*b*d^8*s^2 - 6*E^2*b*d^7*s + 5*E^2*b*d^6) * hs

theorem N1_term (a b e d s E : 𝔸) (hed : e * d = 1) (hs : s ^ 6 = 0) :
    (a * (e + s) + 2 * b) * (ivt d s * s * E) ^ 3 =
      -(E ^ 3 * s ^ 3 * ((-(a * d ^ 2 + 2 * b * d ^ 3)) + 2 * (a * d ^ 3 + 3 * b * d ^ 4) * s +
        3 * (-(a * d ^ 4 + 4 * b * d ^ 5)) * s ^ 2)) := by
  unfold ivt
  linear_combination (-E^3*a*d^17*s^18 + 3*E^3*a*d^16*s^17 - 6*E^3*a*d^15*s^16 + 10*E^3*a*d^14*s^15 - 15*E^3*a*d^13*s^14 + 21*E^3*a*d^12*s^13 - 25*E^3*a*d^11*s^12 + 27*E^3*a*d^10*s^11 - 27*E^3*a*d^9*s^10 + 25*E^3*a*d^8*s^9 - 21*E^3*a*d^7*s^8 + 15*E^3*a*d^6*s^7 - 10*E^3*a*d^5*s^6 + 6*E^3*a*d^4*s^5 - 3*E^3*a*d^3*s^4 + E^3*a*d^2*s^3) * hed + (-E^3*a*d^18*s^13 + 2*E^3*a*d^17*s^12 - 3*E^3*a*d^16*s^11 + 4*E^3*a*d^15*s^10 - 5*E^3*a*d^14*s^9 + 6*E^3*a*d^13*s^8 - 4*E^3*a*d^12*s^7 + 2*E^3*a*d^11*s^6 - 2*E^3*a*d^9*s^4 + 4*E^3*a*d^8*s^3 - 6*E^3*a*d^7*s^2 + 5*E^3*a*d^6*s - 4*E^3*a*d^5 - 2*E^3*b*d^18*s^12 + 6*E^3*b*d^17*s^11 - 12*E^3*b*d^16*s^10 + 20*E^3*b*d^15*s^9 - 30*E^3*b*d^14*s^8 + 42*E^3*b*d^13*s^7 - 50*E^3*b*d^12*s^6 + 54*E^3*b*d^11*s^5 - 54*E^3*b*d^10*s^4 + 50*E^3*b*d^9*s^3 - 42*E^3*b*d^8*s^2 + 30*E^3*b*d^7*s - 20*E^3*b*d^6) * hs

end Velu
