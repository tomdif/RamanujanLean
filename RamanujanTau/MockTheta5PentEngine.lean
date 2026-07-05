/-
# Euler pentagonal — stone 2/3 engine: the `E3` dilation (`q ↦ q³`) and the base-`q³` Durfee identity

The pentagonal build is the base-`q³` analogue of the triangular JTP. The base change `q ↦ q³` is
`PowerSeries.expand 3` (as the repo uses `E2 = expand 2` for base `q²`), and it turns the base-`q` Durfee
rectangle identity `durfee_rect_base : rectInf n = 1/(q;q)_∞` into its base-`q³` form for free:

  **`durfee_rect_base_q3`:**  `E3 (rectInf n) = 1/(q³;q³)_∞`.

The exponent collapse driving the pentagonal case is `3·C(k,2) + k = (3k²−k)/2 = e(k)` (the pentagonal
exponent), the base-3 analogue of the square-JTP's `2·C(k,2)+k = k²`. No `sorry`.
-/
import RamanujanTau.MockTheta5DurfeeBase
import RamanujanTau.MockTheta5JacobiFinite

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- Base change `q ↦ q³` on `ℤ⟦q⟧`, i.e. `PowerSeries.expand 3`. -/
noncomputable def E3 : PowerSeries ℤ →+* PowerSeries ℤ := (PowerSeries.expand 3 (by norm_num)).toRingHom

lemma E3_X : E3 qq = qq ^ 3 := PowerSeries.expand_X 3 (by norm_num)

/-- **base-`q³` Durfee rectangle**: `E3 (rectInf n) = 1/(q³;q³)_∞`. -/
lemma durfee_rect_base_q3 (n : ℕ) : E3 (rectInf n) = Ring.inverse (E3 qfacInf) := by
  have hu : IsUnit (E3 qfacInf) := isUnit_qfacInf.map E3
  have h2 : E3 (rectInf n) * E3 qfacInf = 1 := by
    rw [← map_mul, durfee_rect_base, Ring.inverse_mul_cancel qfacInf isUnit_qfacInf, map_one]
  calc E3 (rectInf n)
      = E3 (rectInf n) * (E3 qfacInf * Ring.inverse (E3 qfacInf)) := by
        rw [Ring.mul_inverse_cancel _ hu, mul_one]
    _ = E3 (rectInf n) * E3 qfacInf * Ring.inverse (E3 qfacInf) := by ring
    _ = Ring.inverse (E3 qfacInf) := by rw [h2, one_mul]

end MockTheta5.JTP
