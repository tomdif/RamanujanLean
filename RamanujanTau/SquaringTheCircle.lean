/-
# Ramanujan's "Squaring the Circle" (1913): the accuracy bound

Ramanujan's compass-and-straightedge construction produces a length `RD = (d/2)·√(355/113)`, approximating
the side `(d/2)·√π` of a square equal in area to a circle of diameter `d`. Exact squaring is impossible
(Lindemann 1882), so this is an approximation — and a spectacularly good one, riding on the rational
approximation `355/113 ≈ π` (Zu Chongzhi's Milü).

This file certifies the accuracy: the side-length discrepancy per unit diameter is `(1/2)|√(355/113) − √π|`,
and we prove `|√(355/113) − √π| < 10⁻⁶`. The proof reduces the square-root discrepancy to the *rational*
discrepancy via `(√a − √b)(√a + √b) = a − b` with `√a + √b > 1`, then bounds `|355/113 − π|` by Mathlib's
π-digit bounds. No `sorry`.
-/
import Mathlib.Analysis.Real.Pi.Bounds

namespace Ramanujan

/-- the rational approximation itself: `|355/113 − π| < 10⁻⁶` (Milü agrees with π to six places). -/
theorem milu_approx_pi : |(355 : ℝ) / 113 - Real.pi| < 1 / 10 ^ 6 := by
  have hlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hhi : Real.pi < 3.141593 := Real.pi_lt_d6
  rw [abs_lt]
  constructor <;> [linarith; linarith]

/-- the square-root discrepancy is dominated by the rational one, since `√a + √b > 1`:
`|√(355/113) − √π| ≤ |355/113 − π|`. -/
theorem abs_sqrt_sub_sqrt_le :
    |Real.sqrt (355 / 113) - Real.sqrt Real.pi| ≤ |(355 : ℝ) / 113 - Real.pi| := by
  have hapos : (0 : ℝ) ≤ 355 / 113 := by norm_num
  have hπpos : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hsa : (1 : ℝ) ≤ Real.sqrt (355 / 113) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt (by norm_num)
  have hsb : (1 : ℝ) ≤ Real.sqrt Real.pi := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hfactor : (Real.sqrt (355 / 113) - Real.sqrt Real.pi)
      * (Real.sqrt (355 / 113) + Real.sqrt Real.pi) = 355 / 113 - Real.pi := by
    rw [mul_comm, ← sq_sub_sq, Real.sq_sqrt hapos, Real.sq_sqrt hπpos]
  calc |Real.sqrt (355 / 113) - Real.sqrt Real.pi|
      ≤ |Real.sqrt (355 / 113) - Real.sqrt Real.pi|
          * (Real.sqrt (355 / 113) + Real.sqrt Real.pi) :=
        le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    _ = |(Real.sqrt (355 / 113) - Real.sqrt Real.pi)
          * (Real.sqrt (355 / 113) + Real.sqrt Real.pi)| := by
        rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ Real.sqrt (355 / 113) + Real.sqrt Real.pi by
          linarith)]
    _ = |(355 : ℝ) / 113 - Real.pi| := by rw [hfactor]

/-- **Ramanujan's squaring-the-circle accuracy:** the constructed side `√(355/113)` (per unit diameter)
differs from the true `√π` by less than `10⁻⁶`. -/
theorem ramanujan_squaring_accuracy :
    |Real.sqrt (355 / 113) - Real.sqrt Real.pi| < 1 / 10 ^ 6 :=
  lt_of_le_of_lt abs_sqrt_sub_sqrt_le milu_approx_pi

end Ramanujan
