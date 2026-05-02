import RamanujanTau.Basic

/-! # Small values of `τ`

Computed via reduction in `ℤ[X]`. These are the OEIS A000594 values:
`0, 1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, ...`

Each value is checked by `decide` / `native_decide` on the explicit polynomial
truncation. For a few values we use `native_decide` because the polynomial
arithmetic is heavy; for tiny cases `decide` suffices.
-/

namespace RamanujanTau

/-- τ(2) = -24. -/
theorem tau_two : τ 2 = -24 := by native_decide

/-- τ(3) = 252. -/
theorem tau_three : τ 3 = 252 := by native_decide

/-- τ(4) = -1472. -/
theorem tau_four : τ 4 = -1472 := by native_decide

/-- τ(5) = 4830. -/
theorem tau_five : τ 5 = 4830 := by native_decide

/-- τ(6) = -6048. -/
theorem tau_six : τ 6 = -6048 := by native_decide

/-- τ(7) = -16744. -/
theorem tau_seven : τ 7 = -16744 := by native_decide

/-- τ(8) = 84480. -/
theorem tau_eight : τ 8 = 84480 := by native_decide

/-- τ(9) = -113643. -/
theorem tau_nine : τ 9 = -113643 := by native_decide

/-- τ(10) = -115920. -/
theorem tau_ten : τ 10 = -115920 := by native_decide

/-- τ(11) = 534612 — first prime index. Tests the Hecke value `τ(p)` for `p = 11`. -/
theorem tau_eleven : τ 11 = 534612 := by native_decide

/-- τ(12) = -370944. By Hecke multiplicativity this equals τ(3)·τ(4) = 252 · (-1472). -/
theorem tau_twelve : τ 12 = -370944 := by native_decide

/-- Hecke compatibility check at `n = 12 = 3·4` with `gcd(3,4) = 1`:
`τ(12) = τ(3) · τ(4)`. This is a numerical instance of multiplicativity. -/
theorem tau_mult_check_3_4 : τ 12 = τ 3 * τ 4 := by
  rw [tau_twelve, tau_three, tau_four]; decide

end RamanujanTau
