/-
# Entry 3.27(ii) (Watson; Berndt et al. §29, (29.17))

With `U = G(q)G(q⁴⁴) + q⁹H(q)H(q⁴⁴)` and `V = G(q⁴)G(q¹¹) + q³H(q⁴)H(q¹¹)`:
`UV + q = χ²(q)χ²(q¹¹)`.

Watson's argument is a `3 × 3` determinant: Entry 3.4 at `q⁴` and Entry 3.2 at `q¹¹` are two linear equations in
`G(q⁴⁴)`, `q⁸H(q⁴⁴)`, and so is the definition of `U`. The cofactors of the right-hand column are `V`, `−q` (by Entry
3.4) and `−χ²(q)` (by Entry 3.2). Here the elimination is one explicit linear combination.
(Berndt et al. print the middle row as `H(q⁴), −qG(q⁴)`; the right entry is `−G(q⁴)`.)
-/
import RamanujanTau.Forty.R11
import RamanujanTau.Forty.E04
import RamanujanTau.Forty.E02

set_option autoImplicit false

namespace Forty
open RankProof (Pinf)

lemma S11_chip1 : S 11 (chip 1) = chip 11 := by rw [chip, S_one]; rfl

/-- **Entry 3.27(ii)** (Watson 1933): `UV + q = χ²(q)χ²(q¹¹)`. -/
theorem entry_3_27_ii :
    (G * S 44 G + PowerSeries.X ^ 9 * H * S 44 H) * (S 4 G * S 11 G + PowerSeries.X ^ 3 * S 4 H * S 11 H)
      + PowerSeries.X = chip 1 ^ 2 * chip 11 ^ 2 := by
  have e2 := entry_3_2
  have e4 := entry_3_4
  -- Entry 3.2 at `q¹¹`, Entry 3.4 at `q⁴`
  have E3 := congrArg (S 11) entry_3_2
  have E1 := congrArg (S 4) entry_3_4
  simp only [map_add, map_sub, map_mul, map_pow, map_one, S11_chip1, S_S 11 4 44 rfl, S_S 4 11 44 rfl,
    show S 11 PowerSeries.X = PowerSeries.X ^ 11 from RankProof.Ea_X 11 _,
    show S 4 PowerSeries.X = PowerSeries.X ^ 4 from RankProof.Ea_X 4 _] at E1 E3
  linear_combination (PowerSeries.X ^ 3 * G * S 11 H - PowerSeries.X * H * S 11 G) * E1 - PowerSeries.X * e4
    + (G * S 4 G + PowerSeries.X * H * S 4 H) * E3 + chip 11 ^ 2 * e2

end Forty
