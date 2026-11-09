/-
# Entry 3.22: `G(−q)G(−q⁴) + qH(−q)H(−q⁴) = χ(q²)`

This is the first proof in Berndt et al. §25. Watson's Lemma 4.1 ((4.23) `lemma41a`, (4.24) `lemma41b`), substituted
into Entry 3.5, gives `G(q)G(−q⁴) − qH(q)H(−q⁴) = χ(q²)`. Then `q ↦ −q` gives the entry.
-/
import RamanujanTau.Forty.W41b
import RamanujanTau.Forty.E05

set_option autoImplicit false

namespace Forty
open PowerSeries
open RankProof (Pinf isUnit_Pinf)

/-- Entry 3.22 at `−q`: `G(q)G(−q⁴) − qH(q)H(−q⁴) = χ(q²)`. -/
theorem entry_3_22_neg : G * S 4 (Ng G) - X * H * S 4 (Ng H) = chip 2 := by
  have h5 := entry_3_5
  have a := lemma41a
  have b := lemma41b
  apply mul_left_cancel₀ (Pinf_ne 8 8 (by norm_num) (by norm_num))
  linear_combination (-G) * b + H * a + Pinf 8 8 * h5

/-- **Entry 3.22** (Bressoud; Watson's Lemma 4.1): `G(−q)G(−q⁴) + qH(−q)H(−q⁴) = χ(q²)`. -/
theorem entry_3_22 : Ng G * S 4 (Ng G) + X * Ng H * S 4 (Ng H) = chip 2 := by
  have h := congrArg Ng entry_3_22_neg
  rw [map_sub, map_mul, map_mul, map_mul, Ng_S_ev 4 (by norm_num), Ng_S_ev 4 (by norm_num), Ng_X, chip,
    Ng_S_ev 2 (by norm_num)] at h
  rw [chip]
  linear_combination h

end Forty
