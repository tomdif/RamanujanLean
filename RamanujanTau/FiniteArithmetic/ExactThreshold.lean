import RamanujanTau.BLBound.Threshold
import RamanujanTau.FiniteArithmetic.Complete29
import RamanujanTau.FiniteArithmetic.Complete31

/-!
# Boylan–Webb's threshold at 29 and 31, at every precision

`b₂₉(m) = b₃₁(m) = 2m - 1` for every `m ≥ 1`, with `b_ℓ(m)` the literal Boylan–Webb
invariant `BLBound.bEll`: the least odd `b` for which `X : Λ^odd(b, m) → Λ^odd(b+2, m)`
is a bijection.

Boylan–Webb computed `b₂₉(m)` for `m ≤ 3`. The inputs are the certified error
recurrences behind `Complete29` and `Complete31`, fed to `BLBound.not_mem_of_errors`.
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic

namespace Exact31
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal AllPowers31 Error31 ErrorDynamics31
  Sharp31

lemma obs_odd (n : ℕ) : PadicInt.toZMod (obs (Ll 31 (2 * n + 1))) ≠ 0 := by
  rw [obs_reduce, odd_reduction, ← PowerSeries.smul_eq_C_mul, map_smul, obs_f, smul_eq_mul]
  exact mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero n (by decide))) (by decide)

lemma obs_even (n : ℕ) : PadicInt.toZMod (obs (Ulin 31 (Ll 31 (2 * n + 1)))) = 0 := by
  rw [obs_reduce]
  change obsBar (PowerSeries.map (PadicInt.toZMod (p := 31)) (U 31 (Ll 31 (2 * n + 1)))) = 0
  rw [map_U, odd_reduction, U_C_mul, Cert31.even_step, ← PowerSeries.smul_eq_C_mul, map_smul,
    obs_g, smul_zero]

/-- **`b₃₁(m) = 2m - 1` for every `m ≥ 1`.** -/
theorem bEll_31 (m : ℕ) (hm : 1 ≤ m) : BLBound.bEll 31 m = 2 * m - 1 := by
  obtain ⟨κ, -, G, hmem, hrec, heven, hstep⟩ := normalized_errors
  have hobs : ∀ n, PadicInt.toZMod (obs (Ulin 31 (G n))) = 24 * (2 : ZMod 31) ^ n := by
    intro n
    induction n with
    | zero =>
      simpa using InitialError31.initial_observation CertifyError31.data κ (Ulin 31 (G 0))
        (by simpa using heven 0)
    | succ n ih =>
      rw [divided_step CertifyError31.data _ _ (U_mem _ (hmem n)) (hstep n), ih, pow_succ]
      ring
  refine BLBound.bEll_eq_of_not_mem (by norm_num) m hm fun k hk =>
    BLBound.not_mem_of_errors κ G obs hrec obs_odd obs_even (fun n => ?_) m k hk
  rw [hobs]
  exact mul_ne_zero (by decide) (pow_ne_zero n (by decide))

end Exact31

namespace Exact29
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal AllPowers29 Error29 ErrorDynamics29
  Sharp29

lemma obs_odd (n : ℕ) : PadicInt.toZMod (obs (Ll 29 (2 * n + 1))) ≠ 0 := by
  rw [obs_reduce, odd_reduction, ← PowerSeries.smul_eq_C_mul, map_smul, obs_f, smul_eq_mul]
  exact mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero n (by decide))) (by decide)

lemma obs_even (n : ℕ) : PadicInt.toZMod (obs (Ulin 29 (Ll 29 (2 * n + 1)))) = 0 := by
  rw [obs_reduce]
  change obsBar (PowerSeries.map (PadicInt.toZMod (p := 29)) (U 29 (Ll 29 (2 * n + 1)))) = 0
  rw [map_U, odd_reduction, U_C_mul, Cert29.even_step, ← PowerSeries.smul_eq_C_mul, map_smul,
    obs_g, smul_zero]

/-- **`b₂₉(m) = 2m - 1` for every `m ≥ 1`.** -/
theorem bEll_29 (m : ℕ) (hm : 1 ≤ m) : BLBound.bEll 29 m = 2 * m - 1 := by
  obtain ⟨κ, hκ, G, hmem, hrec, heven, hstep⟩ := normalized_errors
  have hk : PadicInt.toZMod κ = 3 := by
    obtain ⟨d, hd⟩ := hκ
    rw [hd, map_add, map_mul, map_ofNat, map_ofNat]
    rw [show (29 : ZMod 29) = 0 from rfl, zero_mul, add_zero]
  have hobs : ∀ n, PadicInt.toZMod (obs (Ulin 29 (G n))) = 12 * (23 : ZMod 29) ^ n := by
    intro n
    induction n with
    | zero =>
      simpa using InitialError29.initial_observation CertifyError29.data κ (Ulin 29 (G 0)) hk
        (by simpa using heven 0)
    | succ n ih =>
      rw [divided_step CertifyError29.data _ _ (U_mem _ (hmem n)) (hstep n), ih, pow_succ]
      ring
  refine BLBound.bEll_eq_of_not_mem (by norm_num) m hm fun k hk =>
    BLBound.not_mem_of_errors κ G obs hrec obs_odd obs_even (fun n => ?_) m k hk
  rw [hobs]
  exact mul_ne_zero (by decide) (pow_ne_zero n (by decide))

end Exact29

end RamanujanTau.FiniteArithmetic
