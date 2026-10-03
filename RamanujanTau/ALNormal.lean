/-
# Normal forms for Appell–Lerch sums: `z`-shift and `x`-shift

`A(x, q z) = −z⁻¹ A(x, z)` and `A(q x, z/q) = θ(z/q) + (x z / q) A(x, z)`
(equivalently `m(x,q,qz) = m(x,q,z)` and `m(qx,q,z) = 1 − x m(x,q,z)`).
-/
import RamanujanTau.ALThetaCore

set_option autoImplicit false

namespace ALz
open HahnSeries

section Normal
variable {N : ℕ} (hN : 1 ≤ N)
include hN

/-- `A(x, q z) = −z⁻¹ A(x, z)`. -/
theorem Ab_zshift {a β : ℤ} (hlo : -N < a + β) (hhi : a + β + N < N) {cx cp : ℂ} (hx : cx ≠ 0)
    (hp : cp ≠ 0) :
    Ab hN (a := a) (β := β + N) (by omega) (by omega) cx cp =
      -mono (-β) cp⁻¹ * Ab hN (a := a) (β := β) hlo (by omega) cx cp := by
  rw [Ab_eq_sum, Ab_eq_sum]
  refine hsum_reindex' _ _ (Equiv.addRight (-1)) _ fun r => ?_
  simp only [sv, Equiv.coe_addRight]
  rw [aSumF_apply _ _ _ hx hp, aSumF_apply _ _ _ hx hp]
  unfold aTerm
  rw [show (N : ℤ) * (r + -1 - 1) + a + (β + N) = N * (r - 1) + a + β by ring, ← mul_assoc]
  congr 1
  rw [show -mono (-β) cp⁻¹ = mono (-β) (-cp⁻¹) from (single_neg _ _).symm, mono_mul]
  congr 1
  · have h1 := two_c2 (r + -1); have h2 := two_c2 r; nlinarith
  · rw [zpow_add₀ (by norm_num), zpow_add₀ hp]
    field_simp

/-- `A(q x, z/q) = θ(z/q) + (x z/q) A(x, z)`. -/
theorem Ab_xshift {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) {cx cp : ℂ} (hx : cx ≠ 0)
    (hp : cp ≠ 0) (hy : ∀ r : ℤ, mono (N * (r - 1) + a + β) (cx * cp) ≠ 1) :
    Ab hN (a := a + N) (β := β - N) (by omega) (by omega) cx cp =
      θ hN (β - N) cp + mono (a + β - N) (cx * cp) * Ab hN hlo hhi cx cp := by
  have key : ∀ r : ℤ, aTerm N (a + N) (β - N) cx cp r =
      thT N (β - N) cp r + mono (a + β - N) (cx * cp) * aTerm N a β cx cp r := by
    intro r
    unfold aTerm thT thE thC
    rw [show (N : ℤ) * (r - 1) + (a + N) + (β - N) = N * (r - 1) + a + β by ring]
    set y := mono (N * (r - 1) + a + β) (cx * cp) with hydef
    have h1y : (1 : L) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm (hy r))
    have hcM : mono (a + β - N) (cx * cp) * mono (N * c2 r + β * r) ((-1) ^ r * cp ^ r) =
        mono (N * c2 r + (β - N) * r) ((-1) ^ r * cp ^ r) * y := by
      rw [hydef, mono_mul, mono_mul]; congr 1 <;> ring
    rw [← mul_assoc, hcM]
    field_simp
    ring
  rw [Ab_eq_sum, Ab_eq_sum, θ]
  have hsplit : hs (aSumF hN (a := a + N) (β := β - N) (by omega) (by omega) cx cp) =
      hs (thF hN (β - N) cp + mono (a + β - N) (cx * cp) • aSumF hN hlo hhi cx cp) := by
    refine hsum_congr _ _ fun r => ?_
    simp only [SummableFamily.add_apply, SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul]
    rw [aSumF_apply _ _ _ hx hp, aSumF_apply _ _ _ hx hp, thF_apply]
    exact key r
  rw [hsplit, hs_eq, SummableFamily.hsum_add, SummableFamily.hsum_smul]
  rfl

end Normal
end ALz
