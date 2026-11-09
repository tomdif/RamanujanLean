/-
# Berndt et al. (11.7)/(11.10): `f(q,q⁵) = f(q⁸,q¹⁶) + q f(q⁴,q²⁰)`, i.e. `χ(q)χ(−q³) = χ(q¹²)/χ(−q⁸) + qχ(q⁴)/χ(−q²⁴)`

This is the 2-dissection `MTC.dissect2` of the barred theta `θ₆(1,−1) = f(q,q⁵)` (`L11`), turned into a product
identity with `θ_bar` (`P11`). The file also has the helpers `S_S` (`(q ↦ q^a) ∘ (q ↦ q^b) = (q ↦ q^{ab})`) and
`Ng_S_odd`.
-/
import RamanujanTau.Forty.E17

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

lemma S_S (a b c : ℕ) [NeZero a] [NeZero b] [NeZero c] (h : c = a * b) (f : PowerSeries ℤ) : S a (S b f) = S c f := by
  subst h
  show PowerSeries.expand a _ (PowerSeries.expand b _ f) = PowerSeries.expand (a * b) _ f
  exact (PowerSeries.expand_mul a (NeZero.ne a) b (NeZero.ne b) f).symm

lemma Ng_S_odd (a : ℕ) [NeZero a] (ha : Odd a) (f : PowerSeries ℤ) : Ng (S a f) = S a (Ng f) := by
  ext n
  rw [Ng, PowerSeries.coeff_rescale, coeff_S, coeff_S]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne a)), ← Ng, Ng, PowerSeries.coeff_rescale, pow_mul,
      ha.neg_one_pow]
  · simp

private lemma hm6 : 1 ≤ 6 := by norm_num
private lemma hm24 : 1 ≤ 24 := by norm_num

/-- (11.7) in `ℂ((t))`: `θ₆(1,−1) = θ₂₄(8,−1) + t θ₂₄(4,−1)`. -/
theorem L11 : θ hm6 1 (-1) = θ hm24 8 (-1) + mono 1 1 * θ hm24 4 (-1) := by
  rw [dis2 hm6 hm24 rfl 1 (by norm_num : (-1 : ℂ) ≠ 0) 8 (-4) 5 (-1) 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num), inv_m' hm24 4, show -(mono (-4) (-1) : L) = mono (-4) 1 by simp [mono]]
  have m : (mono 5 1 : L) * mono (-4) 1 = mono 1 1 := by rw [mono_mul]; norm_num
  linear_combination θ hm24 4 (-1) * m

/-- (11.7) as a product identity. -/
theorem P11 : J 2 12 * J 6 12 * (J 8 24 * J 4 24) =
    J 16 48 * J 24 48 * (J 1 6 * J 4 24) + PowerSeries.X * (J 8 48 * J 24 48 * (J 1 6 * J 8 24)) := by
  apply ι_inj
  have h := congrArg (· * (ι (J 1 6) * ι (J 8 24) * ι (J 4 24))) L11
  simp only at h
  have b1 := θ_bar hm6 1 le_rfl (by norm_num)
  have b8 := θ_bar hm24 8 (by norm_num) (by norm_num)
  have b4 := θ_bar hm24 4 (by norm_num) (by norm_num)
  norm_num at b1 b8 b4
  simp only [map_mul, map_add, ι_X] at b1 b8 b4 ⊢
  linear_combination h - (ι (J 8 24) * ι (J 4 24)) * b1 + (ι (J 1 6) * ι (J 4 24)) * b8
    + (mono 1 1 * ι (J 1 6) * ι (J 8 24)) * b4

end Forty
