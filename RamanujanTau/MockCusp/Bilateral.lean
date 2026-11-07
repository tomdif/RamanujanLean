/-
# The bilateral form of the rank Appell–Lerch sum

`Ad_bilateral`: with `Q = e^L`, if no denominator vanishes and the bilateral sum converges,

  `1 + Σ_{r≥1} (−1)^r Q^{r(3r+1)/2}(1+Q^r)(1−z)(1−z⁻¹)/((1−zQ^r)(1−Q^r/z))
     = (1−z) Σ_{n∈ℤ} (−1)ⁿ Q^{n(3n+1)/2}/(1 − zQⁿ)`,

where `Q^x` means `e^{xL}`. The terms `n = ±r` pair up to the `r`-th term on the left.
-/
import RamanujanTau.MockCusp.RankDisc
import RamanujanTau.MockCusp.OddCusp

set_option autoImplicit false

namespace MockCusp
open Complex

noncomputable section

/-- `(−1)ⁿ Q^{n(3n+1)/2}/(1 − zQⁿ)` with `Q^x = e^{xL}`. -/
def tmL (z L : ℂ) (n : ℤ) : ℂ := (-1) ^ n * cexp ((3 * (n : ℂ) ^ 2 + n) / 2 * L) / (1 - z * cexp (n * L))

lemma tmL_pair {z L : ℂ} (hz : z ≠ 0) (m : ℕ) (h1 : 1 - z * cexp (((m : ℤ) + 1 : ℤ) * L) ≠ 0)
    (h2 : 1 - z * cexp ((-((m : ℤ) + 1) : ℤ) * L) ≠ 0) :
    (1 - z) * (tmL z L ((m : ℤ) + 1) + tmL z L (-((m : ℤ) + 1))) = aT z m (cexp L) := by
  set w := cexp (((m : ℤ) + 1 : ℤ) * L) with hw
  set E := cexp ((3 * (((m : ℤ) + 1 : ℤ) : ℂ) ^ 2 + (((m : ℤ) + 1 : ℤ) : ℂ)) / 2 * L) with hE
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hwi : cexp ((-((m : ℤ) + 1) : ℤ) * L) = w⁻¹ := by
    rw [hw, ← Complex.exp_neg]; congr 1; push_cast; ring
  have hEi : cexp ((3 * ((-((m : ℤ) + 1) : ℤ) : ℂ) ^ 2 + ((-((m : ℤ) + 1) : ℤ) : ℂ)) / 2 * L) = E * w⁻¹ := by
    rw [hE, hw, ← Complex.exp_neg, ← Complex.exp_add]; congr 1; push_cast; ring
  have hQe : cexp L ^ eN m = E := by
    rw [pow_eq_cexp, hE]
    congr 1
    have := two_mul_eN m
    have h' : (2 : ℂ) * (eN m : ℂ) = ((m + 1) * (3 * m + 4) : ℕ) := by exact_mod_cast this
    push_cast at h' ⊢
    linear_combination L * h' / 2
  have hQw : cexp L ^ (m + 1) = w := by rw [pow_eq_cexp, hw]; push_cast; ring_nf
  have hs : ((-1 : ℂ) ^ (-((m : ℤ) + 1))) = (-1) ^ (m + 1) := by
    rw [zpow_neg, show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, ← inv_pow, inv_neg,
      inv_one]
  have hs' : ((-1 : ℂ) ^ ((m : ℤ) + 1)) = (-1) ^ (m + 1) := by
    rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [hwi] at h2
  have h3 : 1 - z⁻¹ * w ≠ 0 := by
    intro h0; apply h2
    have : w = z := by field_simp at h0; linear_combination -h0
    rw [this, mul_inv_cancel₀ hz, sub_self]
  have h4 : w - z ≠ 0 := by
    intro h0; apply h3; rw [show w = z by linear_combination h0, inv_mul_cancel₀ hz, sub_self]
  have h5 : z - w ≠ 0 := fun h0 => h4 (by linear_combination -h0)
  unfold tmL aT hq
  rw [hEi, hwi, hs, hs', hQe, hQw, ← hw, ← hE]
  rw [show (1 : ℂ) - z * w⁻¹ = (w - z) / w by field_simp]
  field_simp
  ring

/-- **the bilateral form of `Ad`.** -/
theorem Ad_bilateral {z L : ℂ} (hz : z ≠ 0) (hz1 : z ≠ 1) (hden : ∀ n : ℤ, 1 - z * cexp (n * L) ≠ 0)
    (hs : Summable (tmL z L)) : Ad z (cexp L) = (1 - z) * ∑' n, tmL z L n := by
  have hz1' : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have h0 : tmL z L 0 = 1 / (1 - z) := by simp [tmL]
  have hnat := hs.hasSum.nat_add_neg
  have hshift := (hasSum_nat_add_iff' 1).mpr hnat
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, neg_zero, h0] at hshift
  have hfin : HasSum (fun m : ℕ => aT z m (cexp L))
      ((1 - z) * (∑' n, tmL z L n + 1 / (1 - z) - (1 / (1 - z) + 1 / (1 - z)))) := by
    refine (hshift.mul_left (1 - z)).congr_fun fun m => ?_
    simp only [Nat.cast_add, Nat.cast_one]
    exact (tmL_pair hz m (hden _) (hden _)).symm
  rw [Ad, hfin.tsum_eq]
  field_simp
  ring

end

end MockCusp
