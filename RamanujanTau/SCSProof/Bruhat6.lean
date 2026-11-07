/-
# Bruhat decomposition, part 6: the layers `c ≠ 0` and the final bound for `Σ_γ I(γ)`
-/
import RamanujanTau.SCSProof.Bruhat5

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.TauBound
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

lemma dvd_natAbs_self' (c : ℤ) : c ∣ (c.natAbs : ℤ) := by
  rw [Int.natCast_natAbs]; exact self_dvd_abs c

/-- The `r`-th residue class of the layer `c`. -/
lemma hasSum_residue (c : ℤ) (hc : c ≠ 0) (r : ℕ) :
    HasSum (fun q : ℤ => Rt P (q * c.natAbs + r, c))
      (if Nat.Coprime r c.natAbs then ph P c r * Jc P (c : ℝ) (by exact_mod_cast hc) else 0) := by
  have hmod : ∀ q : ℤ, q * c.natAbs + (r : ℤ) ≡ r [ZMOD c] := by
    intro q
    rw [Int.modEq_iff_dvd]
    have : (r : ℤ) - (q * c.natAbs + r) = -(q * c.natAbs) := by ring
    rw [this, dvd_neg]
    exact Dvd.dvd.mul_left (dvd_natAbs_self' c) q
  have hgcd : ∀ q : ℤ, Int.gcd (q * c.natAbs + r) c = Int.gcd (r : ℤ) c := by
    intro q
    obtain ⟨k, hk⟩ := dvd_natAbs_self' c
    have : q * (c.natAbs : ℤ) + r = r + c * (k * q) := by rw [hk]; ring
    rw [this, Int.gcd_add_mul_left_left]
  have hcopiff : Int.gcd (r : ℤ) c = 1 ↔ Nat.Coprime r c.natAbs := by
    rw [Int.gcd]; simp [Nat.Coprime]
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  split_ifs with hcop
  · have hg : Int.gcd (r : ℤ) c = 1 := hcopiff.2 hcop
    have e : ∀ q : ℤ, Rt P (q * c.natAbs + r, c) =
        ph P c r * Kint P (c : ℝ) hcR ((r : ℝ) / c + q * ((c.natAbs : ℝ) / c)) := by
      intro q
      rw [Rt_eq P _ c hc ((hgcd q).trans hg), ph_congr P c _ _ hc ((hgcd q).trans hg) hg (hmod q)]
      congr 1
      congr 1
      push_cast
      field_simp
      rw [natAbs_cast]; ring
    simp_rw [e]
    refine HasSum.mul_left _ ?_
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · have hs : (c.natAbs : ℝ) / c = -1 := by
        rw [natAbs_cast, abs_of_neg (by exact_mod_cast hneg)]
        field_simp
      simp_rw [hs]
      have h0 := hasSum_K P (c : ℝ) hcR (Jp_ne_top P _ _) ((r : ℝ) / c)
      have := (Equiv.neg ℤ).hasSum_iff.2 h0
      convert this using 2 with q
      simp
    · have hs : (c.natAbs : ℝ) / c = 1 := by
        rw [natAbs_cast, abs_of_pos (by exact_mod_cast hpos)]
        field_simp
      simp_rw [hs, mul_one]
      exact hasSum_K P (c : ℝ) hcR (Jp_ne_top P _ _) ((r : ℝ) / c)
  · have : ∀ q : ℤ, Rt P (q * c.natAbs + r, c) = 0 := fun q =>
      Rt_noncop P _ c (by rw [hgcd q]; exact fun h => hcop (hcopiff.1 h))
    simp_rw [this]
    exact hasSum_zero

/-- **The layer `c ≠ 0`.** -/
theorem Tl_eq (c : ℤ) (hc : c ≠ 0) :
    Tl P c = (∑ r ∈ (Finset.range c.natAbs).filter (fun r => Nat.Coprime r c.natAbs), ph P c r) *
      Jc P (c : ℝ) (by exact_mod_cast hc) := by
  haveI : NeZero c.natAbs := ⟨Int.natAbs_ne_zero.2 hc⟩
  unfold Tl
  rw [← (Int.divModEquiv c.natAbs).symm.tsum_eq (fun a => Rt P (a, c))]
  have hsum : Summable fun p : ℤ × Fin c.natAbs => Rt P ((Int.divModEquiv c.natAbs).symm p, c) :=
    ((Int.divModEquiv c.natAbs).symm.summable_iff (f := fun a => Rt P (a, c))).2
      (summable_layer P c)
  rw [← (Equiv.prodComm (Fin c.natAbs) ℤ).tsum_eq]
  have hsum' : Summable fun p : Fin c.natAbs × ℤ =>
      Rt P ((Int.divModEquiv c.natAbs).symm ((Equiv.prodComm (Fin c.natAbs) ℤ) p), c) :=
    ((Equiv.prodComm (Fin c.natAbs) ℤ).summable_iff).2 hsum
  rw [hsum'.tsum_prod' (fun r => hsum'.comp_injective (Prod.mk_right_injective r)), tsum_fintype]
  have hr : ∀ r : Fin c.natAbs, ∑' q : ℤ,
      Rt P ((Int.divModEquiv c.natAbs).symm ((Equiv.prodComm (Fin c.natAbs) ℤ) (r, q)), c) =
      if Nat.Coprime r c.natAbs then ph P c r * Jc P (c : ℝ) (by exact_mod_cast hc) else 0 := by
    intro r
    exact (hasSum_residue P c hc r).tsum_eq
  rw [Finset.sum_congr rfl (fun r _ => hr r), Finset.sum_mul, Finset.sum_filter]
  rw [Fin.sum_univ_eq_sum_range (fun r => if Nat.Coprime r c.natAbs then
    ph P c r * Jc P (c : ℝ) (by exact_mod_cast hc) else 0)]

end RamanujanTau.SCSProof
