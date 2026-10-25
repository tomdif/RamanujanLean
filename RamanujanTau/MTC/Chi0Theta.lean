/-
# The theta boundary terms of the χ₀ cone bookkeeping

* `qfac_eq_Th3`: `(Q;Q)_∞ = Th3 0 2 − Th3 1 4` (the pentagonal series, `Q = t⁶`);
* `Th12_split`: `Th12 0 8 = 1 + Th12 8 20`;  `Th3_split`: `Th3 0 2 = 1 − Th3 2 5`.
-/
import RamanujanTau.MTC.Chi0Cone
import RamanujanTau.MTC.ProdId
import RamanujanTau.RankTheta

set_option autoImplicit false

namespace MTC.Chi0L
open ALz HahnSeries Finset MTC

lemma h6 : 1 ≤ 6 := by norm_num
lemma h18 : 1 ≤ 18 := by norm_num

/-- `θ(t^{12}; t^{18}) = ιN₆ (q;q)_∞`. -/
lemma J6_eq : θ h18 12 1 = ιN h6 MockTheta5.JTP.qfacInf := by
  rw [θu h6 h18 3 2 1 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) le_rfl, ← RankProof.Pinf_one_one,
    ιN_Pinf_split h6 1 1 3 le_rfl le_rfl (by norm_num)]
  simp only [PJ, prod_range_succ, prod_range_zero, one_mul, mul_zero, add_zero, mul_one, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul]
  ring

/-- `ℤ ≃ ℕ ⊕ ℕ`: `k = s ≥ 0` and `k = −1 − s`. -/
def eZ : ℕ ⊕ ℕ ≃ ℤ where
  toFun x := Sum.elim (fun s : ℕ => (s : ℤ)) (fun s : ℕ => -1 - (s : ℤ)) x
  invFun k := if 0 ≤ k then Sum.inl k.toNat else Sum.inr (-1 - k).toNat
  left_inv x := by
    rcases x with s | s
    · simp
    · simp only [Sum.elim_inr]; rw [if_neg (by omega)]; congr; omega
  right_inv k := by
    by_cases hk : 0 ≤ k
    · simp only [if_pos hk, Sum.elim_inl]; omega
    · simp only [if_neg hk, Sum.elim_inr]; omega

lemma c2_neg_one_sub (s : ℤ) : c2 (-1 - s) = c2 s + 2 * s + 1 := by
  have h1 := two_c2 (-1 - s); have h2 := two_c2 s
  nlinarith

theorem qfac_eq_Th3 : ιN h6 MockTheta5.JTP.qfacInf = Th3 0 2 - Th3 1 4 := by
  rw [← J6_eq, θ, sub_eq_add_neg, Th3, Th3]
  have : hs (thF h18 12 1) = hs (th3F 0 2) + hs ((-1 : L) • th3F 1 4) :=
    hs_split _ _ _ eZ
      (fun s => by
        simp only [thF, th3F, monoFam_apply, eZ, Equiv.coe_fn_mk, Sum.elim_inl]
        exact mono_ext (by unfold thE tE3; push_cast; ring) (by unfold thC; simp))
      (fun s => by
        simp only [thF, th3F, monoFam_apply, eZ, Equiv.coe_fn_mk, Sum.elim_inr, SummableFamily.smul_apply,
          HahnSeries.of_symm_smul_of_eq_mul]
        rw [neg_one_mul, neg_mono]
        refine mono_ext (by unfold thE tE3; rw [c2_neg_one_sub]; push_cast; ring) ?_
        unfold thC
        rw [one_zpow, mul_one, zpow_sub₀ (by norm_num), zpow_neg_one, zpow_natCast]
        rcases neg_one_pow_eq_or ℂ s with h | h <;> rw [h] <;> norm_num)
  rw [this, hs_eq, hs_eq, hs_eq, SummableFamily.hsum_smul]
  ring

/-- a single monomial as a family over `Unit`. -/
noncomputable def oneF (E : ℤ) (c : ℂ) : SummableFamily ℤ ℂ Unit :=
  monoFam (fun _ => E) (fun _ => c) E (fun _ => le_rfl) (fun _ => Set.toFinite _)

lemma hs_oneF (E : ℤ) (c : ℂ) : hs (oneF E c) = mono E c := by rw [hs_unique]; rfl

lemma one_L : (1 : L) = mono 0 1 := by rw [mono, HahnSeries.single_zero_one]

theorem Th12_split : Th12 0 8 = 1 + Th12 8 20 := by
  rw [Th12, Th12, hs_split (th12F 0 8) (oneF 0 1) (th12F 8 20) eNat (fun _ => by
      simp only [th12F, oneF, monoFam_apply, eNat, Equiv.coe_fn_mk, Sum.elim_inl]
      exact mono_ext (by unfold tE12; simp [c2]) rfl)
    (fun r => by
      simp only [th12F, monoFam_apply, eNat, Equiv.coe_fn_mk, Sum.elim_inr]
      exact mono_ext (by unfold tE12; push_cast; rw [c2_succ]; ring) rfl), hs_oneF, one_L]

theorem Th3_split : Th3 0 2 = 1 - Th3 2 5 := by
  rw [Th3, Th3, sub_eq_add_neg]
  have : hs (th3F 0 2) = hs (oneF 0 1) + hs ((-1 : L) • th3F 2 5) :=
    hs_split (th3F 0 2) (oneF 0 1) _ eNat (fun _ => by
      simp only [th3F, oneF, monoFam_apply, eNat, Equiv.coe_fn_mk, Sum.elim_inl]
      exact mono_ext (by unfold tE3; simp [c2]) (by simp))
    (fun s => by
      simp only [th3F, monoFam_apply, eNat, Equiv.coe_fn_mk, Sum.elim_inr, SummableFamily.smul_apply,
        HahnSeries.of_symm_smul_of_eq_mul]
      rw [neg_one_mul, neg_mono]
      exact mono_ext (by unfold tE3; push_cast; rw [c2_succ]; ring) (by rw [pow_succ]; ring))
  rw [this, hs_oneF, ← one_L, hs_eq, hs_eq, SummableFamily.hsum_smul]
  ring

/-- **the cone bookkeeping**: the eight cones of the Bailey double sum minus the eight cones of Garvan's
four `f_{12,9,3}` values is `2(q;q)_∞`. -/
theorem cone_identity :
    (Cp 0 8 4 + Cp 1 11 5 - Cp 1 14 4 - Cp 2 17 5 - Cp 4 16 10 - Cp 7 19 11 + Cp 9 22 10 + Cp 12 25 11) -
      (-(Cp 0 7 2 + Cp 15 26 13) + (Cp 1 13 4 + Cp 8 20 11) + (Cp 1 11 5 + Cp 9 22 10) -
        (Cp 4 16 8 + Cp 4 17 7)) = 2 * ιN h6 MockTheta5.JTP.qfacInf := by
  have m1 : Cp 0 7 2 = Th3 0 2 + Cp 7 19 11 := Cp_shift_r 0 7 2
  have m2 : Cp 0 8 4 = Th12 0 8 - Cp 4 17 7 := Cp_shift_s 0 8 4
  have m3 : Cp 4 16 8 = Th12 4 16 - Cp 12 25 11 := Cp_shift_s 4 16 8
  have m4 : Cp 1 14 4 = Th3 1 4 + Cp 15 26 13 := Cp_shift_r 1 14 4
  have m5 : Cp 1 13 4 = Th3 1 4 + Cp 14 25 13 := Cp_shift_r 1 13 4
  have m6 : Cp 4 16 10 = Th12 4 16 - Cp 14 25 13 := Cp_shift_s 4 16 10
  have m7 : Cp 2 17 5 = Th3 2 5 + Cp 19 29 14 := Cp_shift_r 2 17 5
  have m8 : Cp 8 20 11 = Th12 8 20 - Cp 19 29 14 := Cp_shift_s 8 20 11
  rw [qfac_eq_Th3]
  linear_combination m1 + m2 + m3 - m4 - m5 - m6 - m7 - m8 + Th12_split - Th3_split
