/-
# Bruhat decomposition, part 4: the Kloosterman phase and the bound for `Σ_γ I(γ)`

`norm_tsum_Iγ_le`: `‖Σ_γ I(γ)‖ ≤ 2∫⁻‖ft‖ + Σ_{0<|c|≤K₂} ‖S(h,h;|c|)‖ · 64ε³/(|c|Y)`.
-/
import RamanujanTau.SCSProof.Bruhat3

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.TauBound
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

/-! ### The phase -/

/-- `e(−h(a + gcdA(a,c))/c)`, in the shape produced by `Rg_eq`. -/
noncomputable def ph (c a : ℤ) : ℂ :=
  cexp (-2 * π * I * P.h * ((((a : ℤ) : ℝ) + ((Int.gcdA a c : ℤ) : ℝ)) / ((c : ℤ) : ℝ)))

lemma gcdA_mul (a c : ℤ) (h : Int.gcd a c = 1) : a * Int.gcdA a c ≡ 1 [ZMOD c] := by
  have := Int.gcd_eq_gcd_ab a c
  rw [h] at this
  push_cast at this
  rw [Int.ModEq, this]
  simp [Int.add_mul_emod_self_left]

lemma gcdA_congr (c a a' : ℤ) (ha : Int.gcd a c = 1) (ha' : Int.gcd a' c = 1)
    (hmod : a ≡ a' [ZMOD c]) : Int.gcdA a c ≡ Int.gcdA a' c [ZMOD c] := by
  have h1 := gcdA_mul a c ha
  have h2 := gcdA_mul a' c ha'
  have h3 : a * Int.gcdA a' c ≡ 1 [ZMOD c] := (hmod.mul_right _).trans h2
  calc Int.gcdA a c = Int.gcdA a c * 1 := (mul_one _).symm
    _ ≡ Int.gcdA a c * (a * Int.gcdA a' c) [ZMOD c] := h3.symm.mul_left _
    _ = (a * Int.gcdA a c) * Int.gcdA a' c := by ring
    _ ≡ 1 * Int.gcdA a' c [ZMOD c] := h1.mul_right _
    _ = Int.gcdA a' c := one_mul _

/-- `ph` depends only on `a mod c`. -/
lemma ph_congr (c a a' : ℤ) (hc : c ≠ 0) (ha : Int.gcd a c = 1) (ha' : Int.gcd a' c = 1)
    (hmod : a ≡ a' [ZMOD c]) : ph P c a = ph P c a' := by
  unfold ph
  have hg := gcdA_congr c a a' ha ha' hmod
  obtain ⟨k1, hk1⟩ := (Int.modEq_iff_dvd.1 hmod.symm)
  obtain ⟨k2, hk2⟩ := (Int.modEq_iff_dvd.1 hg.symm)
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(P.h : ℤ) * (k1 + k2), ?_⟩
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have h1C : ((a : ℝ) : ℂ) - ((a' : ℝ) : ℂ) = ((c : ℝ) : ℂ) * k1 := by
    have : a - a' = c * k1 := by linarith
    exact_mod_cast this
  have h2C : ((Int.gcdA a c : ℝ) : ℂ) - ((Int.gcdA a' c : ℝ) : ℂ) = ((c : ℝ) : ℂ) * k2 := by
    have : Int.gcdA a c - Int.gcdA a' c = c * k2 := by linarith
    exact_mod_cast this
  push_cast at h1C h2C hcC ⊢
  have hq : ((a : ℂ) + (Int.gcdA a c : ℂ)) / c - ((a' : ℂ) + (Int.gcdA a' c : ℂ)) / c =
      (k1 : ℂ) + k2 := by
    rw [div_sub_div_same, div_eq_iff hcC]
    linear_combination h1C + h2C
  linear_combination (-2 * π * I * (P.h : ℂ)) * hq

/-! ### The phase sum is a Kloosterman sum -/

lemma gcdA_inv (c : ℤ) (hc : c ≠ 0) (r : ℕ) (hr : Nat.Coprime r c.natAbs) :
    ((((r : ZMod c.natAbs)⁻¹).val : ℤ)) ≡ Int.gcdA r c [ZMOD c.natAbs] := by
  haveI : NeZero c.natAbs := ⟨Int.natAbs_ne_zero.2 hc⟩
  have hg : Int.gcd (r : ℤ) c = 1 := by
    rw [Int.gcd]; simpa using hr
  have h1 := gcdA_mul (r : ℤ) c hg
  have h1' : (r : ℤ) * Int.gcdA r c ≡ 1 [ZMOD c.natAbs] := by
    rw [Int.ModEq] at h1 ⊢
    have : ((c.natAbs : ℕ) : ℤ) = |c| := Int.natCast_natAbs c
    rw [this, Int.emod_abs, Int.emod_abs]; exact h1
  have hz : ((r : ℤ) : ZMod c.natAbs) * ((Int.gcdA r c : ℤ) : ZMod c.natAbs) = 1 := by
    have := (ZMod.intCast_eq_intCast_iff _ _ _).2 h1'
    push_cast at this ⊢; exact this
  have hinv : ((r : ZMod c.natAbs))⁻¹ = ((Int.gcdA r c : ℤ) : ZMod c.natAbs) :=
    ZMod.inv_eq_of_mul_eq_one _ _ _ (by exact_mod_cast hz)
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [ZMod.natCast_zmod_val, hinv]

lemma exp_kl_term (c : ℤ) (hc : c ≠ 0) (r : ℕ) (hr : Nat.Coprime r c.natAbs) :
    cexp (2 * π * I * ((P.h : ℂ) * ((r : ℂ) + (Int.gcdA r c : ℂ)) / (c.natAbs : ℂ))) =
      ee ((((P.h : ℤ) : ℂ) * r + ((P.h : ℤ) : ℂ) * ((((r : ZMod c.natAbs)⁻¹).val : ℂ))) /
        (c.natAbs : ℂ)) := by
  unfold ee
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.1 (gcdA_inv c hc r hr)
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨(P.h : ℤ) * k, ?_⟩
  have hn : ((c.natAbs : ℕ) : ℂ) ≠ 0 := by
    have : c.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hc
    exact_mod_cast this
  have hkC : (Int.gcdA r c : ℂ) - ((((r : ZMod c.natAbs)⁻¹).val : ℕ) : ℂ) =
      ((c.natAbs : ℕ) : ℂ) * k := by
    have := congrArg (fun z : ℤ => (z : ℂ)) hk
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] at this
    exact this
  push_cast
  have hq : (P.h : ℂ) * ((r : ℂ) + (Int.gcdA r c : ℂ)) / (c.natAbs : ℂ) -
      ((P.h : ℂ) * r + (P.h : ℂ) * ((((r : ZMod c.natAbs)⁻¹).val : ℕ) : ℂ)) / (c.natAbs : ℂ) =
      (P.h : ℂ) * k := by
    rw [div_sub_div_same, div_eq_iff hn]
    linear_combination (P.h : ℂ) * hkC
  linear_combination (2 * π * I) * hq

lemma natAbs_cast (c : ℤ) : ((c.natAbs : ℕ) : ℝ) = |(c : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- Each phase is a Kloosterman term or its conjugate. -/
lemma ph_eq_term (c : ℤ) (hc : c ≠ 0) (r : ℕ) (hr : Nat.Coprime r c.natAbs) :
    ph P c r = if 0 < c then conj (ee ((((P.h : ℤ) : ℂ) * r + ((P.h : ℤ) : ℂ) *
        ((((r : ZMod c.natAbs)⁻¹).val : ℂ))) / (c.natAbs : ℂ)))
      else ee ((((P.h : ℤ) : ℂ) * r + ((P.h : ℤ) : ℂ) *
        ((((r : ZMod c.natAbs)⁻¹).val : ℂ))) / (c.natAbs : ℂ)) := by
  rw [← exp_kl_term P c hc r hr]
  unfold ph
  split_ifs with hpos
  · rw [← Complex.exp_conj]
    congr 1
    have hca : ((c.natAbs : ℕ) : ℂ) = (c : ℂ) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hpos.le]
    rw [hca]
    simp only [map_mul, map_div₀, map_add, map_natCast, map_intCast, Complex.conj_I,
      Complex.conj_ofReal, map_ofNat]
    push_cast
    ring
  · congr 1
    have hca : ((c.natAbs : ℕ) : ℂ) = -(c : ℂ) := by
      rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos (by omega), Int.cast_neg]
    rw [hca]
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    push_cast
    field_simp

/-- **The phase sum has the size of a Kloosterman sum.** -/
theorem norm_phase_sum (c : ℤ) (hc : c ≠ 0) :
    ‖∑ r ∈ (Finset.range c.natAbs).filter (fun r => Nat.Coprime r c.natAbs), ph P c r‖ =
      ‖kloosterman P.h P.h c.natAbs‖ := by
  unfold kloosterman
  rw [Finset.sum_congr rfl (fun r hr => ph_eq_term P c hc r (Finset.mem_filter.1 hr).2)]
  split_ifs with hpos
  · rw [← map_sum, Complex.norm_conj]
  · rfl

end RamanujanTau.SCSProof
