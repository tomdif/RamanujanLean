/-
# Bruhat decomposition, part 7: the bound for `‖P‖²`

`norm_tsum_Iγ_le`: for `h ≥ 1`, `0 < δ ≤ 1`,
`‖Σ_γ I(γ)‖ ≤ C_δ h ε³ Y^{−3/2−2δ}` with `C_δ` depending only on `δ` (Weil).
-/
import RamanujanTau.SCSProof.Bruhat6

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.TauBound
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

lemma norm_Jc_le (c : ℝ) (hc : c ≠ 0) : ‖Jc P c hc‖ ≤ (Jp P c hc).toReal := by
  refine (norm_integral_le_toReal _).trans (le_of_eq ?_)
  unfold Jp; congr 1; refine lintegral_congr fun q => ?_
  rw [enorm_mul, RCLike.enorm_conj]

lemma Jp_toReal_le (c : ℝ) (hc : c ≠ 0) :
    (Jp P c hc).toReal ≤ 64 * P.ε ^ 3 / (|c| * P.Y) := by
  have hle := Jp_le P c hc
  have hY := P.hY; have hε := P.hε
  have hpos : 0 ≤ 64 * P.ε ^ 3 / (|c| * P.Y) := by positivity
  split_ifs at hle
  · exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans (by rw [ENNReal.toReal_ofReal hpos])
  · rw [nonpos_iff_eq_zero.1 hle]; simpa using hpos

lemma Jp_zero (c : ℝ) (hc : c ≠ 0) (hcY : 2 ≤ |c| * P.Y) : Jp P c hc = 0 := by
  have hle := Jp_le P c hc
  rw [if_neg (by linarith)] at hle
  exact nonpos_iff_eq_zero.1 hle

/-- `g(m) = ‖S(h,h;m)‖ · 64ε³/(mY)`. -/
noncomputable def gK (m : ℕ) : ℝ := ‖kloosterman P.h P.h m‖ * (64 * P.ε ^ 3 / (m * P.Y))

lemma gK_nonneg (m : ℕ) : 0 ≤ gK P m := by
  unfold gK; have := P.hY; have := P.hε; positivity

lemma norm_Tl_le (c : ℤ) (hc : c ≠ 0) : ‖Tl P c‖ ≤ gK P c.natAbs := by
  rw [Tl_eq P c hc, norm_mul, norm_phase_sum P c hc]
  unfold gK
  gcongr
  refine (norm_Jc_le P _ _).trans ((Jp_toReal_le P _ _).trans (le_of_eq ?_))
  rw [← natAbs_cast]

lemma Tl_zero_of_large (c : ℤ) (hc : c ≠ 0) (hcY : 2 ≤ |(c : ℝ)| * P.Y) : Tl P c = 0 := by
  rw [Tl_eq P c hc]
  have : Jc P (c : ℝ) (by exact_mod_cast hc) = 0 := by
    have := norm_Jc_le P (c : ℝ) (by exact_mod_cast hc)
    rw [Jp_zero P _ _ hcY, ENNReal.toReal_zero] at this
    exact norm_le_zero_iff.1 this
  rw [this, mul_zero]

/-- `K₂ = ⌈2/Y⌉`. -/
noncomputable def K2 : ℕ := ⌈2 / P.Y⌉₊

lemma large_of_gt (n : ℕ) (hn : K2 P < n) : 2 ≤ (n : ℝ) * P.Y := by
  have hY := P.hY
  have h1 : 2 / P.Y ≤ K2 P := Nat.le_ceil _
  have h2 : (K2 P : ℝ) + 1 ≤ n := by exact_mod_cast hn
  rw [div_le_iff₀ hY] at h1
  nlinarith

/-- The layer sum bound. -/
theorem norm_tsum_Iγ_le_gK :
    ‖∑' γ, Iγ P γ‖ ≤ 2 * (∫⁻ q, ‖ft P q‖ₑ).toReal +
      2 * ∑ m ∈ Finset.range (K2 P + 2), gK P m := by
  set X := (∫⁻ q, ‖ft P q‖ₑ).toReal
  have hX : 0 ≤ X := ENNReal.toReal_nonneg
  rw [tsum_Iγ_eq_Rt, tsum_Rt_eq]
  have hsT := summable_Tl P
  -- finite support
  have hsupp : ∀ c : ℤ, K2 P < c.natAbs → Tl P c = 0 := by
    intro c hc
    have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
    refine Tl_zero_of_large P c hc0 ?_
    rw [← natAbs_cast]; exact large_of_gt P _ hc
  set H : ℕ → ℝ := fun n => if n ≤ K2 P then (if n = 0 then 2 * X else 0) + gK P n + gK P (n + 1)
    else 0
  have hTH : ∀ n : ℕ, ‖Tl P n‖ + ‖Tl P (-(n + 1 : ℤ))‖ ≤ H n := by
    intro n
    simp only [H]
    split_ifs with hn hn0
    · subst hn0
      have h1 := norm_Tl_zero P
      have h2 := norm_Tl_le P (-(0 + 1 : ℤ)) (by norm_num)
      simp only [Nat.cast_zero] at h1 ⊢
      have : (-(0 + 1 : ℤ)).natAbs = 0 + 1 := by norm_num
      rw [this] at h2
      linarith [gK_nonneg P 0]
    · have h1 := norm_Tl_le P (n : ℤ) (by exact_mod_cast hn0)
      have h2 := norm_Tl_le P (-(n + 1 : ℤ)) (by omega)
      have e1 : ((n : ℤ)).natAbs = n := Int.natAbs_natCast n
      have e2 : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
      rw [e1] at h1; rw [e2] at h2
      linarith
    · have h1 : Tl P n = 0 := hsupp n (by rw [Int.natAbs_natCast]; omega)
      have h2 : Tl P (-(n + 1 : ℤ)) = 0 := hsupp _ (by omega)
      rw [h1, h2]; simp
  have hHsupp : ∀ n ∉ Finset.range (K2 P + 1), H n = 0 := by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp only [H]; rw [if_neg (by omega)]
  have hsN : Summable fun n : ℕ => ‖Tl P n‖ + ‖Tl P (-(n + 1 : ℤ))‖ :=
    hsT.norm.nat_add_neg_add_one
  calc ‖∑' c, Tl P c‖ ≤ ∑' c, ‖Tl P c‖ := norm_tsum_le_tsum_norm hsT.norm
    _ = ∑' n : ℕ, (‖Tl P n‖ + ‖Tl P (-(n + 1 : ℤ))‖) := (tsum_nat_add_neg_add_one hsT.norm).symm
    _ ≤ ∑' n : ℕ, H n := hsN.tsum_le_tsum hTH (summable_of_ne_finset_zero hHsupp)
    _ = ∑ n ∈ Finset.range (K2 P + 1), H n := tsum_eq_sum hHsupp
    _ ≤ 2 * X + 2 * ∑ m ∈ Finset.range (K2 P + 2), gK P m := by
        have hH : ∀ n ∈ Finset.range (K2 P + 1), H n =
            (if n = 0 then 2 * X else 0) + gK P n + gK P (n + 1) := by
          intro n hn
          simp only [H]; rw [if_pos (by simpa [Nat.lt_succ_iff] using hn)]
        rw [Finset.sum_congr rfl hH, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' (Finset.range (K2 P + 1)) 0]
        rw [if_pos (by simp)]
        have hA : ∑ n ∈ Finset.range (K2 P + 1), gK P n ≤
            ∑ m ∈ Finset.range (K2 P + 2), gK P m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
            (fun m _ _ => gK_nonneg P m)
        have hB : ∑ n ∈ Finset.range (K2 P + 1), gK P (n + 1) ≤
            ∑ m ∈ Finset.range (K2 P + 2), gK P m := by
          rw [Finset.sum_range_succ' (fun m => gK P m) (K2 P + 1)]
          linarith [gK_nonneg P 0]
        linarith

end RamanujanTau.SCSProof
