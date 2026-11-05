/-
# The de la Vallée-Poussin zero-free region for every normalized level-one Hecke eigenform

For `f` with `IsNormalizedEigenform f` (weight `k`):

* `fL_zero_free_region` (unconditional): `L(f,ρ) = 0`, `|Im ρ| ≥ t₀` ⇒
  `Re ρ ≤ (k+1)/2 − c / log |Im ρ|`;
* `fL_zero_free_region_left` (unconditional): `(k−1)/2 + c / log |Im ρ| ≤ Re ρ`;
* `fL_zero_free_region_uniform` (under the real edge point `h0 : L(f,(k+1)/2) ≠ 0`, the same
  hypothesis as `EigenformEdge.fL_zeros_in_strip`): every nontrivial zero satisfies
  `(k−1)/2 + c/log(|Im ρ|+2) ≤ Re ρ ≤ (k+1)/2 − c/log(|Im ρ|+2)`.

Abstract layer: `ZFR.L_zero_free_region` on `eigenData f hf`; growth from `fL_growth`; low heights
from the finiteness of `GeneralZeros.zeroSet`.
-/
import RamanujanTau.GeneralZeros.ZFRRegion
import RamanujanTau.GeneralZeros.Count
import RamanujanTau.EigenformEdge.RealPoint

set_option autoImplicit false

namespace RamanujanTau.GeneralZeros

open Complex Set ModularForm
open RamanujanTau.HeckeConvexGeneral RamanujanTau.EigenformEdge
open scoped Real MatrixGroups

variable {k : ℕ} {f : CuspForm 𝒮ℒ (k : ℤ)}

/-- Polynomial growth of the normalized `L(f, s + (k−1)/2)` near the edge. -/
lemma Lf_growth (hf : IsNormalizedEigenform f) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 3 / 4 ≤ s.re → s.re ≤ 11 / 8 → ‖Lf f s‖ ≤ A * (1 + ‖s‖) ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := fL_growth f hf.twelve_le
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨B * (1 + k) ^ 2, by positivity, fun s h1 _ => ?_⟩
  have hre : ((k : ℝ) - 1) / 2 ≤ (s + ((k : ℂ) - 1) / 2).re := by
    simp; linarith
  have hb := hB _ hre
  have hn : ‖s + ((k : ℂ) - 1) / 2‖ ≤ ‖s‖ + k := by
    refine (norm_add_le _ _).trans ?_
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hf.one_le
    have : ‖((k : ℂ) - 1) / 2‖ = ((k : ℝ) - 1) / 2 := by
      rw [show ((k : ℂ) - 1) / 2 = (((k : ℝ) - 1) / 2 : ℝ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    rw [this]; linarith
  have h2 : (1 + ‖s + ((k : ℂ) - 1) / 2‖) ^ 2 ≤ ((1 + k) * (1 + ‖s‖)) ^ 2 := by
    gcongr
    nlinarith [norm_nonneg s]
  rw [Lf]
  calc ‖fL f (s + ((k : ℂ) - 1) / 2)‖ ≤ B * (1 + ‖s + ((k : ℂ) - 1) / 2‖) ^ 2 := hb
    _ ≤ B * ((1 + k) * (1 + ‖s‖)) ^ 2 := by gcongr
    _ = B * (1 + k) ^ 2 * (1 + ‖s‖) ^ 2 := by ring

/-- **de la Vallée-Poussin zero-free region for `L(f,s)`**, `f` any normalized level-one Hecke
eigenform (unconditional, `|Im ρ| ≥ t₀`). -/
theorem fL_zero_free_region (hf : IsNormalizedEigenform f) :
    ∃ c > 0, ∃ t₀ : ℝ, ∀ s : ℂ, fL f s = 0 → t₀ ≤ |s.im| →
      s.re ≤ ((k : ℝ) + 1) / 2 - c / Real.log |s.im| := by
  letI := eigenData f hf
  obtain ⟨c, hc, t₀, h⟩ := ZFR.L_zero_free_region (Lf_growth hf)
  refine ⟨c, hc, t₀, fun s hs hT => ?_⟩
  have hL : EData.L (s - ((k : ℂ) - 1) / 2) = 0 := by
    show Lf f _ = 0
    rw [← Lf_shift hf]; exact hs
  have him : (s - ((k : ℂ) - 1) / 2).im = s.im := by simp
  have hre : (s - ((k : ℂ) - 1) / 2).re = s.re - ((k : ℝ) - 1) / 2 := by simp
  have := h _ hL (by rw [him]; exact hT)
  rw [him, hre] at this
  linarith

/-- Zeros off the real axis are symmetric under `s ↦ k − s`. -/
lemma fL_zero_reflect (hk : 1 ≤ k) {s : ℂ} (hs : fL f s = 0) (him : s.im ≠ 0) :
    fL f ((k : ℂ) - s) = 0 := by
  have hg : s ∈ goodSet := Or.inr him
  have hg' : (k : ℂ) - s ∈ goodSet := Or.inr (by simpa using him)
  rw [← Lam_zero_iff_fL f hg']
  exact Lam_reflect_zero f hk ((Lam_zero_iff_fL f hg).mpr hs)

/-- **Zero-free region, left half** (functional equation). -/
theorem fL_zero_free_region_left (hf : IsNormalizedEigenform f) :
    ∃ c > 0, ∃ t₀ : ℝ, ∀ s : ℂ, fL f s = 0 → t₀ ≤ |s.im| →
      ((k : ℝ) - 1) / 2 + c / Real.log |s.im| ≤ s.re := by
  obtain ⟨c, hc, t₀, h⟩ := fL_zero_free_region hf
  refine ⟨c, hc, max t₀ 1, fun s hs hT => ?_⟩
  have him : s.im ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hT; linarith [le_max_right t₀ 1]
  have h12 := fL_zero_reflect hf.one_le hs him
  have him' : |((k : ℂ) - s).im| = |s.im| := by simp
  have := h _ h12 (by rw [him']; exact le_trans (le_max_left _ _) hT)
  rw [him'] at this
  have e : ((k : ℂ) - s).re = k - s.re := by simp
  rw [e] at this
  linarith

/-- **Zero-free region at all heights**, under the real edge point `L(f,(k+1)/2) ≠ 0`. -/
theorem fL_zero_free_region_uniform (hf : IsNormalizedEigenform f)
    (h0 : fL f (((k : ℂ) + 1) / 2) ≠ 0) :
    ∃ c > 0, ∀ s : ℂ, fL f s = 0 → (∀ n : ℕ, s ≠ -n) →
      s.re ≤ ((k : ℝ) + 1) / 2 - c / Real.log (|s.im| + 2) ∧
      ((k : ℝ) - 1) / 2 + c / Real.log (|s.im| + 2) ≤ s.re := by
  classical
  obtain ⟨c1, hc1, t1, h1⟩ := fL_zero_free_region hf
  obtain ⟨c2, hc2, t2, h2⟩ := fL_zero_free_region_left hf
  set t₀ : ℝ := max (max t1 t2) 2 with ht₀
  set Z : Set ℂ := {u | u ∈ zeroSet f (-t₀ - 1) t₀ ∧ fL f u = 0 ∧ ∀ n : ℕ, u ≠ -n} with hZ
  have hZfin : Z.Finite := (zeroSet_finite f hf.ne_zero (-t₀ - 1) t₀).subset fun u hu => hu.1
  set S := hZfin.toFinset with hS
  set g : ℂ → ℝ := fun u => min (((k : ℝ) + 1) / 2 - u.re) (u.re - ((k : ℝ) - 1) / 2) with hg
  have hgS : ∀ u ∈ S, 0 < g u := by
    intro u hu
    rw [hS, Set.Finite.mem_toFinset] at hu
    obtain ⟨_, hz, hn⟩ := hu
    have := fL_zeros_in_strip hf h0 hz hn
    simp only [hg, lt_min_iff]; constructor <;> linarith [this.1, this.2]
  obtain ⟨ε, hε, hεS⟩ : ∃ ε > 0, ∀ u ∈ S, ε ≤ g u := by
    by_cases hne : S.Nonempty
    · obtain ⟨u0, hu0, hmin⟩ := S.exists_min_image g hne
      exact ⟨g u0, hgS u0 hu0, hmin⟩
    · refine ⟨1, one_pos, fun u hu => absurd ⟨u, hu⟩ hne⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min (min c1 c2) (ε * Real.log 2), by positivity, fun s hs hn => ?_⟩
  set c := min (min c1 c2) (ε * Real.log 2) with hc
  have hc0 : 0 < c := by positivity
  set T := |s.im|
  have hT0 : 0 ≤ T := abs_nonneg _
  have hlogT2 : Real.log 2 ≤ Real.log (T + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hlpos : 0 < Real.log (T + 2) := lt_of_lt_of_le hl2 hlogT2
  by_cases hbig : t₀ ≤ T
  · have hT2 : 2 ≤ T := le_trans (le_max_right _ _) hbig
    have hlT : 0 < Real.log T := Real.log_pos (by linarith)
    have hmono : Real.log T ≤ Real.log (T + 2) := Real.log_le_log (by linarith) (by linarith)
    have hr := h1 s hs (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hbig)
    have hl := h2 s hs (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hbig)
    have k1 : c / Real.log (T + 2) ≤ c1 / Real.log T :=
      div_le_div₀ hc1.le (le_trans (min_le_left _ _) (min_le_left _ _)) hlT hmono
    have k2 : c / Real.log (T + 2) ≤ c2 / Real.log T :=
      div_le_div₀ hc2.le (le_trans (min_le_left _ _) (min_le_right _ _)) hlT hmono
    constructor <;> linarith
  · push Not at hbig
    have hΛ : heckeLambda f s = 0 := by
      rw [heckeLambda_eq_fL f hn, hs, mul_zero]
    have hmem : s ∈ S := by
      rw [hS, Set.Finite.mem_toFinset]
      have := abs_lt.mp hbig
      exact ⟨⟨hΛ, by linarith [this.1], this.2.le⟩, hs, hn⟩
    have hε' := hεS s hmem
    have hk : c / Real.log (T + 2) ≤ ε := by
      rw [div_le_iff₀ hlpos]
      calc c ≤ ε * Real.log 2 := min_le_right _ _
        _ ≤ ε * Real.log (T + 2) := by gcongr
    simp only [hg, le_min_iff] at hε'
    constructor <;> linarith [hε'.1, hε'.2]

/-- **Sanity check `f = Δ`**, recovered from the general theorem (both halves, `|Im| ≥ t₀`). -/
theorem fL_discriminant_zero_free_region :
    ∃ c > 0, ∃ t₀ : ℝ, ∀ s : ℂ, fL (k := 12) DeltaF s = 0 → t₀ ≤ |s.im| →
      11 / 2 + c / Real.log |s.im| ≤ s.re ∧ s.re ≤ 13 / 2 - c / Real.log |s.im| := by
  obtain ⟨c1, hc1, t1, h1⟩ := fL_zero_free_region isNormalizedEigenform_discriminant
  obtain ⟨c2, hc2, t2, h2⟩ := fL_zero_free_region_left isNormalizedEigenform_discriminant
  refine ⟨min c1 c2, lt_min hc1 hc2, max (max t1 t2) 2, fun s hs hT => ?_⟩
  have hT2 : 2 ≤ |s.im| := le_trans (le_max_right _ _) hT
  have hlT : 0 < Real.log |s.im| := Real.log_pos (by linarith)
  have hr := h1 s hs (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT)
  have hl := h2 s hs (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT)
  have k1 : min c1 c2 / Real.log |s.im| ≤ c1 / Real.log |s.im| :=
    div_le_div_of_nonneg_right (min_le_left _ _) hlT.le
  have k2 : min c1 c2 / Real.log |s.im| ≤ c2 / Real.log |s.im| :=
    div_le_div_of_nonneg_right (min_le_right _ _) hlT.le
  have e12 : ((12 : ℕ) : ℝ) = 12 := by norm_num
  rw [e12] at hr hl
  constructor <;> linarith

end RamanujanTau.GeneralZeros
