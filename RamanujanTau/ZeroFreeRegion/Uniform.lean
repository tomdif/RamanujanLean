/-
# The zero-free region at all heights

Combining `Region.tauL_zero_free_region` (`|Im s| ≥ t₀`) with the finiteness of the zeros in
`|Im s| ≤ t₀` (`ZeroCount.zeroSet_finite`) and edge non-vanishing (each such zero has
`11/2 < Re < 13/2`): there is `c > 0` such that every non-trivial zero satisfies

  `11/2 + c / log(|Im s| + 2) ≤ Re s ≤ 13/2 − c / log(|Im s| + 2)`.

There is no exceptional (Siegel-type) zero: the only real zeros of `L(Δ,s)` are `s = 0, −1, −2, …`.
-/
import RamanujanTau.ZeroFreeRegion.Region
import RamanujanTau.ZeroCount.Main

set_option autoImplicit false

namespace RamanujanTau.ZeroFreeRegion

open Complex
open RamanujanTau.EdgeNonvanishing RamanujanTau.HeckeL

/-- **Zero-free region at all heights**, both sides. -/
theorem tauL_zero_free_region_uniform : ∃ c > 0, ∀ s : ℂ, tauL s = 0 → (∀ n : ℕ, s ≠ -n) →
    s.re ≤ 13 / 2 - c / Real.log (|s.im| + 2) ∧ 11 / 2 + c / Real.log (|s.im| + 2) ≤ s.re := by
  classical
  obtain ⟨c1, hc1, t1, h1⟩ := tauL_zero_free_region
  obtain ⟨c2, hc2, t2, h2⟩ := tauL_zero_free_region_left
  set t₀ : ℝ := max (max t1 t2) 2 with ht₀
  set S := (ZeroCount.zeroSet_finite (-t₀ - 1) t₀).toFinset with hS
  set f : ℂ → ℝ := fun u => min (13 / 2 - u.re) (u.re - 11 / 2) with hf
  have hfS : ∀ u ∈ S, 0 < f u := by
    intro u hu
    rw [hS, Set.Finite.mem_toFinset] at hu
    obtain ⟨_, ha, hb, _, _⟩ := hu
    simp only [hf, lt_min_iff]; constructor <;> linarith
  obtain ⟨ε, hε, hεS⟩ : ∃ ε > 0, ∀ u ∈ S, ε ≤ f u := by
    by_cases hne : S.Nonempty
    · obtain ⟨u0, hu0, hmin⟩ := S.exists_min_image f hne
      exact ⟨f u0, hfS u0 hu0, hmin⟩
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
    have hstrip1 : s.re < 13 / 2 := by
      by_contra h; push Not at h; exact tauL_ne_zero_of_ge h hs
    have hstrip2 : 11 / 2 < s.re := by
      by_contra h; push Not at h; exact tauL_ne_zero_of_le h hn hs
    have hmem : s ∈ S := by
      rw [hS, Set.Finite.mem_toFinset]
      have := abs_lt.mp hbig
      exact ⟨hs, hstrip2, hstrip1, by linarith [this.1], this.2.le⟩
    have hε' := hεS s hmem
    have hk : c / Real.log (T + 2) ≤ ε := by
      rw [div_le_iff₀ hlpos]
      calc c ≤ ε * Real.log 2 := min_le_right _ _
        _ ≤ ε * Real.log (T + 2) := by gcongr
    simp only [hf, le_min_iff] at hε'
    constructor <;> linarith [hε'.1, hε'.2]

end RamanujanTau.ZeroFreeRegion
