/-
# The de la Vallée-Poussin zero-free region for `H(s) = ζ(2s)R(s) = ζ(s)L(Sym²Δ,s)`

Let `ρ = β + iγ` be a zero of `HH`, `η = 1 − β`, `σ = 1 + δ`, `Ψ = (z−1)³F(z)` (`PsiS`):

1. **Sign** (`re_logDeriv_PsiS_le`): `‖Ψ(σ)‖²/(σ−1)⁶ = ‖F(σ)‖²` is non-increasing, so
   `Re Ψ'/Ψ(σ) ≤ 3/δ`.
2. **Landau** (`ZeroFreeRegion.landau`, `r = 1/4`, `m = 4`):
   `−Re Ψ'/Ψ(σ) ≤ 48 log(B(9+|γ|)^{10}/δ³) − 4/(δ+η)`.
3. `4/(δ+η) ≤ 3/δ + 48 M` (`coreS`); `δ = 1/(2592 log|γ|)` gives `η ≥ 1/(18144 log|γ|)`.
-/
import RamanujanTau.Sym2ZeroFree.Psi

set_option autoImplicit false

namespace RamanujanTau.Sym2ZeroFree

open Complex Metric Set Filter Topology
open RamanujanTau.EdgeNonvanishing RamanujanTau.TauPNTUncond RamanujanTau.ZeroFreeRegion
open scoped ComplexConjugate

/-- A zero of `HH` (other than the junk value at the pole) has `Re < 1`. -/
lemma re_lt_one_of_HH_zero {s : ℂ} (h : HH s = 0) (h1 : s ≠ 1) : s.re < 1 := by
  by_contra hc
  push Not at hc
  have hs0 : s ≠ 0 := by intro h0; rw [h0] at hc; simp at hc; linarith
  apply KK_ne_zero hc
  rw [KK_eq hs0 h1, h, mul_zero]

/-- **Step 1: the sign condition** `Re Ψ'/Ψ(1+δ) ≤ 3/δ`. -/
theorem re_logDeriv_PsiS_le {γ : ℝ} (hγ : 1 ≤ |γ|) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8) :
    (deriv (PsiS γ) ((1 + δ : ℝ) : ℂ) / PsiS γ ((1 + δ : ℝ) : ℂ)).re ≤ 3 / δ := by
  set x0 : ℝ := 1 + δ with hx0
  have hx1 : 1 < x0 := by linarith
  have hmem : ((x0 : ℝ) : ℂ) ∈ Om :=
    closedBall_subset_Om hδ0 hδ (mem_closedBall_self (by norm_num))
  set D := deriv (PsiS γ) (x0 : ℂ)
  set P := PsiS γ (x0 : ℂ)
  have hP : P ≠ 0 := PsiS_ne_zero γ (by simpa using hx1)
  have hd : HasDerivAt (PsiS γ) D (x0 : ℂ) :=
    ((differentiableOn_PsiS hγ).differentiableAt (isOpen_Om.mem_nhds hmem)).hasDerivAt
  have hr : HasDerivAt (fun σ : ℝ => PsiS γ (σ : ℂ)) D x0 := hd.comp_ofReal
  have hq := hr.norm_sq
  have hden : HasDerivAt (fun σ : ℝ => (σ - 1) ^ 6) (6 * (x0 - 1) ^ 5) x0 := by
    have := ((hasDerivAt_id x0).sub_const 1).pow 6
    simpa using this
  have hne : (x0 - 1) ^ 6 ≠ 0 := pow_ne_zero _ (by linarith)
  have hh := hq.div hden hne
  have hanti : AntitoneOn (fun σ : ℝ => ‖PsiS γ (σ : ℂ)‖ ^ 2 / (σ - 1) ^ 6) (Ioi 1) := by
    have hval : ∀ σ : ℝ, 1 < σ → ‖PsiS γ (σ : ℂ)‖ ^ 2 / (σ - 1) ^ 6 = ‖FS σ γ‖ ^ 2 := by
      intro σ hσ
      rw [PsiS_real γ hσ, norm_mul, norm_pow,
        show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
      have h6 : (σ - 1) ^ 6 ≠ 0 := pow_ne_zero _ (by linarith)
      rw [mul_pow, ← pow_mul, show 3 * 2 = 6 from rfl, mul_div_cancel_left₀ _ h6]
    intro a ha b hb hab
    simp only [mem_Ioi] at ha hb
    simp only
    rw [hval a ha, hval b hb]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_FS_antitone γ ha hab) 2
  have hle := hh.hasDerivWithinAt.nonpos_of_antitoneOn (accPt_Ioi hx1) hanti
  have hδ' : x0 - 1 = δ := by rw [hx0]; ring
  rw [hδ'] at hle
  rw [Complex.inner] at hle
  have hnum : 2 * (D * conj P).re * δ ^ 6 - ‖P‖ ^ 2 * (6 * δ ^ 5) ≤ 0 := by
    have := (div_nonpos_iff.mp hle)
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
    · have : 0 < (δ ^ 6) ^ 2 := by positivity
      linarith
    · exact h1
  have hPn : 0 < ‖P‖ ^ 2 := by positivity
  rw [re_div_eq, div_le_div_iff₀ hPn hδ0]
  have hδ5 : 0 < δ ^ 5 := by positivity
  have : (2 * (D * conj P).re * δ - ‖P‖ ^ 2 * 6) * δ ^ 5 ≤ 0 := by nlinarith
  have h' : 2 * (D * conj P).re * δ - ‖P‖ ^ 2 * 6 ≤ 0 :=
    nonpos_of_mul_nonpos_left this hδ5 |> fun h => by
      by_contra hc; push Not at hc; nlinarith
  nlinarith

/-- **Steps 2–3: the core inequality.** -/
theorem coreS : ∃ B : ℝ, 1 ≤ B ∧ ∀ s : ℂ, HH s = 0 → 1 ≤ |s.im| → ∀ δ : ℝ, 0 < δ →
    δ ≤ 1 / 24 → 1 - s.re ≤ 1 / 24 →
    4 / (δ + (1 - s.re)) ≤ 3 / δ + 48 * Real.log (B * (9 + |s.im|) ^ 10 / δ ^ 3) := by
  obtain ⟨B, hB1, hB⟩ := norm_PsiS_le
  refine ⟨B, hB1, fun s hs hγ δ hδ0 hδ hη => ?_⟩
  set γ := s.im with hγdef
  set η := 1 - s.re with hηdef
  have hs1 : s ≠ 1 := by
    intro h
    have h0 : γ = 0 := by simp [hγdef, h]
    rw [h0, abs_zero] at hγ; linarith
  have hη0 : 0 < η := by have := re_lt_one_of_HH_zero hs hs1; linarith
  set β : ℝ := s.re with hβ
  set z0 : ℂ := ((1 + δ : ℝ) : ℂ) with hz0
  have hδ8 : δ ≤ 1 / 8 := by linarith
  have han : AnalyticOnNhd ℂ (PsiS γ) (closedBall z0 (1 / 4)) :=
    (analyticOnNhd_PsiS hγ).mono (closedBall_subset_Om hδ0 hδ8)
  have hP0 : ‖PsiS γ z0‖ = δ ^ 3 * ‖FS (1 + δ) γ‖ := by
    rw [hz0, PsiS_real γ (by linarith), norm_mul, norm_pow,
      show ((1 + δ : ℝ) : ℂ) - 1 = ((δ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg hδ0.le]
  have hF1 := one_le_norm_FS (σ := 1 + δ) (by linarith) γ
  have hP0ge : δ ^ 3 ≤ ‖PsiS γ z0‖ := by
    rw [hP0]; nlinarith [pow_pos hδ0 3]
  have hPc : PsiS γ z0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hP0ge; linarith [pow_pos hδ0 3]
  set T := |γ|
  set X : ℝ := B * (9 + T) ^ 10 / δ ^ 3 with hX
  have hδ3 : δ ^ 3 < 1 := by
    have : δ < 1 := by linarith
    calc δ ^ 3 < 1 ^ 3 := by gcongr
      _ = 1 := one_pow 3
  have hX1 : 1 < X := by
    rw [hX, lt_div_iff₀ (by positivity), one_mul]
    have h9 : 1 ≤ (9 + T) ^ 10 := one_le_pow₀ (by linarith [abs_nonneg γ])
    nlinarith
  set M := Real.log X with hM
  have hMpos : 0 < M := Real.log_pos hX1
  have hexpM : Real.exp M = X := Real.exp_log (by linarith)
  have hbd : ∀ z ∈ closedBall z0 (1 / 4), ‖PsiS γ z‖ ≤ Real.exp M * ‖PsiS γ z0‖ := by
    intro z hz
    rw [hexpM]
    calc ‖PsiS γ z‖ ≤ B * (9 + T) ^ 10 := hB γ hγ δ hδ0 hδ8 z hz
      _ = X * δ ^ 3 := by rw [hX]; field_simp
      _ ≤ X * ‖PsiS γ z0‖ := by gcongr
  have hzero : ∀ u ∈ closedBall z0 (1 / 4 / 3), PsiS γ u = 0 → u.re ≤ z0.re := by
    intro u _ hu
    by_contra h
    push Not at h
    have : 1 < u.re := by rw [hz0] at h; simp at h; linarith
    exact PsiS_ne_zero γ this hu
  have hρ : ((β : ℝ) : ℂ) ∈ closedBall z0 (1 / 4 / 3) := by
    rw [mem_closedBall, hz0, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (by rw [hβ]; linarith)]
    rw [hβ]; linarith
  have hβOm : ((β : ℝ) : ℂ) ∈ Om := by
    refine ⟨?_, ?_⟩
    · simp only [mem_setOf_eq, ofReal_re]; rw [hβ]; linarith
    · simp
  have h0 : HH ((β : ℂ) + (γ : ℂ) * I) = 0 := by
    convert hs using 2
    apply Complex.ext <;> simp [hβ, hγdef]
  have hord := four_le_order_PsiS hγ hβOm h0
  have hL := landau (by norm_num : (0 : ℝ) < 1 / 4) hMpos han hPc hbd hzero hρ
    (m := 4) (by exact_mod_cast hord)
  have hS := re_logDeriv_PsiS_le hγ hδ0 hδ8
  have hre : (1 / (z0 - (β : ℂ))).re = 1 / (δ + η) := by
    rw [hz0, ← Complex.ofReal_sub, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    congr 1
    rw [hβ, hηdef]; ring
  rw [hre] at hL
  have : (12 : ℝ) * M / (1 / 4) = 48 * M := by ring
  rw [this] at hL
  push_cast at hL
  rw [← hz0] at hS
  have h4 : 4 / (δ + η) = 4 * (1 / (δ + η)) := by ring
  rw [h4]
  linarith

/-- **Zero-free region (de la Vallée-Poussin) for `ζ(2s)R(s) = ζ(s)L(Sym²Δ,s)`**, large heights,
explicit `c = 1/18144`. -/
theorem HH_zero_free_region : ∃ c > 0, ∃ t₀ : ℝ, ∀ s : ℂ, HH s = 0 → t₀ ≤ |s.im| →
    s.re ≤ 1 - c / Real.log |s.im| := by
  obtain ⟨B, hB1, hcore⟩ := coreS
  set D : ℝ := 1296 with hD
  refine ⟨1 / (14 * D), by positivity, max (max 10 B) (2 * D), fun s hs hT => ?_⟩
  set T := |s.im| with hTdef
  have hT10 : 10 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTB : B ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTD : 2 * D ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := by linarith
  have hs1 : s ≠ 1 := by intro h; rw [hTdef, h] at hT10; simp at hT10; linarith
  set L := Real.log T with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hT0]
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 < L := by linarith
  set η := 1 - s.re with hη
  suffices h : 1 / (14 * D) / L ≤ η by linarith
  by_cases hfar : 1 / 24 < η
  · calc 1 / (14 * D) / L ≤ 1 / (14 * D) := div_le_self (by positivity) hL1
      _ ≤ 1 / 24 := by rw [hD]; norm_num
      _ ≤ η := hfar.le
  push Not at hfar
  set δ : ℝ := 1 / (2 * D * L) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ24 : δ ≤ 1 / 24 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
    rw [hD]; nlinarith
  have hc := hcore s hs (by linarith) δ hδ0 hδ24 hfar
  have hlogX : Real.log (B * (9 + T) ^ 10 / δ ^ 3) ≤ 27 * L := by
    have hB0 : 0 < B := by linarith
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    have h1 : Real.log B ≤ L := Real.log_le_log hB0 hTB
    have h2 : Real.log (9 + T) ≤ 2 * L := by
      have : Real.log (9 + T) ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) hT0.ne'] at this
      have := Real.log_two_lt_d9
      linarith
    have h3 : -Real.log δ ≤ 2 * L := by
      rw [hδ, one_div, Real.log_inv, neg_neg, Real.log_mul (by positivity) hL0.ne']
      have h4 : Real.log (2 * D) ≤ L := Real.log_le_log (by positivity) hTD
      have h5 : Real.log L ≤ L := Real.log_le_self hL0.le
      linarith
    push_cast
    linarith
  have h3δ : 3 / δ = 6 * D * L := by rw [hδ]; field_simp; ring
  have hdη : 0 < δ + η := by
    have : 0 < η := by have := re_lt_one_of_HH_zero hs hs1; linarith
    linarith
  have hmain : 4 / (δ + η) ≤ 7 * D * L := by
    calc 4 / (δ + η) ≤ 3 / δ + 48 * Real.log (B * (9 + T) ^ 10 / δ ^ 3) := hc
      _ ≤ 6 * D * L + 48 * (27 * L) := by rw [h3δ]; gcongr
      _ = 7 * D * L := by rw [hD]; ring
  rw [div_le_iff₀ hdη] at hmain
  have hδL : δ * (D * L) = 1 / 2 := by rw [hδ]; field_simp
  rw [div_div, div_le_iff₀ (by positivity)]
  nlinarith

/-! ### Small heights: compactness and `KK ≠ 0` on `Re s ≥ 1` -/

/-- Near the segment `{1 + it : |t| ≤ t₀}` there are no zeros of `KK` (ineffective). -/
theorem KK_ne_zero_near_edge (t₀ : ℝ) : ∃ ε > 0, ∀ s : ℂ, |s.im| ≤ t₀ → 1 - ε < s.re →
    KK s ≠ 0 := by
  set Kset : Set ℂ := (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I) '' Icc (-t₀) t₀ with hKset
  have hKc : IsCompact Kset := isCompact_Icc.image (by fun_prop)
  set W : Set ℂ := {z : ℂ | 1 / 2 < z.re} ∩ KK ⁻¹' {0}ᶜ with hW
  have hcont : ContinuousOn KK {z : ℂ | 1 / 2 < z.re} := fun z hz => by
    have hz' : 1 / 2 < z.re := hz
    have : z ≠ 0 := by intro h; rw [h] at hz'; simp at hz'; linarith
    exact (differentiableAt_KK this).continuousAt.continuousWithinAt
  have hWo : IsOpen W :=
    hcont.isOpen_inter_preimage (isOpen_lt continuous_const Complex.continuous_re)
      isOpen_compl_singleton
  have hKW : Kset ⊆ W := by
    rintro _ ⟨t, _, rfl⟩
    refine ⟨by simp; norm_num, ?_⟩
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff]
    exact KK_ne_zero (by simp)
  obtain ⟨ε, hε, hth⟩ := hKc.exists_thickening_subset_open hWo hKW
  refine ⟨ε, hε, fun s hsi hsr => ?_⟩
  rcases le_or_gt 1 s.re with h1 | h1
  · exact KK_ne_zero h1
  have hmem : s ∈ Metric.thickening ε Kset := by
    rw [Metric.mem_thickening_iff]
    refine ⟨1 + (s.im : ℂ) * I, ⟨s.im, ⟨by linarith [(abs_le.mp hsi).1], (abs_le.mp hsi).2⟩, rfl⟩,
      ?_⟩
    rw [Complex.dist_eq]
    have e : s - (1 + (s.im : ℂ) * I) = ((s.re - 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  exact (hth hmem).2

/-- **Zero-free region at all heights** for `KK(s) = (s−1)ζ(2s)R(s) = (s−1)ζ(s)L(Sym²Δ,s)`.
In particular there is no exceptional real zero (the constant is ineffective). -/
theorem KK_zero_free_region_uniform : ∃ c > 0, ∀ s : ℂ, KK s = 0 →
    s.re ≤ 1 - c / Real.log (|s.im| + 3) := by
  obtain ⟨c1, hc1, t1, h1⟩ := HH_zero_free_region
  set t₀ : ℝ := max t1 2 with ht₀
  obtain ⟨ε, hε, hεK⟩ := KK_ne_zero_near_edge t₀
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨min c1 (ε * Real.log 3), by positivity, fun s hs => ?_⟩
  set c := min c1 (ε * Real.log 3) with hc
  set T := |s.im| with hTdef
  have hT0 : 0 ≤ T := abs_nonneg _
  have hlogT3 : Real.log 3 ≤ Real.log (T + 3) := Real.log_le_log (by norm_num) (by linarith)
  have hlpos : 0 < Real.log (T + 3) := lt_of_lt_of_le hl3 hlogT3
  by_cases hbig : t₀ ≤ T
  · have hT2 : 2 ≤ T := le_trans (le_max_right _ _) hbig
    have hs0 : s ≠ 0 := by intro h; rw [hTdef, h] at hT2; simp at hT2; linarith
    have hs1 : s ≠ 1 := by intro h; rw [hTdef, h] at hT2; simp at hT2; linarith
    have hH : HH s = 0 := by
      rw [KK_eq hs0 hs1] at hs
      rcases mul_eq_zero.mp hs with h | h
      · exact absurd (sub_eq_zero.mp h) hs1
      · exact h
    have hlT : 0 < Real.log T := Real.log_pos (by linarith)
    have hmono : Real.log T ≤ Real.log (T + 3) := Real.log_le_log (by linarith) (by linarith)
    have hr := h1 s hH (le_trans (le_max_left _ _) hbig)
    have k1 : c / Real.log (T + 3) ≤ c1 / Real.log T :=
      div_le_div₀ hc1.le (min_le_left _ _) hlT hmono
    linarith
  · push Not at hbig
    have hre : s.re ≤ 1 - ε := by
      by_contra h; push Not at h
      exact hεK s hbig.le h hs
    have hk : c / Real.log (T + 3) ≤ ε := by
      rw [div_le_iff₀ hlpos]
      calc c ≤ ε * Real.log 3 := min_le_right _ _
        _ ≤ ε * Real.log (T + 3) := by gcongr
    linarith

/-- **Uniform zero-free region for `ζ(2s)R(s) = ζ(s)L(Sym²Δ,s)`**: `HH(s) ≠ 0` for
`Re s > 1 − c/log(|Im s|+3)`, `s ≠ 1`. -/
theorem HH_ne_zero_region : ∃ c > 0, ∀ s : ℂ, s ≠ 1 →
    1 - c / Real.log (|s.im| + 3) < s.re → HH s ≠ 0 := by
  obtain ⟨c, hc, h⟩ := KK_zero_free_region_uniform
  refine ⟨min c (1 / 2), by positivity, fun s hs1 hre hH => ?_⟩
  have hl : 1 < Real.log (|s.im| + 3) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9
    linarith [abs_nonneg s.im]
  have hlpos : 0 < Real.log (|s.im| + 3) := by linarith
  have hmc : min c (1 / 2) / Real.log (|s.im| + 3) < 1 / 2 := by
    rw [div_lt_iff₀ hlpos]
    have := min_le_right c (1 / 2)
    linarith
  have hk : min c (1 / 2) / Real.log (|s.im| + 3) ≤ c / Real.log (|s.im| + 3) :=
    div_le_div_of_nonneg_right (min_le_left _ _) hlpos.le
  have hs0 : s ≠ 0 := by
    intro h0
    have : s.re = 0 := by rw [h0]; simp
    linarith
  have := h s (by rw [KK_eq hs0 hs1, hH, mul_zero])
  linarith

/-- **Uniform zero-free region for the Rankin–Selberg series** `R(s) = Σ λ(n)² n^{−s}`
(continued, `Rcont`): `R(s) ≠ 0` for `Re s > 1 − c/log(|Im s|+3)`, `s ≠ 1`. -/
theorem Rcont_ne_zero_region : ∃ c > 0, ∀ s : ℂ, s ≠ 1 →
    1 - c / Real.log (|s.im| + 3) < s.re → RankinSelbergFE.Rcont s ≠ 0 := by
  obtain ⟨c, hc, h⟩ := HH_ne_zero_region
  refine ⟨min c (1 / 2), by positivity, fun s hs1 hre hR => ?_⟩
  have hl : 1 < Real.log (|s.im| + 3) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9
    linarith [abs_nonneg s.im]
  have hlpos : 0 < Real.log (|s.im| + 3) := by linarith
  have hmc : min c (1 / 2) / Real.log (|s.im| + 3) < 1 / 2 := by
    rw [div_lt_iff₀ hlpos]
    have := min_le_right c (1 / 2)
    linarith
  have hre2 : 1 / 2 < s.re := by linarith
  have hk : min c (1 / 2) / Real.log (|s.im| + 3) ≤ c / Real.log (|s.im| + 3) :=
    div_le_div_of_nonneg_right (min_le_left _ _) hlpos.le
  have hζ : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hH : HH s ≠ 0 := h s hs1 (by linarith)
  have e : RankinSelbergFE.Rcont s = HH s / riemannZeta (2 * s) := by
    simp only [RankinSelbergFE.Rcont, HH]
  rw [e] at hR
  exact div_ne_zero hH hζ hR

/-- **`L(Sym²Δ, s) ≠ 0`** (`Lsym2 = HH/ζ`) for `Re s > 1 − c/log(|Im s|+3)`, `s ≠ 1`,
at every point where `ζ(s) ≠ 0`. (In Lean `Lsym2 = HH/ζ` is junk at zeros of `ζ`; the genuine
statement about `ζ(s)L(Sym²Δ,s)` is `HH_ne_zero_region`.) -/
theorem Lsym2_ne_zero_region : ∃ c > 0, ∀ s : ℂ, s ≠ 1 → riemannZeta s ≠ 0 →
    1 - c / Real.log (|s.im| + 3) < s.re → Lsym2 s ≠ 0 := by
  obtain ⟨c, hc, h⟩ := HH_ne_zero_region
  exact ⟨c, hc, fun s hs1 hζ hre => div_ne_zero (h s hs1 hre) hζ⟩

end RamanujanTau.Sym2ZeroFree
