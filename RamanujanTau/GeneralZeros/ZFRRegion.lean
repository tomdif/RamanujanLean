/-
# Zero-free region, abstract layer: the de la Vallée-Poussin region for `EData`

Port of `ZeroFreeRegion/Region.lean` (right half), normalized coordinates (edge `Re s = 1`):

  `L(s) = 0`, `|Im s| ≥ t₀`  ⇒  `Re s ≤ 1 − c / log |Im s|`     (`L_zero_free_region`)

with `c = 1/18144`, for every `EData` with polynomial growth of `L` near the edge.  The edge
non-vanishing used is `EigenformEdge.L_ne_zero_edge_of_ne` (off the real axis, unconditional).
-/
import RamanujanTau.GeneralZeros.ZFRPsi
import RamanujanTau.ZeroFreeRegion.Landau

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.GeneralZeros.ZFR

open Complex Metric Set Filter Topology
open RamanujanTau.EigenformEdge EData RamanujanTau.ZeroFreeRegion
open scoped ComplexConjugate

variable [EData]

lemma L_ne_zero_of_ge_of_im {s : ℂ} (hs : 1 ≤ s.re) (him : s.im ≠ 0) : L s ≠ 0 := by
  rcases hs.lt_or_eq with h | h
  · exact L_ne_zero_of_gt h
  · have e : s = 1 + (s.im : ℂ) * I := by
      apply Complex.ext <;> simp [← h]
    rw [e]; exact L_ne_zero_edge_of_ne him

lemma accPt_Ioi {x a : ℝ} (hx : a < x) : AccPt x (𝓟 (Ioi a)) := by
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨x + ε / 2, ⟨hball ?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith)]; linarith
  · simp only [mem_Ioi]; linarith
  · intro h; linarith

lemma re_div_eq (a b : ℂ) : (a / b).re = (a * conj b).re / ‖b‖ ^ 2 := by
  rw [Complex.div_re, ← Complex.normSq_eq_norm_sq]
  simp only [mul_re, conj_re, conj_im]
  ring

/-- **Step 1: the sign condition** `Re Ψ'/Ψ(1+δ) ≤ 3/δ`. -/
theorem re_logDeriv_Psi_le {γ : ℝ} (hγ : 1 ≤ |γ|) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8) :
    (deriv (Psi γ) ((1 + δ : ℝ) : ℂ) / Psi γ ((1 + δ : ℝ) : ℂ)).re ≤ 3 / δ := by
  set x0 : ℝ := 1 + δ with hx0
  have hx1 : 1 < x0 := by linarith
  have hmem : ((x0 : ℝ) : ℂ) ∈ Om :=
    closedBall_subset_Om hδ0 hδ (mem_closedBall_self (by norm_num))
  set D := deriv (Psi γ) (x0 : ℂ)
  set P := Psi γ (x0 : ℂ)
  have hP : P ≠ 0 := Psi_ne_zero γ (by simpa using hx1)
  have hd : HasDerivAt (Psi γ) D (x0 : ℂ) :=
    ((differentiableOn_Psi hγ).differentiableAt (isOpen_Om.mem_nhds hmem)).hasDerivAt
  have hr : HasDerivAt (fun σ : ℝ => Psi γ (σ : ℂ)) D x0 := hd.comp_ofReal
  have hq := hr.norm_sq
  have hden : HasDerivAt (fun σ : ℝ => (σ - 1) ^ 6) (6 * (x0 - 1) ^ 5) x0 := by
    have := ((hasDerivAt_id x0).sub_const 1).pow 6
    simpa using this
  have hne : (x0 - 1) ^ 6 ≠ 0 := pow_ne_zero _ (by linarith)
  have hh := hq.div hden hne
  have hanti : AntitoneOn (fun σ : ℝ => ‖Psi γ (σ : ℂ)‖ ^ 2 / (σ - 1) ^ 6) (Ioi 1) := by
    have hval : ∀ σ : ℝ, 1 < σ → ‖Psi γ (σ : ℂ)‖ ^ 2 / (σ - 1) ^ 6 = ‖Fval σ γ‖ ^ 2 := by
      intro σ hσ
      rw [Psi_real γ hσ, norm_mul, norm_pow,
        show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
      have h6 : (σ - 1) ^ 6 ≠ 0 := pow_ne_zero _ (by linarith)
      rw [mul_pow, ← pow_mul, show 3 * 2 = 6 from rfl, mul_div_cancel_left₀ _ h6]
    intro a ha b hb hab
    simp only [mem_Ioi] at ha hb
    simp only
    rw [hval a ha, hval b hb]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_Fval_antitone γ ha hab) 2
  have hle := hh.hasDerivWithinAt.nonpos_of_antitoneOn (accPt_Ioi hx1) hanti
  have hδ' : x0 - 1 = δ := by rw [hx0]; ring
  rw [hδ'] at hle
  rw [Complex.inner] at hle
  have hd6 : 0 < (δ ^ 6) ^ 2 := by positivity
  have hnum : 2 * (D * conj P).re * δ ^ 6 - ‖P‖ ^ 2 * (6 * δ ^ 5) ≤ 0 := by
    have := (div_nonpos_iff.mp hle)
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · exact h1
  have hPn : 0 < ‖P‖ ^ 2 := by positivity
  rw [re_div_eq, div_le_div_iff₀ hPn hδ0]
  have hδ5 : 0 < δ ^ 5 := by positivity
  have : (2 * (D * conj P).re * δ - ‖P‖ ^ 2 * 6) * δ ^ 5 ≤ 0 := by nlinarith
  have h' : 2 * (D * conj P).re * δ - ‖P‖ ^ 2 * 6 ≤ 0 :=
    nonpos_of_mul_nonpos_left this hδ5 |> fun h => by
      by_contra hc; push Not at hc; nlinarith
  nlinarith

/-- **Step 2–3: the core inequality** `4/(δ+η) ≤ 3/δ + 48 log(B(9+|γ|)^{10}/δ³)`. -/
theorem core (hgrowth : ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 3 / 4 ≤ s.re → s.re ≤ 11 / 8 →
      ‖L s‖ ≤ A * (1 + ‖s‖) ^ 2) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ s : ℂ, L s = 0 → 1 ≤ |s.im| → ∀ δ : ℝ, 0 < δ →
    δ ≤ 1 / 24 → 1 - s.re ≤ 1 / 24 →
    4 / (δ + (1 - s.re)) ≤ 3 / δ + 48 * Real.log (B * (9 + |s.im|) ^ 10 / δ ^ 3) := by
  obtain ⟨B, hB1, hB⟩ := norm_Psi_le hgrowth
  refine ⟨B, hB1, fun s hs hγ δ hδ0 hδ hη => ?_⟩
  set γ := s.im with hγdef
  set η := 1 - s.re with hηdef
  have hη0 : 0 < η := by
    by_contra h
    push Not at h
    exact L_ne_zero_of_ge_of_im (by linarith)
      (by intro h0; rw [← hγdef] at h0; rw [h0] at hγ; simp at hγ; linarith) hs
  set β : ℝ := s.re with hβ
  set z0 : ℂ := ((1 + δ : ℝ) : ℂ) with hz0
  have hδ8 : δ ≤ 1 / 8 := by linarith
  have han : AnalyticOnNhd ℂ (Psi γ) (closedBall z0 (1 / 4)) :=
    (analyticOnNhd_Psi hγ).mono (closedBall_subset_Om hδ0 hδ8)
  have hP0 : ‖Psi γ z0‖ = δ ^ 3 * ‖Fval (1 + δ) γ‖ := by
    rw [hz0, Psi_real γ (by linarith), norm_mul, norm_pow,
      show ((1 + δ : ℝ) : ℂ) - 1 = ((δ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg hδ0.le]
  have hF1 := one_le_norm_Fval (σ := 1 + δ) (by linarith) γ
  have hP0ge : δ ^ 3 ≤ ‖Psi γ z0‖ := by
    rw [hP0]; nlinarith [pow_pos hδ0 3]
  have hPc : Psi γ z0 ≠ 0 := by
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
  have hbd : ∀ z ∈ closedBall z0 (1 / 4), ‖Psi γ z‖ ≤ Real.exp M * ‖Psi γ z0‖ := by
    intro z hz
    rw [hexpM]
    calc ‖Psi γ z‖ ≤ B * (9 + T) ^ 10 := hB γ hγ δ hδ0 hδ8 z hz
      _ = X * δ ^ 3 := by rw [hX]; field_simp
      _ ≤ X * ‖Psi γ z0‖ := by gcongr
  have hzero : ∀ u ∈ closedBall z0 (1 / 4 / 3), Psi γ u = 0 → u.re ≤ z0.re := by
    intro u _ hu
    by_contra h
    push Not at h
    have : 1 < u.re := by rw [hz0] at h; simp at h; linarith
    exact Psi_ne_zero γ this hu
  have hρ : ((β : ℝ) : ℂ) ∈ closedBall z0 (1 / 4 / 3) := by
    rw [mem_closedBall, hz0, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (by rw [hβ]; linarith)]
    rw [hβ]; linarith
  have hβOm : ((β : ℝ) : ℂ) ∈ Om := by
    refine ⟨?_, ?_⟩
    · simp only [mem_setOf_eq, ofReal_re]; rw [hβ]; linarith
    · simp
  have h0 : Ln ((β : ℂ) + γ * I) = 0 := by
    rw [Ln]
    convert hs using 2
    apply Complex.ext <;> simp [hβ, hγdef]
  have hord := four_le_order hγ hβOm h0
  have hL := landau (by norm_num : (0 : ℝ) < 1 / 4) hMpos han hPc hbd hzero hρ
    (m := 4) (by exact_mod_cast hord)
  have hS := re_logDeriv_Psi_le hγ hδ0 hδ8
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

/-- **Zero-free region (de la Vallée-Poussin) for `L(Δ,s)`, right half.** -/
theorem L_zero_free_region (hgrowth : ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 3 / 4 ≤ s.re → s.re ≤ 11 / 8 →
      ‖L s‖ ≤ A * (1 + ‖s‖) ^ 2) :
    ∃ c > 0, ∃ t₀ : ℝ, ∀ s : ℂ, L s = 0 → t₀ ≤ |s.im| →
    s.re ≤ 1 - c / Real.log |s.im| := by
  obtain ⟨B, hB1, hcore⟩ := core hgrowth
  set D : ℝ := 1296 with hD
  refine ⟨1 / (14 * D), by positivity, max (max 10 B) (2 * D), fun s hs hT => ?_⟩
  set T := |s.im| with hTdef
  have hT10 : 10 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTB : B ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTD : 2 * D ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hT0]
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 < L := by linarith
  set η := 1 - s.re with hη
  -- goal: `c / L ≤ η`
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
  -- bound the logarithm
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
    have : 0 < η := by
      by_contra h; push Not at h
      exact L_ne_zero_of_ge_of_im (by linarith)
        (by intro h0; rw [h0] at hTdef; simp at hTdef; linarith) hs
    linarith
  have hmain : 4 / (δ + η) ≤ 7 * D * L := by
    calc 4 / (δ + η) ≤ 3 / δ + 48 * Real.log (B * (9 + T) ^ 10 / δ ^ 3) := hc
      _ ≤ 6 * D * L + 48 * (27 * L) := by rw [h3δ]; gcongr
      _ = 7 * D * L := by rw [hD]; ring
  rw [div_le_iff₀ hdη] at hmain
  have hδL : δ * (D * L) = 1 / 2 := by rw [hδ]; field_simp
  rw [div_div, div_le_iff₀ (by positivity)]
  nlinarith

end RamanujanTau.GeneralZeros.ZFR
