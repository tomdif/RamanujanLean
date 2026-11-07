/-
# (SK) from the diagonal / off-diagonal split of the lag correlations

`SKSplitHyp θ` (named hypothesis, mentions no zeros): for Selberg's mollifier `y = ⌊T^θ⌋`,
`h = K/log T`, there is an admissible weight `φ ≥ 1_{[T,2T]}` on `[A,B]` such that

* (diag) `∫_0^h∫_0^h∫_A^B φ(t) DiagLag(t+x, x'−x) ≤ (D/√K) T h²`  — the explicit diagonal
  `bdn = acm` of the exact lag expansion (`Expand.lag_product`);
* (off)  `∫_0^h∫_0^h∫_A^B φ(t) OffLag(t+x, x'−x) ≤ (1/√K) T h²` — the off-diagonal remainder
  (expected `≪ T^{1−δ}`: shifted convolution sums, cf. `TwistedMoment`);
* (`DiagLag` is jointly continuous — a regularity clause).

Then (SK) holds (`sk_of_split`, level 2), and together with `HafnerBridge.QFHyp` (which gives
(MV2) via `HafnerBridge2.mv2_of_QF`) the positive proportion of critical zeros follows
(`tauL_positive_proportion_of_QF_split`, level 2 on `QFHyp ∧ SKSplitHyp θ`).
-/
import RamanujanTau.SelbergKey.Expand
import RamanujanTau.HafnerBridge2.Main

set_option autoImplicit false

namespace RamanujanTau.SelbergKey

open Complex MeasureTheory Set Filter RamanujanTau.HeckeL
open scoped Real

/-- An admissible window: `φ` continuous, `φ ≥ 0`, `φ ≥ 1` on `[T,2T] ⊆ [A,B]`. -/
def Admissible (T A B : ℝ) (φ : ℝ → ℝ) : Prop :=
  Continuous φ ∧ (∀ t, 0 ≤ φ t) ∧ (∀ t ∈ Icc T (2 * T), 1 ≤ φ t) ∧ A ≤ T ∧ 2 * T ≤ B

/-- The weighted lag integral `∫_0^h ∫_0^h ∫_A^B φ(t) G(t+x, x'−x)`. -/
noncomputable def lagInt (G : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) (A B h : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..h, ∫ x' in (0:ℝ)..h, ∫ t in A..B, φ t * G (t + x) (x' - x)

lemma cont_lag {G : ℝ → ℝ → ℝ} (hG : Continuous (Function.uncurry G)) {φ : ℝ → ℝ}
    (hφ : Continuous φ) :
    Continuous (fun q : (ℝ × ℝ) × ℝ => φ q.2 * G (q.2 + q.1.1) (q.1.2 - q.1.1)) := by
  refine (hφ.comp continuous_snd).mul ?_
  have : Continuous (fun q : (ℝ × ℝ) × ℝ => ((q.2 + q.1.1), (q.1.2 - q.1.1))) := by fun_prop
  exact hG.comp this

lemma lagInt_add {G₁ G₂ : ℝ → ℝ → ℝ} (h₁ : Continuous (Function.uncurry G₁))
    (h₂ : Continuous (Function.uncurry G₂)) {φ : ℝ → ℝ} (hφ : Continuous φ) (A B h : ℝ) :
    lagInt (fun u v => G₁ u v + G₂ u v) φ A B h = lagInt G₁ φ A B h + lagInt G₂ φ A B h := by
  unfold lagInt
  have c₁ := cont_lag h₁ hφ
  have c₂ := cont_lag h₂ hφ
  -- continuity of the inner integrals in `x'` (for fixed `x`) and in `(x, x')`
  have i₁ : Continuous (fun p : ℝ × ℝ => ∫ t in A..B, φ t * G₁ (t + p.1) (p.2 - p.1)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (p : ℝ × ℝ) t => φ t * G₁ (t + p.1) (p.2 - p.1)) c₁ A B
  have i₂ : Continuous (fun p : ℝ × ℝ => ∫ t in A..B, φ t * G₂ (t + p.1) (p.2 - p.1)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (p : ℝ × ℝ) t => φ t * G₂ (t + p.1) (p.2 - p.1)) c₂ A B
  have j₁ : Continuous (fun x : ℝ => ∫ x' in (0:ℝ)..h, ∫ t in A..B, φ t * G₁ (t + x) (x' - x)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x x' => ∫ t in A..B, φ t * G₁ (t + x) (x' - x)) i₁ 0 h
  have j₂ : Continuous (fun x : ℝ => ∫ x' in (0:ℝ)..h, ∫ t in A..B, φ t * G₂ (t + x) (x' - x)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x x' => ∫ t in A..B, φ t * G₂ (t + x) (x' - x)) i₂ 0 h
  rw [← intervalIntegral.integral_add (j₁.intervalIntegrable _ _) (j₂.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun x _ => ?_
  have k₁ : Continuous (fun x' : ℝ => ∫ t in A..B, φ t * G₁ (t + x) (x' - x)) :=
    i₁.comp (Continuous.prodMk continuous_const continuous_id)
  have k₂ : Continuous (fun x' : ℝ => ∫ t in A..B, φ t * G₂ (t + x) (x' - x)) :=
    i₂.comp (Continuous.prodMk continuous_const continuous_id)
  rw [← intervalIntegral.integral_add (k₁.intervalIntegrable _ _) (k₂.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun x' _ => ?_
  have l₁ : Continuous (fun t : ℝ => φ t * G₁ (t + x) (x' - x)) :=
    c₁.comp (Continuous.prodMk (continuous_const (y := ((x, x') : ℝ × ℝ))) continuous_id)
  have l₂ : Continuous (fun t : ℝ => φ t * G₂ (t + x) (x' - x)) :=
    c₂.comp (Continuous.prodMk (continuous_const (y := ((x, x') : ℝ × ℝ))) continuous_id)
  rw [← intervalIntegral.integral_add (l₁.intervalIntegrable _ _) (l₂.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

lemma continuous_Fsel (β : ℕ → ℝ) (y : ℕ) : Continuous (Fsel β y) :=
  HafnerProportion.continuous_ZH.mul (HafnerProportion.continuous_wM _ y)

lemma continuous_lagProd (β : ℕ → ℝ) (y : ℕ) :
    Continuous (Function.uncurry fun u v : ℝ => Fsel β y u * Fsel β y (u + v)) := by
  have hF := continuous_Fsel β y
  exact (hF.comp continuous_fst).mul (hF.comp (continuous_fst.add continuous_snd))

/-- **Exact lag form of the weighted Selberg integral** (level 1). -/
theorem weighted_eq_lagInt (β : ℕ → ℝ) (y : ℕ) {φ : ℝ → ℝ} (hφ : Continuous φ)
    {A B h : ℝ} (hAB : A ≤ B) (hh : 0 ≤ h) :
    ∫ t in A..B, φ t * (∫ u in t..t + h, Fsel β y u) ^ 2 =
      lagInt (fun u v => Fsel β y u * Fsel β y (u + v)) φ A B h := by
  rw [weighted_shortInt_sq (continuous_Fsel β y) hφ hAB hh]
  unfold lagInt
  refine intervalIntegral.integral_congr fun x _ => intervalIntegral.integral_congr fun x' _ =>
    intervalIntegral.integral_congr fun t _ => ?_
  simp only
  congr 3; ring

/-- **The named split hypothesis for Selberg's key lemma.** -/
def SKSplitHyp (θ : ℝ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    ∃ (φ : ℝ → ℝ) (A B : ℝ), Admissible T A B φ ∧
      Continuous (Function.uncurry (DiagLag (HafnerMV2.βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊)) ∧
      lagInt (DiagLag (HafnerMV2.βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) φ A B (K / Real.log T) ≤
        D / Real.sqrt K * T * (K / Real.log T) ^ 2 ∧
      lagInt (OffLag (HafnerMV2.βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) φ A B (K / Real.log T) ≤
        1 / Real.sqrt K * T * (K / Real.log T) ^ 2

/-- **(SK) from the split hypothesis** (level 2): exactly the (SK) conjunct of
`SelbergCoeffs.SelbergMollHyp`. -/
theorem sk_of_split {θ : ℝ} (H : SKSplitHyp θ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∫ t in Set.Icc T (2 * T), HafnerProportion.selI HafnerProportion.ZH
          (HafnerProportion.wM (SelbergCoeffs.bSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) (K / Real.log T) t ^ 2) ≤
        D / Real.sqrt K * T * (K / Real.log T) ^ 2 := by
  obtain ⟨D, hD, hK⟩ := H
  refine ⟨D + 1, by linarith, fun K hK1 => ?_⟩
  obtain ⟨T₀, hT₀⟩ := hK K hK1
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  obtain ⟨φ, A, B, ⟨hφ, hφ0, hφ1, hAT, hTB⟩, hcont, hdiag, hoff⟩ := hT₀ T (le_trans (le_max_left _ _) hT)
  set y := ⌊T ^ θ⌋₊
  set β := HafnerMV2.βSel y
  set h := K / Real.log T with hhdef
  have hh : 0 ≤ h := div_nonneg (by linarith) (Real.log_nonneg hT1)
  have hb : SelbergCoeffs.bSel y = fun n => (β n : ℂ) := HafnerMV2.bSel_eq y
  have hsel : ∀ t, HafnerProportion.selI HafnerProportion.ZH
      (HafnerProportion.wM (SelbergCoeffs.bSel y) y) h t = ∫ u in t..t + h, Fsel β y u := by
    intro t; rw [hb]; rfl
  simp_rw [hsel]
  have h1 := sk_le_weighted (continuous_Fsel β y) hφ hφ0 hAT hTB (by linarith) hφ1 (h := h)
  rw [weighted_eq_lagInt β y hφ (by linarith) hh] at h1
  have hOff : Continuous (Function.uncurry (OffLag β y)) := by
    have := (continuous_lagProd β y).sub hcont
    exact this
  have hsplit : lagInt (fun u v => Fsel β y u * Fsel β y (u + v)) φ A B h =
      lagInt (DiagLag β y) φ A B h + lagInt (OffLag β y) φ A B h := by
    rw [← lagInt_add hcont hOff hφ]
    unfold OffLag; congr 1; funext u v; ring
  rw [hsplit] at h1
  have e : D / Real.sqrt K * T * h ^ 2 + 1 / Real.sqrt K * T * h ^ 2 =
      (D + 1) / Real.sqrt K * T * h ^ 2 := by ring
  linarith

/-- **(MV2) + (SK) for Selberg's mollifier from `QFHyp` and `SKSplitHyp`** (level 2). -/
theorem selbergMollHyp_of_QF_split {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 81600)
    (hQ : HafnerBridge.QFHyp) (hS : SKSplitHyp θ) : SelbergCoeffs.SelbergMollHyp := by
  obtain ⟨B, T₁, hMV⟩ := HafnerBridge2.mv2_of_QF hθ0 hθ hQ
  obtain ⟨D, hD, hSK⟩ := sk_of_split hS
  refine ⟨θ, max B 1, D, hθ0, by linarith, by positivity, hD, fun K hK1 => ?_⟩
  obtain ⟨T₂, hT₂⟩ := hSK K hK1
  refine ⟨max (max T₁ T₂) 0, fun T hT => ⟨?_, hT₂ T (le_trans (le_trans (le_max_right _ _)
    (le_max_left _ _)) hT)⟩⟩
  have hT0 : 0 ≤ T := le_trans (le_max_right _ _) hT
  refine (hMV T (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT)).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) hT0

/-- **Hafner's positive proportion for `L(Δ,s)`, conditional on `QFHyp ∧ SKSplitHyp θ`**
(level 2): `N₀(3T) ≥ c·N(3T)`. -/
theorem tauL_positive_proportion_of_QF_split {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 81600)
    (hQ : HafnerBridge.QFHyp) (hS : SKSplitHyp θ) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ tauL (6 + γ * I) = 0) ∧
        c * (ZeroCount.zeroCount (3 * T) : ℝ) ≤ S.card :=
  SelbergCoeffs.tauL_positive_proportion_of_moll (selbergMollHyp_of_QF_split hθ0 hθ hQ hS)

end RamanujanTau.SelbergKey
