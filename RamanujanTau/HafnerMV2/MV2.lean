/-
# Hafner's (MV2) from the twisted moment, conditional on the diagonal bound `DiagHyp`

`mv2_of_diag`: for `0 < θ`, `136 θ ≤ 1/600` and `DiagHyp θ`,

    ∫_T^{3T} |L(6+iu) M(6+iu)²|² du ≤ B T,   M = Mc (bSel ⌊T^θ⌋) ⌊T^θ⌋ (Selberg's mollifier).

`DiagHyp θ` bounds the smoothed diagonal `Σ_{p,q} κ(p,q) MainTw(h_p, h_q, X, X^{299/300}) ≪ T` for
`X ∈ [T/2, 3T]`. It contains no `L`-values.
-/
import RamanujanTau.HafnerMV2.Expand

set_option autoImplicit false

namespace RamanujanTau.HafnerMV2

open Complex MeasureTheory Set Filter
open RamanujanTau.HafnerProportion RamanujanTau.HeckeL RamanujanTau.TwistedMoment RamanujanTau.GoodSecondTerm
open RamanujanTau.SelbergCoeffs
open scoped Interval

/-! ### Removing the averaging (upper bound) -/

lemma Av_real {G : ℝ → ℝ} (X H : ℝ) :
    Av X H (fun t => (G t : ℂ)) = (((1 / H) * ∫ u in X..X + H, ∫ t in (16 : ℝ)..u, G t : ℝ) : ℂ) := by
  unfold Av
  simp_rw [intervalIntegral.integral_ofReal]
  push_cast; ring

lemma prim_mono {G : ℝ → ℝ} (hG : Continuous G) (hG0 : ∀ u, 0 ≤ G u) {a b : ℝ} (ha : 16 ≤ a) (hab : a ≤ b) :
    (∫ t in (16 : ℝ)..a, G t) ≤ ∫ t in (16 : ℝ)..b, G t :=
  intervalIntegral.integral_mono_interval le_rfl ha hab (Eventually.of_forall fun t => hG0 t)
    (hG.intervalIntegrable 16 b)

/-- **Sharp cutoff from the averages.** -/
theorem sharp_le {G : ℝ → ℝ} (hG : Continuous G) (hG0 : ∀ u, 0 ≤ G u) {T X₁ H₁ H₃ : ℝ}
    (h16 : 16 ≤ X₁) (hH₁ : 0 < H₁) (h1 : X₁ + H₁ ≤ T) (hH₃ : 0 < H₃) :
    ∫ u in T..3 * T, G u ≤ (Av (3 * T) H₃ (fun t => (G t : ℂ))).re - (Av X₁ H₁ (fun t => (G t : ℂ))).re := by
  rw [Av_real, Av_real, Complex.ofReal_re, Complex.ofReal_re]
  set I : ℝ → ℝ := fun u => ∫ t in (16 : ℝ)..u, G t with hI
  have hIc : Continuous I := intervalIntegral.continuous_primitive (fun a b => hG.intervalIntegrable a b) 16
  have hT16 : 16 ≤ T := by linarith
  -- upper average
  have hu : H₃ * I (3 * T) ≤ ∫ u in (3 * T)..(3 * T + H₃), I u := by
    have := intervalIntegral.integral_mono_on (a := 3 * T) (b := 3 * T + H₃) (f := fun _ => I (3 * T)) (g := I)
      (by linarith) ((continuous_const (y := I (3 * T))).intervalIntegrable (μ := volume) _ _)
      (hIc.intervalIntegrable _ _) (fun u hu => prim_mono hG hG0 (by linarith) hu.1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    calc H₃ * I (3 * T) = (3 * T + H₃ - 3 * T) * I (3 * T) := by ring
      _ ≤ _ := this
  have hl : (∫ u in X₁..(X₁ + H₁), I u) ≤ H₁ * I T := by
    have := intervalIntegral.integral_mono_on (a := X₁) (b := X₁ + H₁) (f := I) (g := fun _ => I T)
      (by linarith) (hIc.intervalIntegrable _ _)
      ((continuous_const (y := I T)).intervalIntegrable (μ := volume) _ _)
      (fun u hu => prim_mono hG hG0 (by linarith [hu.1]) (by linarith [hu.2]))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    calc _ ≤ _ := this
      _ = H₁ * I T := by ring
  have hsplit : ∫ u in T..3 * T, G u = I (3 * T) - I T := by
    simp only [hI]
    rw [intervalIntegral.integral_interval_sub_left (hG.intervalIntegrable _ _) (hG.intervalIntegrable _ _)]
  rw [hsplit]
  have e3 : I (3 * T) ≤ 1 / H₃ * ∫ u in (3 * T)..(3 * T + H₃), I u := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hH₃]; linarith
  have e1 : 1 / H₁ * (∫ u in X₁..(X₁ + H₁), I u) ≤ I T := by
    rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hH₁]; linarith
  linarith

/-! ### Selberg's mollifier as a real sequence -/

/-- The real Selberg coefficients `α(n)(1 − log n/log y)` on `[1, y]`. -/
noncomputable def βSel (y n : ℕ) : ℝ := if 1 ≤ n ∧ n ≤ y then alpha n * (1 - Real.log n / Real.log y) else 0

lemma bSel_eq (y : ℕ) : bSel y = fun n => (βSel y n : ℂ) := by
  funext n; unfold bSel βSel; split_ifs <;> simp

lemma abs_βSel_le (y n : ℕ) : |βSel y n| ≤ Real.sqrt n := by
  have h := norm_bSel_le_sqrt y n
  rw [bSel_eq, Complex.norm_real, Real.norm_eq_abs, one_mul, ← Real.sqrt_eq_rpow] at h
  exact h

/-! ### The diagonal hypothesis -/

/-- The smoothed diagonal of the mollified second moment. -/
noncomputable def DiagSum (β : ℕ → ℝ) (y : ℕ) (X H : ℝ) : ℂ :=
  ∑ p ∈ PS y, ∑ q ∈ PS y, (κ β p q : ℂ) * MainTw (hP p) (hP q) X H

/-- **Named hypothesis**: the diagonal (`kM = hN`) part of `∫^X |LM²|²` is `O(T)` for `X ≍ T`. -/
def DiagHyp (θ : ℝ) : Prop :=
  ∃ B T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ X ∈ Icc (T / 2) (3 * T),
    ‖DiagSum (βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊ X (X ^ (299 / 300 : ℝ))‖ ≤ B * T

lemma abs_κ_le (y : ℕ) {p q : ℕ × ℕ} (hp : p ∈ PS y) (hq : q ∈ PS y) : |κ (βSel y) p q| ≤ 1 / 2 := by
  have hc : ∀ r ∈ PS y, |cP (βSel y) r| * Real.exp (-(LP r / 2)) ≤ 1 := by
    intro r hr
    have hr' := hr
    simp only [PS, Finset.mem_product, Finset.mem_Icc] at hr'
    have h1 : (1 : ℝ) ≤ r.1 := by exact_mod_cast hr'.1.1
    have h2 : (1 : ℝ) ≤ r.2 := by exact_mod_cast hr'.2.1
    unfold cP
    rw [abs_mul, LP_eq hr]
    have a1 := abs_βSel_le y r.1
    have a2 := abs_βSel_le y r.2
    have hs : Real.sqrt r.1 * Real.sqrt r.2 * Real.exp (-((Real.log r.1 + Real.log r.2) / 2)) = 1 := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith),
        Real.rpow_def_of_pos (by linarith), ← Real.exp_add, ← Real.exp_add]
      rw [show Real.log r.1 * (1 / 2) + Real.log r.2 * (1 / 2) + -((Real.log r.1 + Real.log r.2) / 2) = 0 by ring,
        Real.exp_zero]
    calc |βSel y r.1| * |βSel y r.2| * Real.exp (-((Real.log r.1 + Real.log r.2) / 2))
        ≤ Real.sqrt r.1 * Real.sqrt r.2 * Real.exp (-((Real.log r.1 + Real.log r.2) / 2)) := by gcongr
      _ = 1 := hs
  unfold κ
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have e : |cP (βSel y) p * cP (βSel y) q * Real.exp (-((LP p + LP q) / 2))| =
      (|cP (βSel y) p| * Real.exp (-(LP p / 2))) * (|cP (βSel y) q| * Real.exp (-(LP q / 2))) := by
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      show -((LP p + LP q) / 2) = -(LP p / 2) + -(LP q / 2) by ring, Real.exp_add]; ring
  rw [e]
  have := hc p hp
  have := hc q hq
  have h0 : 0 ≤ |cP (βSel y) q| * Real.exp (-(LP q / 2)) := by positivity
  nlinarith

lemma hP_le (y : ℕ) {p : ℕ × ℕ} (hp : p ∈ PS y) : (hP p : ℝ) ≤ (y : ℝ) ^ 2 := by
  simp only [PS, Finset.mem_product, Finset.mem_Icc] at hp
  unfold hP; push_cast
  have h1 : (p.1 : ℝ) ≤ y := by exact_mod_cast hp.1.2
  have h2 : (p.2 : ℝ) ≤ y := by exact_mod_cast hp.2.2
  rw [sq]; exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The error of one average: `‖Av(|LM²|²) − DiagSum‖ ≤ (C/2) y^{136} X^{599/600}`. -/
lemma avg_err {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (h k : ℕ), 1 ≤ h → 1 ≤ k → ∀ X : ℝ, 2 ^ (300 : ℕ) ≤ X →
      ‖TwAv h k X (X ^ (299 / 300 : ℝ)) - MainTw h k X (X ^ (299 / 300 : ℝ))‖ ≤
        C * ((h * k : ℕ) : ℝ) ^ 33 * X ^ (599 / 600 : ℝ))
    (y : ℕ) (hy : 1 ≤ y) {X : ℝ} (hX : 2 ^ (300 : ℕ) ≤ X) (hX16 : 16 ≤ X) :
    ‖Av X (X ^ (299 / 300 : ℝ)) (fun u => ((‖tauL (6 + u * I) * Mc (bSel y) y (6 + u * I) ^ 2‖ ^ 2 : ℝ) : ℂ)) -
      DiagSum (βSel y) y X (X ^ (299 / 300 : ℝ))‖ ≤ C / 2 * (y : ℝ) ^ 136 * X ^ (599 / 600 : ℝ) := by
  have hH0 : 0 < X ^ (299 / 300 : ℝ) := by positivity
  rw [bSel_eq, Av_LM2 (βSel y) y hX16 hH0]
  unfold DiagSum
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  have hyr : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hp0 : 0 ≤ X ^ (599 / 600 : ℝ) := by positivity
  have hterm : ∀ p ∈ PS y, ∀ q ∈ PS y,
      ‖(κ (βSel y) p q : ℂ) * (TwAv (hP p) (hP q) X (X ^ (299 / 300 : ℝ)) -
        MainTw (hP p) (hP q) X (X ^ (299 / 300 : ℝ)))‖ ≤ C / 2 * (y : ℝ) ^ 132 * X ^ (599 / 600 : ℝ) := by
    intro p hp q hq
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_κ_le y hp hq
    have h2 := hC (hP p) (hP q) (hP_pos hp) (hP_pos hq) X hX
    have h3 : ((hP p * hP q : ℕ) : ℝ) ^ 33 ≤ (y : ℝ) ^ 132 := by
      push_cast
      have := mul_le_mul (hP_le y hp) (hP_le y hq) (Nat.cast_nonneg _) (by positivity)
      calc ((hP p : ℝ) * hP q) ^ 33 ≤ ((y : ℝ) ^ 2 * (y : ℝ) ^ 2) ^ 33 :=
            pow_le_pow_left₀ (by positivity) this 33
        _ = (y : ℝ) ^ 132 := by ring
    calc |κ (βSel y) p q| * ‖TwAv (hP p) (hP q) X (X ^ (299 / 300 : ℝ)) - MainTw (hP p) (hP q) X (X ^ (299 / 300 : ℝ))‖
        ≤ 1 / 2 * (C * (y : ℝ) ^ 132 * X ^ (599 / 600 : ℝ)) := by
          refine mul_le_mul h1 (h2.trans ?_) (norm_nonneg _) (by norm_num)
          gcongr
      _ = _ := by ring
  have hcard : ((PS y).card : ℝ) = (y : ℝ) ^ 2 := by
    simp [PS, Finset.card_product]; ring
  calc ‖∑ p ∈ PS y, ∑ q ∈ PS y, (κ (βSel y) p q : ℂ) * (TwAv (hP p) (hP q) X (X ^ (299 / 300 : ℝ)) -
        MainTw (hP p) (hP q) X (X ^ (299 / 300 : ℝ)))‖
      ≤ ∑ p ∈ PS y, ∑ q ∈ PS y, C / 2 * (y : ℝ) ^ 132 * X ^ (599 / 600 : ℝ) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq => hterm p hp q hq)
    _ = ((PS y).card : ℝ) * (((PS y).card : ℝ) * (C / 2 * (y : ℝ) ^ 132 * X ^ (599 / 600 : ℝ))) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [hcard]; ring

set_option maxHeartbeats 1600000 in
/-- **Hafner's (MV2), conditional on `DiagHyp`.** -/
theorem mv2_of_diag {θ : ℝ} (hθ0 : 0 < θ) (hθ : 136 * θ ≤ 1 / 600) (hD : DiagHyp θ) :
    ∃ B T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∫ u in T..(3 * T), ‖tauL (6 + u * I) * Mc (bSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊ (6 + u * I) ^ 2‖ ^ 2) ≤ B * T := by
  obtain ⟨C, hC0, hC⟩ := twisted_moment
  obtain ⟨B, T₀, hB⟩ := hD
  refine ⟨2 * B + 3 * C, max T₀ (2 ^ (301 : ℕ)), fun T hT => ?_⟩
  have hTT₀ : T₀ ≤ T := (le_max_left _ _).trans hT
  have hT301 : (2 : ℝ) ^ (301 : ℕ) ≤ T := (le_max_right _ _).trans hT
  clear hT
  have hT64 : (64 : ℝ) ≤ T :=
    le_trans (by calc (64 : ℝ) = 2 ^ (6 : ℕ) := by norm_num
      _ ≤ 2 ^ (301 : ℕ) := pow_le_pow_right₀ (by norm_num) (by norm_num)) hT301
  have hX1 : (2 : ℝ) ^ (300 : ℕ) ≤ T / 2 := by
    rw [le_div_iff₀ two_pos, ← pow_succ]; exact hT301
  have hX3 : (2 : ℝ) ^ (300 : ℕ) ≤ 3 * T :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : 300 ≤ 301)).trans
      (hT301.trans (by clear hT301 hX1; linarith))
  set y := ⌊T ^ θ⌋₊ with hydef
  have hyT : (y : ℝ) ≤ T ^ θ := Nat.floor_le (by clear hT301 hX1 hX3; positivity)
  have hy1 : 1 ≤ y := Nat.le_floor (by
    clear hT301 hX1 hX3; exact_mod_cast Real.one_le_rpow (by linarith) hθ0.le)
  have e1 := avg_err hC0 hC y hy1 hX1 (by clear hT301 hX1 hX3; linarith)
  have e3 := avg_err hC0 hC y hy1 hX3 (by clear hT301 hX1 hX3; linarith)
  clear hX1 hX3 hT301
  have d1 := hB T hTT₀ (T / 2) ⟨le_rfl, by linarith⟩
  have d3 := hB T hTT₀ (3 * T) ⟨by linarith, le_rfl⟩
  have hT1 : (64 : ℝ) ≤ T := hT64
  rw [← hydef] at d1 d3
  set G : ℝ → ℝ := fun u => ‖tauL (6 + u * I) * Mc (bSel y) y (6 + u * I) ^ 2‖ ^ 2 with hG
  have hGc : Continuous G := by
    have h1 := differentiable_Mc (bSel y) y
    have h2 := tauLSeries_entire
    refine (Continuous.norm ?_).pow 2
    refine (h2.continuous.comp (by fun_prop)).mul ((h1.continuous.comp (by fun_prop)).pow 2)
  have hG0 : ∀ u, 0 ≤ G u := fun u => by positivity
  set H₁ := (T / 2) ^ (299 / 300 : ℝ)
  set H₃ := (3 * T) ^ (299 / 300 : ℝ)
  have hH₁ : 0 < H₁ := by positivity
  have hH₃ : 0 < H₃ := by positivity
  have hH₁le : H₁ ≤ T / 2 := by
    calc H₁ ≤ (T / 2) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = T / 2 := Real.rpow_one _
  have hs := sharp_le hGc hG0 (T := T) (X₁ := T / 2) (H₁ := H₁) (H₃ := H₃) (by linarith [hT64]) hH₁ (by linarith [hH₁le]) hH₃
  -- bounds
  set A₁ := Av (T / 2) H₁ (fun t => (G t : ℂ))
  set A₃ := Av (3 * T) H₃ (fun t => (G t : ℂ))
  have hA₁ : ‖A₁‖ ≤ B * T + C / 2 * (y : ℝ) ^ 136 * (T / 2) ^ (599 / 600 : ℝ) := by
    have := norm_sub_norm_le A₁ (DiagSum (βSel y) y (T / 2) H₁)
    linarith [e1, d1]
  have hA₃ : ‖A₃‖ ≤ B * T + C / 2 * (y : ℝ) ^ 136 * (3 * T) ^ (599 / 600 : ℝ) := by
    have := norm_sub_norm_le A₃ (DiagSum (βSel y) y (3 * T) H₃)
    linarith [e3, d3]
  have hr1 : -(A₁.re) ≤ ‖A₁‖ := by have := Complex.abs_re_le_norm A₁; linarith [neg_abs_le A₁.re]
  have hr3 : A₃.re ≤ ‖A₃‖ := (le_abs_self _).trans (Complex.abs_re_le_norm A₃)
  -- y^136 X^{599/600} ≤ T
  have hT0 : (0 : ℝ) < T := by linarith
  have hy136 : (y : ℝ) ^ 136 ≤ T ^ (136 * θ) := by
    calc (y : ℝ) ^ 136 ≤ (T ^ θ) ^ 136 := pow_le_pow_left₀ (by positivity) hyT 136
      _ = T ^ (136 * θ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; ring_nf
  have hpow : ∀ c : ℝ, 0 < c → c ≤ 3 → (c * T) ^ (599 / 600 : ℝ) ≤ 3 * T ^ (599 / 600 : ℝ) := by
    intro c hc0 hc3
    rw [Real.mul_rpow hc0.le hT0.le]
    gcongr
    calc c ^ (599 / 600 : ℝ) ≤ 3 ^ (599 / 600 : ℝ) := Real.rpow_le_rpow hc0.le hc3 (by norm_num)
      _ ≤ 3 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 3 := Real.rpow_one 3
  have hTT : T ^ (136 * θ) * T ^ (599 / 600 : ℝ) ≤ T := by
    rw [← Real.rpow_add hT0]
    calc T ^ (136 * θ + 599 / 600) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = T := Real.rpow_one T
  have q1 : (T / 2) ^ (599 / 600 : ℝ) ≤ 3 * T ^ (599 / 600 : ℝ) := by
    have := hpow (1 / 2) (by norm_num) (by norm_num); rwa [show 1 / 2 * T = T / 2 by ring] at this
  have q3 := hpow 3 (by norm_num) le_rfl
  have hY : 0 ≤ (y : ℝ) ^ 136 := by positivity
  have k1 : C / 2 * (y : ℝ) ^ 136 * (T / 2) ^ (599 / 600 : ℝ) ≤ C / 2 * 3 * T := by
    calc C / 2 * (y : ℝ) ^ 136 * (T / 2) ^ (599 / 600 : ℝ) ≤ C / 2 * T ^ (136 * θ) * (3 * T ^ (599 / 600 : ℝ)) := by
          gcongr
      _ = C / 2 * 3 * (T ^ (136 * θ) * T ^ (599 / 600 : ℝ)) := by ring
      _ ≤ C / 2 * 3 * T := by gcongr
  have k3 : C / 2 * (y : ℝ) ^ 136 * (3 * T) ^ (599 / 600 : ℝ) ≤ C / 2 * 3 * T := by
    calc C / 2 * (y : ℝ) ^ 136 * (3 * T) ^ (599 / 600 : ℝ) ≤ C / 2 * T ^ (136 * θ) * (3 * T ^ (599 / 600 : ℝ)) := by
          gcongr
      _ = C / 2 * 3 * (T ^ (136 * θ) * T ^ (599 / 600 : ℝ)) := by ring
      _ ≤ C / 2 * 3 * T := by gcongr
  show ∫ u in T..3 * T, G u ≤ (2 * B + 3 * C) * T
  linarith

end RamanujanTau.HafnerMV2
