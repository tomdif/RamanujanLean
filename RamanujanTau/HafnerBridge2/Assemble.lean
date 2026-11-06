/-
# Assembly: `DiagHyp θ ⇐ QFHyp`, hence (MV2) `⇐ QFHyp`

* `regroup`: `Σ_{p∈[1,y]²} β(p₁)β(p₂) F(p₁p₂) = Σ_{h≤y²} c(h) F(h)` with `c = βSel ∗ βSel` (`cS`).
* `diag_decomp`: `DiagSum = 2r₀(Q⁰(y) I₁ + Q¹(y) I₀) + R`, `|R| ≤ Z y^{26} (X+H)^{9/10}`.
* `diag_of_QF`: `QFHyp → DiagHyp θ` for `0 < θ ≤ 1/260`.
* `mv2_of_QF`: `QFHyp →` (MV2) for `0 < θ ≤ 1/81600` (via `HafnerMV2.mv2_of_diag`).
-/
import RamanujanTau.HafnerBridge2.PairBound

set_option autoImplicit false

namespace RamanujanTau.HafnerBridge2

open MeasureTheory Set Filter Topology Complex
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.GoodSecondTerm2 RamanujanTau.TwistedMoment
open RamanujanTau.HafnerBridge RamanujanTau.HafnerMV2
open scoped Interval

/-! ### Regrouping `Σ_{p,q}` into `Σ_{h,k}` -/

lemma βSel_out {y n : ℕ} (hn : ¬ (1 ≤ n ∧ n ≤ y)) : βSel y n = 0 := by
  unfold βSel; rw [if_neg hn]

lemma fiber_sum (y h : ℕ) (hh : 1 ≤ h) :
    ∑ p ∈ (PS y).filter (fun p => hP p = h), cP (βSel y) p = cS y h := by
  unfold cS
  rw [← Nat.sum_divisorsAntidiagonal (fun a b => βSel y a * βSel y b)]
  refine Finset.sum_subset (fun p hp => ?_) (fun p hp hp' => ?_)
  · rw [Finset.mem_filter] at hp
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨hp.2, by omega⟩
  · rw [Nat.mem_divisorsAntidiagonal] at hp
    have : ¬ ((1 ≤ p.1 ∧ p.1 ≤ y) ∧ (1 ≤ p.2 ∧ p.2 ≤ y)) := by
      intro hc
      apply hp'
      rw [Finset.mem_filter]
      refine ⟨?_, hp.1⟩
      simp only [PS, Finset.mem_product, Finset.mem_Icc]; exact hc
    have h1 : 1 ≤ p.1 := by
      rcases Nat.eq_zero_or_pos p.1 with h0 | h0
      · rw [h0, zero_mul] at hp; omega
      · exact h0
    have h2 : 1 ≤ p.2 := by
      rcases Nat.eq_zero_or_pos p.2 with h0 | h0
      · rw [h0, mul_zero] at hp; omega
      · exact h0
    unfold cP
    by_cases ha : p.1 ≤ y
    · have hb : ¬ (1 ≤ p.2 ∧ p.2 ≤ y) := fun hb => this ⟨⟨h1, ha⟩, hb⟩
      rw [βSel_out hb, mul_zero]
    · rw [βSel_out (fun h => ha h.2), zero_mul]

lemma regroup (y : ℕ) (F : ℕ → ℝ) :
    ∑ p ∈ PS y, cP (βSel y) p * F (hP p) = ∑ h ∈ Finset.Icc 1 (y ^ 2), cS y h * F h := by
  have hmaps : ∀ p ∈ PS y, hP p ∈ Finset.Icc 1 (y ^ 2) := by
    intro p hp
    rw [Finset.mem_Icc]
    refine ⟨hP_pos hp, ?_⟩
    have := hP_le y hp
    exact_mod_cast this
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.mem_Icc] at hh
  rw [← fiber_sum y h hh.1, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [(Finset.mem_filter.mp hp).2]

lemma regroup2 (y : ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ p ∈ PS y, ∑ q ∈ PS y, cP (βSel y) p * cP (βSel y) q * G (hP p) (hP q) =
      ∑ h ∈ Finset.Icc 1 (y ^ 2), ∑ k ∈ Finset.Icc 1 (y ^ 2), cS y h * cS y k * G h k := by
  have e1 : ∀ p ∈ PS y, ∑ q ∈ PS y, cP (βSel y) p * cP (βSel y) q * G (hP p) (hP q) =
      cP (βSel y) p * ∑ k ∈ Finset.Icc 1 (y ^ 2), cS y k * G (hP p) k := by
    intro p _
    rw [← regroup y (G (hP p)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => by ring
  rw [Finset.sum_congr rfl e1, regroup y (fun h => ∑ k ∈ Finset.Icc 1 (y ^ 2), cS y k * G h k)]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring

/-! ### `κ · 2√(hk) = cP cP` -/

lemma κ_two_sqrt (y : ℕ) {p q : ℕ × ℕ} (hp : p ∈ PS y) (hq : q ∈ PS y) :
    κ (βSel y) p q * (2 * Real.sqrt ((hP p * hP q : ℕ) : ℝ)) = cP (βSel y) p * cP (βSel y) q := by
  have h1 : (1 : ℝ) ≤ hP p := by exact_mod_cast hP_pos hp
  have h2 : (1 : ℝ) ≤ hP q := by exact_mod_cast hP_pos hq
  unfold κ LP
  have hs : Real.sqrt ((hP p * hP q : ℕ) : ℝ) = Real.exp ((Real.log (hP p : ℝ) + Real.log (hP q : ℝ)) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by push_cast; positivity)]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]; ring_nf
  rw [hs]
  have : Real.exp (-((Real.log (hP p : ℝ) + Real.log (hP q : ℝ)) / 2)) *
      Real.exp ((Real.log (hP p : ℝ) + Real.log (hP q : ℝ)) / 2) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (cP (βSel y) p * cP (βSel y) q) * this

/-! ### The decomposition of `DiagSum` -/

lemma abs_cP_le (y : ℕ) {p : ℕ × ℕ} (hp : p ∈ PS y) : |cP (βSel y) p| ≤ y := by
  simp only [PS, Finset.mem_product, Finset.mem_Icc] at hp
  unfold cP
  rw [abs_mul]
  have a1 := abs_βSel_le y p.1
  have a2 := abs_βSel_le y p.2
  have b1 : Real.sqrt p.1 ≤ Real.sqrt y := Real.sqrt_le_sqrt (by exact_mod_cast hp.1.2)
  have b2 : Real.sqrt p.2 ≤ Real.sqrt y := Real.sqrt_le_sqrt (by exact_mod_cast hp.2.2)
  calc |βSel y p.1| * |βSel y p.2| ≤ Real.sqrt y * Real.sqrt y :=
        mul_le_mul (a1.trans b1) (a2.trans b2) (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = y := Real.mul_self_sqrt (Nat.cast_nonneg _)

/-- The main bilinear term `2r₀(Q⁰ I₁ + Q¹ I₀)`. -/
lemma main_sum (y : ℕ) (X H : ℝ) :
    ∑ h ∈ Finset.Icc 1 (y ^ 2), ∑ k ∈ Finset.Icc 1 (y ^ 2),
        cS y h * cS y k * (2 * r0 / (Nat.lcm h k : ℝ) * (q0 h k * I1 X H + q1 h k * I0 X H)) =
      2 * r0 * (Q0 y * I1 X H + Q1 y * I0 X H) := by
  unfold Q0 Q1
  rw [mul_add, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold q0 q1
  ring

theorem diag_decomp : ∃ Z : ℝ, 0 ≤ Z ∧ ∀ y : ℕ, 1 ≤ y → ∀ X H : ℝ, 16 ≤ X → 0 < H →
    ∃ D R : ℝ, DiagSum (βSel y) y X H = (D : ℂ) ∧ D = 2 * r0 * (Q0 y * I1 X H + Q1 y * I0 X H) + R ∧
      |R| ≤ Z * (y : ℝ) ^ 26 * (X + H) ^ (9 / 10 : ℝ) := by
  obtain ⟨Z, hZ0, hPE⟩ := pair_eval
  refine ⟨Z, hZ0, fun y hy X H hX hH => ?_⟩
  set W : ℕ → ℕ → ℝ := fun h k => Wint X H (Phi (fseq h k) (Real.log ((h * k : ℕ) : ℝ))) with hW
  set Mm : ℕ → ℕ → ℝ := fun h k => 2 * r0 / (Nat.lcm h k : ℝ) * (q0 h k * I1 X H + q1 h k * I0 X H) with hMm
  set D := ∑ p ∈ PS y, ∑ q ∈ PS y, cP (βSel y) p * cP (βSel y) q * W (hP p) (hP q) with hD
  refine ⟨D, D - 2 * r0 * (Q0 y * I1 X H + Q1 y * I0 X H), ?_, by ring, ?_⟩
  · unfold DiagSum
    rw [hD]; push_cast
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
    rw [(hPE (hP p) (hP q) (hP_pos hp) (hP_pos hq) X H hX hH).1]
    have := κ_two_sqrt y hp hq
    have e : κ (βSel y) p q * (2 * Real.sqrt ((hP p * hP q : ℕ) : ℝ) *
        Wint X H (Phi (fseq (hP p) (hP q)) (Real.log ((hP p * hP q : ℕ) : ℝ)))) =
        cP (βSel y) p * cP (βSel y) q * W (hP p) (hP q) := by
      simp only [hW]; rw [← this]; ring
    exact_mod_cast e
  · have hsplit : D - 2 * r0 * (Q0 y * I1 X H + Q1 y * I0 X H) =
        ∑ p ∈ PS y, ∑ q ∈ PS y, cP (βSel y) p * cP (βSel y) q * (W (hP p) (hP q) - Mm (hP p) (hP q)) := by
      rw [← main_sum y X H]
      have := regroup2 y Mm
      simp only [hMm] at this
      rw [← this, hD, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => by ring
    rw [hsplit]
    have hcard : ((PS y).card : ℝ) = (y : ℝ) ^ 2 := by
      simp [PS, Finset.card_product]; ring
    have hb : ∀ p ∈ PS y, ∀ q ∈ PS y, |cP (βSel y) p * cP (βSel y) q * (W (hP p) (hP q) - Mm (hP p) (hP q))| ≤
        Z * (y : ℝ) ^ 22 * (X + H) ^ (9 / 10 : ℝ) := by
      intro p hp q hq
      have e := (hPE (hP p) (hP q) (hP_pos hp) (hP_pos hq) X H hX hH).2
      have hpq : ((hP p * hP q : ℕ) : ℝ) ≤ (y : ℝ) ^ 4 := by
        push_cast
        have := hP_le y hp; have := hP_le y hq
        calc (hP p : ℝ) * hP q ≤ (y : ℝ) ^ 2 * (y : ℝ) ^ 2 := by
              exact mul_le_mul (hP_le y hp) (hP_le y hq) (Nat.cast_nonneg _) (by positivity)
          _ = (y : ℝ) ^ 4 := by ring
      have hY : 0 ≤ (X + H) ^ (9 / 10 : ℝ) := by positivity
      rw [abs_mul, abs_mul]
      calc |cP (βSel y) p| * |cP (βSel y) q| * |W (hP p) (hP q) - Mm (hP p) (hP q)|
          ≤ (y : ℝ) * y * (Z * ((y : ℝ) ^ 4) ^ 5 * (X + H) ^ (9 / 10 : ℝ)) := by
            refine mul_le_mul (mul_le_mul (abs_cP_le y hp) (abs_cP_le y hq) (abs_nonneg _) (Nat.cast_nonneg _))
              (e.trans ?_) (abs_nonneg _) (by positivity)
            gcongr
        _ = Z * (y : ℝ) ^ 22 * (X + H) ^ (9 / 10 : ℝ) := by ring
    calc _ ≤ ∑ p ∈ PS y, ∑ q ∈ PS y, |cP (βSel y) p * cP (βSel y) q * (W (hP p) (hP q) - Mm (hP p) (hP q))| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ PS y, ∑ q ∈ PS y, Z * (y : ℝ) ^ 22 * (X + H) ^ (9 / 10 : ℝ) :=
          Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hb p hp q hq
      _ = ((PS y).card : ℝ) * (((PS y).card : ℝ) * (Z * (y : ℝ) ^ 22 * (X + H) ^ (9 / 10 : ℝ))) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = _ := by rw [hcard]; ring

/-! ### Bounds for `I₀`, `I₁` -/

lemma I0_bounds {X H : ℝ} (hX : 16 ≤ X) (hH : 0 < H) : 0 ≤ I0 X H ∧ I0 X H ≤ X + H := by
  have hc : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc 16 (X + H)) := continuousOn_const
  refine ⟨Wint_nonneg hX hH hc (fun _ _ => zero_le_one), (Wint_le hX hH hc (fun _ _ => zero_le_one)).trans ?_⟩
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]; linarith

lemma I1_bounds {X H : ℝ} (hX : 16 ≤ X) (hH : 0 < H) : 0 ≤ I1 X H ∧ I1 X H ≤ (X + H) * Real.log (X + H) := by
  have hc : ContinuousOn ellT (Icc 16 (X + H)) := continuousOn_ellT'
  have h0 : ∀ t ∈ Icc 16 (X + H), 0 ≤ ellT t := fun t ht => ellT_nonneg ht.1
  refine ⟨Wint_nonneg hX hH hc h0, (Wint_le hX hH hc h0).trans ?_⟩
  have hXH : (16 : ℝ) ≤ X + H := by linarith
  have hlog : ∀ t ∈ Icc (16 : ℝ) (X + H), ellT t ≤ Real.log (X + H) := by
    intro t ht
    have h1 := ellT_mono (by linarith [ht.1] : (0 : ℝ) < t) ht.2
    have h2 : ellT (X + H) ≤ Real.log (X + H) := by
      unfold ellT
      rw [Real.log_div (by linarith) (by positivity)]
      have : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by have := Real.pi_gt_three; linarith)
      linarith
    linarith
  have hlog0 : 0 ≤ Real.log (X + H) := Real.log_nonneg (by linarith)
  calc (∫ t in (16 : ℝ)..X + H, ellT t) ≤ ∫ t in (16 : ℝ)..X + H, Real.log (X + H) :=
        intervalIntegral.integral_mono_on hXH (hc.intervalIntegrable_of_Icc hXH) intervalIntegrable_const hlog
    _ = (X + H - 16) * Real.log (X + H) := by rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ (X + H) * Real.log (X + H) := by nlinarith

/-! ### `DiagHyp θ ⇐ QFHyp` -/

set_option maxHeartbeats 1600000 in
/-- **`QFHyp` implies `DiagHyp θ`** for `0 < θ ≤ 1/260`. -/
theorem diag_of_QF {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 260) (hQ : QFHyp) : DiagHyp θ := by
  obtain ⟨Z, hZ0, hdec⟩ := diag_decomp
  obtain ⟨B, y₀, hB⟩ := hQ
  have hB0 : 0 ≤ B := by
    have := hB (⌈|y₀|⌉₊ + 2) (by
      have := Nat.le_ceil |y₀|; have := le_abs_self y₀; push_cast; linarith)
    exact (abs_nonneg _).trans this.2
  set A : ℝ := 2 * (|y₀| + 4) with hA
  have hA8 : 8 ≤ A := by have := abs_nonneg y₀; linarith
  set T₀ : ℝ := max 64 (A ^ (1 / θ)) with hT₀
  have hr0 := r0_pos
  refine ⟨12 * r0 * B * (4 / θ + 1) + 6 * Z, T₀, fun T hT X hXI => ?_⟩
  have hT64 : (64 : ℝ) ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hTA : A ≤ T ^ θ := by
    have h1 : A ^ (1 / θ) ≤ T := (le_max_right _ _).trans hT
    calc A = (A ^ (1 / θ)) ^ θ := by
          rw [← Real.rpow_mul (by linarith)]; field_simp; rw [Real.rpow_one]
      _ ≤ T ^ θ := Real.rpow_le_rpow (by positivity) h1 hθ0.le
  set y := ⌊T ^ θ⌋₊ with hydef
  have hyT : (y : ℝ) ≤ T ^ θ := Nat.floor_le (by positivity)
  have hyT' : T ^ θ - 1 < y := Nat.sub_one_lt_floor _
  have hy_half : T ^ θ / 2 ≤ y := by linarith
  have hy1 : 1 ≤ y := by
    have : (1 : ℝ) < y := by linarith
    exact_mod_cast this.le
  have hy0 : y₀ ≤ y := by have := le_abs_self y₀; linarith
  have hy2 : (2 : ℝ) ≤ y := by linarith
  obtain ⟨hQ0, hQ1⟩ := hB y hy0
  -- the parameters
  have hX16 : 16 ≤ X := by linarith [hXI.1]
  have hX0 : 0 < X := by linarith
  set H := X ^ (299 / 300 : ℝ) with hHdef
  have hH0 : 0 < H := Real.rpow_pos_of_pos hX0 _
  have hHX : H ≤ X := by
    calc H ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = X := Real.rpow_one X
  have hXH6 : X + H ≤ 6 * T := by linarith [hXI.2]
  obtain ⟨D, R, hDS, hDR, hR⟩ := hdec y hy1 X H hX16 hH0
  rw [hDS, Complex.norm_real, Real.norm_eq_abs, hDR]
  obtain ⟨hI00, hI0⟩ := I0_bounds hX16 hH0
  obtain ⟨hI10, hI1⟩ := I1_bounds hX16 hH0
  -- logs
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogXH : Real.log (X + H) ≤ 2 * Real.log T := by
    calc Real.log (X + H) ≤ Real.log (T * T) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log T := by rw [Real.log_mul hT0.ne' hT0.ne']; ring
  have hlogy : θ / 2 * Real.log T ≤ Real.log y := by
    have h1 : Real.log (T ^ θ / 2) ≤ Real.log y := Real.log_le_log (by positivity) hy_half
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hT0] at h1
    have h4 : Real.log 4 ≤ θ * Real.log T := by
      rw [← Real.log_rpow hT0]; exact Real.log_le_log (by norm_num) (by linarith)
    have h22 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hlogy0 : 0 < Real.log y := lt_of_lt_of_le (by positivity) hlogy
  -- main term
  have hmain : |2 * r0 * (Q0 y * I1 X H + Q1 y * I0 X H)| ≤ 12 * r0 * B * (4 / θ + 1) * T := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have e1 : |Q0 y * I1 X H| ≤ B / Real.log y * ((X + H) * Real.log (X + H)) := by
      rw [abs_mul, abs_of_nonneg hI10]; exact mul_le_mul hQ0 hI1 hI10 (by positivity)
    have e2 : |Q1 y * I0 X H| ≤ B * (X + H) := by
      rw [abs_mul, abs_of_nonneg hI00]; exact mul_le_mul hQ1 hI0 hI00 hB0
    have e3 : B / Real.log y * ((X + H) * Real.log (X + H)) ≤ B * (6 * T) * (4 / θ) := by
      have hr : Real.log (X + H) / Real.log y ≤ 4 / θ := by
        rw [div_le_div_iff₀ hlogy0 hθ0]
        nlinarith
      have hXH0 : 0 ≤ X + H := by linarith
      calc B / Real.log y * ((X + H) * Real.log (X + H)) = B * (X + H) * (Real.log (X + H) / Real.log y) := by
            field_simp
        _ ≤ B * (6 * T) * (4 / θ) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hXH6 hB0) hr
            · exact div_nonneg (Real.log_nonneg (by linarith)) hlogy0.le
            · positivity
    calc 2 * r0 * |Q0 y * I1 X H + Q1 y * I0 X H| ≤ 2 * r0 * (|Q0 y * I1 X H| + |Q1 y * I0 X H|) := by
          gcongr; exact abs_add_le _ _
      _ ≤ 2 * r0 * (B * (6 * T) * (4 / θ) + B * (6 * T)) := by
          gcongr
          · exact e1.trans e3
          · exact e2.trans (mul_le_mul_of_nonneg_left hXH6 hB0)
      _ = 12 * r0 * B * (4 / θ + 1) * T := by ring
  -- error term
  have herr : |R| ≤ 6 * Z * T := by
    have hy26 : (y : ℝ) ^ 26 ≤ T ^ (1 / 10 : ℝ) := by
      calc (y : ℝ) ^ 26 ≤ (T ^ θ) ^ 26 := pow_le_pow_left₀ (Nat.cast_nonneg _) hyT 26
        _ = T ^ (θ * 26) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
        _ ≤ T ^ (1 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hXHp : (X + H) ^ (9 / 10 : ℝ) ≤ 6 * T ^ (9 / 10 : ℝ) := by
      calc (X + H) ^ (9 / 10 : ℝ) ≤ (6 * T) ^ (9 / 10 : ℝ) := Real.rpow_le_rpow (by linarith) hXH6 (by norm_num)
        _ = 6 ^ (9 / 10 : ℝ) * T ^ (9 / 10 : ℝ) := Real.mul_rpow (by norm_num) hT0.le
        _ ≤ 6 * T ^ (9 / 10 : ℝ) := by
            gcongr
            calc (6 : ℝ) ^ (9 / 10 : ℝ) ≤ 6 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 6 := Real.rpow_one 6
    have hTT : T ^ (1 / 10 : ℝ) * T ^ (9 / 10 : ℝ) = T := by
      rw [← Real.rpow_add hT0]; norm_num
    calc |R| ≤ Z * (y : ℝ) ^ 26 * (X + H) ^ (9 / 10 : ℝ) := hR
      _ ≤ Z * T ^ (1 / 10 : ℝ) * (6 * T ^ (9 / 10 : ℝ)) := by gcongr
      _ = 6 * Z * (T ^ (1 / 10 : ℝ) * T ^ (9 / 10 : ℝ)) := by ring
      _ = 6 * Z * T := by rw [hTT]
  calc |2 * r0 * (Q0 y * I1 X H + Q1 y * I0 X H) + R| ≤ |2 * r0 * (Q0 y * I1 X H + Q1 y * I0 X H)| + |R| :=
        abs_add_le _ _
    _ ≤ 12 * r0 * B * (4 / θ + 1) * T + 6 * Z * T := add_le_add hmain herr
    _ = (12 * r0 * B * (4 / θ + 1) + 6 * Z) * T := by ring

open RamanujanTau.HafnerProportion RamanujanTau.HeckeL RamanujanTau.SelbergCoeffs in
/-- **Hafner's (MV2) from the quadratic-form hypothesis.** -/
theorem mv2_of_QF {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 81600) (hQ : QFHyp) :
    ∃ B T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∫ u in T..(3 * T), ‖tauL (6 + u * I) * Mc (bSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊ (6 + u * I) ^ 2‖ ^ 2) ≤ B * T :=
  mv2_of_diag hθ0 (by linarith) (diag_of_QF hθ0 (by linarith) hQ)

end RamanujanTau.HafnerBridge2
