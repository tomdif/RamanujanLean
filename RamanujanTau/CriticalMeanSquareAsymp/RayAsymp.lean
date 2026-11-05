/-
# The weighted asymptotic: `∫ |Λ(6+it)|² e^{2βt} dt ~ 12‖Δ‖² κ^{-12} log(1/κ)`

Here `κ = cot β → 0⁺` as `β → π/2⁻`.  By `weighted_parseval` the left side is
`2π ∫_ℝ Ru β`.  The integrand is even up to `β ↦ −β`
(`Ru β (−u) = Ru (−β) u`, from `Λ(12−s) = Λ(s)`), and `Ru (∓β)` is the integrand along
the ray `τ = ±w + iκw`, `w = sin β · e^u`.  On each ray:

* `w ∈ [s, 1]` contributes `O(κ^{-12})` (sup bound `|Δ| ≤ M y^{-6}`);
* `w ∈ [1, n+1]`, `n = ⌊1/κ⌋`, contributes `κ^{-12} (∑_{N ≤ n} A(κN)/N + O(1))`
  (`Block.sum_sharp`), with `A(y) = ∫₀¹|Δ(x+iy)|²y¹² dx → (3/π)‖Δ‖²` (Zagier,
  `EisensteinReal.Horo.tendsto_Aint_zagier`), so the sum is `~ (3/π)‖Δ‖² log(1/κ)`
  (`Harmonic.harm_tendsto`);
* `w ≥ n+1` contributes `O(κ^{-12})` (cusp decay).

Total: `2π · 2 · (3/π)‖Δ‖² = 12‖Δ‖²`.
-/
import RamanujanTau.CriticalMeanSquareAsymp.Block
import RamanujanTau.CriticalMeanSquareAsymp.Harmonic

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquareAsymp

open Complex MeasureTheory Set Filter Topology
open UpperHalfPlane hiding I
open RamanujanTau.HardyZeros RamanujanTau.HardyCountHafner
  RamanujanTau.CriticalMeanSquare RamanujanTau.CriticalMeanSquareLower
open scoped Real Interval

lemma Ru_eq_Gs (β u : ℝ) : Ru β u = ‖Gs 6 ((u : ℂ) + β * I)‖ ^ 2 := by
  unfold Ru Gs; norm_num

/-- **Evenness** up to `β ↦ −β`. -/
lemma Ru_even {β : ℝ} (hβ : |β| < π / 2) (u : ℝ) : Ru β (-u) = Ru (-β) u := by
  rw [Ru_eq_Gs, Ru_eq_Gs]
  have h1 : (((-u : ℝ) : ℂ) + β * I) ∈ strip := by
    show |(((-u : ℝ) : ℂ) + β * I).im| < π / 2; simpa using hβ
  have h2 : (((u : ℝ) : ℂ) + ((-β : ℝ) : ℂ) * I) ∈ strip := by
    show |(((u : ℝ) : ℂ) + ((-β : ℝ) : ℂ) * I).im| < π / 2; simpa using hβ
  have e1 := Phis_eq_strip (le_refl 6) (by norm_num) h1
  have e2 := Phis_eq_strip (le_refl 6) (by norm_num) h2
  have e3 : Phis 6 (((-u : ℝ) : ℂ) + β * I) = Phis 6 (((u : ℝ) : ℂ) + ((-β : ℝ) : ℂ) * I) := by
    rw [← Phis_six_neg]; congr 1; push_cast; ring
  rw [e1, e2] at e3
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * π := by positivity
    exact_mod_cast this.ne'
  have := mul_left_cancel₀ h2π e3
  rw [this]

lemma ray_point_neg (β u : ℝ) (hs : 0 < Real.sin β) :
    cexp ((u : ℂ) + ((-β : ℝ) : ℂ) * I) * I =
      pt (1 * (Real.sin β * Real.exp u)) (Real.cos β / Real.sin β * (Real.sin β * Real.exp u)) := by
  rw [Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  unfold pt
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    push_cast
    ring
  · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    push_cast
    field_simp
    ring

lemma ray_point_pos (β u : ℝ) (hs : 0 < Real.sin β) :
    cexp ((u : ℂ) + (β : ℂ) * I) * I =
      pt (-1 * (Real.sin β * Real.exp u)) (Real.cos β / Real.sin β * (Real.sin β * Real.exp u)) := by
  rw [ray_point β u hs, neg_one_mul]

lemma Ru_eq_gen {β' σ s κ : ℝ} (hs : 0 < s)
    (hpt : ∀ u : ℝ, cexp ((u : ℂ) + (β' : ℂ) * I) * I = pt (σ * (s * Real.exp u)) (κ * (s * Real.exp u)))
    (u : ℝ) : Ru β' u = Gsig σ κ (s * Real.exp u) / s ^ 12 * (s * Real.exp u) := by
  unfold Ru Gsig
  rw [hpt u, norm_mul, mul_pow, Complex.norm_exp]
  have hre : (6 * ((u : ℂ) + β' * I)).re = 6 * u := by simp
  rw [hre]
  have he : Real.exp (6 * u) ^ 2 = Real.exp u ^ 12 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; push_cast; ring_nf
  rw [he]
  field_simp

/-- Change of variables `w = s e^u` for a general ray integrand. -/
lemma integral_change {R g : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (hg : ContinuousOn g (Ioi 0))
    (hR : ∀ u, R u = g (s * Real.exp u) / s ^ 12 * (s * Real.exp u)) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∫ u in Real.log (a / s)..Real.log (b / s), R u = (∫ w in a..b, g w) / s ^ 12 := by
  have hcv := intervalIntegral.integral_comp_mul_deriv'
    (a := Real.log (a / s)) (b := Real.log (b / s))
    (f := fun u => s * Real.exp u) (f' := fun u => s * Real.exp u)
    (g := fun w => g w / s ^ 12)
    (fun u _ => (Real.hasDerivAt_exp u).const_mul s)
    (continuous_const.mul Real.continuous_exp).continuousOn
    ((hg.div_const _).mono (by
      rintro _ ⟨u, _, rfl⟩; show 0 < s * Real.exp u; positivity))
  simp only [Function.comp_apply] at hcv
  rw [Real.exp_log (div_pos ha hs), Real.exp_log (div_pos hb hs),
    mul_div_cancel₀ _ hs.ne', mul_div_cancel₀ _ hs.ne'] at hcv
  rw [← intervalIntegral.integral_div, ← hcv]
  exact intervalIntegral.integral_congr (fun u _ => hR u)

/-- Cusp tail. -/
lemma tail_bound {σ s κ M U : ℝ} {R : ℝ → ℝ} (hs : 0 < s) (hκ : 0 < κ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖Dc z‖ * z.im ^ 6 ≤ M * Real.exp (-(π * z.im)))
    (hR : ∀ u, R u = Gsig σ κ (s * Real.exp u) / s ^ 12 * (s * Real.exp u))
    (hRi : IntegrableOn R (Ioi U)) (hU : 1 ≤ κ * (s * Real.exp U)) :
    κ ^ 12 * ∫ u in Ioi U, R u ≤ M ^ 2 / s ^ 12 := by
  have hpt : ∀ u ∈ Ioi U, κ ^ 12 * R u ≤ M ^ 2 / s ^ 12 * Real.exp U * Real.exp (-u) := by
    intro u hu
    have hu' : U < u := hu
    set w := s * Real.exp u with hw
    have hw0 : 0 < w := by positivity
    have him : 0 < (pt (σ * w) (κ * w)).im := by rw [pt_im]; positivity
    have hb := hM _ him
    rw [pt_im] at hb
    have hκw : u - U ≤ κ * w := by
      have h1 : κ * w = κ * (s * Real.exp U) * Real.exp (u - U) := by
        rw [hw, Real.exp_sub]; field_simp
      have h2 : u - U + 1 ≤ Real.exp (u - U) := Real.add_one_le_exp _
      have h3 : 1 * Real.exp (u - U) ≤ κ * (s * Real.exp U) * Real.exp (u - U) :=
        mul_le_mul_of_nonneg_right hU (Real.exp_pos _).le
      linarith
    have hexp : Real.exp (-(π * (κ * w))) ^ 2 ≤ Real.exp U * Real.exp (-u) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : 1 ≤ π := by linarith [Real.pi_gt_three]
      have hκw0 : 0 ≤ κ * w := by positivity
      push_cast; nlinarith
    have hsq : (‖Dc (pt (σ * w) (κ * w))‖ * (κ * w) ^ 6) ^ 2 ≤
        M ^ 2 * (Real.exp U * Real.exp (-u)) := by
      have h0 : 0 ≤ ‖Dc (pt (σ * w) (κ * w))‖ * (κ * w) ^ 6 := by positivity
      calc (‖Dc (pt (σ * w) (κ * w))‖ * (κ * w) ^ 6) ^ 2 ≤ (M * Real.exp (-(π * (κ * w)))) ^ 2 :=
            pow_le_pow_left₀ h0 hb 2
        _ = M ^ 2 * Real.exp (-(π * (κ * w))) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
    rw [hR u, ← hw]
    unfold Gsig
    have e : κ ^ 12 * (w ^ 11 * ‖Dc (pt (σ * w) (κ * w))‖ ^ 2 / s ^ 12 * w) =
        (‖Dc (pt (σ * w) (κ * w))‖ * (κ * w) ^ 6) ^ 2 / s ^ 12 := by ring
    rw [e, show M ^ 2 / s ^ 12 * Real.exp U * Real.exp (-u) =
      M ^ 2 * (Real.exp U * Real.exp (-u)) / s ^ 12 by ring]
    gcongr
  have hint2 : IntegrableOn (fun u => M ^ 2 / s ^ 12 * Real.exp U * Real.exp (-u)) (Ioi U) :=
    (integrableOn_exp_neg_Ioi U).const_mul _
  rw [← integral_const_mul]
  refine (setIntegral_mono_on (hRi.const_mul _) hint2 measurableSet_Ioi hpt).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_neg_Ioi, mul_assoc, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, mul_one]

/-- **One ray, decomposed.** -/
lemma ray_decomp {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {M A : ℝ} (hM0 : 0 ≤ M) (hA0 : 0 ≤ A)
    (hMb : ∀ z : ℂ, 0 < z.im →
      ‖Dc z‖ ≤ M / z.im ^ 6 ∧ ‖Dc z‖ * z.im ^ 6 ≤ M * Real.exp (-(π * z.im)))
    (hA : ∀ x y₁ y₂ y₀ : ℝ, 0 < y₀ → y₀ ≤ y₁ → y₀ ≤ y₂ →
      ‖Dc (pt x y₁) - Dc (pt x y₂)‖ ≤ A * |y₁ - y₂| / y₀ ^ 7)
    {s κ : ℝ} (hs : 1 / 2 ≤ s) (hs1 : s < 1) (hκ : 0 < κ) (hκ1 : κ < 1) {R : ℝ → ℝ}
    (hR : ∀ u, R u = Gsig σ κ (s * Real.exp u) / s ^ 12 * (s * Real.exp u))
    (hRi : Integrable R) :
    |s ^ 12 * (κ ^ 12 * ∫ u in Ioi 0, R u) -
      ∑ j ∈ Finset.range ⌊1 / κ⌋₊, EisensteinReal.Horo.Aint (κ * ((j : ℝ) + 1)) / ((j : ℝ) + 1)| ≤
      2 * M ^ 2 + 2 * (2047 * M ^ 2 + 2 * A * M) := by
  have hs0 : 0 < s := by linarith
  set n := ⌊1 / κ⌋₊ with hn
  set N₂ : ℝ := (n : ℝ) + 1 with hN₂
  have hN₂1 : 1 ≤ N₂ := by rw [hN₂]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hκN : 1 ≤ κ * N₂ := by
    have := Nat.lt_floor_add_one (1 / κ)
    rw [← hn, div_lt_iff₀ hκ] at this
    rw [hN₂]; linarith
  set U := Real.log (N₂ / s) with hU
  have hU0 : 0 ≤ U := Real.log_nonneg (by rw [le_div_iff₀ hs0]; linarith)
  have hsU : s * Real.exp U = N₂ := by rw [hU, Real.exp_log (by positivity)]; field_simp
  have hR0 : ∀ u, 0 ≤ R u := fun u => by
    rw [hR u]; have := Gsig_nonneg σ κ (show 0 ≤ s * Real.exp u by positivity); positivity
  -- split at `U`
  have hsplit : ∫ u in Ioi 0, R u = (∫ u in (0 : ℝ)..U, R u) + ∫ u in Ioi U, R u := by
    rw [← Ioc_union_Ioi_eq_Ioi hU0, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      hRi.integrableOn hRi.integrableOn, intervalIntegral.integral_of_le hU0]
  have hcv : ∫ u in (0 : ℝ)..U, R u = (∫ w in s..N₂, Gsig σ κ w) / s ^ 12 := by
    have := integral_change hs0 (continuousOn_Gsig σ hκ) hR hs0 (by positivity : 0 < N₂)
    rw [div_self hs0.ne', Real.log_one] at this
    exact this
  have hii : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable (Gsig σ κ) volume a b := by
    intro a b ha hb
    refine ContinuousOn.intervalIntegrable ((continuousOn_Gsig σ hκ).mono ?_)
    intro w hw
    show 0 < w
    have : 0 < min a b := lt_min ha hb
    linarith [hw.1]
  have hsplit2 : ∫ w in s..N₂, Gsig σ κ w = (∫ w in s..1, Gsig σ κ w) + ∫ w in (1 : ℝ)..N₂, Gsig σ κ w :=
    (intervalIntegral.integral_add_adjacent_intervals (hii _ _ hs0 one_pos)
      (hii _ _ one_pos (by linarith))).symm
  -- the piece `[s, 1]`
  have hκ12 : 0 < κ ^ 12 := by positivity
  have hP1 : 0 ≤ κ ^ 12 * ∫ w in s..1, Gsig σ κ w ∧ κ ^ 12 * ∫ w in s..1, Gsig σ κ w ≤ M ^ 2 := by
    constructor
    · exact mul_nonneg hκ12.le (intervalIntegral.integral_nonneg hs1.le fun w hw =>
        Gsig_nonneg σ κ (by linarith [hw.1]))
    · have hpt : ∀ w ∈ Ι s 1, ‖κ ^ 12 * Gsig σ κ w‖ ≤ 2 * M ^ 2 := by
        intro w hw
        rw [uIoc_of_le hs1.le] at hw
        obtain ⟨hw1, hw2⟩ := hw
        have hw0 : 0 < w := by linarith
        have him : 0 < (pt (σ * w) (κ * w)).im := by rw [pt_im]; positivity
        have hb := (hMb _ him).1
        rw [pt_im] at hb
        have hb2 : ‖Dc (pt (σ * w) (κ * w))‖ ^ 2 ≤ (M / (κ * w) ^ 6) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hκ12.le (Gsig_nonneg σ κ hw0.le))]
        unfold Gsig
        have e : κ ^ 12 * (w ^ 11 * (M / (κ * w) ^ 6) ^ 2) = M ^ 2 / w := by
          field_simp
        have h1 : κ ^ 12 * (w ^ 11 * ‖Dc (pt (σ * w) (κ * w))‖ ^ 2) ≤ M ^ 2 / w := by
          rw [← e]; gcongr
        have h2 : M ^ 2 / w ≤ 2 * M ^ 2 := by
          rw [div_le_iff₀ hw0]; nlinarith [sq_nonneg M]
        linarith
      have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs] at this
      have h3 := (le_abs_self _).trans this
      have h4 : 2 * M ^ 2 * |1 - s| ≤ M ^ 2 := by
        rw [abs_of_pos (by linarith)]; nlinarith [sq_nonneg M]
      linarith
  -- the tail
  have hP3 : 0 ≤ κ ^ 12 * ∫ u in Ioi U, R u ∧ κ ^ 12 * ∫ u in Ioi U, R u ≤ M ^ 2 / s ^ 12 := by
    refine ⟨mul_nonneg hκ12.le (setIntegral_nonneg measurableSet_Ioi fun u _ => hR0 u), ?_⟩
    exact tail_bound hs0 hκ (fun z hz => (hMb z hz).2) hR hRi.integrableOn (by rw [hsU]; exact hκN)
  -- the blocks
  have hP2 := sum_sharp hM0 hA0 (fun z hz => (hMb z hz).1) hA hσ hκ n
  rw [← hN₂] at hP2
  -- assemble
  have hs12 : 0 < s ^ 12 := by positivity
  have eq : s ^ 12 * (κ ^ 12 * ∫ u in Ioi 0, R u) =
      κ ^ 12 * (∫ w in s..1, Gsig σ κ w) + κ ^ 12 * (∫ w in (1 : ℝ)..N₂, Gsig σ κ w) +
        s ^ 12 * (κ ^ 12 * ∫ u in Ioi U, R u) := by
    rw [hsplit, hcv, hsplit2]; field_simp
  rw [eq]
  have hP3' : s ^ 12 * (κ ^ 12 * ∫ u in Ioi U, R u) ≤ M ^ 2 := by
    have := mul_le_mul_of_nonneg_left hP3.2 hs12.le
    rwa [mul_div_cancel₀ _ hs12.ne'] at this
  have hP3'' : 0 ≤ s ^ 12 * (κ ^ 12 * ∫ u in Ioi U, R u) := mul_nonneg hs12.le hP3.1
  rw [abs_le] at hP2 ⊢
  constructor <;> linarith [hP1.1, hP1.2]

/-- `cot β → 0⁺` as `β → π/2⁻`. -/
lemma tendsto_cot : Tendsto (fun β => Real.cos β / Real.sin β) (𝓝[<] (π / 2)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : ContinuousAt (fun β => Real.cos β / Real.sin β) (π / 2) :=
      Real.continuous_cos.continuousAt.div Real.continuous_sin.continuousAt (by simp)
    have := h.tendsto
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT (show 0 < π / 2 by positivity)] with β hβ
    exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [hβ.1, Real.pi_pos], hβ.2⟩)
      (Real.sin_pos_of_pos_of_lt_pi hβ.1 (by linarith [hβ.2, Real.pi_pos]))

lemma tendsto_sin_pow : Tendsto (fun β => Real.sin β ^ 12) (𝓝[<] (π / 2)) (𝓝 1) := by
  have := (Real.continuous_sin.pow 12).continuousAt (x := π / 2) |>.tendsto
  simp only [Real.sin_pi_div_two, one_pow] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- The horocycle constant `c₀ = (3/π)‖Δ‖²`. -/
noncomputable def c0 : ℝ := 3 / π * EisensteinReal.petNormSq

lemma alg_identity {a L S t : ℝ} (ht : t ≠ 0) (hL : L ≠ 0) :
    a / L = (S / L + (t * a - S) / L) / t := by
  field_simp; ring

/-- `κ¹² ∫_0^∞ Ru (±β) / log(1/κ) → c₀` along one ray. -/
lemma ray_tendsto {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {R : ℝ → ℝ → ℝ}
    (hR : ∀ β, 0 < Real.sin β → ∀ u, R β u =
      Gsig σ (Real.cos β / Real.sin β) (Real.sin β * Real.exp u) / Real.sin β ^ 12 *
        (Real.sin β * Real.exp u))
    (hRi : ∀ β, 0 < β → β < π / 2 → Integrable (R β)) :
    Tendsto (fun β => (Real.cos β / Real.sin β) ^ 12 * (∫ u in Ioi 0, R β u) /
      Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2)) (𝓝 c0) := by
  obtain ⟨M, hM0, hMb⟩ := exists_Dc_bounds
  obtain ⟨A, hA0, hA⟩ := exists_Dc_lip
  set C₁ := 2 * M ^ 2 + 2 * (2047 * M ^ 2 + 2 * A * M) with hC₁
  set Sm : ℝ → ℝ := fun κ => ∑ j ∈ Finset.range ⌊1 / κ⌋₊,
    EisensteinReal.Horo.Aint (κ * ((j : ℝ) + 1)) / ((j : ℝ) + 1) with hSm
  -- the harmonic limit
  obtain ⟨G0, hG00, hG0⟩ := EisensteinReal.Horo.exists_G_le
  have hAint0 : ∀ y, 0 < y → 0 ≤ EisensteinReal.Horo.Aint y := fun y hy =>
    EisensteinReal.Horo.Aint_nonneg y
  have hAintH : ∀ y, 0 < y → EisensteinReal.Horo.Aint y ≤ G0 := by
    intro y hy
    unfold EisensteinReal.Horo.Aint
    rw [dif_pos hy]
    have h := intervalIntegral.integral_mono_on (f := fun x => RankinSelberg.G (RankinSelberg.hp hy x))
      (g := fun _ => G0) zero_le_one ?_ (intervalIntegrable_const (μ := MeasureTheory.volume))
      (fun x _ => hG0 _)
    · simpa using h
    · exact (EisensteinReal.Horo.continuous_G_hp hy).intervalIntegrable _ _
  have hH := harm_tendsto hAint0 hAintH EisensteinReal.Horo.tendsto_Aint_zagier
  have hHβ := hH.comp tendsto_cot
  -- the error term
  have hLβ : Tendsto (fun β => Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2)) atTop := by
    have h1 : Tendsto (fun κ : ℝ => Real.log (1 / κ)) (𝓝[>] 0) atTop := by
      have := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
      refine this.congr fun κ => ?_
      simp [one_div]
    exact h1.comp tendsto_cot
  have hev : ∀ᶠ β in 𝓝[<] (π / 2), π / 3 < β ∧ β < π / 2 :=
    Ioo_mem_nhdsLT (show π / 3 < π / 2 by linarith [Real.pi_pos])
  have hE : Tendsto (fun β => (Real.sin β ^ 12 * ((Real.cos β / Real.sin β) ^ 12 *
      ∫ u in Ioi 0, R β u) - Sm (Real.cos β / Real.sin β)) /
      Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2)) (𝓝 0) := by
    have hC : Tendsto (fun β => C₁ / Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2))
        (𝓝 0) := tendsto_const_nhds.div_atTop hLβ
    refine squeeze_zero_norm' ?_ hC
    filter_upwards [hev, hLβ.eventually_gt_atTop 0] with β hβ hL
    obtain ⟨hβ1, hβ2⟩ := hβ
    have hs : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ2⟩
    have hs2 : 1 / 2 ≤ Real.sin β := by
      have h1 : Real.sin (π / 6) ≤ Real.sin β := Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos]) hβ2.le (by linarith [Real.pi_pos])
      rwa [Real.sin_pi_div_six] at h1
    have hs1 : Real.sin β < 1 := by
      have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl hβ2
      rwa [Real.sin_pi_div_two] at this
    have hκ1 : Real.cos β / Real.sin β < 1 := by
      rw [div_lt_one hs]
      have h1 : Real.cos β < Real.cos (π / 4) := Real.cos_lt_cos_of_nonneg_of_le_pi
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      have h2 : Real.sin (π / 4) < Real.sin β := Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by linarith [Real.pi_pos]) hβ2.le (by linarith [Real.pi_pos])
      rw [Real.cos_pi_div_four] at h1; rw [Real.sin_pi_div_four] at h2
      linarith
    have hd := ray_decomp hσ hM0 hA0 hMb hA hs2 hs1 (div_pos hc hs) hκ1 (hR β hs)
      (hRi β (by linarith [Real.pi_pos]) hβ2)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right hd hL.le
  -- combine
  have hlim := (hHβ.add hE).div tendsto_sin_pow one_ne_zero
  rw [add_zero, div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev, hLβ.eventually_gt_atTop 0] with β hβ hL
  have hs : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, hβ.1])
    (by linarith [Real.pi_pos, hβ.2])
  have key := alg_identity (a := (Real.cos β / Real.sin β) ^ 12 * ∫ u in Ioi 0, R β u)
    (L := Real.log (1 / (Real.cos β / Real.sin β))) (S := Sm (Real.cos β / Real.sin β))
    (pow_ne_zero 12 hs.ne') hL.ne'
  exact key.symm

end RamanujanTau.CriticalMeanSquareAsymp
