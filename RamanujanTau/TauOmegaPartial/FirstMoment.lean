/-
# Mean-square lower bound on lines just right of the critical line, uniform in `σ'`

For `k/2 + 1/8 ≤ σ' ≤ k/2 + 1/4` and `Y ≥ Y₀`:

    ∫_Y^{2Y} |L(f, σ'+iy)|² dy ≥ c₃ Y.

Proof: first moment of `G(s) = L(f,s) m^s` (`m` = least index with `a(m) ≠ 0`). On a far-right line
`G = a(m) + O(|a(m)|/2)` (`tail_small`), so `|∫_Y^{2Y} G| ≥ |a(m)|Y/2`; the rectangle to `Re s = σ'`
costs only the horizontal sides, `≪ Y^{7/8}` by convexity; then Cauchy–Schwarz.
-/
import RamanujanTau.TauOmegaPartial.FE
import RamanujanTau.KernelPhase.Pieces

set_option autoImplicit false

namespace RamanujanTau.TauOmegaPartial

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups Real Interval

variable {k : ℕ}

/-- Cauchy–Schwarz on an interval: `(∫_a^b g)² ≤ (b−a) ∫_a^b g²`. -/
lemma sq_integral_le {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
  set I1 := ∫ x in a..b, g x
  set I2 := ∫ x in a..b, g x ^ 2
  set μ := I1 / (b - a)
  have hba : 0 < b - a := by linarith
  have h0 : 0 ≤ ∫ x in a..b, (g x - μ) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun x _ => sq_nonneg _
  have hexp : ∫ x in a..b, (g x - μ) ^ 2 = I2 - 2 * μ * I1 + μ ^ 2 * (b - a) := by
    have e : ∀ x, (g x - μ) ^ 2 = g x ^ 2 - 2 * μ * g x + μ ^ 2 := fun x => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    · simp [smul_eq_mul]; ring
    · exact (hg.pow 2).intervalIntegrable _ _
    · exact (hg.const_smul (2 * μ)).intervalIntegrable _ _
    · exact ((hg.pow 2).sub (hg.const_smul (2 * μ))).intervalIntegrable _ _
    · exact intervalIntegrable_const
  rw [hexp] at h0
  have hμ : μ * (b - a) = I1 := by simp only [μ]; field_simp
  nlinarith

/-- **Uniform convexity bound on the horizontal sides**: `‖L(f, x+iy)‖ ≤ K y^{7/8}`
for `k/2 + 1/8 ≤ x ≤ c`, `y ≥ 1`. -/
lemma horiz_bound (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) (c : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : ℝ, (k : ℝ) / 2 + 1 / 8 ≤ x → x ≤ c → 1 ≤ y →
      ‖fL f ((x : ℂ) + y * I)‖ ≤ K * y ^ ((7 : ℝ) / 8) := by
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨C, hC0, hC⟩ := fC_bound f hk (ε := 1 / 2) (by norm_num) le_rfl
  obtain ⟨D, hD0, hD⟩ := fL_bounded_of_gt f (by omega) (σ := ((k : ℝ) + 2) / 2) (by linarith)
  set c' : ℝ := |c| + 1 with hc'
  have hc'1 : 1 ≤ c' := by rw [hc']; linarith [abs_nonneg c]
  refine ⟨2 * Real.exp 10 * C * c' ^ ((7 : ℝ) / 8) + D, by positivity, fun x y hx1 hx2 hy => ?_⟩
  set s : ℂ := (x : ℂ) + y * I with hs
  have hsre : s.re = x := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  have hy78 : 1 ≤ y ^ ((7 : ℝ) / 8) := Real.one_le_rpow hy (by norm_num)
  have hA0 : 0 ≤ 2 * Real.exp 10 * C * c' ^ ((7 : ℝ) / 8) := by positivity
  rcases le_or_gt x (((k : ℝ) + 2) / 2) with hx | hx
  · have hL := fL_line f hk (ε := 1 / 2) (by norm_num) le_rfl hC (s := s)
      (by rw [hsre]; linarith) (by rw [hsre]; linarith)
    rw [hsre] at hL
    set θ : ℝ := ((k : ℝ) + 1) / 2 + 1 / 2 - x with hθ
    have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
    have hθ1 : θ ≤ 7 / 8 := by rw [hθ]; linarith
    have hn : ‖s / 2‖ ≤ c' * y := by
      rw [norm_div, Complex.norm_two, div_le_iff₀ (by norm_num)]
      refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
      rw [hsre, hsim, abs_of_nonneg (by linarith : (0:ℝ) ≤ y), hc']
      have : |x| ≤ |c| := by rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; exact hx2
      nlinarith [abs_nonneg c]
    have hp : ‖s / 2‖ ^ θ ≤ (c' * y) ^ ((7 : ℝ) / 8) := by
      have hcy : 1 ≤ c' * y := by nlinarith
      calc ‖s / 2‖ ^ θ ≤ (c' * y) ^ θ := Real.rpow_le_rpow (norm_nonneg _) hn hθ0
        _ ≤ (c' * y) ^ ((7 : ℝ) / 8) := Real.rpow_le_rpow_of_exponent_le hcy hθ1
    rw [Real.mul_rpow (by linarith) (by linarith)] at hp
    calc ‖fL f s‖ ≤ 2 * Real.exp 10 * C * ‖s / 2‖ ^ θ := hL
      _ ≤ 2 * Real.exp 10 * C * (c' ^ ((7 : ℝ) / 8) * y ^ ((7 : ℝ) / 8)) := by gcongr
      _ ≤ (2 * Real.exp 10 * C * c' ^ ((7 : ℝ) / 8) + D) * y ^ ((7 : ℝ) / 8) := by
        nlinarith
  · have := hD s (by rw [hsre]; exact hx.le)
    nlinarith

/-- **Uniform mean-square lower bound** on the lines `k/2 + 1/8 ≤ σ' ≤ k/2 + 1/4`. -/
theorem first_moment (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {m : ℕ} (hm : 1 ≤ m)
    (hlow : ∀ n < m, coef f n = 0) (hm0 : coef f m ≠ 0) :
    ∃ c3 : ℝ, 0 < c3 ∧ ∃ Y0 : ℝ, 1 ≤ Y0 ∧ ∀ σ' : ℝ, (k : ℝ) / 2 + 1 / 8 ≤ σ' →
      σ' ≤ (k : ℝ) / 2 + 1 / 4 → ∀ Y : ℝ, Y0 ≤ Y →
        c3 * Y ≤ ∫ y in Y..2 * Y, ‖fL f ((σ' : ℂ) + y * I)‖ ^ 2 := by
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨c, hc, htail⟩ := tail_small f (by omega) hm hlow hm0
  obtain ⟨K, hK0, hK⟩ := horiz_bound f hk c
  set a : ℝ := ‖coef f m‖ with ha
  have ha0 : 0 < a := norm_pos_iff.2 hm0
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set mc : ℝ := (m : ℝ) ^ c with hmc
  have hmc1 : 1 ≤ mc := Real.one_le_rpow hmR (by linarith)
  set G : ℂ → ℂ := fun s => fL f s * (m : ℂ) ^ s with hG
  have hm0' : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hGd : Differentiable ℂ G :=
    (fL_entire f (by omega)).mul (differentiable_id.const_cpow (Or.inl hm0'))
  have hGc : Continuous G := hGd.continuous
  have hGn : ∀ x y : ℝ, x ≤ c → ‖G ((x : ℂ) + y * I)‖ ≤ mc * ‖fL f ((x : ℂ) + y * I)‖ := by
    intro x y hx
    simp only [hG, norm_mul]
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    have : ((x : ℂ) + y * I).re = x := by simp
    rw [this, mul_comm]
    gcongr
    exact Real.rpow_le_rpow_of_exponent_le hmR hx
  set E : ℝ := 4 * (c - (k : ℝ) / 2) * mc * K with hE
  have hE0 : 0 ≤ E := by rw [hE]; have : 0 ≤ c - (k : ℝ) / 2 := by linarith
                         positivity
  set Y0 : ℝ := max 1 ((4 * E / a) ^ (8 : ℕ)) with hY0
  refine ⟨a ^ 2 / (16 * mc ^ 2), by positivity, Y0, le_max_left _ _, fun σ' h1 h2 Y hY => ?_⟩
  have hY1 : 1 ≤ Y := le_trans (le_max_left _ _) hY
  have hY0' : 0 < Y := by linarith
  have hσc : σ' ≤ c := by linarith
  -- horizontal sides
  have hhor : ∀ y₀ : ℝ, 1 ≤ y₀ → y₀ ≤ 2 * Y →
      ‖∫ x in σ'..c, G ((x : ℂ) + y₀ * I)‖ ≤ E / 2 * Y ^ ((7 : ℝ) / 8) := by
    intro y₀ hy1 hy2
    have hb : ∀ x ∈ Ι σ' c, ‖G ((x : ℂ) + y₀ * I)‖ ≤ mc * (K * y₀ ^ ((7 : ℝ) / 8)) := by
      intro x hx
      rw [Set.uIoc_of_le hσc] at hx
      exact (hGn x y₀ hx.2).trans (by gcongr; exact hK x y₀ (by linarith [hx.1]) hx.2 hy1)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
    have hp : y₀ ^ ((7 : ℝ) / 8) ≤ 2 * Y ^ ((7 : ℝ) / 8) := by
      calc y₀ ^ ((7 : ℝ) / 8) ≤ (2 * Y) ^ ((7 : ℝ) / 8) :=
            Real.rpow_le_rpow (by linarith) hy2 (by norm_num)
        _ = 2 ^ ((7 : ℝ) / 8) * Y ^ ((7 : ℝ) / 8) := Real.mul_rpow (by norm_num) hY0'.le
        _ ≤ 2 * Y ^ ((7 : ℝ) / 8) := by
          gcongr
          calc (2 : ℝ) ^ ((7 : ℝ) / 8) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
    rw [abs_of_nonneg (by linarith), hE]
    have : 0 ≤ c - σ' := by linarith
    have : c - σ' ≤ c - (k : ℝ) / 2 := by linarith
    have : 0 ≤ mc * K := by positivity
    calc mc * (K * y₀ ^ ((7 : ℝ) / 8)) * (c - σ') ≤ mc * (K * (2 * Y ^ ((7 : ℝ) / 8))) * (c - σ') :=
          by gcongr
      _ = 2 * (mc * K) * (c - σ') * Y ^ ((7 : ℝ) / 8) := by ring
      _ ≤ 2 * (mc * K) * (c - (k : ℝ) / 2) * Y ^ ((7 : ℝ) / 8) := by gcongr
      _ = _ := by ring
  have hrect := RamanujanTau.KernelPhase.rect_diff G σ' c Y (2 * Y) hGd.differentiableOn
  have hh1 := hhor Y hY1 (by linarith)
  have hh2 := hhor (2 * Y) (by linarith) le_rfl
  -- right line
  have hright : a * Y / 2 ≤ ‖∫ y in Y..2 * Y, G ((c : ℂ) + y * I)‖ := by
    have hint : IntervalIntegrable (fun y : ℝ => G ((c : ℂ) + y * I)) volume Y (2 * Y) :=
      (hGc.comp (by fun_prop)).intervalIntegrable _ _
    have hdiff : ‖(∫ y in Y..2 * Y, G ((c : ℂ) + y * I)) - (Y : ℂ) * coef f m‖ ≤ a / 2 * Y := by
      have e : (∫ y in Y..2 * Y, G ((c : ℂ) + y * I)) - (Y : ℂ) * coef f m =
          ∫ y in Y..2 * Y, (G ((c : ℂ) + y * I) - coef f m) := by
        rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
          intervalIntegral.integral_const]
        congr 1; rw [Complex.real_smul]; push_cast; ring
      rw [e]
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := Y) (b := 2 * Y) (C := a / 2) (f := fun y => G ((c : ℂ) + y * I) - coef f m)
        (fun y _ => htail y)
      rw [show |2 * Y - Y| = Y by rw [abs_of_nonneg (by linarith)]; ring] at this
      exact this
    have hnY : ‖(Y : ℂ) * coef f m‖ = Y * a := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hY0'.le]
    have := norm_sub_norm_le ((Y : ℂ) * coef f m)
      ((Y : ℂ) * coef f m - (∫ y in Y..2 * Y, G ((c : ℂ) + y * I)))
    rw [sub_sub_cancel, norm_sub_rev, hnY] at this
    linarith
  -- left line
  have hY18 : 4 * E / a ≤ Y ^ ((1 : ℝ) / 8) := by
    have h8 : (4 * E / a) ^ (8 : ℕ) ≤ Y := le_trans (le_max_right _ _) hY
    have h0 : 0 ≤ 4 * E / a := by positivity
    calc 4 * E / a = ((4 * E / a) ^ (8 : ℕ)) ^ ((1 : ℝ) / 8) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
      _ ≤ Y ^ ((1 : ℝ) / 8) := Real.rpow_le_rpow (by positivity) h8 (by norm_num)
  have hYsplit : Y = Y ^ ((7 : ℝ) / 8) * Y ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_add hY0']; norm_num
  have hEY : E * Y ^ ((7 : ℝ) / 8) ≤ a * Y / 4 := by
    have h78 : 0 ≤ Y ^ ((7 : ℝ) / 8) := by positivity
    have : E ≤ a / 4 * Y ^ ((1 : ℝ) / 8) := by
      have := mul_le_mul_of_nonneg_left hY18 (show 0 ≤ a / 4 by positivity)
      calc E = a / 4 * (4 * E / a) := by field_simp
        _ ≤ _ := this
    calc E * Y ^ ((7 : ℝ) / 8) ≤ a / 4 * Y ^ ((1 : ℝ) / 8) * Y ^ ((7 : ℝ) / 8) := by gcongr
      _ = a / 4 * (Y ^ ((7 : ℝ) / 8) * Y ^ ((1 : ℝ) / 8)) := by ring
      _ = a / 4 * Y := by rw [← hYsplit]
      _ = a * Y / 4 := by ring
  have hleft : a * Y / 4 ≤ ‖∫ y in Y..2 * Y, G ((σ' : ℂ) + y * I)‖ := by
    have := norm_sub_norm_le (∫ y in Y..2 * Y, G ((c : ℂ) + y * I))
      (∫ y in Y..2 * Y, G ((σ' : ℂ) + y * I))
    have hb : ‖∫ x in σ'..c, G ((x : ℂ) + (Y : ℝ) * I)‖ +
        ‖∫ x in σ'..c, G ((x : ℂ) + ((2 * Y : ℝ) : ℂ) * I)‖ ≤ E * Y ^ ((7 : ℝ) / 8) := by
      have e2 : ((2 * Y : ℝ) : ℂ) = 2 * (Y : ℂ) := by push_cast; ring
      linarith
    have hrect' := hrect
    push_cast at hrect' hb
    linarith
  -- Cauchy–Schwarz
  set g : ℝ → ℝ := fun y => ‖G ((σ' : ℂ) + y * I)‖ with hg
  have hgc : Continuous g := (hGc.comp (by fun_prop)).norm
  have hcs := sq_integral_le hgc (show Y < 2 * Y by linarith)
  have hni : ‖∫ y in Y..2 * Y, G ((σ' : ℂ) + y * I)‖ ≤ ∫ y in Y..2 * Y, g y :=
    intervalIntegral.norm_integral_le_integral_norm (by linarith)
  have hmono : ∫ y in Y..2 * Y, g y ^ 2 ≤ ∫ y in Y..2 * Y, mc ^ 2 * ‖fL f ((σ' : ℂ) + y * I)‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (hgc.pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul (((fL_entire f (by omega)).continuous.comp
        (by fun_prop)).norm.pow 2)).intervalIntegrable _ _
    · intro y _
      have := hGn σ' y hσc
      have h0 : 0 ≤ g y := norm_nonneg _
      calc g y ^ 2 ≤ (mc * ‖fL f ((σ' : ℂ) + y * I)‖) ^ 2 := pow_le_pow_left₀ h0 this 2
        _ = _ := by ring
  rw [intervalIntegral.integral_const_mul] at hmono
  have hsq : (a * Y / 4) ^ 2 ≤ Y * (mc ^ 2 * ∫ y in Y..2 * Y, ‖fL f ((σ' : ℂ) + y * I)‖ ^ 2) := by
    have h0 : 0 ≤ a * Y / 4 := by positivity
    have := pow_le_pow_left₀ h0 (hleft.trans hni) 2
    have hYY : 2 * Y - Y = Y := by ring
    rw [hYY] at hcs
    nlinarith
  set J := ∫ y in Y..2 * Y, ‖fL f ((σ' : ℂ) + y * I)‖ ^ 2
  have hmc2 : 0 < mc ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

end RamanujanTau.TauOmegaPartial
