/-
# First-moment lower bound for `Z(w) = ζ(2w) D(w)` on `9/16 ≤ Re w ≤ 5/8`, uniform in the line

    ∫_Y^{2Y} ‖Z(σ' + iy)‖ dy ≥ c₃ Y      (9/16 ≤ σ' ≤ 5/8, Y ≥ Y₀),

`c₃`, `Y₀` independent of `σ'`. With `n₀` the least index with `a(n₀) ≠ 0`, `G(w) = Z(w) n₀^w` is
`≈ a(n₀)` on a far-right line (`tail_gen` for `D` and for `ζ`), and the rectangle to `Re w = σ'`
costs only the horizontal sides, `≪ Y^{15/16}` (`Zf_horiz`).
-/
import RamanujanTau.RankinOmega.Analytic

set_option autoImplicit false

namespace RamanujanTau.RankinOmega

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open scoped Real Interval

section FM

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ)
variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

include habs in
lemma summable_a2 : Summable fun n : ℕ => ‖(a n : ℂ)‖ / (n : ℝ) ^ (2 : ℝ) := by
  have hS : LSeriesSummable (fun n => (a n : ℂ)) ((2 : ℝ) : ℂ) :=
    RamanujanTau.RankinSharp.LSeriesSummable_of_one_lt habs (by simp)
  refine hS.norm.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [LSeries.term_of_ne_zero (by omega), norm_div, Complex.norm_natCast_cpow_of_pos h]
    simp

include habs in
/-- **The leading coefficient dominates `Z(w) n₀^w` on a far-right line.** -/
theorem Zf_tail {n0 : ℕ} (hn0 : 1 ≤ n0) (hlow : ∀ n, 0 < n → n < n0 → a n = 0) (ha0 : a n0 ≠ 0) :
    ∃ c : ℝ, 3 ≤ c ∧ ∀ y : ℝ,
      ‖Zf d ((c : ℂ) + y * I) * (n0 : ℂ) ^ ((c : ℂ) + y * I) - a n0‖ ≤ |a n0| / 2 := by
  have hA : 0 < |a n0| := abs_pos.2 ha0
  obtain ⟨ca, -, hca⟩ := tail_gen (fun n => (a n : ℂ)) hn0
    (fun n h1 h2 => by simp [hlow n h1 h2]) (summable_a2 habs) (ε := |a n0| / 4) (by positivity)
  have hs1 : Summable fun n : ℕ => ‖(1 : ℕ → ℂ) n‖ / (n : ℝ) ^ (2 : ℝ) := by
    simp only [Pi.one_apply, norm_one]
    exact Real.summable_one_div_nat_rpow.2 (by norm_num)
  obtain ⟨cz, -, hcz⟩ := tail_gen (1 : ℕ → ℂ) le_rfl (fun n h1 h2 => by omega) hs1
    (ε := 1 / 5) (by norm_num)
  set c : ℝ := max (max ca (cz / 2)) 3 with hc
  have hc3 : 3 ≤ c := le_max_right _ _
  have hca' : ca ≤ c := le_trans (le_max_left _ _) (le_max_left _ _)
  have hcz' : cz ≤ 2 * c := by have := le_trans (le_max_right ca (cz / 2)) (le_max_left _ 3); linarith
  refine ⟨c, hc3, fun y => ?_⟩
  set w : ℂ := (c : ℂ) + y * I with hw
  have hwre : w.re = c := by simp [hw]
  rw [Zf_eq d habs (by rw [hwre]; linarith)]
  have hQ := hca c hca' y
  rw [← hw] at hQ
  have hZ := hcz (2 * c) hcz' (2 * y)
  have e2 : ((2 * c : ℝ) : ℂ) + ((2 * y : ℝ) : ℂ) * I = 2 * w := by rw [hw]; push_cast; ring
  rw [e2, LSeries_one_eq_riemannZeta (by simp [hwre]; linarith)] at hZ
  simp only [Nat.cast_one, one_cpow, mul_one, Pi.one_apply] at hZ
  set Q := LSeries (fun n => (a n : ℂ)) w * (n0 : ℂ) ^ w with hQdef
  have hQn : ‖Q‖ ≤ 5 / 4 * |a n0| := by
    have := norm_le_norm_add_norm_sub' Q (a n0 : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  have e : riemannZeta (2 * w) * LSeries (fun n => (a n : ℂ)) w * (n0 : ℂ) ^ w - a n0 =
      (riemannZeta (2 * w) - 1) * Q + (Q - a n0) := by rw [hQdef]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  calc ‖riemannZeta (2 * w) - 1‖ * ‖Q‖ + ‖Q - a n0‖ ≤ 1 / 5 * (5 / 4 * |a n0|) + |a n0| / 4 := by
        gcongr
    _ = |a n0| / 2 := by ring

include habs in
/-- **Uniform first-moment lower bound** for `‖Z‖` on `9/16 ≤ Re w ≤ 5/8`. -/
theorem Zf_first_moment (hm : 1 ≤ m) {n0 : ℕ} (hn0 : 1 ≤ n0)
    (hlow : ∀ n, 0 < n → n < n0 → a n = 0) (ha0 : a n0 ≠ 0) :
    ∃ c3 : ℝ, 0 < c3 ∧ ∃ Y0 : ℝ, 1 ≤ Y0 ∧ ∀ σ' : ℝ, 9 / 16 ≤ σ' → σ' ≤ 5 / 8 →
      ∀ Y : ℝ, Y0 ≤ Y → c3 * Y ≤ ∫ y in Y..2 * Y, ‖Zf d ((σ' : ℂ) + y * I)‖ := by
  obtain ⟨c, hc3, htail⟩ := Zf_tail d habs hn0 hlow ha0
  obtain ⟨K, hK0, hK⟩ := Zf_horiz d habs hm c (by linarith)
  set A : ℝ := |a n0| with hAdef
  have hA0 : 0 < A := abs_pos.2 ha0
  have hnR : (1 : ℝ) ≤ n0 := by exact_mod_cast hn0
  set mc : ℝ := (n0 : ℝ) ^ c with hmc
  have hmc1 : 1 ≤ mc := Real.one_le_rpow hnR (by linarith)
  set G : ℂ → ℂ := fun w => Zf d w * (n0 : ℂ) ^ w with hG
  have hn0' : (n0 : ℂ) ≠ 0 := by exact_mod_cast (show n0 ≠ 0 by omega)
  have hGd : ∀ w : ℂ, 1 ≤ w.im → DifferentiableAt ℂ G w := by
    intro w hw
    have h0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw; linarith
    have h1 : w ≠ 1 := by intro h; rw [h] at hw; simp at hw; linarith
    exact (differentiableAt_Zf d h0 h1).mul (differentiableAt_id.const_cpow (Or.inl hn0'))
  have hGn : ∀ x y : ℝ, x ≤ c → ‖G ((x : ℂ) + y * I)‖ ≤ mc * ‖Zf d ((x : ℂ) + y * I)‖ := by
    intro x y hx
    simp only [hG, norm_mul]
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    have : ((x : ℂ) + y * I).re = x := by simp
    rw [this, mul_comm]
    gcongr
    exact Real.rpow_le_rpow_of_exponent_le hnR hx
  have hcontG : ∀ x Y : ℝ, 1 ≤ Y → ContinuousOn (fun y : ℝ => G ((x : ℂ) + y * I)) (uIcc Y (2 * Y)) := by
    intro x Y hY y hy
    rw [uIcc_of_le (by linarith)] at hy
    have : 1 ≤ ((x : ℂ) + y * I).im := by simp; linarith [hy.1]
    exact ((hGd _ this).continuousAt.comp (f := fun y : ℝ => (x : ℂ) + y * I) (x := y)
      (by fun_prop)).continuousWithinAt
  have hcontZ : ∀ x Y : ℝ, 1 ≤ Y →
      ContinuousOn (fun y : ℝ => ‖Zf d ((x : ℂ) + y * I)‖) (uIcc Y (2 * Y)) := by
    intro x Y hY y hy
    rw [uIcc_of_le (by linarith)] at hy
    have him : 1 ≤ ((x : ℂ) + y * I).im := by simp; linarith [hy.1]
    have h0 : (x : ℂ) + y * I ≠ 0 := by intro h; rw [h] at him; simp at him; linarith
    have h1 : (x : ℂ) + y * I ≠ 1 := by intro h; rw [h] at him; simp at him; linarith
    exact ((differentiableAt_Zf d h0 h1).continuousAt.comp (f := fun y : ℝ => (x : ℂ) + y * I)
      (x := y) (by fun_prop)).norm.continuousWithinAt
  set E : ℝ := 4 * c * mc * K with hE
  have hE0 : 0 ≤ E := by rw [hE]; have : 0 ≤ c := by linarith
                         positivity
  set Y0 : ℝ := max 1 ((4 * E / A) ^ (16 : ℕ)) with hY0
  refine ⟨A / (4 * mc), by positivity, Y0, le_max_left _ _, fun σ' h1 h2 Y hY => ?_⟩
  have hY1 : 1 ≤ Y := le_trans (le_max_left _ _) hY
  have hY0' : 0 < Y := by linarith
  have hσc : σ' ≤ c := by linarith
  -- horizontal sides
  have hhor : ∀ y₀ : ℝ, 1 ≤ y₀ → y₀ ≤ 2 * Y →
      ‖∫ x in σ'..c, G ((x : ℂ) + y₀ * I)‖ ≤ E / 2 * Y ^ ((15 : ℝ) / 16) := by
    intro y₀ hy1 hy2
    have hb : ∀ x ∈ Ι σ' c, ‖G ((x : ℂ) + y₀ * I)‖ ≤ mc * (K * y₀ ^ ((15 : ℝ) / 16)) := by
      intro x hx
      rw [Set.uIoc_of_le hσc] at hx
      exact (hGn x y₀ hx.2).trans (by gcongr; exact hK x y₀ (by linarith [hx.1]) hx.2 hy1)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
    have hp : y₀ ^ ((15 : ℝ) / 16) ≤ 2 * Y ^ ((15 : ℝ) / 16) := by
      calc y₀ ^ ((15 : ℝ) / 16) ≤ (2 * Y) ^ ((15 : ℝ) / 16) :=
            Real.rpow_le_rpow (by linarith) hy2 (by norm_num)
        _ = 2 ^ ((15 : ℝ) / 16) * Y ^ ((15 : ℝ) / 16) := Real.mul_rpow (by norm_num) hY0'.le
        _ ≤ 2 * Y ^ ((15 : ℝ) / 16) := by
          gcongr
          calc (2 : ℝ) ^ ((15 : ℝ) / 16) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
    rw [abs_of_nonneg (by linarith), hE]
    have : 0 ≤ c - σ' := by linarith
    have : c - σ' ≤ c := by linarith
    have : 0 ≤ mc * K := by positivity
    calc mc * (K * y₀ ^ ((15 : ℝ) / 16)) * (c - σ') ≤ mc * (K * (2 * Y ^ ((15 : ℝ) / 16))) * (c - σ') :=
          by gcongr
      _ = 2 * (mc * K) * (c - σ') * Y ^ ((15 : ℝ) / 16) := by ring
      _ ≤ 2 * (mc * K) * c * Y ^ ((15 : ℝ) / 16) := by gcongr
      _ = _ := by ring
  have hrectD : DifferentiableOn ℂ G ([[σ', c]] ×ℂ [[Y, 2 * Y]]) := by
    intro z hz
    rw [mem_reProdIm, uIcc_of_le hσc, uIcc_of_le (show Y ≤ 2 * Y by linarith)] at hz
    exact (hGd z (by linarith [hz.2.1])).differentiableWithinAt
  have hrect := RamanujanTau.KernelPhase.rect_diff G σ' c Y (2 * Y) hrectD
  have hh1 := hhor Y hY1 (by linarith)
  have hh2 := hhor (2 * Y) (by linarith) le_rfl
  -- right line
  have hright : A * Y / 2 ≤ ‖∫ y in Y..2 * Y, G ((c : ℂ) + y * I)‖ := by
    have hint : IntervalIntegrable (fun y : ℝ => G ((c : ℂ) + y * I)) volume Y (2 * Y) :=
      (hcontG c Y hY1).intervalIntegrable
    have hdiff : ‖(∫ y in Y..2 * Y, G ((c : ℂ) + y * I)) - (Y : ℂ) * a n0‖ ≤ A / 2 * Y := by
      have e : (∫ y in Y..2 * Y, G ((c : ℂ) + y * I)) - (Y : ℂ) * a n0 =
          ∫ y in Y..2 * Y, (G ((c : ℂ) + y * I) - a n0) := by
        rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
          intervalIntegral.integral_const]
        congr 1; rw [Complex.real_smul]; push_cast; ring
      rw [e]
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := Y) (b := 2 * Y) (C := A / 2) (f := fun y => G ((c : ℂ) + y * I) - a n0)
        (fun y _ => htail y)
      rw [show |2 * Y - Y| = Y by rw [abs_of_nonneg (by linarith)]; ring] at this
      exact this
    have hnY : ‖(Y : ℂ) * a n0‖ = Y * A := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hY0'.le, Complex.norm_real,
        Real.norm_eq_abs]
    have := norm_sub_norm_le ((Y : ℂ) * a n0)
      ((Y : ℂ) * a n0 - (∫ y in Y..2 * Y, G ((c : ℂ) + y * I)))
    rw [sub_sub_cancel, norm_sub_rev, hnY] at this
    linarith
  -- left line
  have hY116 : 4 * E / A ≤ Y ^ ((1 : ℝ) / 16) := by
    have h16 : (4 * E / A) ^ (16 : ℕ) ≤ Y := le_trans (le_max_right _ _) hY
    have h0 : 0 ≤ 4 * E / A := by positivity
    calc 4 * E / A = ((4 * E / A) ^ (16 : ℕ)) ^ ((1 : ℝ) / 16) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
      _ ≤ Y ^ ((1 : ℝ) / 16) := Real.rpow_le_rpow (by positivity) h16 (by norm_num)
  have hYsplit : Y = Y ^ ((15 : ℝ) / 16) * Y ^ ((1 : ℝ) / 16) := by
    rw [← Real.rpow_add hY0']; norm_num
  have hEY : E * Y ^ ((15 : ℝ) / 16) ≤ A * Y / 4 := by
    have h78 : 0 ≤ Y ^ ((15 : ℝ) / 16) := by positivity
    have : E ≤ A / 4 * Y ^ ((1 : ℝ) / 16) := by
      have := mul_le_mul_of_nonneg_left hY116 (show 0 ≤ A / 4 by positivity)
      calc E = A / 4 * (4 * E / A) := by field_simp
        _ ≤ _ := this
    calc E * Y ^ ((15 : ℝ) / 16) ≤ A / 4 * Y ^ ((1 : ℝ) / 16) * Y ^ ((15 : ℝ) / 16) := by gcongr
      _ = A / 4 * (Y ^ ((15 : ℝ) / 16) * Y ^ ((1 : ℝ) / 16)) := by ring
      _ = A / 4 * Y := by rw [← hYsplit]
      _ = A * Y / 4 := by ring
  have hleft : A * Y / 4 ≤ ‖∫ y in Y..2 * Y, G ((σ' : ℂ) + y * I)‖ := by
    have := norm_sub_norm_le (∫ y in Y..2 * Y, G ((c : ℂ) + y * I))
      (∫ y in Y..2 * Y, G ((σ' : ℂ) + y * I))
    have hb : ‖∫ x in σ'..c, G ((x : ℂ) + (Y : ℝ) * I)‖ +
        ‖∫ x in σ'..c, G ((x : ℂ) + ((2 * Y : ℝ) : ℂ) * I)‖ ≤ E * Y ^ ((15 : ℝ) / 16) := by
      linarith
    have hrect' := hrect
    push_cast at hrect' hb
    linarith
  -- pass to `‖Z‖`
  have hni : ‖∫ y in Y..2 * Y, G ((σ' : ℂ) + y * I)‖ ≤ ∫ y in Y..2 * Y, ‖G ((σ' : ℂ) + y * I)‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by linarith)
  have hmono : ∫ y in Y..2 * Y, ‖G ((σ' : ℂ) + y * I)‖ ≤
      ∫ y in Y..2 * Y, mc * ‖Zf d ((σ' : ℂ) + y * I)‖ := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (hcontG σ' Y hY1).norm.intervalIntegrable
    · exact ((hcontZ σ' Y hY1).const_smul mc).intervalIntegrable
    · intro y _; exact hGn σ' y hσc
  rw [intervalIntegral.integral_const_mul] at hmono
  have hfin : A * Y / 4 ≤ mc * ∫ y in Y..2 * Y, ‖Zf d ((σ' : ℂ) + y * I)‖ := by linarith
  have hmc0 : 0 < mc := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith

end FM

end RamanujanTau.RankinOmega
