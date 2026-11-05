/-
# A quantitative Hardy theorem for `L(Δ,s)`: `N₀(T) ≫_ε T^{1/2−ε}`

See `docs/HARDY_COUNT.md`.

* `tauL_critical_zero_gaps`: for every `ε > 0` there are `K, T₀` such that every interval
  `[t₀ − K t₀^{1/2+ε}, t₀ + K t₀^{1/2+ε}]`, `t₀ ≥ T₀`, contains an ordinate `t` with
  `L(Δ, 6+it) = 0`.
* `tauL_critical_zeros_count`: for every `ε > 0` there are `c > 0, T₀` such that for `T ≥ T₀`
  there is a finite set `S ⊆ (0,T]` of ordinates of zeros of `L(Δ, 6+it)` with
  `|S| ≥ c T^{1/2−ε}`.

The proof (`Gaps.lean`) is Hardy's method with a triangle window: Fourier inversion of the window
(`Triangle.lean`), the Fourier identity `∫ Λ(6+it) e^{αt} e^{2πiξt} dt = 2π e^{6w} Δ(i e^{w})`
and `sup (Im τ)⁶|Δ(τ)| < ∞` (`Window.lean`), Stirling, and a contour-shift lower bound for
`|∫ L(Δ,6+it) dt|` (`Contour.lean`).
-/
import RamanujanTau.HardyCount.Gaps

set_option autoImplicit false

namespace RamanujanTau.HardyCount

open Complex Set Filter
open RamanujanTau.HeckeL RamanujanTau.HardyZeros
open scoped Real

lemma tauL_zero_of_Zr_zero {t : ℝ} (h0 : Zr t = 0) : tauL (6 + t * I) = 0 := by
  have h1 := Zc_eq_Zr t
  rw [h0, Complex.ofReal_zero] at h1
  have h2 : heckeLambda (6 + t * I) = 0 := h1
  rw [tauL, h2, mul_zero]

/-- Gap theorem with an exponent `θ = 1/2 + ε`, `0 < ε < 1/2`, for `Zr`. -/
lemma Zr_gaps_small {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ K T₀ : ℝ, 0 < K ∧ 1 ≤ T₀ ∧ ∀ t₀ : ℝ, T₀ ≤ t₀ →
      ∃ t ∈ Icc (t₀ - K * t₀ ^ (1 / 2 + ε)) (t₀ + K * t₀ ^ (1 / 2 + ε)), Zr t = 0 :=
  Zr_zero_near hε0 hε1

/-- **Zeros of `L(Δ,s)` on the critical line in short intervals**: gaps `≪_ε t^{1/2+ε}`. -/
theorem tauL_critical_zero_gaps {ε : ℝ} (hε : 0 < ε) :
    ∃ K T₀ : ℝ, 0 < K ∧ 1 ≤ T₀ ∧ ∀ t₀ : ℝ, T₀ ≤ t₀ →
      ∃ t ∈ Icc (t₀ - K * t₀ ^ (1 / 2 + ε)) (t₀ + K * t₀ ^ (1 / 2 + ε)),
        tauL (6 + t * I) = 0 := by
  set ε' : ℝ := min ε (1 / 4) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨K, T₀, hK, hT₀, hgap⟩ := Zr_gaps_small hε'0 hε'1
  refine ⟨K, T₀, hK, hT₀, fun t₀ ht₀ => ?_⟩
  obtain ⟨t, ht, h0⟩ := hgap t₀ ht₀
  have ht₀1 : 1 ≤ t₀ := hT₀.trans ht₀
  have hp : t₀ ^ (1 / 2 + ε') ≤ t₀ ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le ht₀1 (by linarith [min_le_left ε (1 / 4)])
  have hKp := mul_le_mul_of_nonneg_left hp hK.le
  exact ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, tauL_zero_of_Zr_zero h0⟩

/-- Counting for `0 < ε < 1/2`. -/
lemma count_small {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ c T₁ : ℝ, 0 < c ∧ 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T → ∃ S : Finset ℝ,
      (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ tauL (6 + t * I) = 0) ∧ c * T ^ (1 / 2 - ε) ≤ S.card := by
  obtain ⟨K, T₀, hK, hT₀, hgap⟩ := Zr_gaps_small hε0 hε1
  set θ : ℝ := 1 / 2 + ε with hθ
  have hθ1 : 0 < 1 - θ := by rw [hθ]; linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  set T₁ : ℝ := max (2 * T₀) ((12 * K) ^ (1 / (1 - θ))) with hT₁
  refine ⟨1 / (12 * K), T₁, by positivity, (by linarith : (1 : ℝ) ≤ 2 * T₀).trans
    (le_max_left _ _), fun T hT => ?_⟩
  have hT2 : 2 * T₀ ≤ T := (le_max_left _ _).trans hT
  have hT1 : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  set w : ℝ := K * T ^ θ with hw
  have hTθ : 0 < T ^ θ := Real.rpow_pos_of_pos hTpos θ
  have hwpos : 0 < w := mul_pos hK hTθ
  -- `T^{1−θ} ≥ 12 K`
  have hbig : 12 * K ≤ T ^ (1 - θ) := by
    have e : 12 * K = ((12 * K) ^ (1 / (1 - θ))) ^ (1 - θ) := by
      rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hθ1.ne', Real.rpow_one]
    rw [e]
    exact Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hT) hθ1.le
  have hsplit : T ^ (1 - θ) * T ^ θ = T := by rw [← Real.rpow_add hTpos]; simp
  have hTw : T = T ^ (1 - θ) * (w / K) := by
    rw [hw, mul_div_cancel_left₀ _ hK.ne', hsplit]
  have hw12 : 12 * w ≤ T := by
    rw [hTw]
    have : 12 * w = 12 * K * (w / K) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hbig (by positivity)
  -- centres `T/2 + 3wj`, `j < n`
  set n : ℕ := ⌊T / (6 * w)⌋₊ with hn
  have hex : ∀ j : ℕ, ∃ t, (j < n → T / 2 + 3 * w * j - w ≤ t ∧ t ≤ T / 2 + 3 * w * j + w) ∧
      Zr t = 0 := by
    intro j
    set c : ℝ := T / 2 + 3 * w * j with hc
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hcT : T / 2 ≤ c := by rw [hc]; nlinarith
    obtain ⟨t, ht, h0⟩ := hgap c (by linarith)
    refine ⟨t, fun hjn => ?_, h0⟩
    have hcpos : 0 < c := by linarith
    have hjn' : (j : ℝ) + 1 ≤ T / (6 * w) := by
      have h1 : ((j + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hjn
      have h2 : (n : ℝ) ≤ T / (6 * w) := Nat.floor_le (by positivity)
      push_cast at h1; linarith
    have hcle : c ≤ T := by
      have : 3 * w * ((j : ℝ) + 1) ≤ 3 * w * (T / (6 * w)) :=
        mul_le_mul_of_nonneg_left hjn' (by positivity)
      have e : 3 * w * (T / (6 * w)) = T / 2 := by field_simp; ring
      rw [hc]; nlinarith
    have hp : c ^ θ ≤ T ^ θ := Real.rpow_le_rpow hcpos.le hcle hθ0
    have hKp : K * c ^ θ ≤ w := by rw [hw]; exact mul_le_mul_of_nonneg_left hp hK.le
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  choose f hf using hex
  refine ⟨(Finset.range n).image f, fun t ht => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    have hjn : j < n := Finset.mem_range.mp hj
    obtain ⟨⟨h1, h2⟩, h0⟩ := (show _ ∧ _ from ⟨(hf j).1 hjn, (hf j).2⟩)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjn' : (j : ℝ) + 1 ≤ T / (6 * w) := by
      have h1 : ((j + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hjn
      have h2 : (n : ℝ) ≤ T / (6 * w) := Nat.floor_le (by positivity)
      push_cast at h1; linarith
    have : 3 * w * ((j : ℝ) + 1) ≤ 3 * w * (T / (6 * w)) :=
      mul_le_mul_of_nonneg_left hjn' (by positivity)
    have e : 3 * w * (T / (6 * w)) = T / 2 := by field_simp; ring
    refine ⟨by nlinarith, by nlinarith, tauL_zero_of_Zr_zero h0⟩
  · have hinj : Set.InjOn f (Finset.range n : Set ℕ) := by
      have key : ∀ j k : ℕ, j < n → k < n → j < k → f j < f k := by
        intro j k hj hk hjk
        have h1 := ((hf j).1 hj).2
        have h2 := ((hf k).1 hk).1
        have hjk' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
        nlinarith
      intro j hj k hk hfe
      have hj' : j < n := Finset.mem_range.mp hj
      have hk' : k < n := Finset.mem_range.mp hk
      rcases lt_trichotomy j k with h | h | h
      · exact absurd hfe (key j k hj' hk' h).ne
      · exact h
      · exact absurd hfe (key k j hk' hj' h).ne'
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have hfl : T / (6 * w) - 1 < n := by
      have := Nat.lt_floor_add_one (T / (6 * w)); linarith
    have hratio : T / (6 * w) = T ^ (1 - θ) / (6 * K) := by
      rw [div_eq_div_iff (by positivity) (by positivity), hw]
      nth_rewrite 1 [← hsplit]
      ring
    have hexp : (1 / 2 - ε : ℝ) = 1 - θ := by rw [hθ]; ring
    rw [hexp]
    rw [hratio] at hfl
    have : 1 / (12 * K) * T ^ (1 - θ) ≤ T ^ (1 - θ) / (6 * K) - 1 := by
      have h12 : 1 ≤ T ^ (1 - θ) / (12 * K) := by rw [le_div_iff₀ (by positivity)]; linarith
      have e : T ^ (1 - θ) / (6 * K) = 2 * (T ^ (1 - θ) / (12 * K)) := by field_simp; ring
      rw [e, show 1 / (12 * K) * T ^ (1 - θ) = T ^ (1 - θ) / (12 * K) by ring]
      linarith
    linarith

/-- **Quantitative Hardy theorem for `L(Δ,s)`**: `N₀(T) ≫_ε T^{1/2−ε}`.  For every `ε > 0` there
are `c > 0` and `T₀` such that for all `T ≥ T₀` some finite set `S ⊆ (0,T]` of size at least
`c T^{1/2−ε}` consists of ordinates `t` with `L(Δ, 6+it) = 0`. -/
theorem tauL_critical_zeros_count {ε : ℝ} (hε : 0 < ε) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ tauL (6 + t * I) = 0) ∧ c * T ^ (1 / 2 - ε) ≤ S.card := by
  set ε' : ℝ := min ε (1 / 4) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨c, T₁, hc, hT₁, hcount⟩ := count_small hε'0 hε'1
  refine ⟨c, T₁, hc, fun T hT => ?_⟩
  obtain ⟨S, hS, hcard⟩ := hcount T hT
  refine ⟨S, hS, le_trans ?_ hcard⟩
  have hp : T ^ (1 / 2 - ε) ≤ T ^ (1 / 2 - ε') :=
    Real.rpow_le_rpow_of_exponent_le (hT₁.trans hT) (by linarith [min_le_left ε (1 / 4)])
  exact mul_le_mul_of_nonneg_left hp hc.le

/-- The same count for the completed function `Λ(Δ, s)`. -/
theorem heckeLambda_critical_zeros_count {ε : ℝ} (hε : 0 < ε) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ heckeLambda (6 + t * I) = 0) ∧
        c * T ^ (1 / 2 - ε) ≤ S.card := by
  obtain ⟨c, T₀, hc, h⟩ := tauL_critical_zeros_count hε
  refine ⟨c, T₀, hc, fun T hT => ?_⟩
  obtain ⟨S, hS, hcard⟩ := h T hT
  refine ⟨S, fun t ht => ?_, hcard⟩
  obtain ⟨h1, h2, h3⟩ := hS t ht
  refine ⟨h1, h2, ?_⟩
  have hs : ∀ n : ℕ, (6 + t * I : ℂ) ≠ -n :=
    RamanujanTau.HeckeZeros.ne_neg_nat_of_re_pos (by simp)
  rw [heckeLambda_eq_tauL hs, h3, mul_zero]

/-- A concrete instance: `N₀(T) ≫ T^{1/4}` (take `ε = 1/4`). -/
theorem tauL_critical_zeros_count_quarter :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ tauL (6 + t * I) = 0) ∧ c * T ^ (1 / 4 : ℝ) ≤ S.card := by
  obtain ⟨c, T₀, hc, h⟩ := tauL_critical_zeros_count (ε := 1 / 4) (by norm_num)
  refine ⟨c, T₀, hc, fun T hT => ?_⟩
  obtain ⟨S, hS, hcard⟩ := h T hT
  exact ⟨S, hS, by norm_num at hcard ⊢; exact hcard⟩

end RamanujanTau.HardyCount

#print axioms RamanujanTau.HardyCount.tri_inversion
#print axioms RamanujanTau.HardyCount.abs_integral_Zr_exp_tri_le
#print axioms RamanujanTau.HardyCount.norm_integral_tauL_ge
#print axioms RamanujanTau.HardyCount.Zr_zero_near
#print axioms RamanujanTau.HardyCount.tauL_critical_zero_gaps
#print axioms RamanujanTau.HardyCount.tauL_critical_zeros_count
#print axioms RamanujanTau.HardyCount.heckeLambda_critical_zeros_count
#print axioms RamanujanTau.HardyCount.tauL_critical_zeros_count_quarter
