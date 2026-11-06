/-
# The functional-equation factor, uniformly near `σ = 23/4`

For `0 ≤ y ≤ 1/4` and `t > 0` (`Psi_eq`):

    Ψ_{6−y}(t) = |L(Δ,6−y+it)/(6−y+it)|² = (2π)^{−4y} R(y,t) t^{4y−2} |L(Δ,6+y+it)|²,

with `R(y,t) = Q(6−y,6+y,t)² (t/|6−y+it|)²`, `Q(a,b,t) = |Γ(b+it)| / (|Γ(a+it)| t^{b−a})`.

`R_unif`: `R(y,t) → 1` as `t → ∞`, **uniformly** in `y ∈ [0,1/4]`.  `MeanSquareLeft.tendsto_Qr`
is for fixed `a ≤ b`; uniformity comes from running its shift argument with explicit
bounds: for `n : ℕ` and `w = 1 + (7+n)/t`,

    E_n⁻¹ w^{−n} ≤ Q(6−y, 6+y, t) ≤ E_n w^{n+1},        E_n = exp(5/(5+n)),

(`Q(c,c+n) ∈ [1, (1+(c+n)/t)^n]` by `Γ(s+1) = sΓ(s)`, and the sharp fractional bound
`MeanSquareLeft.Qr_frac_bounds`), then `n → ∞` and `t → ∞`.
-/
import RamanujanTau.MeanSquareLeft.Left
import RamanujanTau.Voronoi.Tail

set_option autoImplicit false

namespace RamanujanTau.CramerMeanSquare

open Complex Real Filter Topology
open RamanujanTau.MeanSquareLeft RamanujanTau.HeckeL

lemma norm_vert_bounds {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t) :
    1 ≤ ‖(c : ℂ) + t * I‖ / t ∧ ‖(c : ℂ) + t * I‖ / t ≤ 1 + c / t := by
  constructor
  · rw [le_div_iff₀ ht, one_mul]
    have := Complex.abs_im_le_norm ((c : ℂ) + t * I)
    simp at this
    rw [abs_of_pos ht] at this; exact this
  · rw [div_le_iff₀ ht, add_mul, one_mul, div_mul_cancel₀ _ ht.ne']
    have := Complex.norm_le_abs_re_add_abs_im ((c : ℂ) + t * I)
    simp at this
    rw [abs_of_pos ht, abs_of_nonneg hc] at this; linarith

lemma Qr_nat_bounds {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t) (n : ℕ) :
    1 ≤ Qr c (c + n) t ∧ Qr c (c + n) t ≤ (1 + (c + n) / t) ^ n := by
  induction n with
  | zero =>
    have := (norm_Gamma_vert_pos c ht.ne').ne'
    simp [Qr, this]
  | succ n ih =>
    have hm := Qr_mul c (c + n) (c + n + 1) ht
    have hs := Qr_succ (c + n) ht
    obtain ⟨b1, b2⟩ := norm_vert_bounds (c := c + n) (by positivity) ht
    have e : (c + ((n + 1 : ℕ) : ℝ)) = c + n + 1 := by push_cast; ring
    rw [e, ← hm, hs]
    obtain ⟨i1, i2⟩ := ih
    constructor
    · nlinarith
    · have hmono : 1 + (c + n) / t ≤ 1 + (c + n + 1) / t := by
        have := div_le_div_of_nonneg_right (show c + n ≤ c + n + 1 by linarith) ht.le
        linarith
      calc Qr c (c + n) t * (‖((c + n : ℝ) : ℂ) + t * I‖ / t)
          ≤ (1 + (c + n) / t) ^ n * (1 + (c + n) / t) :=
            mul_le_mul i2 b2 (by linarith) (by positivity)
        _ = (1 + (c + n) / t) ^ (n + 1) := by ring
        _ ≤ (1 + (c + n + 1) / t) ^ (n + 1) := pow_le_pow_left₀ (by positivity) hmono _

/-- **Explicit two-sided bound** for `Q(6−y, 6+y, t)`. -/
lemma Qr_explicit {y t : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) (ht : 0 < t) (n : ℕ) :
    (Real.exp (5 / (5 + n)))⁻¹ * ((1 + (7 + n) / t) ^ n)⁻¹ ≤ Qr (6 - y) (6 + y) t ∧
      Qr (6 - y) (6 + y) t ≤ Real.exp (5 / (5 + n)) * (1 + (7 + n) / t) ^ (n + 1) := by
  set a : ℝ := 6 - y with ha
  set θ : ℝ := 2 * y with hθ
  set w : ℝ := 1 + (7 + n) / t with hw
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hw1 : 1 ≤ w := by
    rw [hw]
    have : 0 ≤ (7 + n) / t := by positivity
    linarith
  have hb : 6 + y = a + θ := by rw [ha, hθ]; ring
  -- factorization
  have hid : Qr a (a + θ) t * Qr (a + θ) (a + θ + n) t =
      Qr a (a + n) t * Qr (a + n) (a + n + θ) t := by
    rw [Qr_mul _ _ _ ht, Qr_mul _ _ _ ht, show a + θ + n = a + n + θ by ring]
  obtain ⟨q1l, q1u⟩ := Qr_nat_bounds (c := a) (by rw [ha]; linarith) ht n
  obtain ⟨q2l, q2u⟩ := Qr_nat_bounds (c := a + θ) (by rw [ha, hθ]; linarith) ht n
  have hcn : 1 ≤ a + n := by rw [ha]; linarith
  obtain ⟨fl, fu⟩ := Qr_frac_bounds (c := a + n) (r := θ) hcn (by rw [hθ]; linarith)
    (by rw [hθ]; linarith) ht
  obtain ⟨v1, v2⟩ := norm_vert_bounds (c := a + n) (by linarith) ht
  have hvw : ‖((a + n : ℝ) : ℂ) + t * I‖ / t ≤ w := by
    refine v2.trans ?_; rw [hw]; gcongr; rw [ha]; linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  have hpw1 : 1 ≤ (‖((a + n : ℝ) : ℂ) + t * I‖ / t) ^ θ := Real.one_le_rpow v1 hθ0
  have hpw2 : (‖((a + n : ℝ) : ℂ) + t * I‖ / t) ^ θ ≤ w := by
    calc (‖((a + n : ℝ) : ℂ) + t * I‖ / t) ^ θ ≤ (‖((a + n : ℝ) : ℂ) + t * I‖ / t) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le v1 hθ1
      _ = _ := Real.rpow_one _
      _ ≤ w := hvw
  have hE : Real.exp (5 / (a + n - 1 / 2)) ≤ Real.exp (5 / (5 + n)) := by
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
    rw [ha]; linarith
  have hE1 : 0 < Real.exp (5 / (a + n - 1 / 2)) := Real.exp_pos _
  have hEn : 0 < Real.exp (5 / (5 + n)) := Real.exp_pos _
  have hn1 : 1 + (a + n) / t ≤ w := by rw [hw]; gcongr; rw [ha]; linarith
  have hn2 : 1 + (a + θ + n) / t ≤ w := by rw [hw]; gcongr; rw [ha, hθ]; linarith
  have hb1 : 0 ≤ 1 + (a + n) / t := by
    have : 0 ≤ (a + n) / t := div_nonneg (by rw [ha]; linarith) ht.le
    linarith
  have hb2 : 0 ≤ 1 + (a + θ + n) / t := by
    have : 0 ≤ (a + θ + n) / t := div_nonneg (by rw [ha, hθ]; linarith) ht.le
    linarith
  have hq1u : Qr a (a + n) t ≤ w ^ n := q1u.trans (pow_le_pow_left₀ hb1 hn1 n)
  have hq2u : Qr (a + θ) (a + θ + n) t ≤ w ^ n :=
    q2u.trans (pow_le_pow_left₀ hb2 hn2 n)
  have hQ2pos : 0 < Qr (a + θ) (a + θ + n) t := by linarith
  have hQ : Qr a (a + θ) t = Qr a (a + n) t * Qr (a + n) (a + n + θ) t /
      Qr (a + θ) (a + θ + n) t := by
    rw [eq_div_iff hQ2pos.ne', hid]
  rw [hb, hQ]
  have hwn : 0 < w ^ n := by positivity
  constructor
  · rw [le_div_iff₀ hQ2pos]
    have hfl : (Real.exp (5 / (5 + n)))⁻¹ ≤ Qr (a + n) (a + n + θ) t := by
      refine le_trans ?_ fl
      calc (Real.exp (5 / (5 + n)))⁻¹ ≤ (Real.exp (5 / (a + n - 1 / 2)))⁻¹ :=
            inv_anti₀ hE1 hE
        _ = (Real.exp (5 / (a + n - 1 / 2)))⁻¹ * 1 := by ring
        _ ≤ _ := by gcongr
    have hF0 : 0 ≤ Qr (a + n) (a + n + θ) t := le_trans (by positivity) hfl
    calc (Real.exp (5 / (5 + n)))⁻¹ * (w ^ n)⁻¹ * Qr (a + θ) (a + θ + n) t
        ≤ (Real.exp (5 / (5 + n)))⁻¹ * (w ^ n)⁻¹ * w ^ n := by gcongr
      _ = (Real.exp (5 / (5 + n)))⁻¹ := by field_simp
      _ ≤ 1 * Qr (a + n) (a + n + θ) t := by linarith
      _ ≤ _ := by gcongr
  · rw [div_le_iff₀ hQ2pos]
    have hfu : Qr (a + n) (a + n + θ) t ≤ Real.exp (5 / (5 + n)) * w := by
      refine fu.trans ?_
      gcongr
    have hF0 : 0 ≤ Qr (a + n) (a + n + θ) t := le_trans (by positivity) fl
    calc Qr a (a + n) t * Qr (a + n) (a + n + θ) t ≤ w ^ n * (Real.exp (5 / (5 + n)) * w) :=
          mul_le_mul hq1u hfu hF0 (by positivity)
      _ = Real.exp (5 / (5 + n)) * w ^ (n + 1) * 1 := by ring
      _ ≤ _ := by gcongr

/-- `R(y,t) = Q(6−y,6+y,t)² (t/|6−y+it|)²`. -/
noncomputable def Rf (y t : ℝ) : ℝ :=
  Qr (6 - y) (6 + y) t ^ 2 * (t / ‖((6 - y : ℝ) : ℂ) + t * I‖) ^ 2

/-- **Uniform Stirling**: `R(y,t) → 1` uniformly in `y ∈ [0,1/4]`. -/
theorem R_unif : ∀ ε : ℝ, 0 < ε → ∃ t0 : ℝ, 1 ≤ t0 ∧ ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 4 →
    ∀ t : ℝ, t0 ≤ t → |Rf y t - 1| ≤ ε := by
  intro ε hε
  -- choose `n` with `E_n` close to `1`
  have hEl : Tendsto (fun n : ℕ => Real.exp (5 / (5 + n))) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => (5 : ℝ) + n) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    have := (tendsto_const_nhds (x := (5 : ℝ))).div_atTop h1
    simpa using (Real.continuous_exp.tendsto 0).comp this
  have hE2 : Tendsto (fun n : ℕ => Real.exp (5 / (5 + n)) ^ 2) atTop (𝓝 1) := by
    simpa using hEl.pow 2
  have hE2i : Tendsto (fun n : ℕ => ((Real.exp (5 / (5 + n)))⁻¹) ^ 2) atTop (𝓝 1) := by
    simpa using (hEl.inv₀ one_ne_zero).pow 2
  obtain ⟨n, hn1, hn2⟩ := ((hE2.eventually (gt_mem_nhds (show (1 : ℝ) < 1 + ε / 2 by linarith))).and
    (hE2i.eventually (lt_mem_nhds (show 1 - ε / 2 < (1 : ℝ) by linarith)))).exists
  set En : ℝ := Real.exp (5 / (5 + n)) with hEn
  have hEn0 : 0 < En := Real.exp_pos _
  -- then `t` large
  have hw : Tendsto (fun t : ℝ => 1 + (7 + n) / t) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := (7 + (n : ℝ)))).div_atTop tendsto_id)
  have hU : Tendsto (fun t : ℝ => En ^ 2 * ((1 + (7 + n) / t) ^ (n + 1)) ^ 2) atTop
      (𝓝 (En ^ 2)) := by
    simpa using (hw.pow (n + 1)).pow 2 |>.const_mul (En ^ 2)
  have hL : Tendsto (fun t : ℝ => (En⁻¹) ^ 2 * (((1 + (7 + n) / t) ^ n)⁻¹) ^ 2 *
      ((1 + (7 + n) / t)⁻¹) ^ 2) atTop (𝓝 ((En⁻¹) ^ 2)) := by
    have h := (((hw.pow n).inv₀ (by simp)).pow 2).const_mul ((En⁻¹) ^ 2) |>.mul
      ((hw.inv₀ one_ne_zero).pow 2)
    simpa using h
  obtain ⟨t1, ht1⟩ := eventually_atTop.1 ((hU.eventually (gt_mem_nhds hn1)).and
    (hL.eventually (lt_mem_nhds hn2)))
  refine ⟨max t1 1, le_max_right _ _, fun y hy0 hy1 t ht => ?_⟩
  have htt1 : t1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ht)
  obtain ⟨hu, hl⟩ := ht1 t htt1
  obtain ⟨ql, qu⟩ := Qr_explicit hy0 hy1 ht0 n
  set w : ℝ := 1 + (7 + n) / t with hwdef
  have hw1 : 1 ≤ w := by
    rw [hwdef]
    have : 0 ≤ (7 + (n : ℝ)) / t := by positivity
    linarith
  obtain ⟨v1, v2⟩ := norm_vert_bounds (c := 6 - y) (by linarith) ht0
  have hv0 : 0 < ‖((6 - y : ℝ) : ℂ) + t * I‖ := by
    have := mul_le_mul_of_nonneg_right v1 ht0.le
    rw [one_mul, div_mul_cancel₀ _ ht0.ne'] at this; linarith
  have hr1 : t / ‖((6 - y : ℝ) : ℂ) + t * I‖ ≤ 1 := by
    rw [div_le_one hv0]
    have := mul_le_mul_of_nonneg_right v1 ht0.le
    rw [one_mul, div_mul_cancel₀ _ ht0.ne'] at this; linarith
  have hr2 : w⁻¹ ≤ t / ‖((6 - y : ℝ) : ℂ) + t * I‖ := by
    have hvw : ‖((6 - y : ℝ) : ℂ) + t * I‖ / t ≤ w := by
      refine v2.trans ?_; rw [hwdef]; gcongr; linarith
    rw [← inv_div]
    exact inv_anti₀ (by positivity) hvw
  have hQ0 : 0 ≤ Qr (6 - y) (6 + y) t := le_trans (by positivity) ql
  have hr0 : 0 ≤ t / ‖((6 - y : ℝ) : ℂ) + t * I‖ := by positivity
  unfold Rf
  rw [abs_le]
  constructor
  · have h1 : ((En⁻¹ * (w ^ n)⁻¹)) ^ 2 ≤ Qr (6 - y) (6 + y) t ^ 2 :=
      pow_le_pow_left₀ (by positivity) ql 2
    have h2 : (w⁻¹) ^ 2 ≤ (t / ‖((6 - y : ℝ) : ℂ) + t * I‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hr2 2
    have h3 : (En⁻¹) ^ 2 * ((w ^ n)⁻¹) ^ 2 * (w⁻¹) ^ 2 ≤
        Qr (6 - y) (6 + y) t ^ 2 * (t / ‖((6 - y : ℝ) : ℂ) + t * I‖) ^ 2 := by
      rw [← mul_pow]; exact mul_le_mul h1 h2 (by positivity) (by positivity)
    linarith
  · have h1 : Qr (6 - y) (6 + y) t ^ 2 ≤ (En * w ^ (n + 1)) ^ 2 :=
      pow_le_pow_left₀ hQ0 qu 2
    have h2 : (t / ‖((6 - y : ℝ) : ℂ) + t * I‖) ^ 2 ≤ 1 := pow_le_one₀ hr0 hr1
    have h3 : Qr (6 - y) (6 + y) t ^ 2 * (t / ‖((6 - y : ℝ) : ℂ) + t * I‖) ^ 2 ≤
        En ^ 2 * (w ^ (n + 1)) ^ 2 := by
      calc Qr (6 - y) (6 + y) t ^ 2 * (t / ‖((6 - y : ℝ) : ℂ) + t * I‖) ^ 2
          ≤ (En * w ^ (n + 1)) ^ 2 * 1 := mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by ring
    linarith

/-- **The functional equation for `Ψ`**: for `0 ≤ y ≤ 1/4`, `t > 0`,
`Ψ_{6−y}(t) = (2π)^{−4y} R(y,t) t^{4y−2} |L(6+y+it)|²`. -/
theorem Psi_eq {y t : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) (ht : 0 < t) :
    RamanujanTau.Voronoi.Psi (6 - y) t = (2 * π) ^ (-(4 * y)) * Rf y t * t ^ (4 * y - 2) *
      ‖tauL (((6 + y : ℝ) : ℂ) + t * I)‖ ^ 2 := by
  unfold RamanujanTau.Voronoi.Psi Rf
  rw [norm_div, div_pow, norm_tauL_fe (σ := 6 - y) (by linarith) t,
    show (12 - (6 - y) : ℝ) = 6 + y by ring]
  set Ga := ‖Complex.Gamma (((6 - y : ℝ) : ℂ) + t * I)‖ with hGa
  set Gb := ‖Complex.Gamma (((6 + y : ℝ) : ℂ) + t * I)‖ with hGb
  set V := ‖((6 - y : ℝ) : ℂ) + t * I‖ with hV
  set Lb := ‖tauL (((6 + y : ℝ) : ℂ) + t * I)‖ with hLb
  have hGa0 : 0 < Ga := norm_Gamma_vert_pos _ ht.ne'
  have hV0 : 0 < V := by
    have := (norm_vert_bounds (c := 6 - y) (by linarith) ht).1
    have := mul_le_mul_of_nonneg_right this ht.le
    rw [one_mul, div_mul_cancel₀ _ ht.ne'] at this; linarith
  have hQ : Qr (6 - y) (6 + y) t = Gb / (Ga * t ^ (2 * y)) := by
    unfold Qr; rw [show (6 + y) - (6 - y) = 2 * y by ring]
  have ht2y : 0 < t ^ (2 * y) := Real.rpow_pos_of_pos ht _
  have hp1 : ((2 * π) ^ (2 * (6 - y) - 12)) ^ 2 = (2 * π) ^ (-(4 * y)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
  have hp2 : (t ^ (2 * y)) ^ 2 = t ^ (4 * y) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; congr 1; push_cast; ring
  have hp3 : t ^ (4 * y - 2) = t ^ (4 * y) / t ^ 2 := by
    rw [Real.rpow_sub ht, Real.rpow_two]
  rw [hQ, hp3]
  have hpow : (2 * π) ^ (-(4 * y)) = ((2 * π) ^ (2 * (6 - y) - 12)) ^ 2 := hp1.symm
  rw [hpow, ← hp2]
  field_simp

end RamanujanTau.CramerMeanSquare
