/-
# Vertical asymptotics of Gamma ratios: `|Γ(b+it)/Γ(a+it)| ~ t^{b−a}` as `t → +∞`

Mathlib has no complex Stirling formula, and `Stirling/GammaRatio.lean` only gives the
two-sided bound with the fixed constant `e¹⁰`.  Here:

* `norm_Gamma_mul_rpow_le_sharp`: the Gauss-product argument of `GammaRatio` with the defect
  kept, `‖Γ(z)‖ ‖z‖^θ ≤ exp(5/(Re z − ½)) ‖Γ(z+θ)‖` (`Re z ≥ 1`, `0 ≤ θ ≤ 1`), and the matching
  upper bound `norm_Gamma_add_le_sharp`.  The constant tends to `1` as `Re z → ∞`.
* `Qr a b t = ‖Γ(b+it)‖ / (‖Γ(a+it)‖ t^{b−a})` is multiplicative (`Qr_mul`), `Qr c (c+1) t =
  ‖c+it‖/t → 1` (`Γ(s+1) = sΓ(s)`), hence `Qr c (c+n) → 1` for all `n : ℕ`.
* `tendsto_Qr`: **for all real `a ≤ b`, `Qr a b t → 1`**.  Write `b − a = m + r`
  (`m ∈ ℕ`, `0 ≤ r < 1`) and shift by `n`:
  `Qr a b · Qr b (b+n) = Qr a (a+n) · Qr (a+n) (a+n+r) · Qr (a+n+r) (a+n+r+m)`; the middle
  factor lies in `[E_n⁻¹, E_n] · (‖a+n+it‖/t)^r` with `E_n = exp(5/(a+n−½)) → 1`.
-/
import RamanujanTau.Stirling.GammaRatio

set_option autoImplicit false

namespace RamanujanTau.MeanSquareLeft

open Complex Real Filter Topology
open RamanujanTau.Stirling

/-- **Sharp core inequality.** For `Re z ≥ 1`, `0 ≤ θ ≤ 1`:
`‖Γ(z)‖ ‖z‖^θ ≤ exp(5/(Re z − ½)) ‖Γ(z+θ)‖`. -/
theorem norm_Gamma_mul_rpow_le_sharp {z : ℂ} (hz : 1 ≤ z.re) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) :
    ‖Complex.Gamma z‖ * ‖z‖ ^ θ ≤ Real.exp (5 / (z.re - 1 / 2)) * ‖Complex.Gamma (z + θ)‖ := by
  set E : ℝ := Real.exp (5 / (z.re - 1 / 2)) with hE
  set c : ℝ := ‖z + 1‖ with hc
  have hlimL : Tendsto (fun n : ℕ => ‖Complex.GammaSeq z n‖ * ‖z‖ ^ θ) atTop
      (𝓝 (‖Complex.Gamma z‖ * ‖z‖ ^ θ)) :=
    ((Complex.GammaSeq_tendsto_Gamma z).norm).mul_const _
  have hlimR : Tendsto (fun n : ℕ => E * (1 + c / n) * ‖Complex.GammaSeq (z + θ) n‖) atTop
      (𝓝 (E * (1 + 0) * ‖Complex.Gamma (z + θ)‖)) :=
    ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat c)).const_mul _).mul
      (Complex.GammaSeq_tendsto_Gamma (z + θ)).norm
  rw [add_zero, mul_one] at hlimR
  refine le_of_tendsto_of_tendsto hlimL hlimR ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : 0 < n := hn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hzpos : ∀ j : ℕ, 0 < ‖z + j‖ := by
    intro j
    have := Complex.abs_re_le_norm (z + j)
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
    simp only [add_re, natCast_re] at this
    rw [abs_of_pos (by linarith)] at this; linarith
  have hzθpos : ∀ j : ℕ, 0 < ‖z + θ + j‖ := by
    intro j
    have := Complex.abs_re_le_norm (z + θ + j)
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
    simp only [add_re, natCast_re, ofReal_re] at this
    rw [abs_of_pos (by linarith)] at this; linarith
  set P := ∏ j ∈ Finset.range (n + 1), ‖z + j‖ with hPdef
  set Q := ∏ j ∈ Finset.range (n + 1), ‖z + θ + j‖ with hQdef
  have hP : 0 < P := Finset.prod_pos fun j _ => hzpos j
  have hQ : 0 < Q := Finset.prod_pos fun j _ => hzθpos j
  have gz : ‖Complex.GammaSeq z n‖ = (n : ℝ) ^ z.re * (n.factorial : ℝ) / P := by
    unfold Complex.GammaSeq
    rw [norm_div, norm_mul, norm_natCast_cpow_of_pos hn0, norm_prod, Complex.norm_natCast]
  have gzθ : ‖Complex.GammaSeq (z + θ) n‖ =
      (n : ℝ) ^ z.re * (n : ℝ) ^ θ * (n.factorial : ℝ) / Q := by
    unfold Complex.GammaSeq
    rw [norm_div, norm_mul, norm_natCast_cpow_of_pos hn0, norm_prod, Complex.norm_natCast]
    simp only [add_re, ofReal_re]
    rw [Real.rpow_add hnR]
  have hprod := prod_norm_add_le hz h0 h1 (n + 1)
  rw [← hPdef, ← hQdef] at hprod
  have hexp : θ * (5 / (z.re - 1 / 2) - 5 / (z.re + ((n + 1 : ℕ) : ℝ) - 1 / 2)) ≤
      5 / (z.re - 1 / 2) := by
    have hn1 : (0:ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have a2 : 0 ≤ 5 / (z.re + ((n + 1 : ℕ) : ℝ) - 1 / 2) := div_nonneg (by norm_num) (by linarith)
    have a3 : 5 / (z.re + ((n + 1 : ℕ) : ℝ) - 1 / 2) ≤ 5 / (z.re - 1 / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    nlinarith
  have hprod' : Q * ‖z‖ ^ θ ≤ E * ‖z + ((n + 1 : ℕ) : ℂ)‖ ^ θ * P := by
    refine hprod.trans ?_
    gcongr
    rw [hE]; exact Real.exp_le_exp.2 hexp
  have hnorm : ‖z + ((n + 1 : ℕ) : ℂ)‖ ≤ (n : ℝ) * (1 + c / n) := by
    rw [mul_add, mul_one, mul_div_cancel₀ _ hnR.ne']
    have : z + ((n + 1 : ℕ) : ℂ) = (z + 1) + (n : ℂ) := by push_cast; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_natCast]; linarith
  have hc0 : 0 ≤ c := norm_nonneg _
  have h1c : 1 ≤ 1 + c / n := by
    have : 0 ≤ c / n := by positivity
    linarith
  have hpow : ‖z + ((n + 1 : ℕ) : ℂ)‖ ^ θ ≤ (n : ℝ) ^ θ * (1 + c / n) := by
    calc ‖z + ((n + 1 : ℕ) : ℂ)‖ ^ θ ≤ ((n : ℝ) * (1 + c / n)) ^ θ :=
          Real.rpow_le_rpow (norm_nonneg _) hnorm h0
      _ = (n : ℝ) ^ θ * (1 + c / n) ^ θ := Real.mul_rpow hnR.le (by linarith)
      _ ≤ (n : ℝ) ^ θ * (1 + c / n) := by
          gcongr
          calc (1 + c / n) ^ θ ≤ (1 + c / n) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le h1c h1
            _ = 1 + c / n := Real.rpow_one _
  rw [gz, gzθ]
  have hnx : 0 < (n : ℝ) ^ z.re * (n.factorial : ℝ) := by positivity
  calc (n : ℝ) ^ z.re * (n.factorial : ℝ) / P * ‖z‖ ^ θ
      = ((n : ℝ) ^ z.re * (n.factorial : ℝ) / (P * Q)) * (Q * ‖z‖ ^ θ) := by
        field_simp
    _ ≤ ((n : ℝ) ^ z.re * (n.factorial : ℝ) / (P * Q)) *
          (E * ((n : ℝ) ^ θ * (1 + c / n)) * P) := by
        exact mul_le_mul_of_nonneg_left (hprod'.trans (by gcongr)) (by positivity)
    _ = E * (1 + c / n) * ((n : ℝ) ^ z.re * (n : ℝ) ^ θ * (n.factorial : ℝ) / Q) := by
        field_simp

/-- **Sharp upper bound.** For `Re z ≥ 1`, `0 ≤ θ ≤ 1`:
`‖Γ(z+θ)‖ ≤ exp(5/(Re z − ½)) ‖z‖^θ ‖Γ(z)‖`. -/
theorem norm_Gamma_add_le_sharp {z : ℂ} (hz : 1 ≤ z.re) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ‖Complex.Gamma (z + θ)‖ ≤ Real.exp (5 / (z.re - 1 / 2)) * ‖z‖ ^ θ * ‖Complex.Gamma z‖ := by
  have hzθ : 1 ≤ (z + θ).re := by simp; linarith
  have hc := norm_Gamma_mul_rpow_le_sharp hzθ (θ := 1 - θ) (by linarith) (by linarith)
  have e : z + (θ : ℂ) + ((1 - θ : ℝ) : ℂ) = z + 1 := by push_cast; ring
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz; linarith
  rw [e, Complex.Gamma_add_one z hz0, norm_mul] at hc
  have hE : Real.exp (5 / ((z + θ).re - 1 / 2)) ≤ Real.exp (5 / (z.re - 1 / 2)) := by
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
    simp; linarith
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos (one_le_norm_of_re hz)
  have hmono : ‖z‖ ^ (1 - θ) ≤ ‖z + θ‖ ^ (1 - θ) :=
    Real.rpow_le_rpow (norm_nonneg _) (norm_le_norm_add_ofReal (by linarith) h0) (by linarith)
  have hsplit : ‖z‖ = ‖z‖ ^ θ * ‖z‖ ^ (1 - θ) := by
    rw [← Real.rpow_add hzpos, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
  have hpos : 0 < ‖z‖ ^ (1 - θ) := Real.rpow_pos_of_pos hzpos _
  have hGn := norm_nonneg (Complex.Gamma z)
  have : ‖Complex.Gamma (z + θ)‖ * ‖z‖ ^ (1 - θ) ≤
      (Real.exp (5 / (z.re - 1 / 2)) * ‖z‖ ^ θ * ‖Complex.Gamma z‖) * ‖z‖ ^ (1 - θ) := by
    calc ‖Complex.Gamma (z + θ)‖ * ‖z‖ ^ (1 - θ)
        ≤ ‖Complex.Gamma (z + θ)‖ * ‖z + θ‖ ^ (1 - θ) := by gcongr
      _ ≤ Real.exp (5 / ((z + θ).re - 1 / 2)) * (‖z‖ * ‖Complex.Gamma z‖) := hc
      _ ≤ Real.exp (5 / (z.re - 1 / 2)) * (‖z‖ * ‖Complex.Gamma z‖) := by gcongr
      _ = Real.exp (5 / (z.re - 1 / 2)) *
          ((‖z‖ ^ θ * ‖z‖ ^ (1 - θ)) * ‖Complex.Gamma z‖) := by rw [← hsplit]
      _ = _ := by ring
  exact le_of_mul_le_mul_right this hpos

/-! ### The normalised ratio `Qr` -/

/-- `Qr a b t = ‖Γ(b+it)‖ / (‖Γ(a+it)‖ t^{b−a})`. -/
noncomputable def Qr (a b t : ℝ) : ℝ :=
  ‖Complex.Gamma ((b : ℂ) + t * I)‖ / (‖Complex.Gamma ((a : ℂ) + t * I)‖ * t ^ (b - a))

lemma Gamma_vert_ne_zero (a : ℝ) {t : ℝ} (ht : t ≠ 0) : Complex.Gamma ((a : ℂ) + t * I) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m h
  have := congrArg Complex.im h
  simp at this
  exact ht this

lemma norm_Gamma_vert_pos (a : ℝ) {t : ℝ} (ht : t ≠ 0) :
    0 < ‖Complex.Gamma ((a : ℂ) + t * I)‖ :=
  norm_pos_iff.2 (Gamma_vert_ne_zero a ht)

lemma Qr_pos (a b : ℝ) {t : ℝ} (ht : 0 < t) : 0 < Qr a b t := by
  unfold Qr
  have := norm_Gamma_vert_pos a ht.ne'
  have := norm_Gamma_vert_pos b ht.ne'
  have := Real.rpow_pos_of_pos ht (b - a)
  positivity

lemma Qr_mul (a b c : ℝ) {t : ℝ} (ht : 0 < t) : Qr a b t * Qr b c t = Qr a c t := by
  unfold Qr
  have h1 := norm_Gamma_vert_pos a ht.ne'
  have h2 := norm_Gamma_vert_pos b ht.ne'
  have h3 := Real.rpow_pos_of_pos ht (b - a)
  have h4 := Real.rpow_pos_of_pos ht (c - b)
  rw [show c - a = (b - a) + (c - b) by ring, Real.rpow_add ht]
  field_simp

lemma Qr_succ (c : ℝ) {t : ℝ} (ht : 0 < t) : Qr c (c + 1) t = ‖(c : ℂ) + t * I‖ / t := by
  unfold Qr
  have hne : (c : ℂ) + t * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have e : ((c + 1 : ℝ) : ℂ) + t * I = ((c : ℂ) + t * I) + 1 := by push_cast; ring
  rw [e, Complex.Gamma_add_one _ hne, norm_mul, show c + 1 - c = 1 by ring, Real.rpow_one]
  have h1 := norm_Gamma_vert_pos c ht.ne'
  field_simp

lemma tendsto_norm_vert_div (c : ℝ) :
    Tendsto (fun t : ℝ => ‖(c : ℂ) + t * I‖ / t) atTop (𝓝 1) := by
  have hup : Tendsto (fun t : ℝ => 1 + |c| / t) atTop (𝓝 1) := by
    have h0 : Tendsto (fun t : ℝ => |c| / t) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := |c|)).div_atTop tendsto_id
    simpa using (tendsto_const_nhds (x := (1:ℝ))).add h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with t ht
    rw [le_div_iff₀ ht, one_mul]
    have := Complex.abs_im_le_norm ((c : ℂ) + t * I)
    simp at this
    rw [abs_of_pos ht] at this; exact this
  · filter_upwards [eventually_gt_atTop 0] with t ht
    rw [div_le_iff₀ ht, add_mul, one_mul, div_mul_cancel₀ _ ht.ne']
    have := Complex.norm_le_abs_re_add_abs_im ((c : ℂ) + t * I)
    simp at this
    rw [abs_of_pos ht] at this; linarith

lemma tendsto_Qr_nat (c : ℝ) (n : ℕ) : Tendsto (fun t => Qr c (c + n) t) atTop (𝓝 1) := by
  induction n with
  | zero =>
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    unfold Qr
    have := norm_Gamma_vert_pos c ht.ne'
    simp [this.ne']
  | succ n ih =>
    have h2 : Tendsto (fun t => Qr c (c + n) t * Qr (c + n) (c + n + 1) t) atTop (𝓝 (1 * 1)) :=
      ih.mul ((tendsto_norm_vert_div (c + n)).congr' (by
        filter_upwards [eventually_gt_atTop 0] with t ht
        rw [Qr_succ _ ht]))
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Qr_mul _ _ _ ht]; push_cast; ring_nf

/-- Two-sided bound for a fractional shift on `Re ≥ 1`. -/
lemma Qr_frac_bounds {c r : ℝ} (hc : 1 ≤ c) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {t : ℝ} (ht : 0 < t) :
    (Real.exp (5 / (c - 1 / 2)))⁻¹ * (‖(c : ℂ) + t * I‖ / t) ^ r ≤ Qr c (c + r) t ∧
      Qr c (c + r) t ≤ Real.exp (5 / (c - 1 / 2)) * (‖(c : ℂ) + t * I‖ / t) ^ r := by
  set z : ℂ := (c : ℂ) + t * I with hz
  have hzre : z.re = c := by simp [hz]
  have hz1 : 1 ≤ z.re := by rw [hzre]; exact hc
  have e : ((c + r : ℝ) : ℂ) + t * I = z + r := by rw [hz]; push_cast; ring
  have hG := norm_Gamma_vert_pos c ht.ne'
  have htr : 0 < t ^ r := Real.rpow_pos_of_pos ht r
  have hdiv : (‖z‖ / t) ^ r = ‖z‖ ^ r / t ^ r := Real.div_rpow (norm_nonneg _) ht.le r
  have hE := Real.exp_pos (5 / (c - 1 / 2))
  have lo := norm_Gamma_mul_rpow_le_sharp hz1 hr0 hr1
  have up := norm_Gamma_add_le_sharp hz1 hr0 hr1
  rw [hzre] at lo up
  unfold Qr
  rw [e, show c + r - c = r by ring, hdiv, ← hz]
  constructor
  · rw [le_div_iff₀ (by positivity)]
    calc (Real.exp (5 / (c - 1 / 2)))⁻¹ * (‖z‖ ^ r / t ^ r) * (‖Complex.Gamma z‖ * t ^ r)
        = (Real.exp (5 / (c - 1 / 2)))⁻¹ * (‖Complex.Gamma z‖ * ‖z‖ ^ r) := by
          field_simp
      _ ≤ (Real.exp (5 / (c - 1 / 2)))⁻¹ *
          (Real.exp (5 / (c - 1 / 2)) * ‖Complex.Gamma (z + r)‖) := by gcongr
      _ = _ := by field_simp
  · rw [div_le_iff₀ (by positivity)]
    calc ‖Complex.Gamma (z + r)‖ ≤ Real.exp (5 / (c - 1 / 2)) * ‖z‖ ^ r * ‖Complex.Gamma z‖ := up
      _ = _ := by field_simp

lemma exists_shift (a : ℝ) {η : ℝ} (hη : 1 < η) :
    ∃ n : ℕ, 1 ≤ a + n ∧ Real.exp (5 / (a + n - 1 / 2)) < η := by
  have h1 : Tendsto (fun n : ℕ => a + (n : ℝ) - 1 / 2) atTop atTop := by
    have := tendsto_natCast_atTop_atTop (R := ℝ)
    exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_left _ _ this)
  have h2 : Tendsto (fun n : ℕ => Real.exp (5 / (a + n - 1 / 2))) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (5 : ℝ))).div_atTop h1
    simpa using (Real.continuous_exp.tendsto 0).comp this
  have h3 := (h2.eventually (gt_mem_nhds hη)).and
    ((tendsto_atTop.1 (tendsto_atTop_add_const_left _ a (tendsto_natCast_atTop_atTop (R := ℝ))))
      1)
  obtain ⟨n, hn⟩ := h3.exists
  exact ⟨n, hn.2, hn.1⟩

/-- **Vertical Gamma-ratio asymptotics.** For real `a ≤ b`,
`‖Γ(b+it)‖ / (‖Γ(a+it)‖ t^{b−a}) → 1` as `t → +∞`. -/
theorem tendsto_Qr {a b : ℝ} (hab : a ≤ b) : Tendsto (Qr a b) atTop (𝓝 1) := by
  set θ := b - a with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  set m : ℕ := ⌊θ⌋₊ with hm
  set r : ℝ := θ - m with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith [Nat.floor_le hθ0]
  have hr1 : r ≤ 1 := by rw [hr]; linarith [Nat.lt_floor_add_one θ]
  -- For each admissible shift `n`, `Qr a b = P_n · F_n` with `P_n → 1`.
  have key : ∀ n : ℕ, 1 ≤ a + n →
      ∃ P : ℝ → ℝ, Tendsto P atTop (𝓝 1) ∧ ∀ᶠ t in atTop,
        (Real.exp (5 / (a + n - 1 / 2)))⁻¹ * P t ≤ Qr a b t ∧
          Qr a b t ≤ Real.exp (5 / (a + n - 1 / 2)) * P t := by
    intro n hn
    refine ⟨fun t => Qr a (a + n) t * Qr (a + n + r) (a + n + r + m) t / Qr b (b + n) t *
      (‖((a + n : ℝ) : ℂ) + t * I‖ / t) ^ r, ?_, ?_⟩
    · have h1 := tendsto_Qr_nat a n
      have h2 := tendsto_Qr_nat (a + n + r) m
      have h3 := tendsto_Qr_nat b n
      have h4 := ((tendsto_norm_vert_div (a + n)).rpow_const (p := r) (Or.inl one_ne_zero))
      have := ((h1.mul h2).div h3 one_ne_zero).mul h4
      simpa using this
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have hb : b + n = a + n + r + m := by rw [hr, hθ]; ring
      have hid : Qr a b t * Qr b (b + n) t =
          Qr a (a + n) t * Qr (a + n) (a + n + r) t * Qr (a + n + r) (a + n + r + m) t := by
        rw [Qr_mul _ _ _ ht, Qr_mul _ _ _ ht, Qr_mul _ _ _ ht, hb]
      have hpos := Qr_pos b (b + n) ht
      have hQab : Qr a b t = Qr a (a + n) t * Qr (a + n + r) (a + n + r + m) t / Qr b (b + n) t *
          Qr (a + n) (a + n + r) t := by
        field_simp; linarith [hid]
      obtain ⟨lo, up⟩ := Qr_frac_bounds (c := a + n) hn hr0 hr1 ht
      have hA : 0 ≤ Qr a (a + n) t * Qr (a + n + r) (a + n + r + m) t / Qr b (b + n) t := by
        have := Qr_pos a (a + n) ht
        have := Qr_pos (a + n + r) (a + n + r + m) ht
        positivity
      rw [hQab]
      constructor
      · calc (Real.exp (5 / (a + n - 1 / 2)))⁻¹ *
              (Qr a (a + n) t * Qr (a + n + r) (a + n + r + m) t / Qr b (b + n) t *
                (‖((a + n : ℝ) : ℂ) + t * I‖ / t) ^ r)
            = (Qr a (a + n) t * Qr (a + n + r) (a + n + r + m) t / Qr b (b + n) t) *
              ((Real.exp (5 / (a + n - 1 / 2)))⁻¹ * (‖((a + n : ℝ) : ℂ) + t * I‖ / t) ^ r) := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left lo hA
      · calc Qr a (a + n) t * Qr (a + n + r) (a + n + r + m) t / Qr b (b + n) t *
              Qr (a + n) (a + n + r) t
            ≤ (Qr a (a + n) t * Qr (a + n + r) (a + n + r + m) t / Qr b (b + n) t) *
              (Real.exp (5 / (a + n - 1 / 2)) * (‖((a + n : ℝ) : ℂ) + t * I‖ / t) ^ r) :=
              mul_le_mul_of_nonneg_left up hA
          _ = _ := by ring
  rw [tendsto_order]
  constructor
  · intro l hl
    rcases le_or_gt l 0 with hl0 | hl0
    · filter_upwards [eventually_gt_atTop 0] with t ht
      exact lt_of_le_of_lt hl0 (Qr_pos a b ht)
    · have hη : 1 < 1 / l := by rw [lt_div_iff₀ hl0, one_mul]; exact hl
      obtain ⟨n, hn, hE⟩ := exists_shift a hη
      obtain ⟨P, hP, hb⟩ := key n hn
      set E := Real.exp (5 / (a + n - 1 / 2))
      have hE0 : 0 < E := Real.exp_pos _
      have hlE : E * l < 1 := by
        have := mul_lt_mul_of_pos_right hE hl0
        rwa [div_mul_cancel₀ _ hl0.ne'] at this
      filter_upwards [hP.eventually (lt_mem_nhds hlE), hb] with t ht1 ht2
      have : l < E⁻¹ * P t := by rw [lt_inv_mul_iff₀ hE0]; exact ht1
      exact lt_of_lt_of_le this ht2.1
  · intro u hu
    obtain ⟨n, hn, hE⟩ := exists_shift a hu
    obtain ⟨P, hP, hb⟩ := key n hn
    set E := Real.exp (5 / (a + n - 1 / 2))
    have hE0 : 0 < E := Real.exp_pos _
    have hu1 : 1 < u / E := by rw [lt_div_iff₀ hE0, one_mul]; exact hE
    filter_upwards [hP.eventually (gt_mem_nhds hu1), hb] with t ht1 ht2
    refine lt_of_le_of_lt ht2.2 ?_
    rw [lt_div_iff₀ hE0] at ht1
    linarith

end RamanujanTau.MeanSquareLeft
