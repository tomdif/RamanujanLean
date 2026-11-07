/-
# The real-direction shift of the first dual kernel

For `Q_j(s) = R_j(s) γₘ(1−s)` (`RankinLandau.Qk`), `Γ(z+1) = zΓ(z)` gives the exact identity

    Q_j(w+1) · P(w) = 16π⁴ · Q_j(w),     P(w) = (−w)(m−w)(w+j+1)(w+m)     (w ≠ 0, m),

so for `G(s) = y^{s+1} Q_1(s)` (the integrand of `J_1(y)`) the modulus satisfies
`‖G(w+1)‖ ‖P(w)‖ = 16π⁴y ‖G(w)‖`. With `‖P(w)‖ ≥ |Im w|⁴` and
`‖P(w)‖ ≤ (‖w+1‖²+1)(‖w‖²+m²)` this controls `‖G‖` on vertical lines far to the right
(`norm_G_add_nat_le`) and far to the left (`norm_G_sub_nat_le`) of the strip
`−1/2 ≤ Re s ≤ 1/2` **with no Stirling formula beyond the strip**.

Also: `Qk_bound_sharp`, the strip bound with the exact exponent `1 − 4 Re s − j` (the proof
of `RankinLandau.Qk_bound`, without its final weakening), and holomorphy of `Q_j` off the
real axis.
-/
import RamanujanTau.RankinLandau.KernelLine

set_option autoImplicit false

namespace RamanujanTau.KernelPhase

open Complex Real Finset
open RamanujanTau.RankinErrorGeneral RamanujanTau.RankinLandau

/-- The shift polynomial `P(w) = (−w)(m−w)(w+j+1)(w+m)`. -/
noncomputable def Pk (m j : ℕ) (w : ℂ) : ℂ := (-w) * ((m : ℂ) - w) * (w + j + 1) * (w + m)

/-- **The exact real shift** `Q_j(w+1) P(w) = 16π⁴ Q_j(w)`. -/
theorem Qk_add_one (m j : ℕ) {w : ℂ} (h0 : w ≠ 0) (hm : w ≠ m) :
    Qk m j (w + 1) * Pk m j w = 16 * (π : ℂ) ^ 4 * Qk m j w := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4pi : ((4 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (4 * π : ℝ) ≠ 0)
  unfold Qk Rk gamM Pk
  rw [show (1 : ℂ) - (w + 1) = -w by ring]
  have g1 : Complex.Gamma (1 - w) = (-w) * Complex.Gamma (-w) := by
    rw [show (1 : ℂ) - w = -w + 1 by ring]; exact Complex.Gamma_add_one _ (neg_ne_zero.2 h0)
  have g2 : Complex.Gamma (1 - w + m) = ((m : ℂ) - w) * Complex.Gamma (-w + m) := by
    rw [show (1 : ℂ) - w + m = ((m : ℂ) - w) + 1 by ring, show -w + (m : ℂ) = (m : ℂ) - w by ring]
    exact Complex.Gamma_add_one _ (sub_ne_zero.2 (Ne.symm hm))
  have g3 : (Complex.Gamma (w + j + 1))⁻¹ = (w + j + 1) * (Complex.Gamma (w + 1 + j + 1))⁻¹ := by
    rw [inv_Gamma_eq_mul]; congr 3; ring
  have g4 : (Complex.Gamma (w + m))⁻¹ = (w + m) * (Complex.Gamma (w + 1 + m))⁻¹ := by
    rw [inv_Gamma_eq_mul]; congr 3; ring
  have c1 : (π : ℂ) ^ (w + 1) = π ^ w * π := by rw [cpow_add _ _ hpi, cpow_one]
  have c2 : (π : ℂ) ^ (-(-w)) = π ^ w := by rw [neg_neg]
  have c3 : (π : ℂ) ^ (-(1 - w)) = π ^ w * (π : ℂ)⁻¹ := by
    rw [show -(1 - w) = w + (-1) by ring, cpow_add _ _ hpi, cpow_neg_one]
  have c4 : ((4 * π : ℝ) : ℂ) ^ (w + 1 + m) =
      ((4 * π : ℝ) : ℂ) ^ (w + m) * ((4 * π : ℝ) : ℂ) := by
    rw [show w + 1 + (m : ℂ) = (w + m) + 1 by ring, cpow_add _ _ h4pi, cpow_one]
  have c5 : ((4 * π : ℝ) : ℂ) ^ (-(-w) - m) = ((4 * π : ℝ) : ℂ) ^ (w - m) := by rw [neg_neg]
  have c6 : ((4 * π : ℝ) : ℂ) ^ (-(1 - w) - m) =
      ((4 * π : ℝ) : ℂ) ^ (w - m) * (((4 * π : ℝ) : ℂ))⁻¹ := by
    rw [show -(1 - w) - (m : ℂ) = (w - m) + (-1) by ring, cpow_add _ _ h4pi, cpow_neg_one]
  rw [g1, g2, g3, g4, c1, c2, c3, c4, c5, c6]
  have e4 : ((4 * π : ℝ) : ℂ) = 4 * (π : ℂ) := by push_cast; ring
  rw [e4]
  field_simp
  ring

/-- The integrand of `J_1(y)`: `G(s) = y^{s+1} Q_1(s)`. -/
noncomputable def G (m : ℕ) (y : ℝ) (s : ℂ) : ℂ := (y : ℂ) ^ (s + ((1 : ℕ) : ℂ)) * Qk m 1 s

lemma Jc_eq_G (m : ℕ) (y : ℝ) :
    Jc m 1 (1 / 2) y = ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, G m y (((1 / 2 : ℝ) : ℂ) + t * I) := rfl

lemma norm_G (m : ℕ) {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ‖G m y s‖ = y ^ (s.re + 1) * ‖Qk m 1 s‖ := by
  unfold G
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

/-- **The modulus recursion** `‖G(w+1)‖ ‖P(w)‖ = 16π⁴ y ‖G(w)‖`. -/
lemma norm_G_add_one (m : ℕ) {y : ℝ} (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (hm : w ≠ m) :
    ‖G m y (w + 1)‖ * ‖Pk m 1 w‖ = 16 * π ^ 4 * y * ‖G m y w‖ := by
  have h := congrArg norm (Qk_add_one m 1 h0 hm)
  rw [norm_mul, norm_mul] at h
  have h16 : ‖(16 : ℂ) * (π : ℂ) ^ 4‖ = 16 * π ^ 4 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [h16] at h
  rw [norm_G m hy, norm_G m hy, mul_assoc, h,
    show (w + 1).re + 1 = (w.re + 1) + 1 by simp, Real.rpow_add hy, Real.rpow_one]
  ring

lemma abs_im_pow_le_norm_Pk (m j : ℕ) (w : ℂ) : |w.im| ^ 4 ≤ ‖Pk m j w‖ := by
  unfold Pk
  simp only [norm_mul]
  have h1 : |w.im| ≤ ‖-w‖ := by simpa using Complex.abs_im_le_norm (-w)
  have h2 : |w.im| ≤ ‖(m : ℂ) - w‖ := by simpa using Complex.abs_im_le_norm ((m : ℂ) - w)
  have h3 : |w.im| ≤ ‖w + j + 1‖ := by simpa using Complex.abs_im_le_norm (w + j + 1)
  have h4 : |w.im| ≤ ‖w + m‖ := by simpa using Complex.abs_im_le_norm (w + m)
  calc |w.im| ^ 4 = |w.im| * |w.im| * |w.im| * |w.im| := by ring
    _ ≤ ‖-w‖ * ‖(m : ℂ) - w‖ * ‖w + j + 1‖ * ‖w + m‖ := by gcongr

lemma norm_Pk_le (m : ℕ) (w : ℂ) : ‖Pk m 1 w‖ ≤ (‖w + 1‖ ^ 2 + 1) * (‖w‖ ^ 2 + (m : ℝ) ^ 2) := by
  have e : Pk m 1 w = -(((w + 1) ^ 2 - 1) * ((m : ℂ) ^ 2 - w ^ 2)) := by unfold Pk; push_cast; ring
  rw [e, norm_neg, norm_mul]
  have a1 : ‖(w + 1) ^ 2 - 1‖ ≤ ‖w + 1‖ ^ 2 + 1 := by
    refine (norm_sub_le _ _).trans ?_; rw [norm_pow, norm_one]
  have a2 : ‖(m : ℂ) ^ 2 - w ^ 2‖ ≤ ‖w‖ ^ 2 + (m : ℝ) ^ 2 := by
    refine (norm_sub_le _ _).trans ?_; rw [norm_pow, norm_pow, Complex.norm_natCast]; linarith
  exact mul_le_mul a1 a2 (norm_nonneg _) (by positivity)

/-- **Shift to the right**: for `Im s ≠ 0`, `‖G(s+k)‖ ≤ ‖G(s)‖ (16π⁴y/(Im s)⁴)^k`. -/
theorem norm_G_add_nat_le (m : ℕ) {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s.im ≠ 0) (k : ℕ) :
    ‖G m y (s + k)‖ ≤ ‖G m y s‖ * (16 * π ^ 4 * y / s.im ^ 4) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    set w : ℂ := s + k with hw
    have hwim : w.im = s.im := by simp [hw]
    have h0 : w ≠ 0 := fun h => hs (by rw [← hwim, h]; simp)
    have hm : w ≠ m := fun h => hs (by rw [← hwim, h]; simp)
    have hrec := norm_G_add_one m hy h0 hm
    have hP := abs_im_pow_le_norm_Pk m 1 w
    rw [hwim] at hP
    have hi4 : 0 < s.im ^ 4 := by positivity
    have hi4' : s.im ^ 4 = |s.im| ^ 4 := by rw [← abs_pow, abs_of_pos hi4]
    have hP' : s.im ^ 4 ≤ ‖Pk m 1 w‖ := by rw [hi4']; exact hP
    rw [show s + ((k + 1 : ℕ) : ℂ) = w + 1 by rw [hw]; push_cast; ring]
    have hT : 0 ≤ 16 * π ^ 4 * y := by positivity
    have key : ‖G m y (w + 1)‖ ≤ 16 * π ^ 4 * y / s.im ^ 4 * ‖G m y w‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hi4]
      calc ‖G m y (w + 1)‖ * s.im ^ 4 ≤ ‖G m y (w + 1)‖ * ‖Pk m 1 w‖ := by gcongr
        _ = 16 * π ^ 4 * y * ‖G m y w‖ := hrec
    calc ‖G m y (w + 1)‖ ≤ 16 * π ^ 4 * y / s.im ^ 4 * ‖G m y w‖ := key
      _ ≤ 16 * π ^ 4 * y / s.im ^ 4 * (‖G m y s‖ * (16 * π ^ 4 * y / s.im ^ 4) ^ k) := by
          gcongr
      _ = ‖G m y s‖ * (16 * π ^ 4 * y / s.im ^ 4) ^ (k + 1) := by ring

/-- **Shift to the left**: for `−1/2 ≤ Re s ≤ 1/2` and `k ≤ K`,
`‖G(s−k)‖ ≤ ‖G(s)‖ (B²/(16π⁴y))^k` with `B = (K+1)² + m² + (Im s)²`. -/
theorem norm_G_sub_nat_le (m : ℕ) (hm1 : 1 ≤ m) {y : ℝ} (hy : 0 < y) {s : ℂ}
    (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 1 / 2) (K : ℕ) :
    ∀ k : ℕ, k ≤ K → ‖G m y (s - k)‖ ≤
      ‖G m y s‖ * ((((K : ℝ) + 1) ^ 2 + (m : ℝ) ^ 2 + s.im ^ 2) ^ 2 / (16 * π ^ 4 * y)) ^ k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkK : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    set w : ℂ := s - ((k + 1 : ℕ) : ℂ) with hw
    have hwre : w.re = s.re - k - 1 := by simp [hw]; ring
    have hwim : w.im = s.im := by simp [hw]
    have h0 : w ≠ 0 := fun h => by
      have := congrArg Complex.re h; rw [hwre] at this; simp at this; linarith
    have hm : w ≠ m := fun h => by
      have := congrArg Complex.re h; rw [hwre] at this; simp at this; linarith
    have hrec := norm_G_add_one m hy h0 hm
    have hw1 : w + 1 = s - k := by rw [hw]; push_cast; ring
    rw [hw1] at hrec
    set B : ℝ := ((K : ℝ) + 1) ^ 2 + (m : ℝ) ^ 2 + s.im ^ 2 with hB
    have hPB : ‖Pk m 1 w‖ ≤ B * B := by
      refine (norm_Pk_le m w).trans ?_
      have e1 : ‖w + 1‖ ^ 2 = (s.re - k) ^ 2 + s.im ^ 2 := by
        rw [hw1, RamanujanTau.Stirling.sq_norm_eq]; simp
      have e2 : ‖w‖ ^ 2 = (s.re - k - 1) ^ 2 + s.im ^ 2 := by
        rw [RamanujanTau.Stirling.sq_norm_eq, hwre, hwim]
      have b1 : (s.re - k) ^ 2 ≤ ((K : ℝ) + 1) ^ 2 := by nlinarith
      have b2 : (s.re - k - 1) ^ 2 ≤ ((K : ℝ) + 1) ^ 2 := by nlinarith
      rw [e1, e2]
      have hm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
      apply mul_le_mul <;> nlinarith [sq_nonneg s.im]
    have hT : 0 < 16 * π ^ 4 * y := by positivity
    have key : ‖G m y w‖ ≤ ‖G m y (s - k)‖ * (B ^ 2 / (16 * π ^ 4 * y)) := by
      rw [mul_div_assoc', le_div_iff₀ hT, mul_comm _ (16 * π ^ 4 * y), ← hrec]
      gcongr
      rw [sq]; exact hPB
    calc ‖G m y w‖ ≤ ‖G m y (s - k)‖ * (B ^ 2 / (16 * π ^ 4 * y)) := key
      _ ≤ (‖G m y s‖ * (B ^ 2 / (16 * π ^ 4 * y)) ^ k) * (B ^ 2 / (16 * π ^ 4 * y)) := by
          gcongr; exact ih (by omega)
      _ = ‖G m y s‖ * (B ^ 2 / (16 * π ^ 4 * y)) ^ (k + 1) := by ring

/-! ### Holomorphy off the real axis -/

lemma differentiableAt_Qk_of_im_ne (m j : ℕ) {s : ℂ} (hs : s.im ≠ 0) :
    DifferentiableAt ℂ (Qk m j) s := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4pi : ((4 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (4 * π : ℝ) ≠ 0)
  have g1 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (1 - s)) s := by
    have := (Complex.differentiableAt_Gamma (1 - s) (fun n h => hs (by
      have := congrArg Complex.im h; simpa using this))).comp s
      ((differentiableAt_const 1).sub differentiableAt_id)
    simpa [Function.comp_def] using this
  have g2 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (1 - s + m)) s := by
    have := (Complex.differentiableAt_Gamma (1 - s + m) (fun n h => hs (by
      have := congrArg Complex.im h; simpa using this))).comp s
      (((differentiableAt_const 1).sub differentiableAt_id).add_const (m : ℂ))
    simpa [Function.comp_def] using this
  have hG : DifferentiableAt ℂ (fun s => gamM m (1 - s)) s := by
    unfold gamM
    refine ((((differentiableAt_const 2).mul ?_).mul g1).mul g2).mul ?_
    · exact ((differentiableAt_const 1).sub differentiableAt_id).neg.const_cpow (Or.inl hpi)
    · exact (((differentiableAt_const 1).sub differentiableAt_id).neg.sub_const _).const_cpow
        (Or.inl h4pi)
  exact (differentiable_Rk m j s).mul hG

lemma differentiableAt_G (m : ℕ) {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s.re < 1 ∨ s.im ≠ 0) :
    DifferentiableAt ℂ (G m y) s := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hQ : DifferentiableAt ℂ (Qk m 1) s := by
    rcases hs with hs | hs
    · exact ((differentiableOn_Qk m 1) s hs).differentiableAt
        (IsOpen.mem_nhds (isOpen_lt Complex.continuous_re continuous_const) hs)
    · exact differentiableAt_Qk_of_im_ne m 1 hs
  exact ((differentiableAt_id.add_const _).const_cpow (Or.inl hy0)).mul hQ

/-! ### The strip bound with the exact exponent -/

theorem Qk_bound_sharp (m j : ℕ) (hm : 1 ≤ m) {A₀ : ℝ} (hA : A₀ ≤ 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, A₀ ≤ s.re → s.re ≤ 1 / 2 →
      ‖Qk m j s‖ ≤ K * (1 + |s.im|) ^ (1 - 4 * s.re - j) := by
  set N : ℕ := ⌈1 - A₀⌉₊ with hN
  have hNA : 1 - A₀ ≤ N := Nat.le_ceil _
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  set R₁ : ℝ := 2 - A₀ + m + j + N + 2 with hR₁
  have hR₁1 : 1 ≤ R₁ := by rw [hR₁]; linarith
  obtain ⟨C, hC0, hC⟩ := norm_Gamma_ratio_unif' hR₁1
  set R₂ : ℝ := |A₀| + j + m + N + 2 with hR₂
  have hR₂1 : 1 ≤ R₂ := by rw [hR₂]; linarith [abs_nonneg A₀]
  set K : ℝ := (j.factorial : ℝ) * C ^ 2 * R₂ ^ (2 * N) * 3 with hK
  refine ⟨K, by positivity, fun s h1 h2 => ?_⟩
  set σ : ℝ := s.re with hσ
  set t : ℝ := s.im with ht
  have ht0 : (0 : ℝ) < 1 + |t| := by positivity
  have hs1 : 1 - s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hΓ1 : Complex.Gamma (1 - s) = Complex.Gamma (2 - s) / (1 - s) := by
    rw [eq_div_iff hs1, show (2 : ℂ) - s = 1 - s + 1 by ring, Complex.Gamma_add_one _ hs1]
    ring
  have hw₁re : (s + j + 1 + N).re = σ + j + 1 + N := by simp [hσ]
  have hw₂re : (s + m + N).re = σ + m + N := by simp [hσ]
  have hw₁im : (s + j + 1 + N).im = t := by simp [ht]
  have hw₂im : (s + m + N).im = t := by simp [ht]
  have hσabs : |σ| ≤ |A₀| + 1 / 2 := by
    rcases le_total 0 σ with h | h
    · rw [abs_of_nonneg h]; linarith [abs_nonneg A₀]
    · rw [abs_of_nonpos h]; linarith [neg_abs_le A₀]
  -- the two `Γ`-ratios
  have r1 : ‖Complex.Gamma (2 - s)‖ * ‖Complex.Gamma (s + j + 1 + N)‖⁻¹ ≤
      C * (1 + |t|) ^ (1 - 2 * σ - j - N) := by
    have hpos : 0 < ‖Complex.Gamma (s + j + 1 + N)‖ := norm_pos_iff.2
      (Complex.Gamma_ne_zero_of_re_pos (by rw [hw₁re]; linarith))
    have := hC (2 - s) (s + j + 1 + N) (by simp [← hσ]; linarith) (by simp [← hσ]; rw [hR₁]; linarith)
      (by rw [hw₁re]; linarith) (by rw [hw₁re, hR₁]; linarith)
      (by rw [hw₁im]; simp [ht])
    rw [hw₁im, hw₁re, show (2 - s).re = 2 - σ by simp [hσ],
      show 2 - σ - (σ + j + 1 + N) = 1 - 2 * σ - j - N by ring] at this
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]; exact this
  have r2 : ‖Complex.Gamma (1 - s + m)‖ * ‖Complex.Gamma (s + m + N)‖⁻¹ ≤
      C * (1 + |t|) ^ (1 - 2 * σ - N) := by
    have hpos : 0 < ‖Complex.Gamma (s + m + N)‖ := norm_pos_iff.2
      (Complex.Gamma_ne_zero_of_re_pos (by rw [hw₂re]; linarith))
    have := hC (1 - s + m) (s + m + N) (by simp [← hσ]; linarith) (by simp [← hσ]; rw [hR₁]; linarith)
      (by rw [hw₂re]; linarith) (by rw [hw₂re, hR₁]; linarith)
      (by rw [hw₂im]; simp [ht])
    rw [hw₂im, hw₂re, show (1 - s + m).re = 1 - σ + m by simp [hσ],
      show 1 - σ + m - (σ + m + N) = 1 - 2 * σ - N by ring] at this
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]; exact this
  -- the two products
  have p1 : ‖∏ i ∈ range N, (s + j + 1 + i)‖ ≤ (R₂ * (1 + |t|)) ^ N := by
    have := norm_prod_add_le (s + j + 1) N hR₂1 (by
      have : |(s + j + 1).re| ≤ |σ| + j + 1 := by
        simp only [add_re, natCast_re, one_re, ← hσ]
        calc |σ + j + 1| ≤ |σ + j| + |(1:ℝ)| := abs_add_le _ _
          _ ≤ |σ| + j + 1 := by
              have := abs_add_le σ (j:ℝ); rw [abs_of_nonneg hj0] at this; rw [abs_one]; linarith
      rw [hR₂]; linarith)
    simpa [ht] using this
  have p2 : ‖∏ i ∈ range N, (s + m + i)‖ ≤ (R₂ * (1 + |t|)) ^ N := by
    have := norm_prod_add_le (s + m) N hR₂1 (by
      have : |(s + m).re| ≤ |σ| + m := by
        simp only [add_re, natCast_re, ← hσ]
        calc |σ + m| ≤ |σ| + |(m:ℝ)| := abs_add_le _ _
          _ = |σ| + m := by rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) m)]
      rw [hR₂]; linarith)
    simpa [ht] using this
  -- the exponential constants
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h4pi : (0 : ℝ) < 4 * π := by positivity
  have c1 : π ^ σ * (4 * π) ^ (σ + m) / 2 * (2 * π ^ (σ - 1) * (4 * π) ^ (σ - 1 - m)) ≤ 1 := by
    have ea : π ^ σ * π ^ (σ - 1) = π ^ (2 * σ - 1) := by
      rw [← Real.rpow_add hpi]; congr 1; ring
    have eb : (4 * π) ^ (σ + m) * (4 * π) ^ (σ - 1 - m) = (4 * π) ^ (2 * σ - 1) := by
      rw [← Real.rpow_add h4pi]; congr 1; ring
    have e : π ^ σ * (4 * π) ^ (σ + m) / 2 * (2 * π ^ (σ - 1) * (4 * π) ^ (σ - 1 - m)) =
        π ^ (2 * σ - 1) * (4 * π) ^ (2 * σ - 1) := by
      rw [← ea, ← eb]; ring
    rw [e]
    have hpi1 : 1 ≤ π := by linarith [Real.pi_gt_three]
    exact mul_le_one₀ (Real.rpow_le_one_of_one_le_of_nonpos hpi1 (by linarith))
      (by positivity) (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith))
  have d1 : ‖1 - s‖⁻¹ ≤ 3 * (1 + |t|) ^ (-1 : ℝ) := by
    have := one_add_abs_le_three_norm_one_sub h2
    rw [Real.rpow_neg_one, ← ht] at *
    have hpos : 0 < ‖1 - s‖ := norm_pos_iff.2 hs1
    rw [inv_le_iff_one_le_mul₀ hpos]
    calc (1 : ℝ) = (1 + |t|) * (1 + |t|)⁻¹ := (mul_inv_cancel₀ ht0.ne').symm
      _ ≤ (3 * ‖1 - s‖) * (1 + |t|)⁻¹ := by gcongr
      _ = 3 * (1 + |t|)⁻¹ * ‖1 - s‖ := by ring
  -- the norm identity
  have hnorm : ‖Qk m j s‖ = (j.factorial : ℝ) *
      (π ^ σ * (4 * π) ^ (σ + m) / 2 * (2 * π ^ (σ - 1) * (4 * π) ^ (σ - 1 - m))) *
      (‖Complex.Gamma (2 - s)‖ * ‖Complex.Gamma (s + j + 1 + N)‖⁻¹) *
      (‖Complex.Gamma (1 - s + m)‖ * ‖Complex.Gamma (s + m + N)‖⁻¹) *
      ‖∏ i ∈ range N, (s + j + 1 + i)‖ * ‖∏ i ∈ range N, (s + m + i)‖ * ‖1 - s‖⁻¹ := by
    unfold Qk Rk gamM
    rw [inv_Gamma_eq_prod (s + j + 1) N, inv_Gamma_eq_prod (s + m) N, hΓ1]
    simp only [norm_mul, norm_div, norm_inv, Complex.norm_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hpi, Complex.norm_cpow_eq_rpow_re_of_pos h4pi,
      Complex.norm_ofNat]
    simp only [add_re, sub_re, neg_re, one_re, natCast_re, ← hσ]
    ring
  -- assemble
  have hfac : (0 : ℝ) ≤ (j.factorial : ℝ) := by positivity
  have hNpow : ((R₂ * (1 + |t|)) ^ N) * ((R₂ * (1 + |t|)) ^ N) =
      R₂ ^ (2 * N) * (1 + |t|) ^ ((2 * N : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, ← pow_add, ← mul_pow, two_mul]
  rw [hnorm]
  calc (j.factorial : ℝ) *
      (π ^ σ * (4 * π) ^ (σ + m) / 2 * (2 * π ^ (σ - 1) * (4 * π) ^ (σ - 1 - m))) *
      (‖Complex.Gamma (2 - s)‖ * ‖Complex.Gamma (s + j + 1 + N)‖⁻¹) *
      (‖Complex.Gamma (1 - s + m)‖ * ‖Complex.Gamma (s + m + N)‖⁻¹) *
      ‖∏ i ∈ range N, (s + j + 1 + i)‖ * ‖∏ i ∈ range N, (s + m + i)‖ * ‖1 - s‖⁻¹
      ≤ (j.factorial : ℝ) * 1 * (C * (1 + |t|) ^ (1 - 2 * σ - j - N)) *
        (C * (1 + |t|) ^ (1 - 2 * σ - N)) * (R₂ * (1 + |t|)) ^ N * (R₂ * (1 + |t|)) ^ N *
        (3 * (1 + |t|) ^ (-1 : ℝ)) := by
        gcongr
    _ = ((j.factorial : ℝ) * C * C * 3) * ((R₂ * (1 + |t|)) ^ N * (R₂ * (1 + |t|)) ^ N) *
          ((1 + |t|) ^ (1 - 2 * σ - j - N) * (1 + |t|) ^ (1 - 2 * σ - N) * (1 + |t|) ^ (-1 : ℝ)) := by
        ring
    _ = K * ((1 + |t|) ^ (1 - 2 * σ - j - N) * (1 + |t|) ^ (1 - 2 * σ - N) *
          (1 + |t|) ^ ((2 * N : ℕ) : ℝ) * (1 + |t|) ^ (-1 : ℝ)) := by
        rw [hNpow, hK]; ring
    _ = K * (1 + |t|) ^ (1 - 4 * σ - j) := by
        rw [← Real.rpow_add ht0, ← Real.rpow_add ht0, ← Real.rpow_add ht0]
        congr 2; push_cast; ring

end RamanujanTau.KernelPhase
