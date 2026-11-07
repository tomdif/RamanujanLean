/-
# The degree-two bent contour: shift recursion and pointwise bounds

For `Q_0(s) = (2π)^{2s} Γ(k−s)/Γ(s+1)` and `G(s) = y^s Q_0(s)` (the integrand of `J_0(y)`),
`Γ(z+1) = zΓ(z)` gives the exact identity

    Q_0(w+1) · P(w) = 4π² · Q_0(w),        P(w) = (k−1−w)(w+1)        (w ≠ k−1),

so `‖G(w+1)‖‖P(w)‖ = 4π²y‖G(w)‖`. With `‖P(w)‖ ≥ |Im w|²` and the AM–GM bound
`‖P(w)‖ ≤ ((k−1−Re w)² + (Re w+1)²)/2 + (Im w)²`, this transports the strip bound
`‖Q_0(s)‖ ≤ K(1+|t|)^{k−1−2Re s}` on `(k−1)/2 ≤ Re s ≤ (k+1)/2` to every point of the contour,
with no Stirling formula beyond the strip and no phase.

Parameters: `y = Y⁴`, `τ = 2πY²` (`τ² = 4π²y`, the stationary height), `n = ⌈Y⌉₊ ≍ √τ`,
`U = Y⁶`, base line `b = (k+1)/2`. The target size is `Y^{2k−1} = y^{k/2−1/4}`.
-/
import RamanujanTau.TauPartialSumsSharp.Kernel
import RamanujanTau.Stirling.Absolute

set_option autoImplicit false

namespace RamanujanTau.TauPartialSumsSharp

open Complex Real Finset

/-- The shift polynomial `P(w) = (k−1−w)(w+1)`. -/
noncomputable def P2 (k : ℕ) (w : ℂ) : ℂ := ((k : ℂ) - 1 - w) * (w + 1)

/-- **The exact real shift** `Q_0(w+1) P(w) = 4π² Q_0(w)`. -/
theorem Q_add_one (k : ℕ) {w : ℂ} (hw : (k : ℂ) - 1 - w ≠ 0) :
    Q k 0 (w + 1) * P2 k w = 4 * (π : ℂ) ^ 2 * Q k 0 w := by
  have hb : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast two_pi_pos'.ne'
  unfold Q P2
  have g1 : Complex.Gamma ((k : ℂ) - w) = ((k : ℂ) - 1 - w) * Complex.Gamma ((k : ℂ) - (w + 1)) := by
    rw [show (k : ℂ) - w = ((k : ℂ) - (w + 1)) + 1 by ring, Complex.Gamma_add_one _
      (by rw [show (k : ℂ) - (w + 1) = (k : ℂ) - 1 - w by ring]; exact hw)]
    ring
  have g2 : (Complex.Gamma (w + ((0 : ℕ) : ℂ) + 1))⁻¹ =
      (w + 1) * (Complex.Gamma (w + 1 + ((0 : ℕ) : ℂ) + 1))⁻¹ := by
    rw [RamanujanTau.RankinLandau.inv_Gamma_eq_mul]; push_cast; ring_nf
  have c1 : ((2 * π : ℝ) : ℂ) ^ (2 * (w + 1)) = ((2 * π : ℝ) : ℂ) ^ (2 * w) * (4 * (π : ℂ) ^ 2) := by
    rw [show 2 * (w + 1) = 2 * w + 2 by ring, Complex.cpow_add _ _ hb,
      show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    push_cast; ring
  rw [g1, g2, c1]
  ring

/-- The integrand of `J_0(y)`: `G(s) = y^s Q_0(s)`. -/
noncomputable def G0 (k : ℕ) (y : ℝ) (s : ℂ) : ℂ := (y : ℂ) ^ (s + ((0 : ℕ) : ℂ)) * Q k 0 s

lemma Jc_eq_G0 (k : ℕ) (σ y : ℝ) :
    Jc k 0 σ y = ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, G0 k y ((σ : ℂ) + t * I) := rfl

lemma norm_G0 (k : ℕ) {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ‖G0 k y s‖ = y ^ s.re * ‖Q k 0 s‖ := by
  unfold G0
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

/-- **The modulus recursion** `‖G(w+1)‖ ‖P(w)‖ = 4π² y ‖G(w)‖`. -/
lemma norm_G0_add_one (k : ℕ) {y : ℝ} (hy : 0 < y) {w : ℂ} (hw : (k : ℂ) - 1 - w ≠ 0) :
    ‖G0 k y (w + 1)‖ * ‖P2 k w‖ = 4 * π ^ 2 * y * ‖G0 k y w‖ := by
  have h := congrArg norm (Q_add_one k hw)
  rw [norm_mul, norm_mul] at h
  have h4 : ‖(4 : ℂ) * (π : ℂ) ^ 2‖ = 4 * π ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [h4] at h
  rw [norm_G0 k hy, norm_G0 k hy, mul_assoc, h,
    show (w + 1).re = w.re + 1 by simp, Real.rpow_add hy, Real.rpow_one]
  ring

lemma ne_of_im_ne (k : ℕ) {w : ℂ} (hw : w.im ≠ 0) : (k : ℂ) - 1 - w ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this; exact hw (by linarith)

lemma ne_of_re_lt (k : ℕ) {w : ℂ} (hw : w.re < (k : ℝ) - 1) : (k : ℂ) - 1 - w ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this; linarith

lemma abs_im_sq_le_norm_P2 (k : ℕ) (w : ℂ) : |w.im| ^ 2 ≤ ‖P2 k w‖ := by
  unfold P2
  rw [norm_mul]
  have h1 : |w.im| ≤ ‖(k : ℂ) - 1 - w‖ := by
    have := Complex.abs_im_le_norm ((k : ℂ) - 1 - w); simpa using this
  have h2 : |w.im| ≤ ‖w + 1‖ := by simpa using Complex.abs_im_le_norm (w + 1)
  calc |w.im| ^ 2 = |w.im| * |w.im| := by ring
    _ ≤ _ := by gcongr

lemma norm_P2_le (k : ℕ) (w : ℂ) :
    ‖P2 k w‖ ≤ (((k : ℝ) - 1 - w.re) ^ 2 + (w.re + 1) ^ 2) / 2 + w.im ^ 2 := by
  unfold P2
  rw [norm_mul]
  have e1 : ‖(k : ℂ) - 1 - w‖ ^ 2 = ((k : ℝ) - 1 - w.re) ^ 2 + w.im ^ 2 := by
    rw [RamanujanTau.Stirling.sq_norm_eq]; simp
  have e2 : ‖w + 1‖ ^ 2 = (w.re + 1) ^ 2 + w.im ^ 2 := by
    rw [RamanujanTau.Stirling.sq_norm_eq]; simp
  nlinarith [sq_nonneg (‖(k : ℂ) - 1 - w‖ - ‖w + 1‖)]

/-- **Shift to the right**: for `Im s ≠ 0`, `‖G(s+m)‖ ≤ ‖G(s)‖ (4π²y/(Im s)²)^m`. -/
theorem norm_G0_add_nat_le (k : ℕ) {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s.im ≠ 0) (m : ℕ) :
    ‖G0 k y (s + m)‖ ≤ ‖G0 k y s‖ * (4 * π ^ 2 * y / s.im ^ 2) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    set w : ℂ := s + m with hw
    have hwim : w.im = s.im := by simp [hw]
    have hrec := norm_G0_add_one k hy (ne_of_im_ne k (w := w) (by rw [hwim]; exact hs))
    have hP := abs_im_sq_le_norm_P2 k w
    rw [hwim, sq_abs] at hP
    have hi2 : 0 < s.im ^ 2 := by positivity
    rw [show s + ((m + 1 : ℕ) : ℂ) = w + 1 by rw [hw]; push_cast; ring]
    have key : ‖G0 k y (w + 1)‖ ≤ 4 * π ^ 2 * y / s.im ^ 2 * ‖G0 k y w‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hi2]
      calc ‖G0 k y (w + 1)‖ * s.im ^ 2 ≤ ‖G0 k y (w + 1)‖ * ‖P2 k w‖ := by gcongr
        _ = 4 * π ^ 2 * y * ‖G0 k y w‖ := hrec
    calc ‖G0 k y (w + 1)‖ ≤ 4 * π ^ 2 * y / s.im ^ 2 * ‖G0 k y w‖ := key
      _ ≤ 4 * π ^ 2 * y / s.im ^ 2 * (‖G0 k y s‖ * (4 * π ^ 2 * y / s.im ^ 2) ^ m) := by
          gcongr
      _ = ‖G0 k y s‖ * (4 * π ^ 2 * y / s.im ^ 2) ^ (m + 1) := by ring

/-- **Shift to the left**: for `(k−1)/2 ≤ Re s ≤ (k+1)/2` and `m ≤ N`,
`‖G(s−m)‖ ≤ ‖G(s)‖ (((N+k)² + (Im s)²)/(4π²y))^m`. -/
theorem norm_G0_sub_nat_le (k : ℕ) (hk : 3 ≤ k) {y : ℝ} (hy : 0 < y) {s : ℂ}
    (h1 : ((k : ℝ) - 1) / 2 ≤ s.re) (h2 : s.re ≤ ((k : ℝ) + 1) / 2) (N : ℕ) :
    ∀ m : ℕ, m ≤ N → ‖G0 k y (s - m)‖ ≤
      ‖G0 k y s‖ * ((((N : ℝ) + k) ^ 2 + s.im ^ 2) / (4 * π ^ 2 * y)) ^ m := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have hmN : (m : ℝ) + 1 ≤ N := by exact_mod_cast hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    set w : ℂ := s - ((m + 1 : ℕ) : ℂ) with hw
    have hwre : w.re = s.re - m - 1 := by simp [hw]; ring
    have hwim : w.im = s.im := by simp [hw]
    have hrec := norm_G0_add_one k hy (ne_of_re_lt k (w := w) (by rw [hwre]; linarith))
    have hw1 : w + 1 = s - m := by rw [hw]; push_cast; ring
    rw [hw1] at hrec
    set B : ℝ := ((N : ℝ) + k) ^ 2 + s.im ^ 2 with hB
    have hPB : ‖P2 k w‖ ≤ B := by
      refine (norm_P2_le k w).trans ?_
      rw [hwre, hwim, hB]
      have b1 : ((k : ℝ) - 1 - (s.re - m - 1)) ^ 2 ≤ ((N : ℝ) + k) ^ 2 := by
        apply pow_le_pow_left₀ (by linarith) (by linarith)
      have b2 : (s.re - m - 1 + 1) ^ 2 ≤ ((N : ℝ) + k) ^ 2 := by
        rw [← sq_abs]; apply pow_le_pow_left₀ (abs_nonneg _)
        rw [abs_le]; constructor <;> linarith
      linarith
    have hT : 0 < 4 * π ^ 2 * y := by positivity
    have key : ‖G0 k y w‖ ≤ ‖G0 k y (s - m)‖ * (B / (4 * π ^ 2 * y)) := by
      rw [mul_div_assoc', le_div_iff₀ hT, mul_comm _ (4 * π ^ 2 * y), ← hrec]
      gcongr
    calc ‖G0 k y w‖ ≤ ‖G0 k y (s - m)‖ * (B / (4 * π ^ 2 * y)) := key
      _ ≤ (‖G0 k y s‖ * (B / (4 * π ^ 2 * y)) ^ m) * (B / (4 * π ^ 2 * y)) := by
          gcongr; exact ih (by omega)
      _ = ‖G0 k y s‖ * (B / (4 * π ^ 2 * y)) ^ (m + 1) := by ring

lemma differentiableAt_G0 (k : ℕ) {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s.re < k ∨ s.im ≠ 0) :
    DifferentiableAt ℂ (G0 k y) s := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  exact ((differentiableAt_id.add_const _).const_cpow (Or.inl hy0)).mul (differentiableAt_Q k 0 hs)

/-! ### Pointwise bounds on the pieces -/

/-- The strip bound on `(k−1)/2 ≤ Re s ≤ (k+1)/2`. -/
def StripB (k : ℕ) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ s : ℂ, ((k : ℝ) - 1) / 2 ≤ s.re → s.re ≤ ((k : ℝ) + 1) / 2 →
    ‖Q k 0 s‖ ≤ K * (1 + |s.im|) ^ ((k : ℝ) - 1 - 2 * s.re - ((0 : ℕ) : ℝ))

lemma exists_stripB (k : ℕ) (hk : 3 ≤ k) : ∃ K, StripB k K := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨K, hK0, hK⟩ := Q_bound k 0 (A := ((k : ℝ) - 1) / 2) (B := ((k : ℝ) + 1) / 2)
    (by simp; linarith) (by linarith)
  exact ⟨K, hK0, hK⟩

lemma rpow4 {Y : ℝ} (hY : 0 ≤ Y) (z : ℝ) : (Y ^ 4) ^ z = Y ^ (4 * z) := by
  rw [← Real.rpow_natCast_mul hY]; norm_num

lemma rpow_nat' {Y : ℝ} (n : ℕ) {z : ℝ} (hz : z = n) : Y ^ z = Y ^ n := by
  rw [hz, Real.rpow_natCast]

variable {k : ℕ} {K Y : ℝ}

lemma base_bound (hSB : StripB k K) (hY : 1 ≤ Y) {s : ℂ} (h1 : ((k : ℝ) - 1) / 2 ≤ s.re)
    (h2 : s.re ≤ ((k : ℝ) + 1) / 2) :
    ‖G0 k (Y ^ 4) s‖ ≤ Y ^ (4 * s.re) * (K * (1 + |s.im|) ^ ((k : ℝ) - 1 - 2 * s.re)) := by
  rw [norm_G0 k (by positivity), rpow4 (by linarith)]
  have := hSB.2 s h1 h2
  rw [show (k : ℝ) - 1 - 2 * s.re - ((0 : ℕ) : ℝ) = (k : ℝ) - 1 - 2 * s.re by push_cast; ring]
    at this
  gcongr

/-- (N1) the original line `Re s = (k+1)/2`. -/
lemma bound_base_line (hSB : StripB k K) (hY : 1 ≤ Y) (t : ℝ) :
    ‖G0 k (Y ^ 4) (((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I)‖ ≤
      K * Y ^ (2 * k + 2) * (1 + |t|) ^ (-2 : ℝ) := by
  have hre : (((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I).re = ((k : ℝ) + 1) / 2 := by simp
  have him : (((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I).im = t := by simp
  have h := base_bound hSB hY (s := ((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I)
    (by rw [hre]; linarith) (by rw [hre])
  rw [hre, him, rpow_nat' (2 * k + 2) (by push_cast; ring),
    show (k : ℝ) - 1 - 2 * (((k : ℝ) + 1) / 2) = -2 by ring] at h
  calc _ ≤ _ := h
    _ = _ := by ring

/-- The base bound at height `|t| = T ≥ 1`, `T ≥ Y^q`: `‖G‖ ≤ K Y^{4σ+q(k−1−2σ)}`. -/
lemma base_bound_height (hSB : StripB k K) (hY : 1 ≤ Y) {s : ℂ} (h1 : ((k : ℝ) - 1) / 2 ≤ s.re)
    (h2 : s.re ≤ ((k : ℝ) + 1) / 2) {T : ℝ} (hT : |s.im| = T) {q : ℝ} (hq : 0 ≤ q)
    (hTq : Y ^ q ≤ T) :
    ‖G0 k (Y ^ 4) s‖ ≤ K * Y ^ (4 * s.re + q * ((k : ℝ) - 1 - 2 * s.re)) := by
  have h := base_bound hSB hY h1 h2
  rw [hT] at h
  have hY0 : 0 < Y := by linarith
  have he : (k : ℝ) - 1 - 2 * s.re ≤ 0 := by linarith
  have hYq : 0 < Y ^ q := Real.rpow_pos_of_pos hY0 q
  have h3 : (1 + T) ^ ((k : ℝ) - 1 - 2 * s.re) ≤ (Y ^ q) ^ ((k : ℝ) - 1 - 2 * s.re) :=
    Real.rpow_le_rpow_of_nonpos hYq (by linarith) he
  rw [← Real.rpow_mul hY0.le] at h3
  have hK := hSB.1
  calc ‖G0 k (Y ^ 4) s‖ ≤ Y ^ (4 * s.re) * (K * (1 + T) ^ ((k : ℝ) - 1 - 2 * s.re)) := h
    _ ≤ Y ^ (4 * s.re) * (K * Y ^ (q * ((k : ℝ) - 1 - 2 * s.re))) := by gcongr
    _ = K * Y ^ (4 * s.re + q * ((k : ℝ) - 1 - 2 * s.re)) := by
        rw [Real.rpow_add hY0]; ring

/-- (N2) the strip at height `±τ`, `τ = 2πY²`: `‖G‖ ≤ K Y^{2k−2}`. -/
lemma bound_tau_base (hk1 : 1 ≤ k) (hSB : StripB k K) (hY : 1 ≤ Y) {s : ℂ} (h1 : ((k : ℝ) - 1) / 2 ≤ s.re)
    (h2 : s.re ≤ ((k : ℝ) + 1) / 2) (hs : |s.im| = 2 * π * Y ^ 2) :
    ‖G0 k (Y ^ 4) s‖ ≤ K * Y ^ (2 * k - 2) := by
  have hY2 : Y ^ (2 : ℝ) ≤ 2 * π * Y ^ 2 := by
    rw [Real.rpow_two]; have := Real.pi_gt_three; nlinarith [sq_nonneg Y]
  have h := base_bound_height hSB hY h1 h2 hs (by norm_num) hY2
  rw [show 4 * s.re + 2 * ((k : ℝ) - 1 - 2 * s.re) = ((2 * k - 2 : ℕ) : ℝ) by
    rw [Nat.cast_sub (by omega)]; push_cast; ring, Real.rpow_natCast] at h
  exact h

/-- (N3) the strip at height `±U`, `U = Y⁶`: `‖G‖ ≤ K Y^{2k−2}`. -/
lemma bound_U_base (hk1 : 1 ≤ k) (hSB : StripB k K) (hY : 1 ≤ Y) {s : ℂ} (h1 : ((k : ℝ) - 1) / 2 ≤ s.re)
    (h2 : s.re ≤ ((k : ℝ) + 1) / 2) (hs : |s.im| = Y ^ 6) :
    ‖G0 k (Y ^ 4) s‖ ≤ K * Y ^ (2 * k - 2) := by
  have h := base_bound_height hSB hY h1 h2 hs (q := 6) (by norm_num)
    (by rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast])
  have hK := hSB.1
  refine h.trans ?_
  rw [← rpow_nat' (Y := Y) (2 * k - 2) (z := ((2 * k - 2 : ℕ) : ℝ)) rfl]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY
    (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)) hK

/-- (C1) the right half of the horizontal segment at `±τ`. -/
lemma bound_tau_right (hk1 : 1 ≤ k) (hSB : StripB k K) (hY : 1 ≤ Y) {σ t : ℝ} (hσ : ((k : ℝ) + 1) / 2 ≤ σ)
    (ht : |t| = 2 * π * Y ^ 2) : ‖G0 k (Y ^ 4) ((σ : ℂ) + t * I)‖ ≤ K * Y ^ (2 * k - 2) := by
  set b : ℝ := ((k : ℝ) + 1) / 2 with hb
  set m : ℕ := ⌈σ - b⌉₊ with hm
  have hm1 : σ - b ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < σ - b + 1 := Nat.ceil_lt_add_one (by linarith)
  set s' : ℂ := ((σ - m : ℝ) : ℂ) + t * I with hs'
  have hre : s'.re = σ - m := by simp [hs']
  have him : s'.im = t := by simp [hs']
  have hsm : s' + m = (σ : ℂ) + t * I := by rw [hs']; push_cast; ring
  have hτp : 0 < 2 * π * Y ^ 2 := by have := Real.pi_pos; positivity
  have ht0 : t ≠ 0 := by
    intro h; rw [h, abs_zero] at ht; linarith
  have hup := norm_G0_add_nat_le k (y := Y ^ 4) (by positivity) (s := s') (by rw [him]; exact ht0) m
  have ht2 : t ^ 2 = 4 * π ^ 2 * Y ^ 4 := by
    have : t ^ 2 = (2 * π * Y ^ 2) ^ 2 := by rw [← ht, sq_abs]
    rw [this]; ring
  rw [hsm, him, ht2, div_self (by positivity), one_pow, mul_one] at hup
  exact hup.trans (bound_tau_base hk1 hSB hY (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him]; exact ht))

/-- The left-shift factor at height `τ` is at most `e`. -/
lemma factor_le (hk : 3 ≤ k) (hY : (k : ℝ) + 3 ≤ Y) {n : ℕ} (hn : (n : ℝ) ≤ Y + 1) {m : ℕ}
    (hm : m ≤ n) :
    ((((n : ℝ) + k) ^ 2 + (2 * π * Y ^ 2) ^ 2) / (4 * π ^ 2 * Y ^ 4)) ^ m ≤ Real.exp 1 := by
  have hpi := Real.pi_gt_three
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hY0 : 0 < Y := by linarith
  set c : ℝ := ((n : ℝ) + k) ^ 2 with hc
  set τ2 : ℝ := (2 * π * Y ^ 2) ^ 2 with hτ2
  have hτ2p : 0 < τ2 := by positivity
  have e : (c + τ2) / (4 * π ^ 2 * Y ^ 4) = 1 + c / τ2 := by
    rw [hτ2]; field_simp; ring
  rw [e]
  have hx : 0 ≤ c / τ2 := by positivity
  have h1 : (1 + c / τ2) ^ m ≤ Real.exp (c / τ2) ^ m := by
    gcongr; linarith [Real.add_one_le_exp (c / τ2)]
  rw [← Real.exp_nat_mul] at h1
  refine h1.trans (Real.exp_le_exp.2 ?_)
  have hm' : (m : ℝ) ≤ 2 * Y := by
    have := (Nat.cast_le (α := ℝ)).2 hm; linarith
  have hcb : c ≤ 4 * Y ^ 2 := by
    have : (n : ℝ) + k ≤ 2 * Y := by linarith
    rw [hc]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  rw [mul_div_assoc', div_le_iff₀ hτ2p, one_mul, hτ2]
  have hπ2 : 9 ≤ π ^ 2 := by nlinarith
  have hY3 : Y ^ 3 ≤ Y ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hc0 : 0 ≤ c := by positivity
  calc (m : ℝ) * c ≤ (2 * Y) * (4 * Y ^ 2) := by
        apply mul_le_mul hm' hcb hc0 (by linarith)
    _ = 8 * Y ^ 3 := by ring
    _ ≤ 8 * Y ^ 4 := by linarith
    _ ≤ (2 * π * Y ^ 2) ^ 2 := by nlinarith [pow_nonneg hY0.le 4]

/-- (C2) the left half of the horizontal segment at `±τ`. -/
lemma bound_tau_left (hk : 3 ≤ k) (hSB : StripB k K) (hY : (k : ℝ) + 3 ≤ Y) {σ t : ℝ}
    (hσ1 : ((k : ℝ) + 1) / 2 - (⌈Y⌉₊ : ℝ) ≤ σ) (hσ2 : σ ≤ ((k : ℝ) + 1) / 2)
    (ht : |t| = 2 * π * Y ^ 2) :
    ‖G0 k (Y ^ 4) ((σ : ℂ) + t * I)‖ ≤ K * Y ^ (2 * k - 2) * Real.exp 1 := by
  have hY1 : 1 ≤ Y := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  set b : ℝ := ((k : ℝ) + 1) / 2 with hb
  set n : ℕ := ⌈Y⌉₊ with hn
  have hnY : (n : ℝ) ≤ Y + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  set m : ℕ := ⌊b - σ⌋₊ with hm
  have hm1 : (m : ℝ) ≤ b - σ := Nat.floor_le (by linarith)
  have hm2 : b - σ < m + 1 := Nat.lt_floor_add_one _
  have hmn' : (m : ℝ) ≤ n := hm1.trans (by linarith)
  have hmn : m ≤ n := by exact_mod_cast hmn'
  set s' : ℂ := ((σ + m : ℝ) : ℂ) + t * I with hs'
  have hre : s'.re = σ + m := by simp [hs']
  have him : s'.im = t := by simp [hs']
  have hsm : s' - m = (σ : ℂ) + t * I := by rw [hs']; push_cast; ring
  have hdown := norm_G0_sub_nat_le k hk (y := Y ^ 4) (by positivity) (s := s')
    (by rw [hre]; linarith) (by rw [hre]; linarith) n m hmn
  have ht2 : t ^ 2 = (2 * π * Y ^ 2) ^ 2 := by rw [← ht, sq_abs]
  rw [hsm, him, ht2] at hdown
  have hbase := bound_tau_base (by omega) hSB hY1 (s := s') (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him]; exact ht)
  have hf := factor_le hk hY hnY hmn
  refine hdown.trans ?_
  have := hSB.1
  gcongr

/-- (C3) the top segments at `±U`, `U = Y⁶` (to the right of the base line). -/
lemma bound_U (hk1 : 1 ≤ k) (hSB : StripB k K) (hY : 3 ≤ Y) {σ t : ℝ} (hσ : ((k : ℝ) + 1) / 2 < σ)
    (ht : |t| = Y ^ 6) : ‖G0 k (Y ^ 4) ((σ : ℂ) + t * I)‖ ≤ K * Y ^ (2 * k - 2) := by
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  set b : ℝ := ((k : ℝ) + 1) / 2 with hb
  set m : ℕ := ⌈σ - b⌉₊ with hm
  have hm1 : σ - b ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < σ - b + 1 := Nat.ceil_lt_add_one (by linarith)
  set s' : ℂ := ((σ - m : ℝ) : ℂ) + t * I with hs'
  have hre : s'.re = σ - m := by simp [hs']
  have him : s'.im = t := by simp [hs']
  have hsm : s' + m = (σ : ℂ) + t * I := by rw [hs']; push_cast; ring
  have ht0 : t ≠ 0 := by
    intro h; rw [h, abs_zero] at ht; have : 0 < Y ^ 6 := by positivity
    linarith
  have hup := norm_G0_add_nat_le k (y := Y ^ 4) (by positivity) (s := s') (by rw [him]; exact ht0) m
  have ht2 : t ^ 2 = Y ^ 12 := by
    have : t ^ 2 = (Y ^ 6) ^ 2 := by rw [← ht, sq_abs]
    rw [this]; ring
  rw [hsm, him, ht2] at hup
  have hbase := bound_U_base hk1 hSB hY1 (s := s') (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him]; exact ht)
  set r : ℝ := 4 * π ^ 2 * Y ^ 4 / Y ^ 12 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by positivity)]
    have hpi := Real.pi_lt_d2
    have h8 : (3 : ℝ) ^ 8 ≤ Y ^ 8 := pow_le_pow_left₀ (by norm_num) hY 8
    have hp2 : π ^ 2 ≤ 3.15 ^ 2 := pow_le_pow_left₀ Real.pi_pos.le hpi.le 2
    have : 4 * π ^ 2 ≤ Y ^ 8 := by nlinarith
    calc 4 * π ^ 2 * Y ^ 4 ≤ Y ^ 8 * Y ^ 4 := by gcongr
      _ = Y ^ 12 := by ring
  have hrm : r ^ m ≤ 1 := pow_le_one₀ hr0 hr1
  have hK := hSB.1
  calc ‖G0 k (Y ^ 4) ((σ : ℂ) + t * I)‖ ≤ ‖G0 k (Y ^ 4) s'‖ * r ^ m := hup
    _ ≤ (K * Y ^ (2 * k - 2)) * 1 := by gcongr
    _ = K * Y ^ (2 * k - 2) := mul_one _

/-- (C4) the right vertical line `Re s = (k+1)/2 + n`. -/
lemma bound_right_line (hSB : StripB k K) (hY : 1 ≤ Y) {t : ℝ} (ht : t ≠ 0) (n : ℕ) :
    ‖G0 k (Y ^ 4) ((((k : ℝ) + 1) / 2 + n : ℝ) + t * I)‖ ≤
      K * Y ^ (2 * k + 2) * (1 + |t|) ^ (-2 : ℝ) * (4 * π ^ 2 * Y ^ 4 / t ^ 2) ^ n := by
  have him : (((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I).im = t := by simp
  have hup := norm_G0_add_nat_le k (y := Y ^ 4) (by positivity)
    (s := ((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I) (by rw [him]; exact ht) n
  rw [show ((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I + n = ((((k : ℝ) + 1) / 2 + n : ℝ) : ℂ) + t * I by
    push_cast; ring, him] at hup
  refine hup.trans ?_
  gcongr
  exact bound_base_line hSB hY t

/-- (C5) the left vertical line `Re s = (k+1)/2 − n`. -/
lemma bound_left_line (hk : 3 ≤ k) (hSB : StripB k K) (hY : 1 ≤ Y) (t : ℝ) (n : ℕ) :
    ‖G0 k (Y ^ 4) ((((k : ℝ) + 1) / 2 - n : ℝ) + t * I)‖ ≤
      K * Y ^ (2 * k + 2) * (1 + |t|) ^ (-2 : ℝ) *
        ((((n : ℝ) + k) ^ 2 + t ^ 2) / (4 * π ^ 2 * Y ^ 4)) ^ n := by
  have hre : (((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I).re = ((k : ℝ) + 1) / 2 := by simp
  have him : (((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I).im = t := by simp
  have hdown := norm_G0_sub_nat_le k hk (y := Y ^ 4) (by positivity)
    (s := ((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I) (by rw [hre]; linarith) (by rw [hre]) n n le_rfl
  rw [show ((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I - n = ((((k : ℝ) + 1) / 2 - n : ℝ) : ℂ) + t * I by
    push_cast; ring, him] at hdown
  refine hdown.trans ?_
  gcongr
  exact bound_base_line hSB hY t

/-- The pointwise majorant on the left line: for `|t| ≤ τ` and `Y ≥ k+3`,
`(1+|t|)^{−2} ρ^n ≤ (4/τ²)((|t|+1)/τ)^n + e^{−Y}`, `ρ = ((n+k)²+t²)/τ²`. -/
lemma left_pointwise (hk : 3 ≤ k) (hY : (k : ℝ) + 3 ≤ Y) {t : ℝ} (ht : |t| ≤ 2 * π * Y ^ 2) :
    (1 + |t|) ^ (-2 : ℝ) *
        (((((⌈Y⌉₊ : ℕ) : ℝ) + k) ^ 2 + t ^ 2) / (4 * π ^ 2 * Y ^ 4)) ^ ⌈Y⌉₊ ≤
      4 / (2 * π * Y ^ 2) ^ 2 * ((|t| + 1) / (2 * π * Y ^ 2)) ^ ⌈Y⌉₊ + Real.exp (-Y) := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  set n : ℕ := ⌈Y⌉₊ with hn
  have hY1 : 1 ≤ Y := by linarith
  have hnY : (n : ℝ) ≤ Y + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hnY' : Y ≤ n := Nat.le_ceil _
  have hpi := Real.pi_gt_three
  have hY0 : 0 < Y := by linarith
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  have hτ0 : 0 < τ := by positivity
  set c : ℝ := ((n : ℝ) + k) ^ 2 with hc
  have hcb : c ≤ 4 * Y ^ 2 := by
    have : (n : ℝ) + k ≤ 2 * Y := by linarith
    rw [hc]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hcτ : c ≤ τ := by
    refine hcb.trans ?_; rw [hτ]; nlinarith [sq_nonneg Y]
  set ρ : ℝ := (c + t ^ 2) / τ ^ 2 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have e : (c + t ^ 2) / (4 * π ^ 2 * Y ^ 4) = ρ := by
    rw [hρ, hτ]; ring
  rw [e]
  have hρle : ρ ≤ (|t| + 1) / τ := by
    rw [hρ, div_le_div_iff₀ (by positivity) hτ0]
    have h1 : t ^ 2 ≤ |t| * τ := by
      rw [← sq_abs, sq]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg t)
    calc (c + t ^ 2) * τ ≤ (τ + |t| * τ) * τ := by gcongr
      _ = (|t| + 1) * τ ^ 2 := by ring
  rcases le_or_gt (τ / 2) |t| with hbig | hsmall
  · have h1 : (1 + |t|) ^ (-2 : ℝ) ≤ 4 / τ ^ 2 := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
        Real.rpow_natCast, inv_le_iff_one_le_mul₀ (by positivity)]
      have : τ ^ 2 ≤ 4 * (1 + |t|) ^ 2 := by nlinarith
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
    have h2 : ρ ^ n ≤ ((|t| + 1) / τ) ^ n := pow_le_pow_left₀ hρ0 hρle _
    have h3 : (1 + |t|) ^ (-2 : ℝ) * ρ ^ n ≤ 4 / τ ^ 2 * ((|t| + 1) / τ) ^ n :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    linarith [Real.exp_pos (-Y)]
  · have h1 : (1 + |t|) ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by norm_num)
    have hρ2 : ρ ≤ 13 / 36 := by
      rw [hρ, div_le_iff₀ (by positivity)]
      have ht2 : t ^ 2 ≤ τ ^ 2 / 4 := by
        rw [← sq_abs]; nlinarith [abs_nonneg t]
      have hc2 : c ≤ τ ^ 2 / 9 := by
        refine hcb.trans ?_
        rw [hτ]
        have hπ2 : 9 ≤ π ^ 2 := by nlinarith
        have hYY : 1 ≤ Y ^ 2 := by nlinarith
        nlinarith [sq_nonneg Y, pow_nonneg hY0.le 4]
      nlinarith
    have he : (13 / 36 : ℝ) ≤ Real.exp (-1) := by
      rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have h2 : ρ ^ n ≤ Real.exp (-Y) := by
      calc ρ ^ n ≤ (Real.exp (-1)) ^ n := pow_le_pow_left₀ hρ0 (hρ2.trans he) n
        _ = Real.exp (-(n : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ Real.exp (-Y) := Real.exp_le_exp.2 (by linarith)
    have h3 : (1 + |t|) ^ (-2 : ℝ) * ρ ^ n ≤ Real.exp (-Y) := by
      calc _ ≤ 1 * Real.exp (-Y) := mul_le_mul h1 h2 (pow_nonneg hρ0 _) zero_le_one
        _ = _ := one_mul _
    have : 0 ≤ 4 / τ ^ 2 * ((|t| + 1) / τ) ^ n := by positivity
    linarith

end RamanujanTau.TauPartialSumsSharp
