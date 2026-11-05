/-
# Pointwise bounds for `‖G‖` on the pieces of the bent contour

Parameters: `Y ≥ 1`, `y = Y⁸`, `τ = 2πY²` (so `τ⁴ = 16π⁴y`: the stationary height),
`n = ⌈Y⌉₊ ≍ √τ`, `U = Y⁸`. The contour replacing `Re s = 1/2` is

* `Re s = 1/2 − n` for `|t| ≤ τ`;  `Re s = 1/2 + n` for `τ ≤ |t| ≤ U`;
* horizontal segments at `t = ±τ` (`1/2 − n ≤ σ ≤ 1/2 + n`) and at `t = ±U`;
* the original line for `|t| ≥ U`.

All bounds come from `Qk_bound_sharp` on `−1/2 ≤ Re s ≤ 1/2` and the exact shift recursion.
-/
import RamanujanTau.KernelPhase.Shift

set_option autoImplicit false

namespace RamanujanTau.KernelPhase

open Complex Real
open RamanujanTau.RankinErrorGeneral RamanujanTau.RankinLandau

/-- The strip bound `‖Q_1(s)‖ ≤ K(1+|Im s|)^{−4 Re s}` on `−1/2 ≤ Re s ≤ 1/2`. -/
def StripBound (m : ℕ) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 1 / 2 →
    ‖Qk m 1 s‖ ≤ K * (1 + |s.im|) ^ (1 - 4 * s.re - ((1 : ℕ) : ℝ))

lemma exists_stripBound (m : ℕ) (hm : 1 ≤ m) : ∃ K, StripBound m K := by
  obtain ⟨K, hK0, hK⟩ := Qk_bound_sharp m 1 hm (A₀ := -1 / 2) (by norm_num)
  exact ⟨K, hK0, hK⟩

lemma rpow8 {Y : ℝ} (hY : 0 ≤ Y) (z : ℝ) : (Y ^ 8) ^ z = Y ^ (8 * z) := by
  rw [← Real.rpow_natCast_mul hY]; norm_num

lemma rpow_nat' {Y : ℝ} (n : ℕ) {z : ℝ} (hz : z = n) : Y ^ z = Y ^ n := by
  rw [hz, Real.rpow_natCast]

variable {m : ℕ} {K Y : ℝ}

lemma base_bound (hSB : StripBound m K) (hY : 1 ≤ Y) {s : ℂ} (h1 : -1 / 2 ≤ s.re)
    (h2 : s.re ≤ 1 / 2) :
    ‖G m (Y ^ 8) s‖ ≤ Y ^ (8 * (s.re + 1)) * (K * (1 + |s.im|) ^ (-4 * s.re)) := by
  rw [norm_G m (by positivity), rpow8 (by linarith)]
  have := hSB.2 s h1 h2
  rw [show 1 - 4 * s.re - ((1 : ℕ) : ℝ) = -4 * s.re by push_cast; ring] at this
  gcongr

/-- (N1) the original line. -/
lemma bound_half (hSB : StripBound m K) (hY : 1 ≤ Y) (t : ℝ) :
    ‖G m (Y ^ 8) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ K * Y ^ 12 * (1 + |t|) ^ (-2 : ℝ) := by
  have hre : (((1 / 2 : ℝ) : ℂ) + t * I).re = 1 / 2 := by simp
  have him : (((1 / 2 : ℝ) : ℂ) + t * I).im = t := by simp
  have h := base_bound hSB hY (s := ((1 / 2 : ℝ) : ℂ) + t * I) (by rw [hre]; norm_num)
    (by rw [hre])
  rw [hre, him, rpow_nat' 12 (by norm_num), show -4 * (1 / 2 : ℝ) = -2 by norm_num] at h
  calc _ ≤ _ := h
    _ = _ := by ring

/-- (N2) the strip at height `±τ`. -/
lemma bound_tau_base (hSB : StripBound m K) (hY : 1 ≤ Y) {s : ℂ} (h1 : -1 / 2 ≤ s.re)
    (h2 : s.re ≤ 1 / 2) (hs : |s.im| = 2 * π * Y ^ 2) :
    ‖G m (Y ^ 8) s‖ ≤ 64 * K * Y ^ 8 := by
  have h := base_bound hSB hY h1 h2
  rw [hs] at h
  set σ := s.re with hσ
  have hY0 : 0 < Y := by linarith
  have hY2 : 1 ≤ Y ^ 2 := by nlinarith
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  have hτ0 : 0 < 1 + τ := by positivity
  have e1 : Y ^ (8 * (σ + 1)) = Y ^ 8 * (Y ^ 2) ^ (4 * σ) := by
    rw [← Real.rpow_natCast_mul hY0.le, show 8 * (σ + 1) = 8 + ((2 : ℕ) : ℝ) * (4 * σ) by
      push_cast; ring, Real.rpow_add hY0, rpow_nat' 8 (by norm_num)]
  have e2 : (1 + τ) ^ (-4 * σ) = ((1 + τ) ^ (4 * σ))⁻¹ := by
    rw [show -4 * σ = -(4 * σ) by ring, Real.rpow_neg hτ0.le]
  set q : ℝ := Y ^ 2 / (1 + τ) with hq
  have e3 : (Y ^ 2) ^ (4 * σ) * ((1 + τ) ^ (4 * σ))⁻¹ = q ^ (4 * σ) := by
    rw [hq, Real.div_rpow (by positivity) hτ0.le]; ring
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one hτ0, hτ]; nlinarith
  have hq8 : 1 / 8 ≤ q := by
    rw [hq, le_div_iff₀ hτ0, hτ]; nlinarith
  have hqb : q ^ (4 * σ) ≤ 64 := by
    refine (Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (show (-2 : ℝ) ≤ 4 * σ by linarith)).trans ?_
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hq0.le, Real.rpow_natCast,
      inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  calc ‖G m (Y ^ 8) s‖ ≤ Y ^ (8 * (σ + 1)) * (K * (1 + τ) ^ (-4 * σ)) := h
    _ = K * Y ^ 8 * q ^ (4 * σ) := by rw [e1, e2, ← e3]; ring
    _ ≤ K * Y ^ 8 * 64 := by have := hSB.1; gcongr
    _ = 64 * K * Y ^ 8 := by ring

/-- (N3) the strip at height `±U = ±Y⁸` (crude). -/
lemma bound_U_base (hSB : StripBound m K) (hY : 1 ≤ Y) {s : ℂ} (h1 : -1 / 2 ≤ s.re)
    (h2 : s.re ≤ 1 / 2) (hs : |s.im| = Y ^ 8) :
    ‖G m (Y ^ 8) s‖ ≤ 4 * K * Y ^ 28 := by
  have h := base_bound hSB hY h1 h2
  rw [hs] at h
  have hY8 : 1 ≤ Y ^ 8 := one_le_pow₀ hY
  have a1 : Y ^ (8 * (s.re + 1)) ≤ Y ^ 12 := by
    rw [← rpow_nat' (Y := Y) 12 (z := 12) (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  have a2 : (1 + Y ^ 8) ^ (-4 * s.re) ≤ 4 * Y ^ 16 := by
    refine (Real.rpow_le_rpow_of_exponent_le (by linarith) (show -4 * s.re ≤ ((2 : ℕ) : ℝ) by
      push_cast; linarith)).trans ?_
    rw [Real.rpow_natCast]; nlinarith
  calc ‖G m (Y ^ 8) s‖ ≤ Y ^ (8 * (s.re + 1)) * (K * (1 + Y ^ 8) ^ (-4 * s.re)) := h
    _ ≤ Y ^ 12 * (K * (4 * Y ^ 16)) := by
        have := hSB.1
        gcongr
    _ = 4 * K * Y ^ 28 := by ring

lemma t4_eq {t Y : ℝ} (ht : |t| = 2 * π * Y ^ 2) : t ^ 4 = 16 * π ^ 4 * Y ^ 8 := by
  have : t ^ 2 = (2 * π * Y ^ 2) ^ 2 := by rw [← ht, sq_abs]
  calc t ^ 4 = (t ^ 2) ^ 2 := by ring
    _ = _ := by rw [this]; ring

/-- (C1) the right half of the horizontal segment at `±τ`. -/
lemma bound_tau_right (hSB : StripBound m K) (hY : 1 ≤ Y) {σ t : ℝ} (hσ : 1 / 2 ≤ σ)
    (ht : |t| = 2 * π * Y ^ 2) : ‖G m (Y ^ 8) ((σ : ℂ) + t * I)‖ ≤ 64 * K * Y ^ 8 := by
  set k : ℕ := ⌈σ - 1 / 2⌉₊ with hk
  have hk1 : σ - 1 / 2 ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < σ - 1 / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  set s' : ℂ := ((σ - k : ℝ) : ℂ) + t * I with hs'
  have hre : s'.re = σ - k := by simp [hs']
  have him : s'.im = t := by simp [hs']
  have hsk : s' + k = (σ : ℂ) + t * I := by rw [hs']; push_cast; ring
  have hτp : 0 < 2 * π * Y ^ 2 := by have := Real.pi_pos; positivity
  have ht0 : t ≠ 0 := by
    intro h; rw [h, abs_zero] at ht; linarith
  have hup := norm_G_add_nat_le m (y := Y ^ 8) (by positivity) (s := s') (by rw [him]; exact ht0) k
  rw [hsk, him, t4_eq ht, div_self (by positivity), one_pow, mul_one] at hup
  exact hup.trans (bound_tau_base hSB hY (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him]; exact ht))

/-- The left-shift factor at height `τ` is bounded. -/
lemma factor_le (hm : 1 ≤ m) (hY : 1 ≤ Y) {n : ℕ} (hn : (n : ℝ) ≤ Y + 1) {k : ℕ} (hk : k ≤ n) :
    ((((n : ℝ) + 1) ^ 2 + (m : ℝ) ^ 2 + (2 * π * Y ^ 2) ^ 2) ^ 2 / (16 * π ^ 4 * Y ^ 8)) ^ k ≤
      Real.exp (9 + (m : ℝ) ^ 2) := by
  have hpi := Real.pi_gt_three
  have hY0 : 0 < Y := by linarith
  set c : ℝ := ((n : ℝ) + 1) ^ 2 + (m : ℝ) ^ 2 with hc
  set τ2 : ℝ := (2 * π * Y ^ 2) ^ 2 with hτ2
  have hτ2p : 0 < τ2 := by positivity
  have e : (c + τ2) ^ 2 / (16 * π ^ 4 * Y ^ 8) = (1 + c / τ2) ^ 2 := by
    rw [hτ2]; field_simp; ring
  rw [e, ← pow_mul]
  have hx : 0 ≤ c / τ2 := by positivity
  have h1 : (1 + c / τ2) ^ (2 * k) ≤ Real.exp (c / τ2) ^ (2 * k) := by
    gcongr; linarith [Real.add_one_le_exp (c / τ2)]
  rw [← Real.exp_nat_mul] at h1
  refine h1.trans (Real.exp_le_exp.2 ?_)
  have hk' : (k : ℝ) ≤ Y + 1 := (Nat.cast_le.2 hk).trans hn
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcb : c ≤ (9 + (m : ℝ) ^ 2) * Y ^ 2 := by
    have e1 : (n : ℝ) + 1 ≤ 3 * Y := by linarith
    have e2 : ((n : ℝ) + 1) ^ 2 ≤ 9 * Y ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have e3 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * Y ^ 2 := by
      have : (1 : ℝ) ≤ Y ^ 2 := by nlinarith
      nlinarith [sq_nonneg (m : ℝ)]
    rw [hc]; nlinarith
  rw [mul_div_assoc', div_le_iff₀ hτ2p, hτ2]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hc0 : 0 ≤ c := by positivity
  have h2 : ((2 * k : ℕ) : ℝ) * c ≤ 4 * Y * ((9 + (m : ℝ) ^ 2) * Y ^ 2) := by
    push_cast
    have : 2 * (k : ℝ) ≤ 4 * Y := by linarith
    calc 2 * (k : ℝ) * c ≤ 4 * Y * c := by gcongr
      _ ≤ _ := by gcongr
  have h3 : 4 * Y * ((9 + (m : ℝ) ^ 2) * Y ^ 2) ≤ (9 + (m : ℝ) ^ 2) * (2 * π * Y ^ 2) ^ 2 := by
    have hm2 : 0 ≤ 9 + (m : ℝ) ^ 2 := by positivity
    have hY3 : Y ^ 3 ≤ Y ^ 4 := pow_le_pow_right₀ hY (by norm_num)
    have hπ2 : 9 ≤ π ^ 2 := by nlinarith
    have hY4 : 0 ≤ Y ^ 4 := by positivity
    have : 4 * Y * Y ^ 2 ≤ (2 * π * Y ^ 2) ^ 2 := by
      calc 4 * Y * Y ^ 2 = 4 * Y ^ 3 := by ring
        _ ≤ 4 * Y ^ 4 := by linarith
        _ ≤ 4 * π ^ 2 * Y ^ 4 := by nlinarith
        _ = (2 * π * Y ^ 2) ^ 2 := by ring
    calc 4 * Y * ((9 + (m : ℝ) ^ 2) * Y ^ 2) = (9 + (m : ℝ) ^ 2) * (4 * Y * Y ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hm2
  linarith

/-- (C2) the left half of the horizontal segment at `±τ`. -/
lemma bound_tau_left (hm : 1 ≤ m) (hSB : StripBound m K) (hY : 1 ≤ Y) {σ t : ℝ}
    (hσ1 : 1 / 2 - (⌈Y⌉₊ : ℝ) ≤ σ) (hσ2 : σ ≤ 1 / 2) (ht : |t| = 2 * π * Y ^ 2) :
    ‖G m (Y ^ 8) ((σ : ℂ) + t * I)‖ ≤ 64 * K * Y ^ 8 * Real.exp (9 + (m : ℝ) ^ 2) := by
  set n : ℕ := ⌈Y⌉₊ with hn
  have hnY : (n : ℝ) ≤ Y + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  set k : ℕ := ⌊1 / 2 - σ⌋₊ with hk
  have hk1 : (k : ℝ) ≤ 1 / 2 - σ := Nat.floor_le (by linarith)
  have hk2 : 1 / 2 - σ < k + 1 := Nat.lt_floor_add_one _
  have hkn' : (k : ℝ) ≤ n := hk1.trans (by linarith)
  have hkn : k ≤ n := by exact_mod_cast hkn'
  set s' : ℂ := ((σ + k : ℝ) : ℂ) + t * I with hs'
  have hre : s'.re = σ + k := by simp [hs']
  have him : s'.im = t := by simp [hs']
  have hsk : s' - k = (σ : ℂ) + t * I := by rw [hs']; push_cast; ring
  have hdown := norm_G_sub_nat_le m hm (y := Y ^ 8) (by positivity) (s := s')
    (by rw [hre]; linarith) (by rw [hre]; linarith) n k hkn
  have ht2 : t ^ 2 = (2 * π * Y ^ 2) ^ 2 := by rw [← ht, sq_abs]
  rw [hsk, him, ht2] at hdown
  have hb := bound_tau_base hSB hY (s := s') (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him]; exact ht)
  have hf := factor_le hm hY hnY hkn
  refine hdown.trans ?_
  calc ‖G m (Y ^ 8) s'‖ * ((((n : ℝ) + 1) ^ 2 + (m : ℝ) ^ 2 + (2 * π * Y ^ 2) ^ 2) ^ 2 /
        (16 * π ^ 4 * Y ^ 8)) ^ k ≤ 64 * K * Y ^ 8 * Real.exp (9 + (m : ℝ) ^ 2) := by
        have := hSB.1
        gcongr

/-- (C3) the top segments at `±U`. -/
lemma bound_U (hSB : StripBound m K) (hY : 2 ≤ Y) {σ t : ℝ} (hσ : 1 / 2 < σ)
    (ht : |t| = Y ^ 8) : ‖G m (Y ^ 8) ((σ : ℂ) + t * I)‖ ≤ 64 * π ^ 4 * K * Y ^ 4 := by
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  set k : ℕ := ⌈σ - 1 / 2⌉₊ with hk
  have hk1 : σ - 1 / 2 ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < σ - 1 / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  have hk0 : k ≠ 0 := by
    intro h; rw [h] at hk1; simp at hk1; linarith
  set s' : ℂ := ((σ - k : ℝ) : ℂ) + t * I with hs'
  have hre : s'.re = σ - k := by simp [hs']
  have him : s'.im = t := by simp [hs']
  have hsk : s' + k = (σ : ℂ) + t * I := by rw [hs']; push_cast; ring
  have ht0 : t ≠ 0 := by
    intro h; rw [h, abs_zero] at ht; have : 0 < Y ^ 8 := by positivity
    linarith
  have hup := norm_G_add_nat_le m (y := Y ^ 8) (by positivity) (s := s') (by rw [him]; exact ht0) k
  have ht4 : t ^ 4 = Y ^ 32 := by
    have : t ^ 2 = (Y ^ 8) ^ 2 := by rw [← ht, sq_abs]
    calc t ^ 4 = (t ^ 2) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  rw [hsk, him, ht4] at hup
  have hb := bound_U_base hSB hY1 (s := s') (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him]; exact ht)
  set r : ℝ := 16 * π ^ 4 * Y ^ 8 / Y ^ 32 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by positivity)]
    have hpi := Real.pi_lt_d2
    have h24 : (2 : ℝ) ^ 24 ≤ Y ^ 24 := pow_le_pow_left₀ (by norm_num) hY 24
    have : 16 * π ^ 4 ≤ Y ^ 24 := by
      have : π ^ 4 ≤ 3.15 ^ 4 := pow_le_pow_left₀ Real.pi_pos.le hpi.le 4
      nlinarith
    calc 16 * π ^ 4 * Y ^ 8 ≤ Y ^ 24 * Y ^ 8 := by gcongr
      _ = Y ^ 32 := by ring
  have hrk : r ^ k ≤ r := pow_le_of_le_one hr0 hr1 hk0
  calc ‖G m (Y ^ 8) ((σ : ℂ) + t * I)‖ ≤ ‖G m (Y ^ 8) s'‖ * r ^ k := hup
    _ ≤ (4 * K * Y ^ 28) * r := by
        have := hSB.1
        gcongr
    _ = 64 * π ^ 4 * K * Y ^ 4 := by
        rw [hr]; field_simp; ring

/-- (C4) the right vertical line `Re s = 1/2 + n`. -/
lemma bound_right_line (hSB : StripBound m K) (hY : 1 ≤ Y) {t : ℝ} (ht : t ≠ 0) (n : ℕ) :
    ‖G m (Y ^ 8) (((1 / 2 + n : ℝ) : ℂ) + t * I)‖ ≤
      K * Y ^ 12 * (1 + |t|) ^ (-2 : ℝ) * (16 * π ^ 4 * Y ^ 8 / t ^ 4) ^ n := by
  have him : (((1 / 2 : ℝ) : ℂ) + t * I).im = t := by simp
  have hup := norm_G_add_nat_le m (y := Y ^ 8) (by positivity)
    (s := ((1 / 2 : ℝ) : ℂ) + t * I) (by rw [him]; exact ht) n
  rw [show ((1 / 2 : ℝ) : ℂ) + t * I + n = ((1 / 2 + n : ℝ) : ℂ) + t * I by push_cast; ring,
    him] at hup
  refine hup.trans ?_
  gcongr
  exact bound_half hSB hY t

/-- (C5) the left vertical line `Re s = 1/2 − n`. -/
lemma bound_left_line (hm : 1 ≤ m) (hSB : StripBound m K) (hY : 1 ≤ Y) (t : ℝ) (n : ℕ) :
    ‖G m (Y ^ 8) (((1 / 2 - n : ℝ) : ℂ) + t * I)‖ ≤
      K * Y ^ 12 * (1 + |t|) ^ (-2 : ℝ) *
        ((((n : ℝ) + 1) ^ 2 + (m : ℝ) ^ 2 + t ^ 2) ^ 2 / (16 * π ^ 4 * Y ^ 8)) ^ n := by
  have hre : (((1 / 2 : ℝ) : ℂ) + t * I).re = 1 / 2 := by simp
  have him : (((1 / 2 : ℝ) : ℂ) + t * I).im = t := by simp
  have hdown := norm_G_sub_nat_le m hm (y := Y ^ 8) (by positivity)
    (s := ((1 / 2 : ℝ) : ℂ) + t * I) (by rw [hre]; norm_num) (by rw [hre]) n n le_rfl
  rw [show ((1 / 2 : ℝ) : ℂ) + t * I - n = ((1 / 2 - n : ℝ) : ℂ) + t * I by push_cast; ring,
    him] at hdown
  refine hdown.trans ?_
  gcongr
  exact bound_half hSB hY t

/-- The pointwise majorant on the left line: for `|t| ≤ τ` and `Y ≥ 9 + m²`,
`(1+|t|)^{−2} ρ^{2n} ≤ (4/τ²)((|t|+c₁)/τ)^{2n} + e^{−Y}`, `c₁ = (9+m²)/(2π)`. -/
lemma left_pointwise (hm : 1 ≤ m) (hY1 : 1 ≤ Y) (hY : 9 + (m : ℝ) ^ 2 ≤ Y) {t : ℝ}
    (ht : |t| ≤ 2 * π * Y ^ 2) :
    (1 + |t|) ^ (-2 : ℝ) *
        (((((⌈Y⌉₊ : ℕ) : ℝ) + 1) ^ 2 + (m : ℝ) ^ 2 + t ^ 2) ^ 2 / (16 * π ^ 4 * Y ^ 8)) ^ ⌈Y⌉₊ ≤
      4 / (2 * π * Y ^ 2) ^ 2 *
          ((|t| + (9 + (m : ℝ) ^ 2) / (2 * π)) / (2 * π * Y ^ 2)) ^ (2 * ⌈Y⌉₊) +
        Real.exp (-Y) := by
  set n : ℕ := ⌈Y⌉₊ with hn
  have hnY : (n : ℝ) ≤ Y + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hnY' : Y ≤ n := Nat.le_ceil _
  have hpi := Real.pi_gt_three
  have hY0 : 0 < Y := by linarith
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  have hτ0 : 0 < τ := by positivity
  set c : ℝ := ((n : ℝ) + 1) ^ 2 + (m : ℝ) ^ 2 with hc
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcb : c ≤ (9 + (m : ℝ) ^ 2) * Y ^ 2 := by
    have e1 : (n : ℝ) + 1 ≤ 3 * Y := by linarith
    have e2 : ((n : ℝ) + 1) ^ 2 ≤ 9 * Y ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have e3 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * Y ^ 2 := by
      have : (1 : ℝ) ≤ Y ^ 2 := by nlinarith
      nlinarith [sq_nonneg (m : ℝ)]
    rw [hc]; nlinarith
  set ρ : ℝ := (c + t ^ 2) / τ ^ 2 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have e : ((c + t ^ 2) ^ 2 / (16 * π ^ 4 * Y ^ 8)) ^ n = ρ ^ (2 * n) := by
    rw [hρ, pow_mul]; congr 1; rw [div_pow, hτ]; ring
  rw [e]
  have hA : 0 ≤ (1 + |t|) ^ (-2 : ℝ) := by positivity
  set c₁ : ℝ := (9 + (m : ℝ) ^ 2) / (2 * π) with hc₁
  have hρle : ρ ≤ (|t| + c₁) / τ := by
    rw [hρ, div_le_div_iff₀ (by positivity) hτ0]
    have h1 : t ^ 2 ≤ |t| * τ := by
      rw [← sq_abs, sq]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg t)
    have hc1τ : c₁ * τ = (9 + (m : ℝ) ^ 2) * Y ^ 2 := by
      rw [hc₁, hτ]; field_simp
    have h2 : c ≤ c₁ * τ := by rw [hc1τ]; exact hcb
    calc (c + t ^ 2) * τ ≤ (c₁ * τ + |t| * τ) * τ := by gcongr
      _ = (|t| + c₁) * τ ^ 2 := by ring
  rcases le_or_gt (τ / 2) |t| with hbig | hsmall
  · -- near the stationary height
    have h1 : (1 + |t|) ^ (-2 : ℝ) ≤ 4 / τ ^ 2 := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
        Real.rpow_natCast, inv_le_iff_one_le_mul₀ (by positivity)]
      have : τ ^ 2 ≤ 4 * (1 + |t|) ^ 2 := by nlinarith
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
    have h2 : ρ ^ (2 * n) ≤ ((|t| + c₁) / τ) ^ (2 * n) := pow_le_pow_left₀ hρ0 hρle _
    have h3 : (1 + |t|) ^ (-2 : ℝ) * ρ ^ (2 * n) ≤ 4 / τ ^ 2 * ((|t| + c₁) / τ) ^ (2 * n) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    linarith [Real.exp_pos (-Y)]
  · -- far from it: `ρ ≤ 1/2`
    have h1 : (1 + |t|) ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by norm_num)
    have hρ2 : ρ ≤ 1 / 2 := by
      rw [hρ, div_le_iff₀ (by positivity)]
      have ht2 : t ^ 2 ≤ τ ^ 2 / 4 := by
        rw [← sq_abs]; nlinarith [abs_nonneg t]
      have hc2 : c ≤ τ ^ 2 / 4 := by
        refine hcb.trans ?_
        rw [hτ]
        have hYY : 9 + (m : ℝ) ^ 2 ≤ Y ^ 2 := hY.trans (by nlinarith)
        have hπ2 : 9 ≤ π ^ 2 := by nlinarith
        have hY4 : 0 ≤ Y ^ 4 := by positivity
        have h4 : Y ^ 2 * Y ^ 2 ≤ (2 * π * Y ^ 2) ^ 2 / 4 := by
          calc Y ^ 2 * Y ^ 2 = 1 * Y ^ 4 := by ring
            _ ≤ π ^ 2 * Y ^ 4 := by gcongr; linarith
            _ = (2 * π * Y ^ 2) ^ 2 / 4 := by ring
        exact (mul_le_mul_of_nonneg_right hYY (sq_nonneg Y)).trans h4
      linarith
    have he : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
      rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have h2 : ρ ^ (2 * n) ≤ Real.exp (-Y) := by
      calc ρ ^ (2 * n) = (ρ ^ 2) ^ n := by rw [pow_mul]
        _ ≤ (Real.exp (-1)) ^ n := by
            have hq : ρ ^ 2 ≤ Real.exp (-1) := by
              have : ρ ^ 2 ≤ 1 / 4 := by nlinarith
              linarith
            exact pow_le_pow_left₀ (sq_nonneg ρ) hq n
        _ = Real.exp (-(n : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ Real.exp (-Y) := Real.exp_le_exp.2 (by linarith)
    have h3 : (1 + |t|) ^ (-2 : ℝ) * ρ ^ (2 * n) ≤ Real.exp (-Y) := by
      calc _ ≤ 1 * Real.exp (-Y) := mul_le_mul h1 h2 (pow_nonneg hρ0 _) zero_le_one
        _ = _ := one_mul _
    have : 0 ≤ 4 / τ ^ 2 * ((|t| + c₁) / τ) ^ (2 * n) := by positivity
    linarith

end RamanujanTau.KernelPhase
