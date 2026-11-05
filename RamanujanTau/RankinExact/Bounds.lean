/-
# Pointwise bounds for `‖G_j‖` on the bent contour, general `j = r + 1`

Same contour as `KernelPhase/Bounds.lean` (`y = Y⁸`, `τ = 2πY²`, `n = ⌈Y⌉₊`, `U = Y⁸`), now
for the kernel `J_{r+1}`. On the original line `‖G_{r+1}‖ ≤ K Y^{12+8r} (1+|t|)^{−(r+2)}`;
at the stationary height `‖G_{r+1}‖ ≪ Y^{8+6r}`. The target is `∫ ≪ Y^{9+6r}`, i.e.
`J_{r+1}(y) ≪ y^{(9+6r)/8} = y^{3(r+1)/4 + 3/8}`.
-/
import RamanujanTau.RankinExact.Shift
import RamanujanTau.KernelPhase.Bounds

set_option autoImplicit false

namespace RamanujanTau.RankinExact

open Complex Real
open RamanujanTau.RankinErrorGeneral RamanujanTau.RankinLandau RamanujanTau.KernelPhase

/-- The strip bound `‖Q_{r+1}(s)‖ ≤ K(1+|Im s|)^{1−4 Re s−(r+1)}` on `−1/2 ≤ Re s ≤ 1/2`. -/
def StripBoundJ (m r : ℕ) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 1 / 2 →
    ‖Qk m (r + 1) s‖ ≤ K * (1 + |s.im|) ^ (1 - 4 * s.re - ((r + 1 : ℕ) : ℝ))

lemma exists_stripBoundJ (m r : ℕ) (hm : 1 ≤ m) : ∃ K, StripBoundJ m r K := by
  obtain ⟨K, hK0, hK⟩ := Qk_bound_sharp m (r + 1) hm (A₀ := -1 / 2) (by norm_num)
  exact ⟨K, hK0, hK⟩

/-- The constant `D = (r+4)² + m²` of the left shifts. -/
noncomputable def Dc (m r : ℕ) : ℝ := ((r : ℝ) + 4) ^ 2 + (m : ℝ) ^ 2

lemma Dc_ge (m r : ℕ) : 16 ≤ Dc m r := by
  unfold Dc; nlinarith [Nat.cast_nonneg (α := ℝ) r, sq_nonneg (m : ℝ)]

lemma rpow_negNat {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : x ^ (-(k : ℝ)) = (x ^ k)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_natCast]

variable {m r : ℕ} {K Y : ℝ}

lemma base_boundJ (hSB : StripBoundJ m r K) (hY : 1 ≤ Y) {s : ℂ} (h1 : -1 / 2 ≤ s.re)
    (h2 : s.re ≤ 1 / 2) :
    ‖Gj m (r + 1) (Y ^ 8) s‖ ≤ Y ^ (8 * (s.re + ((r + 1 : ℕ) : ℝ))) *
      (K * (1 + |s.im|) ^ (1 - 4 * s.re - ((r + 1 : ℕ) : ℝ))) := by
  rw [norm_Gj m (r + 1) (by positivity), rpow8 (by linarith)]
  have := hSB.2 s h1 h2
  gcongr

/-- (N1) the original line. -/
lemma bound_halfJ (hSB : StripBoundJ m r K) (hY : 1 ≤ Y) (t : ℝ) :
    ‖Gj m (r + 1) (Y ^ 8) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      K * Y ^ (12 + 8 * r) * (1 + |t|) ^ (-((r + 2 : ℕ) : ℝ)) := by
  have hre : (((1 / 2 : ℝ) : ℂ) + t * I).re = 1 / 2 := by simp
  have him : (((1 / 2 : ℝ) : ℂ) + t * I).im = t := by simp
  have h := base_boundJ hSB hY (s := ((1 / 2 : ℝ) : ℂ) + t * I) (by rw [hre]; norm_num)
    (by rw [hre])
  rw [hre, him, rpow_nat' (12 + 8 * r) (by push_cast; ring),
    show 1 - 4 * (1 / 2 : ℝ) - ((r + 1 : ℕ) : ℝ) = -((r + 2 : ℕ) : ℝ) by push_cast; ring] at h
  calc _ ≤ _ := h
    _ = _ := by ring

/-- (N2) the strip at height `±τ`. -/
lemma bound_tau_baseJ (hSB : StripBoundJ m r K) (hY : 1 ≤ Y) {s : ℂ} (h1 : -1 / 2 ≤ s.re)
    (h2 : s.re ≤ 1 / 2) (hs : |s.im| = 2 * π * Y ^ 2) :
    ‖Gj m (r + 1) (Y ^ 8) s‖ ≤ 64 * K * Y ^ (8 + 6 * r) := by
  have h := base_boundJ hSB hY h1 h2
  rw [hs] at h
  set σ := s.re with hσ
  have hY0 : 0 < Y := by linarith
  have hY2 : 1 ≤ Y ^ 2 := by nlinarith
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  have hτ0 : 0 < 1 + τ := by positivity
  have e1 : Y ^ (8 * (σ + ((r + 1 : ℕ) : ℝ))) = Y ^ (8 + 8 * r) * (Y ^ 2) ^ (4 * σ) := by
    rw [← Real.rpow_natCast_mul hY0.le, show 8 * (σ + ((r + 1 : ℕ) : ℝ)) =
      ((8 + 8 * r : ℕ) : ℝ) + ((2 : ℕ) : ℝ) * (4 * σ) by push_cast; ring, Real.rpow_add hY0,
      Real.rpow_natCast]
  have e2 : (1 + τ) ^ (1 - 4 * σ - ((r + 1 : ℕ) : ℝ)) = ((1 + τ) ^ (4 * σ))⁻¹ * ((1 + τ) ^ r)⁻¹ := by
    rw [show 1 - 4 * σ - ((r + 1 : ℕ) : ℝ) = -(4 * σ) + -((r : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hτ0, Real.rpow_neg hτ0.le, rpow_negNat hτ0.le]
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
  have hτY : Y ^ 2 ≤ 1 + τ := by rw [hτ]; nlinarith
  have hr : ((1 + τ) ^ r)⁻¹ ≤ ((Y ^ 2) ^ r)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hτY r)
  have e4 : Y ^ (8 + 8 * r) * ((Y ^ 2) ^ r)⁻¹ = Y ^ (8 + 6 * r) := by
    rw [← pow_mul, show 8 + 8 * r = (8 + 6 * r) + 2 * r by ring, pow_add]
    field_simp
  have hK := hSB.1
  calc ‖Gj m (r + 1) (Y ^ 8) s‖ ≤ Y ^ (8 * (σ + ((r + 1 : ℕ) : ℝ))) *
        (K * (1 + τ) ^ (1 - 4 * σ - ((r + 1 : ℕ) : ℝ))) := h
    _ = K * Y ^ (8 + 8 * r) * q ^ (4 * σ) * ((1 + τ) ^ r)⁻¹ := by rw [e1, e2, ← e3]; ring
    _ ≤ K * Y ^ (8 + 8 * r) * 64 * ((Y ^ 2) ^ r)⁻¹ := by gcongr
    _ = 64 * K * (Y ^ (8 + 8 * r) * ((Y ^ 2) ^ r)⁻¹) := by ring
    _ = 64 * K * Y ^ (8 + 6 * r) := by rw [e4]

/-- (N3) the strip at height `±U = ±Y⁸` (crude). -/
lemma bound_U_baseJ (hSB : StripBoundJ m r K) (hY : 1 ≤ Y) {s : ℂ} (h1 : -1 / 2 ≤ s.re)
    (h2 : s.re ≤ 1 / 2) (hs : |s.im| = Y ^ 8) :
    ‖Gj m (r + 1) (Y ^ 8) s‖ ≤ 4 * K * Y ^ 28 := by
  have h := base_boundJ hSB hY h1 h2
  rw [hs] at h
  have hY0 : 0 < Y := by linarith
  have hY8 : 1 ≤ Y ^ 8 := one_le_pow₀ hY
  have hU0 : 0 < 1 + Y ^ 8 := by positivity
  have a1 : Y ^ (8 * (s.re + ((r + 1 : ℕ) : ℝ))) ≤ Y ^ (12 + 8 * r) := by
    rw [← rpow_nat' (Y := Y) (12 + 8 * r) (z := ((12 + 8 * r : ℕ) : ℝ)) rfl]
    exact Real.rpow_le_rpow_of_exponent_le hY (by push_cast; linarith)
  have e2 : (1 + Y ^ 8) ^ (1 - 4 * s.re - ((r + 1 : ℕ) : ℝ)) =
      (1 + Y ^ 8) ^ (-4 * s.re) * ((1 + Y ^ 8) ^ r)⁻¹ := by
    rw [show 1 - 4 * s.re - ((r + 1 : ℕ) : ℝ) = -4 * s.re + -((r : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hU0, rpow_negNat hU0.le]
  have a2 : (1 + Y ^ 8) ^ (-4 * s.re) ≤ 4 * Y ^ 16 := by
    refine (Real.rpow_le_rpow_of_exponent_le (by linarith) (show -4 * s.re ≤ ((2 : ℕ) : ℝ) by
      push_cast; linarith)).trans ?_
    rw [Real.rpow_natCast]; nlinarith
  have a3 : ((1 + Y ^ 8) ^ r)⁻¹ ≤ ((Y ^ 8) ^ r)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) r)
  have e4 : Y ^ (12 + 8 * r) * (4 * Y ^ 16) * ((Y ^ 8) ^ r)⁻¹ = 4 * Y ^ 28 := by
    rw [← pow_mul, pow_add]; field_simp
  have hK := hSB.1
  rw [e2] at h
  calc ‖Gj m (r + 1) (Y ^ 8) s‖ ≤ Y ^ (8 * (s.re + ((r + 1 : ℕ) : ℝ))) *
        (K * ((1 + Y ^ 8) ^ (-4 * s.re) * ((1 + Y ^ 8) ^ r)⁻¹)) := h
    _ ≤ Y ^ (12 + 8 * r) * (K * ((4 * Y ^ 16) * ((Y ^ 8) ^ r)⁻¹)) := by gcongr
    _ = K * (Y ^ (12 + 8 * r) * (4 * Y ^ 16) * ((Y ^ 8) ^ r)⁻¹) := by ring
    _ = 4 * K * Y ^ 28 := by rw [e4]; ring

/-- (C1) the right half of the horizontal segment at `±τ`. -/
lemma bound_tau_rightJ (hSB : StripBoundJ m r K) (hY : 1 ≤ Y) {σ t : ℝ} (hσ : 1 / 2 ≤ σ)
    (ht : |t| = 2 * π * Y ^ 2) :
    ‖Gj m (r + 1) (Y ^ 8) ((σ : ℂ) + t * I)‖ ≤ 64 * K * Y ^ (8 + 6 * r) := by
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
  have hup := norm_Gj_add_nat_le m (r + 1) (y := Y ^ 8) (by positivity) (s := s')
    (by rw [him]; exact ht0) k
  rw [hsk, him, t4_eq ht, div_self (by positivity), one_pow, mul_one] at hup
  exact hup.trans (bound_tau_baseJ hSB hY (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him]; exact ht))

/-- The left-shift factor at height `τ` is bounded by `e^D`. -/
lemma factor_leJ (hY : 1 ≤ Y) {n : ℕ} (hn : (n : ℝ) ≤ Y + 1) {k : ℕ} (hk : k ≤ n) :
    ((((n : ℝ) + r + 2) ^ 2 + (m : ℝ) ^ 2 + (2 * π * Y ^ 2) ^ 2) ^ 2 / (16 * π ^ 4 * Y ^ 8)) ^ k ≤
      Real.exp (Dc m r) := by
  have hpi := Real.pi_gt_three
  have hY0 : 0 < Y := by linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  set c : ℝ := ((n : ℝ) + r + 2) ^ 2 + (m : ℝ) ^ 2 with hc
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
  have hcb : c ≤ Dc m r * Y ^ 2 := by
    have e1 : (n : ℝ) + r + 2 ≤ ((r : ℝ) + 4) * Y := by
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ (r : ℝ) + 3) (by linarith : (0 : ℝ) ≤ Y - 1)
      linarith
    have e2 : ((n : ℝ) + r + 2) ^ 2 ≤ ((r : ℝ) + 4) ^ 2 * Y ^ 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) + r + 2 := by positivity
      nlinarith
    have e3 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * Y ^ 2 := by
      have : (1 : ℝ) ≤ Y ^ 2 := by nlinarith
      nlinarith [sq_nonneg (m : ℝ)]
    rw [hc, Dc]; nlinarith
  rw [mul_div_assoc', div_le_iff₀ hτ2p, hτ2]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hc0 : 0 ≤ c := by positivity
  have hD0 : 0 ≤ Dc m r := by have := Dc_ge m r; linarith
  have h2 : ((2 * k : ℕ) : ℝ) * c ≤ 4 * Y * (Dc m r * Y ^ 2) := by
    push_cast
    have : 2 * (k : ℝ) ≤ 4 * Y := by linarith
    calc 2 * (k : ℝ) * c ≤ 4 * Y * c := by gcongr
      _ ≤ _ := by gcongr
  have h3 : 4 * Y * (Dc m r * Y ^ 2) ≤ Dc m r * (2 * π * Y ^ 2) ^ 2 := by
    have hY3 : Y ^ 3 ≤ Y ^ 4 := pow_le_pow_right₀ hY (by norm_num)
    have hπ2 : 9 ≤ π ^ 2 := by nlinarith
    have hY4 : 0 ≤ Y ^ 4 := by positivity
    have : 4 * Y * Y ^ 2 ≤ (2 * π * Y ^ 2) ^ 2 := by
      calc 4 * Y * Y ^ 2 = 4 * Y ^ 3 := by ring
        _ ≤ 4 * Y ^ 4 := by linarith
        _ ≤ 4 * π ^ 2 * Y ^ 4 := by nlinarith
        _ = (2 * π * Y ^ 2) ^ 2 := by ring
    calc 4 * Y * (Dc m r * Y ^ 2) = Dc m r * (4 * Y * Y ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hD0
  linarith

lemma cast_r2 (K : ℕ) : ((K : ℝ) + ((r + 1 : ℕ) : ℝ) + 1) = (K : ℝ) + r + 2 := by
  push_cast; ring

/-- (C2) the left half of the horizontal segment at `±τ`. -/
lemma bound_tau_leftJ (hm : 1 ≤ m) (hSB : StripBoundJ m r K) (hY : 1 ≤ Y) {σ t : ℝ}
    (hσ1 : 1 / 2 - (⌈Y⌉₊ : ℝ) ≤ σ) (hσ2 : σ ≤ 1 / 2) (ht : |t| = 2 * π * Y ^ 2) :
    ‖Gj m (r + 1) (Y ^ 8) ((σ : ℂ) + t * I)‖ ≤ 64 * K * Y ^ (8 + 6 * r) * Real.exp (Dc m r) := by
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
  have hdown := norm_Gj_sub_nat_le m (r + 1) hm (y := Y ^ 8) (by positivity) (s := s')
    (by rw [hre]; linarith) (by rw [hre]; linarith) n k hkn
  have ht2 : t ^ 2 = (2 * π * Y ^ 2) ^ 2 := by rw [← ht, sq_abs]
  rw [hsk, him, ht2, cast_r2] at hdown
  have hb := bound_tau_baseJ hSB hY (s := s') (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him]; exact ht)
  have hf := factor_leJ (m := m) (r := r) hY hnY hkn
  refine hdown.trans ?_
  have := hSB.1
  gcongr

/-- (C3) the top segments at `±U`. -/
lemma bound_UJ (hSB : StripBoundJ m r K) (hY : 2 ≤ Y) {σ t : ℝ} (hσ : 1 / 2 < σ)
    (ht : |t| = Y ^ 8) : ‖Gj m (r + 1) (Y ^ 8) ((σ : ℂ) + t * I)‖ ≤ 64 * π ^ 4 * K * Y ^ 4 := by
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
  have hup := norm_Gj_add_nat_le m (r + 1) (y := Y ^ 8) (by positivity) (s := s')
    (by rw [him]; exact ht0) k
  have ht4 : t ^ 4 = Y ^ 32 := by
    have : t ^ 2 = (Y ^ 8) ^ 2 := by rw [← ht, sq_abs]
    calc t ^ 4 = (t ^ 2) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  rw [hsk, him, ht4] at hup
  have hb := bound_U_baseJ hSB hY1 (s := s') (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him]; exact ht)
  set q : ℝ := 16 * π ^ 4 * Y ^ 8 / Y ^ 32 with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one (by positivity)]
    have hpi := Real.pi_lt_d2
    have h24 : (2 : ℝ) ^ 24 ≤ Y ^ 24 := pow_le_pow_left₀ (by norm_num) hY 24
    have : 16 * π ^ 4 ≤ Y ^ 24 := by
      have : π ^ 4 ≤ 3.15 ^ 4 := pow_le_pow_left₀ Real.pi_pos.le hpi.le 4
      nlinarith
    calc 16 * π ^ 4 * Y ^ 8 ≤ Y ^ 24 * Y ^ 8 := by gcongr
      _ = Y ^ 32 := by ring
  have hqk : q ^ k ≤ q := pow_le_of_le_one hq0 hq1 hk0
  calc ‖Gj m (r + 1) (Y ^ 8) ((σ : ℂ) + t * I)‖ ≤ ‖Gj m (r + 1) (Y ^ 8) s'‖ * q ^ k := hup
    _ ≤ (4 * K * Y ^ 28) * q := by
        have := hSB.1
        gcongr
    _ = 64 * π ^ 4 * K * Y ^ 4 := by
        rw [hq]; field_simp; ring

/-- (C4) the right vertical line `Re s = 1/2 + n`. -/
lemma bound_right_lineJ (hSB : StripBoundJ m r K) (hY : 1 ≤ Y) {t : ℝ} (ht : t ≠ 0) (n : ℕ) :
    ‖Gj m (r + 1) (Y ^ 8) (((1 / 2 + n : ℝ) : ℂ) + t * I)‖ ≤
      K * Y ^ (12 + 8 * r) * (1 + |t|) ^ (-((r + 2 : ℕ) : ℝ)) *
        (16 * π ^ 4 * Y ^ 8 / t ^ 4) ^ n := by
  have him : (((1 / 2 : ℝ) : ℂ) + t * I).im = t := by simp
  have hup := norm_Gj_add_nat_le m (r + 1) (y := Y ^ 8) (by positivity)
    (s := ((1 / 2 : ℝ) : ℂ) + t * I) (by rw [him]; exact ht) n
  rw [show ((1 / 2 : ℝ) : ℂ) + t * I + n = ((1 / 2 + n : ℝ) : ℂ) + t * I by push_cast; ring,
    him] at hup
  refine hup.trans ?_
  gcongr
  exact bound_halfJ hSB hY t

/-- (C5) the left vertical line `Re s = 1/2 − n`. -/
lemma bound_left_lineJ (hm : 1 ≤ m) (hSB : StripBoundJ m r K) (hY : 1 ≤ Y) (t : ℝ) (n : ℕ) :
    ‖Gj m (r + 1) (Y ^ 8) (((1 / 2 - n : ℝ) : ℂ) + t * I)‖ ≤
      K * Y ^ (12 + 8 * r) * (1 + |t|) ^ (-((r + 2 : ℕ) : ℝ)) *
        ((((n : ℝ) + r + 2) ^ 2 + (m : ℝ) ^ 2 + t ^ 2) ^ 2 / (16 * π ^ 4 * Y ^ 8)) ^ n := by
  have hre : (((1 / 2 : ℝ) : ℂ) + t * I).re = 1 / 2 := by simp
  have him : (((1 / 2 : ℝ) : ℂ) + t * I).im = t := by simp
  have hdown := norm_Gj_sub_nat_le m (r + 1) hm (y := Y ^ 8) (by positivity)
    (s := ((1 / 2 : ℝ) : ℂ) + t * I) (by rw [hre]; norm_num) (by rw [hre]) n n le_rfl
  rw [show ((1 / 2 : ℝ) : ℂ) + t * I - n = ((1 / 2 - n : ℝ) : ℂ) + t * I by push_cast; ring,
    him, cast_r2] at hdown
  refine hdown.trans ?_
  gcongr
  exact bound_halfJ hSB hY t

/-- The pointwise majorant on the left line: for `|t| ≤ τ` and `Y ≥ D`,
`(1+|t|)^{−(r+2)} ρ^{2n} ≤ (2/τ)^{r+2}((|t|+c₁)/τ)^{2n} + e^{−Y}`, `c₁ = D/(2π)`. -/
lemma left_pointwiseJ (hY1 : 1 ≤ Y) (hY : Dc m r ≤ Y) {t : ℝ}
    (ht : |t| ≤ 2 * π * Y ^ 2) :
    (1 + |t|) ^ (-((r + 2 : ℕ) : ℝ)) *
        (((((⌈Y⌉₊ : ℕ) : ℝ) + r + 2) ^ 2 + (m : ℝ) ^ 2 + t ^ 2) ^ 2 /
          (16 * π ^ 4 * Y ^ 8)) ^ ⌈Y⌉₊ ≤
      (2 / (2 * π * Y ^ 2)) ^ (r + 2) *
          ((|t| + Dc m r / (2 * π)) / (2 * π * Y ^ 2)) ^ (2 * ⌈Y⌉₊) +
        Real.exp (-Y) := by
  set n : ℕ := ⌈Y⌉₊ with hn
  have hnY : (n : ℝ) ≤ Y + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hnY' : Y ≤ n := Nat.le_ceil _
  have hpi := Real.pi_gt_three
  have hY0 : 0 < Y := by linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  have hτ0 : 0 < τ := by positivity
  set c : ℝ := ((n : ℝ) + r + 2) ^ 2 + (m : ℝ) ^ 2 with hc
  have hcb : c ≤ Dc m r * Y ^ 2 := by
    have e1 : (n : ℝ) + r + 2 ≤ ((r : ℝ) + 4) * Y := by
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ (r : ℝ) + 3) (by linarith : (0 : ℝ) ≤ Y - 1)
      linarith
    have e2 : ((n : ℝ) + r + 2) ^ 2 ≤ ((r : ℝ) + 4) ^ 2 * Y ^ 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) + r + 2 := by positivity
      nlinarith
    have e3 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * Y ^ 2 := by
      have : (1 : ℝ) ≤ Y ^ 2 := by nlinarith
      nlinarith [sq_nonneg (m : ℝ)]
    rw [hc, Dc]; nlinarith
  set ρ : ℝ := (c + t ^ 2) / τ ^ 2 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have e : ((c + t ^ 2) ^ 2 / (16 * π ^ 4 * Y ^ 8)) ^ n = ρ ^ (2 * n) := by
    rw [hρ, pow_mul]; congr 1; rw [div_pow, hτ]; ring
  rw [e]
  have hA : 0 ≤ (1 + |t|) ^ (-((r + 2 : ℕ) : ℝ)) := by positivity
  set c₁ : ℝ := Dc m r / (2 * π) with hc₁
  have hρle : ρ ≤ (|t| + c₁) / τ := by
    rw [hρ, div_le_div_iff₀ (by positivity) hτ0]
    have h1 : t ^ 2 ≤ |t| * τ := by
      rw [← sq_abs, sq]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg t)
    have hc1τ : c₁ * τ = Dc m r * Y ^ 2 := by
      rw [hc₁, hτ]; field_simp
    have h2 : c ≤ c₁ * τ := by rw [hc1τ]; exact hcb
    calc (c + t ^ 2) * τ ≤ (c₁ * τ + |t| * τ) * τ := by gcongr
      _ = (|t| + c₁) * τ ^ 2 := by ring
  have h1pos : 0 < 1 + |t| := by positivity
  rcases le_or_gt (τ / 2) |t| with hbig | hsmall
  · -- near the stationary height
    have h1 : (1 + |t|) ^ (-((r + 2 : ℕ) : ℝ)) ≤ (2 / τ) ^ (r + 2) := by
      rw [rpow_negNat h1pos.le, show 2 / τ = (τ / 2)⁻¹ by rw [inv_div], inv_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) _)
    have h2 : ρ ^ (2 * n) ≤ ((|t| + c₁) / τ) ^ (2 * n) := pow_le_pow_left₀ hρ0 hρle _
    have h3 : (1 + |t|) ^ (-((r + 2 : ℕ) : ℝ)) * ρ ^ (2 * n) ≤
        (2 / τ) ^ (r + 2) * ((|t| + c₁) / τ) ^ (2 * n) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    linarith [Real.exp_pos (-Y)]
  · -- far from it: `ρ ≤ 1/2`
    have h1 : (1 + |t|) ^ (-((r + 2 : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t])
        (by have := Nat.cast_nonneg (α := ℝ) (r + 2); linarith)
    have hρ2 : ρ ≤ 1 / 2 := by
      rw [hρ, div_le_iff₀ (by positivity)]
      have ht2 : t ^ 2 ≤ τ ^ 2 / 4 := by
        rw [← sq_abs]; nlinarith [abs_nonneg t]
      have hc2 : c ≤ τ ^ 2 / 4 := by
        refine hcb.trans ?_
        rw [hτ]
        have hYY : Dc m r ≤ Y ^ 2 := hY.trans (by nlinarith)
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
              have : ρ ^ 2 ≤ 1 / 4 := by
                rw [sq]
                calc ρ * ρ ≤ (1 / 2) * (1 / 2) := mul_le_mul hρ2 hρ2 hρ0 (by norm_num)
                  _ = 1 / 4 := by norm_num
              linarith
            exact pow_le_pow_left₀ (sq_nonneg ρ) hq n
        _ = Real.exp (-(n : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ Real.exp (-Y) := Real.exp_le_exp.2 (by linarith)
    have h3 : (1 + |t|) ^ (-((r + 2 : ℕ) : ℝ)) * ρ ^ (2 * n) ≤ Real.exp (-Y) := by
      calc _ ≤ 1 * Real.exp (-Y) := mul_le_mul h1 h2 (pow_nonneg hρ0 _) zero_le_one
        _ = _ := one_mul _
    have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; have := Dc_ge m r; positivity
    have : 0 ≤ (2 / τ) ^ (r + 2) * ((|t| + c₁) / τ) ^ (2 * n) :=
      mul_nonneg (pow_nonneg (by positivity) _)
        (pow_nonneg (div_nonneg (by positivity) hτ0.le) _)
    linarith

end RamanujanTau.RankinExact
