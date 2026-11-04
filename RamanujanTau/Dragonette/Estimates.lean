/-
# Closed-form estimates

* `phi_bound`: for `‖s‖ = e^{−t}`, `0 < t ≤ 1/32`: `‖φ(s)‖ ≤ (−r;r²)_∞ · (1/t) · e^{−1/(2400t)}`;
* `Oz_real_le`: `(−r;r²)_∞ ≤ 2 e^{π²/(24t)}` for small `t`.
-/
import RamanujanTau.Dragonette.Bounds

set_option autoImplicit false

namespace Dragonette
open Complex Finset Filter HardyRamanujan
open scoped Real Topology

lemma exp_neg_ge_one_sub (x : ℝ) : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]

set_option maxHeartbeats 1600000 in
/-- **the uniform bound on `φ`**. -/
theorem phi_bound {s : ℂ} {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 32) (hs : ‖s‖ = Real.exp (-t)) :
    ‖MockTheta3.Radial.gA (-s)‖ ≤ ‖Oz ((Real.exp (-t) : ℝ) : ℂ)‖ * (1 / t) * Real.exp (-(1 / (2400 * t))) := by
  set r := Real.exp (-t) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hs1 : ‖s‖ < 1 := by rw [hs]; exact hr1
  have hr31 : 31 / 32 ≤ r := by have := exp_neg_ge_one_sub t; linarith
  set N : ℕ := ⌈1 / (32 * t)⌉₊ with hN
  have hx : 1 ≤ 1 / (32 * t) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hN1 : 1 / (32 * t) ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) ≤ 1 / (32 * t) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hN3 : (N : ℝ) ≤ 1 / (16 * t) := by
    have : 1 / (16 * t) = 2 * (1 / (32 * t)) := by field_simp; ring
    linarith
  have hS1 := Sx_ge_one hr0.le hr1 zero_le_one le_rfl
  have hmain := norm_gA_le hs1 N
  rw [hs, ← Sx_one_eq hr0.le hr1] at *
  -- first piece
  have hh := Sx_half hr0.le hr1
  have h1r : 1 - r ^ 2 ≤ 2 * t := by
    have : Real.exp (-t) ^ 2 = Real.exp (-(2 * t)) := by rw [← Real.exp_nat_mul]; ring_nf
    rw [hr, this]; linarith [exp_neg_ge_one_sub (2 * t)]
  have h1r0 : 0 < 1 - r ^ 2 := by nlinarith
  have hD : 31 / (64 * t) ≤ r / (1 - r ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) h1r0]; nlinarith
  have h2N : (2 : ℝ) ^ N ≤ 3 * Real.exp (1 / (40 * t)) := by
    have e : (2 : ℝ) ^ N = Real.exp (N * Real.log 2) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [e]
    have hl := Real.log_two_lt_d9
    have hl0 := Real.log_pos one_lt_two
    have : (N : ℝ) * Real.log 2 ≤ 1 / (40 * t) + 1 := by
      have h40 : 1 / (32 * t) * Real.log 2 ≤ 1 / (40 * t) := by
        rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      nlinarith
    calc Real.exp (N * Real.log 2) ≤ Real.exp (1 / (40 * t) + 1) := Real.exp_le_exp.mpr this
      _ = Real.exp 1 * Real.exp (1 / (40 * t)) := by rw [Real.exp_add]; ring
      _ ≤ 3 * Real.exp (1 / (40 * t)) := by gcongr; linarith [Real.exp_one_lt_d9]
  have hP1 : (N : ℝ) * 2 ^ N * Sx r (1 / 2) ≤ Sx r 1 * (3 / (16 * t)) * Real.exp (-(1 / (2400 * t))) := by
    have hE : Real.exp (-(r / (1 - r ^ 2)) / 4) ≤ Real.exp (-(31 / (256 * t))) := by
      apply Real.exp_le_exp.mpr
      have : 31 / (256 * t) = 31 / (64 * t) / 4 := by field_simp; ring
      rw [this]; linarith
    have hSh : Sx r (1 / 2) ≤ Sx r 1 * Real.exp (-(31 / (256 * t))) :=
      hh.trans (mul_le_mul_of_nonneg_left hE (by linarith))
    have hexp : Real.exp (1 / (40 * t)) * Real.exp (-(31 / (256 * t))) ≤ Real.exp (-(1 / (2400 * t))) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have e : 1 / (40 * t) + -(31 / (256 * t)) = (1 / 40 - 31 / 256) * (1 / t) := by ring
      have e2 : -(1 / (2400 * t)) = (-(1 / 2400)) * (1 / t) := by ring
      rw [e, e2]
      have : 0 < 1 / t := by positivity
      nlinarith
    have hS0 : 0 ≤ Sx r (1 / 2) := by linarith [Sx_ge_one hr0.le hr1 (x := 1 / 2) (by norm_num) (by norm_num)]
    calc (N : ℝ) * 2 ^ N * Sx r (1 / 2) ≤ (1 / (16 * t)) * (3 * Real.exp (1 / (40 * t))) *
          (Sx r 1 * Real.exp (-(31 / (256 * t)))) := by gcongr
      _ = Sx r 1 * (3 / (16 * t)) * (Real.exp (1 / (40 * t)) * Real.exp (-(31 / (256 * t)))) := by
          ring
      _ ≤ _ := by gcongr
  -- second piece
  set M : ℕ := N / 2 with hM
  have hM1 : (N : ℝ) ≤ 2 * M + 1 := by
    have := Nat.div_add_mod N 2
    have h2 := Nat.mod_lt N (by norm_num : 0 < 2)
    have : N ≤ 2 * M + 1 := by omega
    exact_mod_cast this
  have hM2 : 2 * (M : ℝ) ≤ N := by
    have := Nat.div_mul_le_self N 2
    have : 2 * M ≤ N := by omega
    exact_mod_cast this
  have hr4 : 1 / 2 ≤ r ^ (4 * M) := by
    have : r ^ (4 * M) = Real.exp (-(4 * M * t)) := by
      rw [hr, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [this]
    have h : 4 * (M : ℝ) * t ≤ 1 / 8 + 1 / 8 := by
      have : 4 * (M : ℝ) * t ≤ 2 * t * (1 / (32 * t) + 1) := by nlinarith
      have e : 2 * t * (1 / (32 * t) + 1) = 1 / 16 + 2 * t := by field_simp; ring
      linarith
    have := exp_neg_ge_one_sub (4 * M * t)
    linarith
  have hg : Real.exp (-(7 / 16 * (M : ℝ) * r ^ (4 * M)) / 8) ≤ 2 * Real.exp (-(1 / (2400 * t))) := by
    have hMlow : 1 / (64 * t) - 1 / 2 ≤ (M : ℝ) := by
      have : 1 / (64 * t) = (1 / (32 * t)) / 2 := by field_simp; ring
      linarith
    have hM0 : 0 ≤ (M : ℝ) := by positivity
    have : 7 / (16384 * t) - 7 / 512 ≤ 7 / 16 * (M : ℝ) * r ^ (4 * M) / 8 := by
      have e : 7 / (16384 * t) - 7 / 512 = 7 / 128 * (1 / 2) * (1 / (64 * t) - 1 / 2) := by field_simp; ring
      rw [e]
      have h1 : 7 / 128 * (1 / 2) * (1 / (64 * t) - 1 / 2) ≤ 7 / 128 * (1 / 2) * M := by gcongr
      have h2 : (M : ℝ) / 2 ≤ M * r ^ (4 * M) := by
        have := mul_le_mul_of_nonneg_left hr4 hM0; linarith
      have e3 : 7 / 16 * (M : ℝ) * r ^ (4 * M) / 8 = 7 / 128 * (M * r ^ (4 * M)) := by ring
      rw [e3]; linarith
    calc Real.exp (-(7 / 16 * (M : ℝ) * r ^ (4 * M)) / 8) ≤ Real.exp (-(7 / (16384 * t) - 7 / 512)) := by
          rw [neg_div]; exact Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (7 / 512) * Real.exp (-(7 / (16384 * t))) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ 2 * Real.exp (-(1 / (2400 * t))) := by
          have h72 : Real.exp (7 / 512) ≤ 2 := by
            refine (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)).trans ?_
            norm_num
          have hexp' : Real.exp (-(7 / (16384 * t))) ≤ Real.exp (-(1 / (2400 * t))) := by
            apply Real.exp_le_exp.mpr
            rw [neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]; linarith
          exact mul_le_mul h72 hexp' (Real.exp_pos _).le (by norm_num)
  have hS0 : 0 ≤ Sx r 1 := zero_le_one.trans hS1
  have h16 : 2 ≤ 1 / (16 * t) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hE0 := Real.exp_pos (-(1 / (2400 * t)))
  calc _ ≤ (N : ℝ) * 2 ^ N * Sx r (1 / 2) + Sx r 1 * Real.exp (-(7 / 16 * (M : ℝ) * r ^ (4 * M)) / 8) := hmain
    _ ≤ Sx r 1 * (3 / (16 * t)) * Real.exp (-(1 / (2400 * t))) + Sx r 1 * (2 * Real.exp (-(1 / (2400 * t)))) := by
        gcongr
    _ = Sx r 1 * (3 / (16 * t) + 2) * Real.exp (-(1 / (2400 * t))) := by ring
    _ ≤ Sx r 1 * (1 / t) * Real.exp (-(1 / (2400 * t))) := by
        gcongr
        have : 3 / (16 * t) + 1 / (16 * t) = 1 / (4 * t) := by field_simp; ring
        have : 1 / (4 * t) ≤ 1 / t := by gcongr; linarith
        linarith

/-- the real value: `(−r;r²)_∞ ≤ 2e^{π²/(24t)}` once the cusp corrections are small. -/
theorem Oz_real_le {t : ℝ} (ht : 0 < t) (h1 : 1 ≤ π ^ 2 / t)
    (hη : (4 * C0 + 4) * Real.exp (-(π ^ 2 / t)) ≤ 1 / 15) :
    ‖Oz ((Real.exp (-t) : ℝ) : ℂ)‖ ≤ 2 * Real.exp (π ^ 2 / (24 * t)) := by
  have hz : 0 < ((t : ℂ)).re := by simpa using ht
  have hre : ((π : ℂ) ^ 2 / (t : ℂ)).re = π ^ 2 / t := by
    rw [show (π : ℂ) ^ 2 / (t : ℂ) = ((π ^ 2 / t : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  have hF := (Fr_near hz (by rw [hre]; exact h1) (by rw [hre]; linarith)).1
  rw [hre] at hF
  have hFr : ‖Fr (t : ℂ)‖ ≤ 2 := by
    have := norm_add_le (Fr (t : ℂ) - 1) 1
    simp at this; linarith
  rw [Complex.ofReal_exp, Complex.ofReal_neg, Oz_transform hz, norm_mul, norm_exp]
  have : (π ^ 2 / (24 * (t : ℂ)) - (t : ℂ) / 24).re ≤ π ^ 2 / (24 * t) := by
    rw [show (π : ℂ) ^ 2 / (24 * (t : ℂ)) - (t : ℂ) / 24 = ((π ^ 2 / (24 * t) - t / 24 : ℝ) : ℂ) by push_cast; ring,
      ofReal_re]
    linarith
  calc Real.exp (π ^ 2 / (24 * (t : ℂ)) - (t : ℂ) / 24).re * ‖Fr (t : ℂ)‖ ≤
      Real.exp (π ^ 2 / (24 * t)) * 2 := by gcongr
    _ = _ := by ring

end Dragonette
