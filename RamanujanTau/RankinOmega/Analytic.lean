/-
# Analytic inputs on the reflected line `Re w = 1 − σ ∈ [9/16, 5/8]`

For Rankin–Selberg data `d : RSDataM m a κ` (weight `m + 1`, `m ≥ 1`), with `Lam d` the completed
function (`Lam(1−s) = Lam(s)`), put

    Z(w) = Lam(w) γₘ(w)⁻¹  ( = ζ(2w) ∑ aₙ n^{−w}  for Re w > 1 ).

* `gamma_ratio_lower`: `‖γₘ(σ−iy)⁻¹‖ ≥ c_g y^{2−4σ} ‖γₘ(1−σ+iy)⁻¹‖`, uniformly for `3/8 ≤ σ ≤ 1/2`, `y ≥ 1`;
* `tail_gen`: the leading coefficient dominates a Dirichlet series on far-right lines;
* `Zf_horiz`: `‖Z(x+iy)‖ ≤ K y^{15/16}` for `9/16 ≤ x ≤ c`, `y ≥ 1` (convexity, `Stirling.Efun_bound_eps`);
* `Zf_first_moment`: `∫_Y^{2Y} ‖Z(σ'+iy)‖ dy ≥ c₃ Y`, uniformly for `9/16 ≤ σ' ≤ 5/8`.
-/
import RamanujanTau.Stirling.ConvexEps
import RamanujanTau.RankinLandau.GammaUnif
import RamanujanTau.KernelPhase.Pieces

set_option autoImplicit false

namespace RamanujanTau.RankinOmega

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open scoped Real Interval

/-! ### The gamma ratio -/

lemma norm_invGamM (m : ℕ) (s : ℂ) :
    ‖invGamM m s‖ = Real.pi ^ s.re * (4 * Real.pi) ^ (s.re + m) / 2 /
      (‖Complex.Gamma s‖ * ‖Complex.Gamma (s + m)‖) := by
  unfold invGamM
  rw [norm_mul, norm_mul, norm_div, norm_mul, norm_inv, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi)]
  simp only [Complex.add_re, Complex.natCast_re, Complex.norm_ofNat]
  field_simp

/-- **Uniform `Γ`-ratio lower bound** across `Re s = 1/2`. -/
theorem gamma_ratio_lower (m : ℕ) (hm : 1 ≤ m) :
    ∃ cg : ℝ, 0 < cg ∧ ∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 1 / 2 → 1 ≤ y →
      cg * y ^ (2 - 4 * σ) * ‖invGamM m (((1 - σ : ℝ) : ℂ) + y * I)‖ ≤
        ‖invGamM m ((σ : ℂ) - y * I)‖ := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨C, hC0, hC⟩ := RamanujanTau.RankinLandau.norm_Gamma_ratio_unif' (R := m + 1) (by linarith)
  refine ⟨1 / (8 * Real.pi ^ 2 * C ^ 2), by positivity, fun σ y h1 h2 hy => ?_⟩
  set s : ℂ := (σ : ℂ) - y * I with hs
  set w : ℂ := ((1 - σ : ℝ) : ℂ) + y * I with hw
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = -y := by simp [hs]
  have hwre : w.re = 1 - σ := by simp [hw]
  have hwim : w.im = y := by simp [hw]
  have hy0 : 0 < y := by linarith
  -- (i) `Γ(s+1)` vs `Γ(w+1)`
  have g1 := hC (s + 1) (w + 1) (by simp [hsre]; linarith) (by simp [hsre]; linarith)
    (by simp [hwre]; linarith) (by simp [hwre]; linarith) (by simp [hsim, hwim])
  have g2 := hC (s + m) (w + m) (by simp [hsre]; linarith) (by simp [hsre]; linarith)
    (by simp [hwre]; linarith) (by simp [hwre]; linarith) (by simp [hsim, hwim])
  have e1 : (s + 1).re - (w + 1).re = 2 * σ - 1 := by simp [hsre, hwre]; ring
  have e2 : (s + m).re - (w + m).re = 2 * σ - 1 := by simp [hsre, hwre]; ring
  have e3 : |(w + 1).im| = y := by simp [hwim, abs_of_pos hy0]
  have e4 : |(w + (m : ℂ)).im| = y := by simp [hwim, abs_of_pos hy0]
  rw [e1, e3] at g1
  rw [e2, e4] at g2
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hw0 : w ≠ 0 := by intro h; have := congrArg Complex.im h; rw [hwim] at this; simp at this; linarith
  rw [Complex.Gamma_add_one s hs0, Complex.Gamma_add_one w hw0, norm_mul, norm_mul] at g1
  have hns : y ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s; rw [hsim, abs_neg, abs_of_pos hy0] at this; exact this
  have hnw : ‖w‖ ≤ 2 * y := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [hwre, hwim, abs_of_nonneg (by linarith), abs_of_pos hy0]; linarith
  set P : ℝ := (1 + y) ^ (2 * σ - 1) with hP
  have hP0 : 0 < P := by positivity
  have hPy : P ≤ y ^ (2 * σ - 1) := Real.rpow_le_rpow_of_nonpos hy0 (by linarith) (by linarith)
  have hGw : 0 < ‖Complex.Gamma w‖ := norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by linarith))
  have hGwm : 0 < ‖Complex.Gamma (w + m)‖ :=
    norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by simp [hwre]; linarith))
  have hGs : 0 < ‖Complex.Gamma s‖ := norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by linarith))
  have hGsm : 0 < ‖Complex.Gamma (s + m)‖ :=
    norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by simp [hsre]; linarith))
  have hsn : 0 < ‖s‖ := by linarith
  -- `‖Γ(s)‖ ≤ 2 C P ‖Γ(w)‖`
  have hG1 : ‖Complex.Gamma s‖ ≤ 2 * C * P * ‖Complex.Gamma w‖ := by
    have : ‖s‖ * ‖Complex.Gamma s‖ ≤ ‖s‖ * (2 * C * P * ‖Complex.Gamma w‖) := by
      calc ‖s‖ * ‖Complex.Gamma s‖ ≤ C * P * (‖w‖ * ‖Complex.Gamma w‖) := g1
        _ ≤ C * P * (2 * y * ‖Complex.Gamma w‖) := by gcongr
        _ ≤ C * P * (2 * ‖s‖ * ‖Complex.Gamma w‖) := by gcongr
        _ = ‖s‖ * (2 * C * P * ‖Complex.Gamma w‖) := by ring
    exact le_of_mul_le_mul_left this hsn
  have hGG : ‖Complex.Gamma s‖ * ‖Complex.Gamma (s + m)‖ ≤
      2 * C ^ 2 * y ^ (4 * σ - 2) * (‖Complex.Gamma w‖ * ‖Complex.Gamma (w + m)‖) := by
    have hPP : P * P ≤ y ^ (4 * σ - 2) := by
      have : y ^ (4 * σ - 2) = y ^ (2 * σ - 1) * y ^ (2 * σ - 1) := by
        rw [← Real.rpow_add hy0]; ring_nf
      rw [this]; exact mul_le_mul hPy hPy hP0.le (by positivity)
    calc ‖Complex.Gamma s‖ * ‖Complex.Gamma (s + m)‖
        ≤ (2 * C * P * ‖Complex.Gamma w‖) * (C * P * ‖Complex.Gamma (w + m)‖) := by
          gcongr
      _ = 2 * C ^ 2 * (P * P) * (‖Complex.Gamma w‖ * ‖Complex.Gamma (w + m)‖) := by ring
      _ ≤ _ := by gcongr
  -- the prefactors
  rw [norm_invGamM, norm_invGamM, hsre, hwre]
  have hπ : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hπ4 : (1 : ℝ) ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
  have hpre : Real.pi ^ (1 - σ) * (4 * Real.pi) ^ (1 - σ + m) ≤
      4 * Real.pi ^ 2 * (Real.pi ^ σ * (4 * Real.pi) ^ (σ + m)) := by
    have a1 : Real.pi ^ (1 - σ) = Real.pi ^ σ * Real.pi ^ (1 - 2 * σ) := by
      rw [← Real.rpow_add Real.pi_pos]; ring_nf
    have a2 : (4 * Real.pi) ^ (1 - σ + m) = (4 * Real.pi) ^ (σ + m) * (4 * Real.pi) ^ (1 - 2 * σ) := by
      rw [← Real.rpow_add (by positivity)]; ring_nf
    have b1 : Real.pi ^ (1 - 2 * σ) ≤ Real.pi := by
      calc Real.pi ^ (1 - 2 * σ) ≤ Real.pi ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hπ (by linarith)
        _ = Real.pi := Real.rpow_one _
    have b2 : (4 * Real.pi) ^ (1 - 2 * σ) ≤ 4 * Real.pi := by
      calc (4 * Real.pi) ^ (1 - 2 * σ) ≤ (4 * Real.pi) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hπ4 (by linarith)
        _ = 4 * Real.pi := Real.rpow_one _
    rw [a1, a2]
    have : 0 ≤ Real.pi ^ σ * (4 * Real.pi) ^ (σ + m) := by positivity
    calc Real.pi ^ σ * Real.pi ^ (1 - 2 * σ) * ((4 * Real.pi) ^ (σ + m) * (4 * Real.pi) ^ (1 - 2 * σ))
        = (Real.pi ^ σ * (4 * Real.pi) ^ (σ + m)) * (Real.pi ^ (1 - 2 * σ) * (4 * Real.pi) ^ (1 - 2 * σ)) := by ring
      _ ≤ (Real.pi ^ σ * (4 * Real.pi) ^ (σ + m)) * (Real.pi * (4 * Real.pi)) := by gcongr
      _ = _ := by ring
  set Ps : ℝ := Real.pi ^ σ * (4 * Real.pi) ^ (σ + m) with hPs
  set Pw : ℝ := Real.pi ^ (1 - σ) * (4 * Real.pi) ^ (1 - σ + m) with hPw
  set Gs := ‖Complex.Gamma s‖ * ‖Complex.Gamma (s + m)‖ with hGsdef
  set Gw := ‖Complex.Gamma w‖ * ‖Complex.Gamma (w + m)‖ with hGwdef
  have hGs0 : 0 < Gs := by positivity
  have hGw0 : 0 < Gw := by positivity
  have hPs0 : 0 < Ps := by positivity
  have hPw0 : 0 ≤ Pw := by positivity
  have hyy : y ^ (2 - 4 * σ) * y ^ (4 * σ - 2) = 1 := by
    rw [← Real.rpow_add hy0]; simp
  have hy1 : 0 < y ^ (2 - 4 * σ) := by positivity
  rw [div_div, div_div]
  rw [show 1 / (8 * Real.pi ^ 2 * C ^ 2) * y ^ (2 - 4 * σ) * (Pw / (2 * Gw)) =
    (y ^ (2 - 4 * σ) * Pw) / (16 * Real.pi ^ 2 * C ^ 2 * Gw) by field_simp; ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- `y^{2−4σ} Pw · 2 Gs ≤ Ps · 16 π² C² Gw`
  have key1 : y ^ (2 - 4 * σ) * Gs ≤ 2 * C ^ 2 * Gw := by
    calc y ^ (2 - 4 * σ) * Gs ≤ y ^ (2 - 4 * σ) * (2 * C ^ 2 * y ^ (4 * σ - 2) * Gw) := by gcongr
      _ = 2 * C ^ 2 * Gw * (y ^ (2 - 4 * σ) * y ^ (4 * σ - 2)) := by ring
      _ = 2 * C ^ 2 * Gw := by rw [hyy, mul_one]
  calc y ^ (2 - 4 * σ) * Pw * (2 * Gs) = 2 * Pw * (y ^ (2 - 4 * σ) * Gs) := by ring
    _ ≤ 2 * (4 * Real.pi ^ 2 * Ps) * (2 * C ^ 2 * Gw) := by gcongr
    _ = Ps * (16 * Real.pi ^ 2 * C ^ 2 * Gw) := by ring

/-! ### Leading coefficient on far-right lines -/

lemma rpow_split (A : ℝ) {n m : ℝ} (hn : 0 < n) (hm : 0 < m) (c x : ℝ) :
    A / n ^ x * m ^ x = A / n ^ c * m ^ c * (m / n) ^ (x - c) := by
  have e1 : n ^ x = n ^ c * n ^ (x - c) := by rw [← Real.rpow_add hn]; ring_nf
  have e2 : m ^ x = m ^ c * m ^ (x - c) := by rw [← Real.rpow_add hm]; ring_nf
  rw [e1, e2, Real.div_rpow hm.le hn.le]
  have h1 : 0 < n ^ c := Real.rpow_pos_of_pos hn c
  have h2 : 0 < n ^ (x - c) := Real.rpow_pos_of_pos hn _
  field_simp

/-- **The leading coefficient dominates** `L(b, x+iy) m^{x+iy}` for all `x ≥ c₀`. -/
theorem tail_gen (b : ℕ → ℂ) {m : ℕ} (hm : 1 ≤ m) (hlow : ∀ n, 0 < n → n < m → b n = 0)
    {c1 : ℝ} (hsum : Summable fun n : ℕ => ‖b n‖ / (n : ℝ) ^ c1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c0 : ℝ, c1 ≤ c0 ∧ ∀ x : ℝ, c0 ≤ x → ∀ y : ℝ,
      ‖LSeries b ((x : ℂ) + y * I) * (m : ℂ) ^ ((x : ℂ) + y * I) - b m‖ ≤ ε := by
  set S1 : ℝ := ∑' n : ℕ, ‖b n‖ / (n : ℝ) ^ c1 with hS1
  have hS10 : 0 ≤ S1 := tsum_nonneg fun n =>
    div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set q : ℝ := (m : ℝ) / (m + 1) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by linarith)]; linarith
  set M : ℝ := (m : ℝ) ^ c1 * S1 + 1 with hM
  have hM0 : 0 < M := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < ε / M by positivity) hq1
  refine ⟨c1 + N, by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)], fun x hx y => ?_⟩
  set s : ℂ := (x : ℂ) + y * I with hs
  have hsre : s.re = x := by simp [hs]
  have hmpos : 0 < m := by omega
  have hxc : (N : ℝ) ≤ x - c1 := by linarith
  have hnm : ‖(m : ℂ) ^ s‖ = (m : ℝ) ^ x := by
    rw [Complex.norm_natCast_cpow_of_pos hmpos, hsre]
  have hqN : q ^ (x - c1) ≤ q ^ N := by
    have hqp : 0 < q := by positivity
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hqp hq1.le hxc
  -- termwise bound
  set T : ℕ → ℂ := fun n => LSeries.term b s n * (m : ℂ) ^ s with hT
  set B : ℕ → ℝ := fun n => q ^ N * (m : ℝ) ^ c1 * (‖b n‖ / (n : ℝ) ^ c1) with hB
  have hBsum : Summable B := hsum.mul_left _
  have hpt : ∀ n, ‖(if n = m then 0 else T n)‖ ≤ B n := by
    intro n
    have hB0 : 0 ≤ B n := by
      simp only [hB]
      exact mul_nonneg (by positivity) (div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    by_cases h : n = m
    · rw [if_pos h, norm_zero]; exact hB0
    rw [if_neg h]
    rcases Nat.lt_or_gt_of_ne h with hlt | hgt
    · rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp [hT, LSeries.term]; exact hB0
      · simp [hT, LSeries.term, hlow n h0 hlt]; exact hB0
    · have hn0 : 0 < n := by omega
      have hnR : (m : ℝ) + 1 ≤ n := by exact_mod_cast hgt
      have hnpos : (0 : ℝ) < n := by linarith
      simp only [hT, LSeries.term, if_neg (show n ≠ 0 by omega), norm_mul, norm_div,
        Complex.norm_natCast_cpow_of_pos hn0, hsre, hnm]
      rw [rpow_split _ hnpos (by linarith) c1 x, hB]
      have hr : (m : ℝ) / n ≤ q := by
        rw [hq, div_le_div_iff₀ hnpos (by linarith)]; nlinarith
      have hmn0 : 0 ≤ (m : ℝ) / n := by positivity
      have h1 : ((m : ℝ) / n) ^ (x - c1) ≤ q ^ (x - c1) :=
        Real.rpow_le_rpow hmn0 hr (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
      have h0 : 0 ≤ ‖b n‖ / (n : ℝ) ^ c1 * (m : ℝ) ^ c1 := by positivity
      calc ‖b n‖ / (n : ℝ) ^ c1 * (m : ℝ) ^ c1 * ((m : ℝ) / n) ^ (x - c1)
          ≤ ‖b n‖ / (n : ℝ) ^ c1 * (m : ℝ) ^ c1 * q ^ N := by gcongr; exact h1.trans hqN
        _ = _ := by ring
  -- summability of the L-series at `s`
  have hLS : LSeriesSummable b s := by
    refine Summable.of_norm_bounded (g := fun n => ‖b n‖ / (n : ℝ) ^ c1) hsum fun n => ?_
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      simp only [LSeries.term_zero, norm_zero]
      exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h0
      rw [LSeries.term_of_ne_zero (by omega), norm_div, Complex.norm_natCast_cpow_of_pos h0, hsre]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos (by linarith) _)
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]))
  have hTsum : Summable T := hLS.mul_right _
  have hTm : T m = b m := by
    simp only [hT, LSeries.term, if_neg (show m ≠ 0 by omega)]
    have : (m : ℂ) ^ s ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h (by exact_mod_cast hmpos.ne')
    field_simp
  have hite : Summable (fun n => ‖(if n = m then 0 else T n)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hBsum
  have hsplit : LSeries b s * (m : ℂ) ^ s - b m = ∑' n, (if n = m then 0 else T n) := by
    rw [LSeries, ← tsum_mul_right, hTsum.tsum_eq_add_tsum_ite m, hTm]
    ring
  rw [hsplit]
  calc ‖∑' n, (if n = m then 0 else T n)‖ ≤ ∑' n, ‖(if n = m then 0 else T n)‖ :=
        norm_tsum_le_tsum_norm hite
    _ ≤ ∑' n, B n := hite.tsum_le_tsum hpt hBsum
    _ = q ^ N * (m : ℝ) ^ c1 * S1 := by rw [hB, tsum_mul_left]
    _ ≤ q ^ N * M := by rw [hM]; nlinarith [pow_nonneg hq0 N]
    _ ≤ ε / M * M := by gcongr
    _ = ε := by field_simp

/-! ### The function `Z = Lam · γₘ⁻¹` -/

section Z

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ)

/-- `Z(w) = Lam(w) γₘ(w)⁻¹`. -/
noncomputable def Zf (w : ℂ) : ℂ := Lam d w * invGamM m w

lemma differentiableAt_Lam {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) : DifferentiableAt ℂ (Lam d) w := by
  have hw1 : w - 1 ≠ 0 := sub_ne_zero.2 h1
  have h1' : DifferentiableAt ℂ (fun s : ℂ => 1 / (s - 1)) w :=
    (differentiableAt_const (1 : ℂ)).div ((differentiableAt_id (x := w)).sub_const 1) hw1
  have h0' : DifferentiableAt ℂ (fun s : ℂ => 1 / s) w :=
    (differentiableAt_const (1 : ℂ)).div (differentiableAt_id (x := w)) h0
  have : Lam d = fun s => d.Λ₀ s + (κ : ℂ) * (1 / (s - 1) - 1 / s) := rfl
  rw [this]
  exact (d.diff w).add ((h1'.sub h0').const_mul _)

lemma differentiableAt_Zf {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) : DifferentiableAt ℂ (Zf d) w :=
  (differentiableAt_Lam d h0 h1).mul (differentiable_invGamM m w)

variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

include habs in
lemma Zf_eq {w : ℂ} (hw : 1 < w.re) :
    Zf d w = riemannZeta (2 * w) * LSeries (fun n => (a n : ℂ)) w := by
  unfold Zf
  rw [Lam_eq d habs hw]
  have := gamM_mul_invGamM m (s := w) (by linarith)
  linear_combination (riemannZeta (2 * w) * LSeries (fun n => (a n : ℂ)) w) * this

include habs in
/-- **Uniform convexity bound on horizontal segments.** -/
theorem Zf_horiz (hm : 1 ≤ m) (c : ℝ) (hc : 0 ≤ c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : ℝ, 9 / 16 ≤ x → x ≤ c → 1 ≤ y →
      ‖Zf d ((x : ℂ) + y * I)‖ ≤ K * y ^ ((15 : ℝ) / 16) := by
  obtain ⟨B, hB⟩ := Stirling.Efun_bound_eps d habs hm (ε := 1 / 32) (by norm_num) (by norm_num)
    (σ₁ := 9 / 16) (by norm_num) (by norm_num)
  obtain ⟨Zb, hZb0, hZb⟩ := Stirling.exists_norm_zeta_le2
  have hD0 := Stirling.Deps_nonneg (a := a) (3 / 2)
  set B' : ℝ := max B 0 with hB'
  refine ⟨B' * (c + 4) ^ ((31 : ℝ) / 16) + Zb * Stirling.Deps a (3 / 2), by positivity,
    fun x y hx1 hx2 hy => ?_⟩
  set w : ℂ := (x : ℂ) + y * I with hw
  have hwre : w.re = x := by simp [hw]
  have hwim : w.im = y := by simp [hw]
  have hy0 : 0 < y := by linarith
  have hy1516 : 1 ≤ y ^ ((15 : ℝ) / 16) := Real.one_le_rpow hy (by norm_num)
  have hA : 0 ≤ B' * (c + 4) ^ ((31 : ℝ) / 16) := by positivity
  have hZD : 0 ≤ Zb * Stirling.Deps a (3 / 2) := by positivity
  rcases le_or_gt x (5 / 2) with hx | hx
  · have h0 : w ≠ 0 := by intro h; have := congrArg Complex.im h; rw [hwim] at this; simp at this; linarith
    have h1 : w ≠ 1 := by intro h; have := congrArg Complex.im h; rw [hwim] at this; simp at this; linarith
    have hE := hB w (by rw [hwre]; exact hx1) (by rw [hwre]; exact hx)
    rw [show (3 : ℝ) + 2 * (1 / 32) - 2 * (9 / 16) = 31 / 16 by norm_num] at hE
    have hEq : Efun d w = (w - 1) * Zf d w := by rw [Efun_eq d h0 h1, Zf]; ring
    have hw1 : y ≤ ‖w - 1‖ := by
      have := Complex.abs_im_le_norm (w - 1)
      have him : (w - 1).im = y := by simp [hwim]
      rw [him, abs_of_pos hy0] at this; exact this
    have hw3 : ‖w + 3‖ ≤ (c + 4) * y := by
      refine (Complex.norm_le_abs_re_add_abs_im (w + 3)).trans ?_
      have hre : (w + 3).re = x + 3 := by simp [hwre]
      have him : (w + 3).im = y := by simp [hwim]
      rw [hre, him, abs_of_pos (by linarith), abs_of_pos hy0]; nlinarith
    have hpow : ‖w + 3‖ ^ ((31 : ℝ) / 16) ≤ (c + 4) ^ ((31 : ℝ) / 16) * y ^ ((31 : ℝ) / 16) := by
      rw [← Real.mul_rpow (by linarith) hy0.le]
      exact Real.rpow_le_rpow (norm_nonneg _) hw3 (by norm_num)
    have hy3116 : y ^ ((31 : ℝ) / 16) = y * y ^ ((15 : ℝ) / 16) := by
      rw [show (31 : ℝ) / 16 = 1 + 15 / 16 by norm_num, Real.rpow_add hy0, Real.rpow_one]
    have hEle : ‖Efun d w‖ ≤ B' * ((c + 4) ^ ((31 : ℝ) / 16) * y ^ ((31 : ℝ) / 16)) := by
      calc ‖Efun d w‖ ≤ B * ‖w + 3‖ ^ ((31 : ℝ) / 16) := hE
        _ ≤ B' * ‖w + 3‖ ^ ((31 : ℝ) / 16) := by gcongr; exact le_max_left _ _
        _ ≤ _ := by gcongr
    rw [hEq, norm_mul] at hEle
    have hZ0 := norm_nonneg (Zf d w)
    have : y * ‖Zf d w‖ ≤ y * (B' * (c + 4) ^ ((31 : ℝ) / 16) * y ^ ((15 : ℝ) / 16)) := by
      calc y * ‖Zf d w‖ ≤ ‖w - 1‖ * ‖Zf d w‖ := by gcongr
        _ ≤ _ := hEle
        _ = _ := by rw [hy3116]; ring
    have := le_of_mul_le_mul_left this hy0
    nlinarith
  · rw [Zf_eq d habs (by rw [hwre]; linarith), norm_mul]
    have h1 := hZb (2 * w) (by simp [hwre]; linarith)
    have h2 := Stirling.norm_LSeries_le_Deps habs (ε := 3 / 2) (by norm_num) (s := w)
      (by rw [hwre]; linarith)
    have : ‖riemannZeta (2 * w)‖ * ‖LSeries (fun n => (a n : ℂ)) w‖ ≤ Zb * Stirling.Deps a (3 / 2) :=
      mul_le_mul h1 h2 (norm_nonneg _) hZb0
    nlinarith

end Z

end RamanujanTau.RankinOmega
