/-
# Phragmén–Lindelöf for the Rankin–Selberg L-function

`fPL_bound`: for `RSData a κ`, the entire function
`f(s) = (s(s−1)Λ₀(s) + κ) γ(s)⁻¹ (s+3)^{−19}` is bounded on `−3/2 ≤ Re s ≤ 5/2`.
-/
import RamanujanTau.RankinError.Landau

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Complex Real MeasureTheory Set Filter Topology Asymptotics

section PL

variable {a : ℕ → ℝ} {κ : ℝ} (d : RSData a κ)

/-- The function to which Phragmén–Lindelöf is applied. -/
noncomputable def fPL (s : ℂ) : ℂ := (s * (s - 1) * d.Λ₀ s + κ) * invGam s / (s + 3) ^ 19

lemma num_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s - 1 ≠ 0) :
    s * (s - 1) * d.Λ₀ s + κ = s * (s - 1) * (d.Λ₀ s + κ * (1 / (s - 1) - 1 / s)) := by
  field_simp; ring

lemma ne_zero_of_re {s : ℂ} {r : ℝ} (h : s.re = r) (hr : r ≠ 0) : s ≠ 0 := by
  intro h'; rw [h'] at h; simp at h; exact hr h.symm

lemma fPL_eq_right {s : ℂ} (hs : 2 < s.re) :
    fPL d s = s * (s - 1) * riemannZeta (2 * s) * LSeries (fun n => (a n : ℂ)) s / (s + 3) ^ 19 := by
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have h1 : s - 1 ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  unfold fPL
  rw [num_eq d h0 h1, ← d.unfold s hs]
  have := gam_mul_invGam (s := s) (by linarith)
  linear_combination (s * (s - 1) * riemannZeta (2 * s) * LSeries (fun n => (a n : ℂ)) s /
    (s + 3) ^ 19) * this

variable (hsum : LSeriesSummable (fun n => (a n : ℂ)) ((5 / 2 : ℝ) : ℂ))

/-- `D₅ = ∑ ‖term a (5/2) n‖`. -/
noncomputable def D5 : ℝ := ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) ((5 / 2 : ℝ) : ℂ) n‖

include hsum in
lemma right_edge (Z : ℝ) (hZ0 : 0 ≤ Z) (hZ : ∀ w : ℂ, 5 ≤ w.re → ‖riemannZeta w‖ ≤ Z)
    {s : ℂ} (hs : s.re = 5 / 2) : ‖fPL d s‖ ≤ Z * D5 (a := a) := by
  rw [fPL_eq_right d (by rw [hs]; norm_num)]
  have hD : ‖LSeries (fun n => (a n : ℂ)) s‖ ≤ D5 (a := a) := norm_LSeries_le hsum (s := s) (by simp [hs])
  have hz := hZ (2 * s) (by simp [hs]; norm_num)
  have h3 := one_le_norm_add_three (s := s) (by rw [hs]; norm_num)
  have hn1 := norm_le_norm_add_three (s := s) (by rw [hs]; norm_num)
  have hn2 := norm_sub_one_le_norm_add_three (s := s) (by rw [hs]; norm_num)
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow]
  have hD0 : 0 ≤ D5 (a := a) := tsum_nonneg fun _ => norm_nonneg _
  have hpow : ‖s + 3‖ ^ 2 ≤ ‖s + 3‖ ^ 19 := pow_le_pow_right₀ h3 (by norm_num)
  have hpos : 0 < ‖s + 3‖ ^ 19 := by positivity
  rw [div_le_iff₀ hpos]
  calc ‖s‖ * ‖s - 1‖ * ‖riemannZeta (2 * s)‖ * ‖LSeries (fun n => (a n : ℂ)) s‖
      ≤ ‖s + 3‖ * ‖s + 3‖ * Z * D5 (a := a) := by gcongr
    _ = Z * D5 (a := a) * ‖s + 3‖ ^ 2 := by ring
    _ ≤ Z * D5 (a := a) * ‖s + 3‖ ^ 19 := by gcongr

include hsum in
lemma left_edge (Z : ℝ) (hZ0 : 0 ≤ Z) (hZ : ∀ w : ℂ, 5 ≤ w.re → ‖riemannZeta w‖ ≤ Z)
    {s : ℂ} (hs : s.re = -3 / 2) : ‖fPL d s‖ ≤ Z * D5 (a := a) * (2 ^ 9 * 13 ^ 19) := by
  set w : ℂ := 1 - s with hw
  have hwre : w.re = 5 / 2 := by rw [hw]; simp [hs]; norm_num
  have hnum : s * (s - 1) * d.Λ₀ s + κ =
      w * (w - 1) * (gam w * riemannZeta (2 * w) * LSeries (fun n => (a n : ℂ)) w) := by
    have h0 : w ≠ 0 := ne_zero_of_re hwre (by norm_num)
    have h1 : w - 1 ≠ 0 := ne_zero_of_re (r := 3 / 2) (by simp [hwre]; norm_num) (by norm_num)
    rw [d.unfold w (by rw [hwre]; norm_num), ← num_eq d h0 h1, hw, d.fe s]; ring
  unfold fPL
  rw [hnum]
  have hrat := gamma_ratio_le hs
  rw [← hw] at hrat
  have hD : ‖LSeries (fun n => (a n : ℂ)) w‖ ≤ D5 (a := a) :=
    norm_LSeries_le hsum (s := w) (by simp [hwre])
  have hz := hZ (2 * w) (by simp [hwre]; norm_num)
  have hD0 : 0 ≤ D5 (a := a) := tsum_nonneg fun _ => norm_nonneg _
  set u : ℂ := s + 2 with hu
  have hs3 : s + 3 = u + 1 := by rw [hu]; ring
  have hww : ‖w * (w - 1)‖ ≤ (‖u‖ + 13) ^ 2 := by
    have e1 : w = 3 - u := by rw [hw, hu]; ring
    rw [e1, norm_mul]
    have a1 : ‖3 - u‖ ≤ ‖u‖ + 13 := by
      have := norm_sub_le (3 : ℂ) u
      rw [show ‖(3 : ℂ)‖ = 3 by simp] at this; linarith
    have a2 : ‖3 - u - 1‖ ≤ ‖u‖ + 13 := by
      have := norm_sub_le (2 : ℂ) u
      rw [show (3 : ℂ) - u - 1 = 2 - u by ring, Complex.norm_two] at *; linarith
    calc ‖3 - u‖ * ‖3 - u - 1‖ ≤ (‖u‖ + 13) * (‖u‖ + 13) := by gcongr
      _ = (‖u‖ + 13) ^ 2 := by ring
  -- `‖u‖ + 13 ≤ 13 ‖u + 1‖`
  have hu1 : ‖u‖ + 13 ≤ 13 * ‖u + 1‖ := by
    have hre : u.re = 1 / 2 := by rw [hu]; simp [hs]; norm_num
    have b1 : 3 / 2 ≤ ‖u + 1‖ := by
      have := Complex.abs_re_le_norm (u + 1); simp [hre] at this; norm_num at this; linarith
    have b2 : ‖u‖ - 1 ≤ ‖u + 1‖ := by
      have := norm_sub_le (u + 1) 1; rw [add_sub_cancel_right, norm_one] at this; linarith
    rcases le_or_gt ‖u‖ (13 / 2) with h | h
    · linarith
    · linarith
  have hpos : 0 < ‖u + 1‖ := by
    have := Complex.abs_re_le_norm (u + 1)
    have hre : u.re = 1 / 2 := by rw [hu]; simp [hs]; norm_num
    simp [hre] at this; norm_num at this; linarith
  have hsplit : w * (w - 1) * (gam w * riemannZeta (2 * w) * LSeries (fun n => (a n : ℂ)) w) *
      invGam s / (s + 3) ^ 19 = (w * (w - 1)) * riemannZeta (2 * w) *
        LSeries (fun n => (a n : ℂ)) w * (gam w * invGam s) / (u + 1) ^ 19 := by
    rw [hs3]; ring
  rw [hsplit, norm_div, norm_mul, norm_mul, norm_mul, norm_pow, div_le_iff₀ (by positivity)]
  have hB : (‖u‖ + 13) ^ 19 ≤ 13 ^ 19 * ‖u + 1‖ ^ 19 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hu1 _
  calc ‖w * (w - 1)‖ * ‖riemannZeta (2 * w)‖ * ‖LSeries (fun n => (a n : ℂ)) w‖ *
        ‖gam w * invGam s‖
      ≤ (‖u‖ + 13) ^ 2 * Z * D5 (a := a) * (2 ^ 9 * (‖u‖ + 13) ^ 17) := by gcongr
    _ = Z * D5 (a := a) * 2 ^ 9 * (‖u‖ + 13) ^ 19 := by ring
    _ ≤ Z * D5 (a := a) * 2 ^ 9 * (13 ^ 19 * ‖u + 1‖ ^ 19) := by gcongr
    _ = Z * D5 (a := a) * (2 ^ 9 * 13 ^ 19) * ‖u + 1‖ ^ 19 := by ring

lemma differentiableOn_fPL : DifferentiableOn ℂ (fPL d) {s : ℂ | -2 < s.re} := by
  intro s hs
  have h3 : (s + 3) ^ 19 ≠ 0 := by
    apply pow_ne_zero; intro h; have := congrArg re h; simp at this; simp at hs; linarith
  unfold fPL
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.div ?_ (by fun_prop) h3
  exact (((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
    (d.diff s)).add_const _).mul (differentiable_invGam s)

lemma norm_le_exp_abs_im {s : ℂ} {r : ℝ} (hr0 : 0 ≤ r) (hre : |s.re| ≤ r) :
    ‖s‖ ≤ (r + 1) * Real.exp |s.im| := by
  have h1 : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
  have h2 : |s.im| + 1 ≤ Real.exp |s.im| := Real.add_one_le_exp _
  have h3 : 1 ≤ Real.exp |s.im| := Real.one_le_exp (abs_nonneg _)
  nlinarith [abs_nonneg s.im]

lemma fPL_growth : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, -3 / 2 < s.re → s.re < 5 / 2 → 1 ≤ |s.im| →
    ‖fPL d s‖ ≤ K * Real.exp ((2 * π + 2) * |s.im|) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_inv_Gamma_le (A := 3 / 2) (by norm_num)
  have hπ := Real.pi_pos
  set K : ℝ := (16 * |d.L₀| + |κ|) * (π ^ (3:ℝ) * (4 * π) ^ (14:ℝ)) * C ^ 2 with hK
  refine ⟨K, by positivity, fun s h1 h2 ht => ?_⟩
  set t := |s.im| with htdef
  have hS3 := one_le_norm_add_three (s := s) (by linarith)
  -- numerator
  have hn : ‖s * (s - 1) * d.Λ₀ s + κ‖ ≤ (16 * |d.L₀| + |κ|) * Real.exp (2 * t) := by
    have e1 : ‖s‖ ≤ 4 * Real.exp t := by
      have := norm_le_exp_abs_im (s := s) (r := 3) (by norm_num)
        (by rw [abs_le]; constructor <;> linarith)
      linarith
    have e2 : ‖s - 1‖ ≤ 4 * Real.exp t := by
      have h := norm_le_exp_abs_im (s := s - 1) (r := 3) (by norm_num)
        (by simp only [sub_re, one_re]; rw [abs_le]; constructor <;> linarith)
      simp only [sub_im, one_im, sub_zero] at h
      linarith
    have hL := d.bdd s h1.le h2.le
    have hL' : ‖d.Λ₀ s‖ ≤ |d.L₀| := hL.trans (le_abs_self _)
    have hexp : Real.exp (2 * t) = Real.exp t * Real.exp t := by rw [← Real.exp_add]; ring_nf
    have h1e : 1 ≤ Real.exp (2 * t) := Real.one_le_exp (by positivity)
    calc ‖s * (s - 1) * d.Λ₀ s + κ‖ ≤ ‖s‖ * ‖s - 1‖ * ‖d.Λ₀ s‖ + |κ| := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (4 * Real.exp t) * (4 * Real.exp t) * |d.L₀| + |κ| := by gcongr
      _ = 16 * |d.L₀| * Real.exp (2 * t) + |κ| := by rw [hexp]; ring
      _ ≤ (16 * |d.L₀| + |κ|) * Real.exp (2 * t) := by nlinarith [abs_nonneg κ]
  -- `invGam`
  have hg : ‖invGam s‖ ≤ (π ^ (3:ℝ) * (4 * π) ^ (14:ℝ)) * C ^ 2 * Real.exp (2 * π * t) := by
    unfold invGam
    have g1 := hC s (by linarith) ht
    have g2 := hC (s + 11) (by simp; linarith) (by simpa using ht)
    simp only [add_im, im_ofNat, add_zero] at g2
    rw [norm_mul, norm_mul, norm_div, norm_mul, Complex.norm_two,
      show (π : ℂ) = ((π : ℝ) : ℂ) from rfl, norm_cpow_pos π hπ, norm_cpow_pos _ (by positivity)]
    have p1 : π ^ s.re ≤ π ^ (3:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
    have p2 : (4 * π) ^ (s + 11).re ≤ (4 * π) ^ (14:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [Real.pi_gt_three]) (by simp; linarith)
    have hexp : Real.exp (2 * π * t) = Real.exp (π * t) * Real.exp (π * t) := by
      rw [← Real.exp_add]; ring_nf
    rw [hexp]
    calc π ^ s.re * (4 * π) ^ (s + 11).re / 2 * ‖(Complex.Gamma s)⁻¹‖ * ‖(Complex.Gamma (s + 11))⁻¹‖
        ≤ π ^ (3:ℝ) * (4 * π) ^ (14:ℝ) / 1 * (C * Real.exp (π * t)) * (C * Real.exp (π * t)) := by
          gcongr; norm_num
      _ = _ := by ring
  unfold fPL
  rw [norm_div, norm_mul, norm_pow]
  have hp : 1 ≤ ‖s + 3‖ ^ 19 := one_le_pow₀ hS3
  rw [div_le_iff₀ (by positivity)]
  have hexp2 : Real.exp (2 * t) * Real.exp (2 * π * t) = Real.exp ((2 * π + 2) * t) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖s * (s - 1) * d.Λ₀ s + κ‖ * ‖invGam s‖
      ≤ ((16 * |d.L₀| + |κ|) * Real.exp (2 * t)) *
        ((π ^ (3:ℝ) * (4 * π) ^ (14:ℝ)) * C ^ 2 * Real.exp (2 * π * t)) := by gcongr
    _ = K * Real.exp ((2 * π + 2) * t) := by rw [← hexp2, hK]; ring
    _ ≤ K * Real.exp ((2 * π + 2) * t) * ‖s + 3‖ ^ 19 := le_mul_of_one_le_right (by positivity) hp

include hsum in
theorem fPL_bound : ∃ C : ℝ, ∀ s : ℂ, -3 / 2 ≤ s.re → s.re ≤ 5 / 2 → ‖fPL d s‖ ≤ C := by
  obtain ⟨Z, hZ0, hZ⟩ := exists_norm_zeta_le
  obtain ⟨K, hK0, hK⟩ := fPL_growth d
  have hD0 : 0 ≤ D5 (a := a) := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨Z * D5 (a := a) * (2 ^ 9 * 13 ^ 19), fun s h1 h2 => ?_⟩
  have hclos : closure (re ⁻¹' Ioo (-3 / 2 : ℝ) (5 / 2)) ⊆ {s : ℂ | -2 < s.re} := by
    rw [closure_preimage_re, closure_Ioo (by norm_num)]
    intro z hz; simp only [mem_preimage, mem_Icc] at hz; simp; linarith [hz.1]
  refine PhragmenLindelof.vertical_strip ((differentiableOn_fPL d).mono hclos).diffContOnCl
    ⟨1 / 2, by rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]; linarith [Real.pi_gt_three],
      4 * π + 4, ?_⟩ (fun z hz => le_trans (left_edge d hsum Z hZ0 hZ hz) le_rfl)
    (fun z hz => le_trans (right_edge d hsum Z hZ0 hZ hz)
      (le_mul_of_one_le_right (by positivity) (by norm_num))) h1 h2
  refine IsBigO.of_bound K ?_
  have him : ∀ᶠ z : ℂ in comap (_root_.abs ∘ im) atTop, 1 ≤ |z.im| :=
    tendsto_comap.eventually (eventually_ge_atTop (1:ℝ))
  have hstrip : ∀ᶠ z : ℂ in 𝓟 (re ⁻¹' Ioo (-3 / 2 : ℝ) (5 / 2)),
      z ∈ re ⁻¹' Ioo (-3 / 2 : ℝ) (5 / 2) := eventually_principal.2 fun z hz => hz
  filter_upwards [him.filter_mono inf_le_left, hstrip.filter_mono inf_le_right] with z hz1 hz2
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine (hK z hz2.1 hz2.2 hz1).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK0)
  have := Real.add_one_le_exp (1 / 2 * |z.im|)
  have hπ := Real.pi_pos
  nlinarith [abs_nonneg z.im]

end PL

end RamanujanTau.RankinError
