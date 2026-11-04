/-
# A genuine convexity bound for the Rankin–Selberg function

Write `E(s) = (s−1) ζ(2s) D(s)` (entire, `Efun`). Convexity predicts
`|E(σ+it)| ≪ |t|^{1 + (3 − 2σ)}` on `−1/2 ≤ σ ≤ 3/2` (degree-4 conductor, edges at `3/2` and
its reflection `−1/2`). We prove this exactly on the lines where the `Γ`-ratio is computable
without Stirling, and the constant-exponent interpolation between them:

* **Step A** (`fA_bound`): Phragmén–Lindelöf on `[−1/2, 3/2]` for the *variable-exponent*
  function `f_A(s) = E(s) Γ(s+1) / (Γ(4−s)(s+3))`. On `Re s = 3/2`, `4−s = conj(s+1)` so the
  ratio has modulus `1`; on `Re s = −1/2` the functional equation and an exact `Γ`-ratio
  computation (`ratioA_le`, a degree-15/degree-15 rational function of `u = s+1`) bound it.
* **Step B** (`Efun_line`): on `Re s = σ_L` with `n = 3 − 2σ_L ∈ ℕ`,
  `Γ(4−s) = Γ(conj(s+1) + n) = ∏_{j<n}(conj(s+1)+j) Γ(conj(s+1))`, so `|E| ≤ C|s+3|^{n+1}`.
* **Step C** (`Efun_bound`): constant-exponent Phragmén–Lindelöf on `[σ_L, 3/2]`, plus
  absolute convergence on `[3/2, 5/2]`: `|E(s)| ≤ B |s+3|^{n+1}` on `σ_L ≤ Re s ≤ 5/2`.

Used with `σ_L = 1/2` (`n = 2`) and `σ_L = 0` (`n = 3`).
-/
import RamanujanTau.RankinSharp.Efun

set_option autoImplicit false

namespace RamanujanTau.RankinSharp

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.RankinError

lemma norm_prod_ge {u : ℂ} (hu : 0 ≤ u.re) (p : ℕ) :
    ‖u‖ ^ p ≤ ‖∏ j ∈ Finset.range p, (u + j)‖ := by
  rw [norm_prod]
  have : ‖u‖ ^ p = ∏ _j ∈ Finset.range p, ‖u‖ := by rw [Finset.prod_const, Finset.card_range]
  rw [this]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro j _
  apply norm_le_norm_of_sq
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  simp [Complex.normSq_apply]; nlinarith

lemma exists_norm_zeta_le3 : ∃ Z : ℝ, 0 ≤ Z ∧ ∀ w : ℂ, 3 ≤ w.re → ‖riemannZeta w‖ ≤ Z := by
  have h1 : LSeriesSummable 1 ((3 : ℝ) : ℂ) := LSeriesSummable_one_iff.2 (by simp)
  refine ⟨∑' n, ‖LSeries.term 1 ((3 : ℝ) : ℂ) n‖, tsum_nonneg fun _ => norm_nonneg _,
    fun w hw => ?_⟩
  rw [← LSeries_one_eq_riemannZeta (by linarith)]
  exact norm_LSeries_le h1 (by simpa using hw)

/-- The exact `Γ`-ratio on the left edge `Re s = −1/2`. -/
lemma ratioA_le {s : ℂ} (hs : s.re = -1 / 2) :
    ‖(s - 1) * gam (1 - s) * invGam s * Complex.Gamma (s + 1) * (Complex.Gamma (4 - s))⁻¹ /
      (s + 3)‖ ≤ 25 ^ 15 := by
  set u : ℂ := s + 1 with hu
  have hure : u.re = 1 / 2 := by rw [hu]; simp [hs]; norm_num
  have hu0 : 0 < u.re := by rw [hure]; norm_num
  have hcu0 : 0 < (starRingEnd ℂ u).re := by simp [hure]
  have hun : 1 / 2 ≤ ‖u‖ := by have := Complex.abs_re_le_norm u; rw [hure] at this; simpa using this
  have hGu := Complex.Gamma_ne_zero_of_re_pos hu0
  have hGcu := Complex.Gamma_ne_zero_of_re_pos hcu0
  have hcu_ne : starRingEnd ℂ u ≠ 0 := by
    intro h; have := congrArg re h; simp [hure] at this
  have hu1 : u - 1 ≠ 0 := by intro h; have := congrArg re h; simp [hure] at this; norm_num at this
  -- Gamma values
  have G1 : Complex.Gamma (1 - s) = starRingEnd ℂ u * Complex.Gamma (starRingEnd ℂ u) := by
    rw [show 1 - s = starRingEnd ℂ u + 1 by apply Complex.ext <;> simp [hu, hs] <;> norm_num,
      Complex.Gamma_add_one _ hcu_ne]
  have G12 : Complex.Gamma (1 - s + 11) =
      (∏ j ∈ Finset.range 12, (starRingEnd ℂ u + j)) * Complex.Gamma (starRingEnd ℂ u) := by
    rw [← Gamma_add_nat hcu0 12]; congr 1
    apply Complex.ext <;> simp [hu, hs] <;> norm_num
  have G4 : Complex.Gamma (4 - s) =
      (∏ j ∈ Finset.range 4, (starRingEnd ℂ u + j)) * Complex.Gamma (starRingEnd ℂ u) := by
    rw [← Gamma_add_nat hcu0 4]; congr 1
    apply Complex.ext <;> simp [hu, hs] <;> norm_num
  have G11 : Complex.Gamma (s + 11) = (∏ j ∈ Finset.range 10, (u + j)) * Complex.Gamma u := by
    rw [← Gamma_add_nat hu0 10]; congr 1; rw [hu]; push_cast; ring
  have Gs : Complex.Gamma u = (u - 1) * Complex.Gamma s := by
    have := Complex.Gamma_add_one (u - 1) hu1
    rw [sub_add_cancel] at this; rw [this, hu]; ring_nf
  have hGs : Complex.Gamma s ≠ 0 := by intro h; rw [h, mul_zero] at Gs; exact hGu Gs
  have hP10 : ∏ j ∈ Finset.range 10, (u + j) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro j _ h; have := congrArg re h; simp [hure] at this
    have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have hP4 : ∏ j ∈ Finset.range 4, (starRingEnd ℂ u + j) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro j _ h; have := congrArg re h; simp [hure] at this
    have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have hu2 : u + 2 ≠ 0 := by intro h; have := congrArg re h; simp [hure] at this; norm_num at this
  -- the π-factors
  have hpi : ‖(π : ℂ) ^ (-(1 - s)) * (π : ℂ) ^ s‖ ≤ 1 := by
    rw [norm_mul, show (π : ℂ) = ((π : ℝ) : ℂ) from rfl, norm_cpow_pos π Real.pi_pos,
      norm_cpow_pos π Real.pi_pos, ← Real.rpow_add Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp [hs]; norm_num
  have h4pi : ‖((4 * π : ℝ) : ℂ) ^ (-(1 - s) - 11) * ((4 * π : ℝ) : ℂ) ^ (s + 11)‖ ≤ 1 := by
    rw [norm_mul, norm_cpow_pos _ (by positivity), norm_cpow_pos _ (by positivity),
      ← Real.rpow_add (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.pi_gt_three])
    simp [hs]; norm_num
  have hsplit : (s - 1) * gam (1 - s) * invGam s * Complex.Gamma (s + 1) *
      (Complex.Gamma (4 - s))⁻¹ / (s + 3) =
      ((π : ℂ) ^ (-(1 - s)) * (π : ℂ) ^ s) *
      (((4 * π : ℝ) : ℂ) ^ (-(1 - s) - 11) * ((4 * π : ℝ) : ℂ) ^ (s + 11)) *
      ((s - 1) * Complex.Gamma (1 - s) * Complex.Gamma (1 - s + 11) * (Complex.Gamma s)⁻¹ *
        (Complex.Gamma (s + 11))⁻¹ * Complex.Gamma (s + 1) * (Complex.Gamma (4 - s))⁻¹ /
        (s + 3)) := by
    unfold gam invGam; ring
  have hY : (s - 1) * Complex.Gamma (1 - s) * Complex.Gamma (1 - s + 11) * (Complex.Gamma s)⁻¹ *
        (Complex.Gamma (s + 11))⁻¹ * Complex.Gamma (s + 1) * (Complex.Gamma (4 - s))⁻¹ /
        (s + 3) =
      (starRingEnd ℂ u * (∏ j ∈ Finset.range 12, (starRingEnd ℂ u + j)) * (u - 1) * (u - 2)) /
        ((∏ j ∈ Finset.range 10, (u + j)) * (∏ j ∈ Finset.range 4, (starRingEnd ℂ u + j)) *
          (u + 2)) * (Complex.Gamma (starRingEnd ℂ u) * (Complex.Gamma u)⁻¹) := by
    rw [G1, G12, G4, G11, show s + 1 = u from rfl, Gs,
      show s - 1 = u - 2 by rw [hu]; ring, show s + 3 = u + 2 by rw [hu]; ring]
    field_simp
  have hratio : ‖Complex.Gamma (starRingEnd ℂ u) * (Complex.Gamma u)⁻¹‖ = 1 := by
    rw [norm_mul, norm_inv, norm_Gamma_conj, mul_inv_cancel₀ (norm_ne_zero_iff.2 hGu)]
  rw [hsplit, hY]
  generalize (π : ℂ) ^ (-(1 - s)) * (π : ℂ) ^ s = P at hpi ⊢
  generalize ((4 * π : ℝ) : ℂ) ^ (-(1 - s) - 11) * ((4 * π : ℝ) : ℂ) ^ (s + 11) = Q at h4pi ⊢
  generalize Complex.Gamma (starRingEnd ℂ u) * (Complex.Gamma u)⁻¹ = R at hratio ⊢
  rw [norm_mul, norm_mul, norm_mul, hratio, mul_one, norm_div]
  -- numerator and denominator
  have hc : ‖starRingEnd ℂ u‖ = ‖u‖ := Complex.norm_conj u
  have hnum : ‖starRingEnd ℂ u * (∏ j ∈ Finset.range 12, (starRingEnd ℂ u + j)) * (u - 1) *
      (u - 2)‖ ≤ 25 ^ 15 * ‖u‖ ^ 15 := by
    rw [norm_mul, norm_mul, norm_mul, hc]
    have p12 := norm_prod_le_pow (u := starRingEnd ℂ u) 12
    rw [hc] at p12
    have a1 : ‖u‖ + ((12 : ℕ) : ℝ) ≤ 25 * ‖u‖ := by push_cast; linarith
    have a2 : ‖u - 1‖ ≤ 25 * ‖u‖ := by
      have := norm_sub_le u 1; rw [norm_one] at this; linarith
    have a3 : ‖u - 2‖ ≤ 25 * ‖u‖ := by
      have := norm_sub_le u 2; rw [Complex.norm_two] at this; linarith
    calc ‖u‖ * ‖∏ j ∈ Finset.range 12, (starRingEnd ℂ u + j)‖ * ‖u - 1‖ * ‖u - 2‖
        ≤ (25 * ‖u‖) * (25 * ‖u‖) ^ 12 * (25 * ‖u‖) * (25 * ‖u‖) := by
          gcongr
          · linarith [norm_nonneg u]
          · exact p12.trans (pow_le_pow_left₀ (by positivity) a1 _)
      _ = 25 ^ 15 * ‖u‖ ^ 15 := by ring
  have hden : ‖u‖ ^ 15 ≤ ‖(∏ j ∈ Finset.range 10, (u + j)) *
      (∏ j ∈ Finset.range 4, (starRingEnd ℂ u + j)) * (u + 2)‖ := by
    rw [norm_mul, norm_mul]
    have d1 := norm_prod_ge hu0.le 10
    have d2 := norm_prod_ge hcu0.le 4
    rw [hc] at d2
    have d3 : ‖u‖ ≤ ‖u + 2‖ := by
      apply norm_le_norm_of_sq; simp [Complex.normSq_apply]; nlinarith
    calc ‖u‖ ^ 15 = ‖u‖ ^ 10 * ‖u‖ ^ 4 * ‖u‖ := by ring
      _ ≤ _ := by gcongr
  have hu15 : 0 < ‖u‖ ^ 15 := by positivity
  have hfrac : ‖starRingEnd ℂ u * (∏ j ∈ Finset.range 12, (starRingEnd ℂ u + j)) * (u - 1) *
      (u - 2)‖ / ‖(∏ j ∈ Finset.range 10, (u + j)) *
      (∏ j ∈ Finset.range 4, (starRingEnd ℂ u + j)) * (u + 2)‖ ≤ 25 ^ 15 := by
    rw [div_le_iff₀ (hu15.trans_le hden)]
    calc _ ≤ 25 ^ 15 * ‖u‖ ^ 15 := hnum
      _ ≤ _ := by gcongr
  calc _ ≤ 1 * 1 * 25 ^ 15 := by gcongr
    _ = (25 : ℝ) ^ 15 := by ring

section A

variable {a : ℕ → ℝ} {κ : ℝ} (d : RSData a κ)

/-- The variable-exponent Phragmén–Lindelöf function. -/
noncomputable def fA (s : ℂ) : ℂ :=
  Efun d s * Complex.Gamma (s + 1) * (Complex.Gamma (4 - s))⁻¹ / (s + 3)

lemma differentiableOn_fA : DifferentiableOn ℂ (fA d) {s : ℂ | -1 < s.re} := by
  intro s hs
  simp only [mem_setOf_eq] at hs
  have h3 : s + 3 ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
  have hG : DifferentiableAt ℂ (fun s => Complex.Gamma (s + 1)) s := by
    refine (Complex.differentiableAt_Gamma (s + 1) fun m h => ?_).comp s
      (differentiableAt_id.add_const (1 : ℂ))
    have := congrArg re h; simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hG4 : DifferentiableAt ℂ (fun s => (Complex.Gamma (4 - s))⁻¹) s := by
    have := (Complex.differentiable_one_div_Gamma (4 - s)).comp s
      ((differentiableAt_const (4 : ℂ)).sub differentiableAt_id)
    simpa [Function.comp_def] using this
  unfold fA
  exact ((((differentiable_Efun d s).mul hG).mul hG4).div (by fun_prop) h3).differentiableWithinAt

variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

/-- `D_{3/2} = ∑ ‖aₙ n^{−3/2}‖`. -/
noncomputable def D32 : ℝ := ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖

lemma D32_nonneg : 0 ≤ D32 (a := a) := tsum_nonneg fun _ => norm_nonneg _

include habs in
lemma norm_LSeries_le_D32 {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖LSeries (fun n => (a n : ℂ)) s‖ ≤ D32 (a := a) :=
  norm_LSeries_le (LSeriesSummable_of_one_lt habs (by simp; norm_num)) (by simpa using hs)

include habs in
/-- `‖E(s)‖ ≤ ‖s+3‖ Z₃ D_{3/2}` for `Re s ≥ 3/2`. -/
lemma Efun_right {Z : ℝ} (hZ0 : 0 ≤ Z) (hZ : ∀ w : ℂ, 3 ≤ w.re → ‖riemannZeta w‖ ≤ Z)
    {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖Efun d s‖ ≤ ‖s + 3‖ * (Z * D32 (a := a)) := by
  rw [Efun_eq_LSeries' d habs (by linarith), norm_mul, norm_mul]
  have h1 := norm_sub_one_le_norm_add_three (s := s) (by linarith)
  have h2 := hZ (2 * s) (by simp; linarith)
  have h3 := norm_LSeries_le_D32 habs hs
  calc ‖s - 1‖ * ‖riemannZeta (2 * s)‖ * ‖LSeries (fun n => (a n : ℂ)) s‖
      ≤ ‖s + 3‖ * Z * D32 (a := a) := by gcongr
    _ = _ := by ring

include habs in
lemma fA_right {Z : ℝ} (hZ0 : 0 ≤ Z) (hZ : ∀ w : ℂ, 3 ≤ w.re → ‖riemannZeta w‖ ≤ Z)
    {s : ℂ} (hs : s.re = 3 / 2) : ‖fA d s‖ ≤ Z * D32 (a := a) := by
  have hc : 4 - s = starRingEnd ℂ (s + 1) := by
    apply Complex.ext <;> simp [hs] <;> norm_num
  have hG0 := Complex.Gamma_ne_zero_of_re_pos (s := s + 1) (by simp [hs]; norm_num)
  have hrat : ‖Complex.Gamma (s + 1) * (Complex.Gamma (4 - s))⁻¹‖ = 1 := by
    rw [hc, norm_mul, norm_inv, norm_Gamma_conj, mul_inv_cancel₀ (norm_ne_zero_iff.2 hG0)]
  have h3 : 0 < ‖s + 3‖ := lt_of_lt_of_le one_pos (one_le_norm_add_three (by linarith))
  unfold fA
  rw [mul_assoc, norm_div, norm_mul, hrat, mul_one, div_le_iff₀ h3]
  have := Efun_right d habs hZ0 hZ (s := s) (by rw [hs])
  linarith

include habs in
lemma fA_left {Z : ℝ} (hZ0 : 0 ≤ Z) (hZ : ∀ w : ℂ, 3 ≤ w.re → ‖riemannZeta w‖ ≤ Z)
    {s : ℂ} (hs : s.re = -1 / 2) : ‖fA d s‖ ≤ 25 ^ 15 * (Z * D32 (a := a)) := by
  set w : ℂ := 1 - s with hw
  have hwre : w.re = 3 / 2 := by rw [hw]; simp [hs]; norm_num
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hE : Efun d s = (s - 1) * gam w * invGam s *
      (riemannZeta (2 * w) * LSeries (fun n => (a n : ℂ)) w) := by
    rw [Efun_eq d h0 h1, ← Lam_fe d s, ← hw, Lam_eq d habs (by rw [hwre]; norm_num)]; ring
  have hsplit : fA d s = ((s - 1) * gam (1 - s) * invGam s * Complex.Gamma (s + 1) *
      (Complex.Gamma (4 - s))⁻¹ / (s + 3)) *
      (riemannZeta (2 * w) * LSeries (fun n => (a n : ℂ)) w) := by
    unfold fA; rw [hE, hw]; ring
  rw [hsplit, norm_mul, norm_mul]
  have hr := ratioA_le hs
  have hz := hZ (2 * w) (by simp [hwre]; norm_num)
  have hD := norm_LSeries_le_D32 habs (s := w) (by rw [hwre])
  calc _ ≤ 25 ^ 15 * (Z * D32 (a := a)) := by gcongr

lemma fA_growth : ∃ K L : ℝ, ∀ s : ℂ, -1 / 2 < s.re → s.re < 3 / 2 → 1 ≤ |s.im| →
    ‖fA d s‖ ≤ K * Real.exp (L * |s.im|) := by
  obtain ⟨K, L, hKL⟩ := Efun_growth d
  obtain ⟨C, hC0, hC⟩ := exists_norm_inv_Gamma_le (A := 3 / 2) (by norm_num)
  have hcont : ContinuousOn Real.Gamma (Icc (1 / 2 : ℝ) (5 / 2)) := by
    intro x hx
    refine (Real.differentiableAt_Gamma (fun m => ?_)).continuousAt.continuousWithinAt
    intro h; have := hx.1; rw [h] at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
  obtain ⟨G, hG⟩ := (isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨|K| * |G| * C, |L| + π, fun s h1 h2 ht => ?_⟩
  have hE := hKL s (by linarith) (by linarith) ht
  have hE' : ‖Efun d s‖ ≤ |K| * Real.exp (|L| * |s.im|) :=
    hE.trans (mul_le_mul (le_abs_self K) (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
      (le_abs_self L) (abs_nonneg _))) (Real.exp_pos _).le (abs_nonneg K))
  have hg1 : ‖Complex.Gamma (s + 1)‖ ≤ |G| := by
    refine (norm_Gamma_le_Gamma_re (by simp; linarith)).trans ?_
    have := hG (s + 1).re ⟨by simp; linarith, by simp; linarith⟩
    rw [Real.norm_eq_abs] at this
    exact ((le_abs_self _).trans this).trans (le_abs_self G)
  have hg4 := hC (4 - s) (by simp; linarith) (by simpa using ht)
  simp only [sub_im, im_ofNat, zero_sub, abs_neg] at hg4
  have h3 : 1 ≤ ‖s + 3‖ := one_le_norm_add_three (by linarith)
  unfold fA
  rw [norm_div, norm_mul, norm_mul, div_le_iff₀ (by linarith)]
  have hexp : Real.exp ((|L| + π) * |s.im|) = Real.exp (|L| * |s.im|) * Real.exp (π * |s.im|) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖Efun d s‖ * ‖Complex.Gamma (s + 1)‖ * ‖(Complex.Gamma (4 - s))⁻¹‖
      ≤ (|K| * Real.exp (|L| * |s.im|)) * |G| * (C * Real.exp (π * |s.im|)) := by gcongr
    _ = |K| * |G| * C * Real.exp ((|L| + π) * |s.im|) := by rw [hexp]; ring
    _ ≤ |K| * |G| * C * Real.exp ((|L| + π) * |s.im|) * ‖s + 3‖ :=
        le_mul_of_one_le_right (by positivity) h3

include habs in
/-- **Step A.** `‖f_A‖ ≤ 25¹⁵ Z₃ D_{3/2}` on `−1/2 ≤ Re s ≤ 3/2`. -/
theorem fA_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖fA d s‖ ≤ C := by
  obtain ⟨Z, hZ0, hZ⟩ := exists_norm_zeta_le3
  obtain ⟨K, L, hKL⟩ := fA_growth d
  have hD0 := D32_nonneg (a := a)
  refine ⟨25 ^ 15 * (Z * D32 (a := a)), by positivity, fun s h1 h2 => ?_⟩
  refine pl_strip (a' := -1) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
    (differentiableOn_fA d) hKL (fun z hz => fA_left d habs hZ0 hZ hz)
    (fun z hz => (fA_right d habs hZ0 hZ hz).trans ?_) h1 h2
  have : 0 ≤ Z * D32 (a := a) := by positivity
  nlinarith

/-- **Step B.** On `Re s = σ_L` with `n = 3 − 2σ_L`, `0 ≤ σ_L`: `‖E(s)‖ ≤ C ‖s+3‖^{n+1}`. -/
lemma Efun_line {C : ℝ} (hC : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖fA d s‖ ≤ C)
    {σL : ℝ} {n : ℕ} (hn : (n : ℝ) = 3 - 2 * σL) (h0 : 0 ≤ σL) {s : ℂ} (hs : s.re = σL) :
    ‖Efun d s‖ ≤ C * ‖s + 3‖ ^ (n + 1) := by
  have hn3 : (n : ℝ) ≤ 3 := by linarith
  have hσ : σL ≤ 3 / 2 := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  set v : ℂ := starRingEnd ℂ (s + 1) with hv
  have hv0 : 0 < v.re := by simp [hv, hs]; linarith
  have h4 : 4 - s = v + n := by
    apply Complex.ext
    · simp [hv, hs]; linarith
    · simp [hv]
  have hG1 := Complex.Gamma_ne_zero_of_re_pos (s := s + 1) (by simp [hs]; linarith)
  have hG4 : Complex.Gamma (4 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp [hs]; linarith)
  have h3 : s + 3 ≠ 0 := by intro h; have := congrArg re h; simp [hs] at this; linarith
  have hE : Efun d s = fA d s * (Complex.Gamma (4 - s) * (Complex.Gamma (s + 1))⁻¹) * (s + 3) := by
    unfold fA; field_simp
  have hratio : ‖Complex.Gamma (4 - s) * (Complex.Gamma (s + 1))⁻¹‖ ≤ ‖s + 3‖ ^ n := by
    rw [h4, Gamma_add_nat hv0 n, hv, mul_assoc, norm_mul, norm_mul, norm_inv, norm_Gamma_conj,
      mul_inv_cancel₀ (norm_ne_zero_iff.2 hG1), mul_one, norm_prod]
    have : ‖s + 3‖ ^ n = ∏ _j ∈ Finset.range n, ‖s + 3‖ := by
      rw [Finset.prod_const, Finset.card_range]
    rw [this]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro j hj
    have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast (Finset.mem_range.1 hj)
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    apply norm_le_norm_of_sq
    simp [Complex.normSq_apply, hs]
    nlinarith
  have hfa := hC s (by rw [hs]; linarith) (by rw [hs]; exact hσ)
  rw [hE, norm_mul, norm_mul, pow_succ]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hfa
  calc ‖fA d s‖ * ‖Complex.Gamma (4 - s) * (Complex.Gamma (s + 1))⁻¹‖ * ‖s + 3‖
      ≤ C * ‖s + 3‖ ^ n * ‖s + 3‖ := by gcongr
    _ = _ := by ring

include habs in
/-- **Step C.** `‖E(s)‖ ≤ B ‖s+3‖^{n+1}` on `σ_L ≤ Re s ≤ 5/2`, where `n = 3 − 2σ_L`,
`0 ≤ σ_L < 3/2`. -/
theorem Efun_bound {σL : ℝ} {n : ℕ} (hn : (n : ℝ) = 3 - 2 * σL) (h0 : 0 ≤ σL)
    (h1 : σL < 3 / 2) : ∃ B : ℝ, ∀ s : ℂ, σL ≤ s.re → s.re ≤ 5 / 2 →
      ‖Efun d s‖ ≤ B * ‖s + 3‖ ^ (n + 1) := by
  obtain ⟨C, hC0, hC⟩ := fA_bound d habs
  obtain ⟨Z, hZ0, hZ⟩ := exists_norm_zeta_le3
  obtain ⟨K, L, hKL⟩ := Efun_growth d
  have hD0 := D32_nonneg (a := a)
  set B : ℝ := C + Z * D32 (a := a) with hB
  have hB0 : 0 ≤ Z * D32 (a := a) := by positivity
  refine ⟨B, fun s hs1 hs2 => ?_⟩
  have h3 : 1 ≤ ‖s + 3‖ := one_le_norm_add_three (by linarith)
  have h3p : 0 < ‖s + 3‖ ^ (n + 1) := by positivity
  rcases le_or_gt (3 / 2) s.re with hr | hr
  · -- absolute convergence
    have := Efun_right d habs hZ0 hZ hr
    calc ‖Efun d s‖ ≤ ‖s + 3‖ * (Z * D32 (a := a)) := this
      _ ≤ ‖s + 3‖ ^ (n + 1) * B := by
          gcongr
          · exact le_self_pow₀ h3 (by omega)
          · linarith
      _ = _ := by ring
  · -- Phragmén–Lindelöf for `g = E/(s+3)^{n+1}` on `[σ_L, 3/2]`
    set g : ℂ → ℂ := fun z => Efun d z / (z + 3) ^ (n + 1) with hg
    have hgd : DifferentiableOn ℂ g {z : ℂ | -1 < z.re} := by
      intro z hz
      simp only [mem_setOf_eq] at hz
      have : (z + 3) ^ (n + 1) ≠ 0 := by
        apply pow_ne_zero; intro h; have := congrArg re h; simp at this; linarith
      exact ((differentiable_Efun d z).div (by fun_prop) this).differentiableWithinAt
    have hgn : ∀ z : ℂ, -2 ≤ z.re → ‖g z‖ = ‖Efun d z‖ / ‖z + 3‖ ^ (n + 1) := by
      intro z _; simp [hg, norm_pow]
    have hgle : ∀ z : ℂ, -2 ≤ z.re → ‖g z‖ ≤ ‖Efun d z‖ := by
      intro z hz
      rw [hgn z hz]
      exact div_le_self (norm_nonneg _) (one_le_pow₀ (one_le_norm_add_three hz))
    have hgrow : ∀ z : ℂ, σL < z.re → z.re < 3 / 2 → 1 ≤ |z.im| →
        ‖g z‖ ≤ K * Real.exp (L * |z.im|) := fun z hz1 hz2 ht =>
      (hgle z (by linarith)).trans (hKL z (by linarith) (by linarith) ht)
    have hleft : ∀ z : ℂ, z.re = σL → ‖g z‖ ≤ B := by
      intro z hz
      rw [hgn z (by linarith)]
      have h3z : 0 < ‖z + 3‖ ^ (n + 1) := pow_pos (lt_of_lt_of_le one_pos
        (one_le_norm_add_three (by linarith))) _
      rw [div_le_iff₀ h3z]
      have := Efun_line d hC hn h0 hz
      nlinarith
    have hright : ∀ z : ℂ, z.re = 3 / 2 → ‖g z‖ ≤ B := by
      intro z hz
      rw [hgn z (by linarith)]
      have h3z : 1 ≤ ‖z + 3‖ := one_le_norm_add_three (by linarith)
      rw [div_le_iff₀ (by positivity)]
      have := Efun_right d habs hZ0 hZ (s := z) (by rw [hz])
      calc ‖Efun d z‖ ≤ ‖z + 3‖ * (Z * D32 (a := a)) := this
        _ ≤ ‖z + 3‖ ^ (n + 1) * B := by
            gcongr
            · exact le_self_pow₀ h3z (by omega)
            · linarith
        _ = _ := by ring
    have hgs := pl_strip (a' := -1) (by linarith) h1 (by linarith [Real.pi_gt_three]) hgd hgrow
      hleft hright hs1 hr.le
    rw [hgn s (by linarith), div_le_iff₀ h3p] at hgs
    exact hgs

end A

end RamanujanTau.RankinSharp
