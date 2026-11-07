/-
# The exact dual expansion of the Riesz means of `a(n)` (weight `2m`)

For `r ≥ 5` and every real `x`,

    W_r(x) = Σ_{n≤x} a(n)(x−n)^r = (r!/(2π)^r) Σ_n a(n) k_r(n, x),
    k_j(n, x) = (−1)^m (1/2π) ∫_ℝ z^{−(2m+1+j)} exp(2π(xz − n/z)) dt,   z = 1 + it   (`dual_W`).

The sign `(−1)^m = i^{−2m}` comes from the modular relation.  `kB_eq_Ik`:
`k_j(n,x) = (−1)^m (x/n)^{(2m+j)/2} I_{2m+j}(2π√(nx))`.  Generalizes `VoronoiTrunc/Dual.lean`.
-/
import RamanujanTau.VoronoiTruncGeneral.Data

set_option autoImplicit false

namespace RamanujanTau.VoronoiTruncGeneral

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.VoronoiTrunc (zl zl_re zl_im sq_norm_zl one_le_norm_zl zl_ne_zero continuous_zl
  re_inv_zl inv_norm_zl_pow_le gE kE norm_gE_le continuous_gE integrable_gE hasDerivAt_kE
  continuous_kE riesz_term It continuous_It fk Ik Ck Ck_nonneg lineInt_eq_Ik LineInt
  sqrt_mul_sqrt_div sqrt_mul_eq DkC_summable)

variable {m : ℕ} {a : ℕ → ℝ}

/-- `n^p e^{−na} ≤ p! (2/a)^p e^{−na/2}`. -/
lemma pow_mul_exp_le (p : ℕ) {b : ℝ} (hb : 0 < b) (n : ℕ) :
    (n : ℝ) ^ p * Real.exp (-(n * b)) ≤ (Nat.factorial p : ℝ) * (2 / b) ^ p * (Real.exp (-(b / 2))) ^ n := by
  have h := Real.pow_div_factorial_le_exp (x := n * b / 2) (by positivity) p
  have hf : (0 : ℝ) < Nat.factorial p := by exact_mod_cast Nat.factorial_pos p
  rw [div_le_iff₀ hf] at h
  have e1 : (n : ℝ) ^ p = (2 / b) ^ p * (n * b / 2) ^ p := by
    rw [← mul_pow]; congr 1; field_simp
  have e2 : (Real.exp (-(b / 2))) ^ n = Real.exp (-(n * b)) * Real.exp (n * b / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  rw [e1, e2]
  have : 0 ≤ (2 / b) ^ p * Real.exp (-(n * b)) := by positivity
  have h3 : (2 / b) ^ p * (n * b / 2) ^ p * Real.exp (-(n * b)) =
      ((2 / b) ^ p * Real.exp (-(n * b))) * (n * b / 2) ^ p := by ring
  rw [h3]
  calc ((2 / b) ^ p * Real.exp (-(n * b))) * (n * b / 2) ^ p
      ≤ ((2 / b) ^ p * Real.exp (-(n * b))) * (Real.exp (n * b / 2) * (Nat.factorial p : ℝ)) :=
        mul_le_mul_of_nonneg_left h this
    _ = _ := by ring

/-- `Σ_n |a(n)| e^{−nb} ≤ K b^{−(p+1)}` for `0 < b ≤ 2π`, if `|a(n)| ≤ A n^p`. -/
lemma coef_exp_sum {p : ℕ} {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ n : ℕ, |a n| ≤ A * (n : ℝ) ^ p)
    {b : ℝ} (hb : 0 < b) (hb' : b ≤ 2 * π) :
    Summable (fun n : ℕ => |a n| * Real.exp (-(n * b))) ∧
      ∑' n : ℕ, |a n| * Real.exp (-(n * b)) ≤
        A * (Nat.factorial p : ℝ) * 2 ^ (p + 1) * (1 + π) * (b ^ (p + 1))⁻¹ := by
  set q := Real.exp (-(b / 2)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hg : Summable fun n : ℕ => A * ((Nat.factorial p : ℝ) * (2 / b) ^ p * q ^ n) :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_left _).mul_left A
  have hbd : ∀ n : ℕ, |a n| * Real.exp (-(n * b)) ≤ A * ((Nat.factorial p : ℝ) * (2 / b) ^ p * q ^ n) := by
    intro n
    calc |a n| * Real.exp (-(n * b)) ≤ A * (n : ℝ) ^ p * Real.exp (-(n * b)) := by
          gcongr; exact hA n
      _ = A * ((n : ℝ) ^ p * Real.exp (-(n * b))) := by ring
      _ ≤ A * ((Nat.factorial p : ℝ) * (2 / b) ^ p * q ^ n) :=
          mul_le_mul_of_nonneg_left (pow_mul_exp_le p hb n) hA0
  have hs : Summable (fun n : ℕ => |a n| * Real.exp (-(n * b))) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hbd hg
  refine ⟨hs, (hs.tsum_le_tsum hbd hg).trans ?_⟩
  rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have h1 : b / 2 / (1 + b / 2) ≤ 1 - q := by
    have := Real.add_one_le_exp (b / 2)
    rw [hq, Real.exp_neg, div_le_iff₀ (by positivity)]
    have hpos := Real.exp_pos (b / 2)
    field_simp
    nlinarith
  have h2 : (1 - q)⁻¹ ≤ (1 + π) * (2 / b) := by
    have hpos : 0 < b / 2 / (1 + b / 2) := by positivity
    calc (1 - q)⁻¹ ≤ (b / 2 / (1 + b / 2))⁻¹ := inv_anti₀ hpos h1
      _ = (1 + b / 2) * (2 / b) := by field_simp
      _ ≤ (1 + π) * (2 / b) := by gcongr; linarith
  calc A * ((Nat.factorial p : ℝ) * (2 / b) ^ p * (1 - q)⁻¹)
      ≤ A * ((Nat.factorial p : ℝ) * (2 / b) ^ p * ((1 + π) * (2 / b))) := by gcongr
    _ = A * (Nat.factorial p : ℝ) * 2 ^ (p + 1) * (1 + π) * (b ^ (p + 1))⁻¹ := by
        rw [div_pow, pow_succ, pow_succ]; field_simp

/-- `‖gE M n y t‖` exactly. -/
lemma norm_gE (M n : ℕ) (x t : ℝ) :
    ‖gE M n x t‖ = (‖zl t‖ ^ M)⁻¹ * (Real.exp (2 * π * x) * Real.exp (-(n * (2 * π / (1 + t ^ 2))))) := by
  unfold gE
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_exp, ← Real.exp_add]
  congr 2
  have : (2 * π * ((x : ℂ) * zl t - (n : ℂ) * (zl t)⁻¹)).re = 2 * π * (x - n * (1 / (1 + t ^ 2))) := by
    simp only [mul_re, sub_re, ofReal_re, ofReal_im, zl_re, zl_im, natCast_re, natCast_im,
      re_inv_zl, zero_mul, sub_zero, mul_one]
    simp
  rw [this]; field_simp; ring

/-! ### The kernel -/

/-- The sign `(−1)^m`. -/
noncomputable def sg (m : ℕ) : ℂ := (-1 : ℂ) ^ m

lemma norm_sg (m : ℕ) : ‖sg m‖ = 1 := by simp [sg]

lemma sg_mul_sg (m : ℕ) : sg m * sg m = 1 := by
  unfold sg; rw [← mul_pow]; simp

/-- **The Schläfli kernel** `k_j(n,x) = (−1)^m (1/2π) ∫ z^{−(2m+1+j)} e^{2π(xz − n/z)} dt`. -/
noncomputable def kB (m j n : ℕ) (x : ℝ) : ℂ := sg m * kE (2 * m + 1 + j) n x

/-- The coefficients as complex numbers. -/
noncomputable def ac (a : ℕ → ℝ) (n : ℕ) : ℂ := (a n : ℂ)

lemma norm_ac (n : ℕ) : ‖ac a n‖ = |a n| := by
  unfold ac; rw [Complex.norm_real, Real.norm_eq_abs]

/-! ### The dual expansion -/

lemma WC_eq_tsum (hd : VData m a) {r : ℕ} (hr : 1 ≤ r) (x : ℝ) :
    TauPartialSumsSharp.WC (ac a) r x = ∑' n : ℕ, ac a n * (((max (x - n) 0) ^ r : ℝ) : ℂ) := by
  unfold TauPartialSumsSharp.WC
  symm
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊)]
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    have hx : 0 ≤ x := by
      by_contra h; rw [Nat.floor_of_nonpos (not_le.1 h).le] at h2; omega
    have : (n : ℝ) ≤ x := (Nat.cast_le.2 h2).trans (Nat.floor_le hx)
    rw [max_eq_left (by linarith)]; push_cast; rfl
  · intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [ac, hd.zero]
    · have : ⌊x⌋₊ < n := by
        by_contra h; exact hn (Finset.mem_Icc.2 ⟨hpos, not_lt.1 h⟩)
      have hxn : x < n := by
        rcases le_or_gt 0 x with hx | hx
        · exact (Nat.floor_lt hx).1 this
        · linarith [Nat.cast_nonneg (α := ℝ) n]
      rw [max_eq_right (by linarith), zero_pow (by omega)]; simp

/-- The integrand of the first interchange. -/
noncomputable def F1 (a : ℕ → ℝ) (r : ℕ) (x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ac a n * (cexp (((2 * π * (x - n) : ℝ) : ℂ) * zl t) * ((zl t) ^ (r + 1))⁻¹)

/-- The integrand of the second interchange. -/
noncomputable def G1 (m : ℕ) (a : ℕ → ℝ) (r : ℕ) (x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ac a n * gE (2 * m + 1 + r) n x t

lemma norm_F1_le {r : ℕ} (hr : 1 ≤ r) (x : ℝ) (n : ℕ) (t : ℝ) :
    ‖F1 a r x n t‖ ≤ |a n| * Real.exp (-(n * (2 * π))) * Real.exp (2 * π * x) * (1 + t ^ 2)⁻¹ := by
  unfold F1
  rw [norm_mul, norm_mul, Complex.norm_exp, norm_inv, norm_pow, norm_ac]
  have hre : (((2 * π * (x - n) : ℝ) : ℂ) * zl t).re = 2 * π * (x - n) := by
    simp [mul_re, zl_re, zl_im]
  rw [hre]
  have h1 := inv_norm_zl_pow_le (m := r + 1) (by omega) t
  have e : Real.exp (2 * π * (x - n)) = Real.exp (-(n * (2 * π))) * Real.exp (2 * π * x) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have : 0 ≤ |a n| * (Real.exp (-(n * (2 * π))) * Real.exp (2 * π * x)) := by positivity
  calc |a n| * (Real.exp (-(n * (2 * π))) * Real.exp (2 * π * x) * (‖zl t‖ ^ (r + 1))⁻¹)
      ≤ |a n| * (Real.exp (-(n * (2 * π))) * Real.exp (2 * π * x) * (1 + t ^ 2)⁻¹) := by gcongr
    _ = _ := by ring

lemma continuous_F1 (r : ℕ) (x : ℝ) (n : ℕ) : Continuous (F1 a r x n) := by
  unfold F1
  have hz := continuous_zl
  exact continuous_const.mul ((Complex.continuous_exp.comp (continuous_const.mul hz)).mul
    ((hz.pow _).inv₀ fun t => pow_ne_zero _ (zl_ne_zero t)))

lemma integrable_F1 {r : ℕ} (hr : 1 ≤ r) (x : ℝ) (n : ℕ) : Integrable (F1 a r x n) :=
  Integrable.mono' (integrable_inv_one_add_sq.const_mul _) (continuous_F1 r x n).aestronglyMeasurable
    (Eventually.of_forall (norm_F1_le hr x n))

lemma summable_F1 (hd : VData m a) {r : ℕ} (hr : 1 ≤ r) (x : ℝ) :
    Summable fun n => ∫ t, ‖F1 a r x n t‖ := by
  obtain ⟨A, hA0, hA⟩ := hd.abs_le
  obtain ⟨hs, -⟩ := coef_exp_sum hA0 hA (b := 2 * π) (by positivity) le_rfl
  have hb : ∀ n : ℕ, ∫ t, ‖F1 a r x n t‖ ≤ (|a n| * Real.exp (-(n * (2 * π)))) * (Real.exp (2 * π * x) * π) := by
    intro n
    calc ∫ t, ‖F1 a r x n t‖ ≤ ∫ t, |a n| * Real.exp (-(n * (2 * π))) * Real.exp (2 * π * x) * (1 + t ^ 2)⁻¹ :=
          integral_mono (integrable_F1 hr x n).norm (integrable_inv_one_add_sq.const_mul _)
            (norm_F1_le hr x n)
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]; ring
  exact Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hb (hs.mul_right _)

lemma tsum_F1 (r : ℕ) (x t : ℝ) :
    ∑' n, F1 a r x n t = cexp (2 * π * x * zl t) * ((zl t) ^ (r + 1))⁻¹ * Dq a (zl t) := by
  unfold Dq F1 ac
  rw [← tsum_mul_left]
  congr 1; funext n
  have : cexp (((2 * π * (x - n) : ℝ) : ℂ) * zl t) = cexp (2 * π * x * zl t) * cexp (-2 * π * n * zl t) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [this]; ring

lemma modular_step (hd : VData m a) (r : ℕ) (x t : ℝ) :
    cexp (2 * π * x * zl t) * ((zl t) ^ (r + 1))⁻¹ * Dq a (zl t) = sg m * ∑' n, G1 m a r x n t := by
  have hre : 0 < (zl t).re := by rw [zl_re]; norm_num
  rw [hd.modular _ hre]
  unfold Dq G1 gE ac sg
  have e : ∀ n : ℕ, (a n : ℂ) * (((zl t) ^ (2 * m + 1 + r))⁻¹ * cexp (2 * π * (x * zl t - n * (zl t)⁻¹))) =
      (cexp (2 * π * x * zl t) * ((zl t) ^ (r + 1))⁻¹ * ((zl t) ^ (2 * m))⁻¹) *
        ((a n : ℂ) * cexp (-2 * π * n * (zl t)⁻¹)) := by
    intro n
    rw [show 2 * m + 1 + r = 2 * m + (r + 1) by ring, pow_add, mul_inv]
    have e : cexp (2 * π * (x * zl t - n * (zl t)⁻¹)) =
        cexp (2 * π * x * zl t) * cexp (-2 * π * n * (zl t)⁻¹) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [e]; ring
  simp_rw [e]
  rw [tsum_mul_left]; ring

lemma norm_G1 (r : ℕ) (x : ℝ) (n : ℕ) (t : ℝ) :
    ‖G1 m a r x n t‖ = (‖zl t‖ ^ (2 * m + 1 + r))⁻¹ * Real.exp (2 * π * x) *
      (|a n| * Real.exp (-(n * (2 * π / (1 + t ^ 2))))) := by
  unfold G1; rw [norm_mul, norm_gE, norm_ac]; ring

lemma integrable_G1 {r : ℕ} (hr : 1 ≤ r) (x : ℝ) (n : ℕ) : Integrable (G1 m a r x n) := by
  unfold G1; exact (integrable_gE (by omega) n x).const_mul _

lemma summable_G1 (hd : VData m a) {r : ℕ} (hr : 5 ≤ r) (x : ℝ) :
    Summable fun n => ∫ t, ‖G1 m a r x n t‖ := by
  obtain ⟨A, hA0, hA⟩ := hd.abs_le
  set K := A * (Nat.factorial (m + 1) : ℝ) * 2 ^ (m + 1 + 1) * (1 + π) with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ t : ℝ, Summable (fun n : ℕ => ‖G1 m a r x n t‖) ∧
      ∑' n, ‖G1 m a r x n t‖ ≤ Real.exp (2 * π * x) * K * ((2 * π) ^ (m + 1 + 1))⁻¹ * (1 + t ^ 2)⁻¹ := by
    intro t
    have ha : 0 < 2 * π / (1 + t ^ 2) := by positivity
    have ha' : 2 * π / (1 + t ^ 2) ≤ 2 * π := div_le_self (by positivity) (by nlinarith [sq_nonneg t])
    obtain ⟨hs, hle⟩ := coef_exp_sum hA0 hA ha ha'
    simp_rw [norm_G1]
    refine ⟨hs.mul_left _, ?_⟩
    rw [tsum_mul_left]
    have hz : (‖zl t‖ ^ (2 * m + 1 + r))⁻¹ ≤ ((1 + t ^ 2) ^ (m + 1 + 2))⁻¹ := by
      apply inv_anti₀ (by positivity)
      rw [← sq_norm_zl, ← pow_mul]
      exact pow_le_pow_right₀ (one_le_norm_zl t) (by omega)
    have ha8 : ((2 * π / (1 + t ^ 2)) ^ (m + 1 + 1))⁻¹ = (1 + t ^ 2) ^ (m + 1 + 1) * ((2 * π) ^ (m + 1 + 1))⁻¹ := by
      rw [div_pow, inv_div]; field_simp
    have hle' : ∑' n, |a n| * Real.exp (-(n * (2 * π / (1 + t ^ 2)))) ≤
        K * ((2 * π / (1 + t ^ 2)) ^ (m + 1 + 1))⁻¹ := by
      rw [hK]; exact hle
    calc (‖zl t‖ ^ (2 * m + 1 + r))⁻¹ * Real.exp (2 * π * x) *
          ∑' n, |a n| * Real.exp (-(n * (2 * π / (1 + t ^ 2))))
        ≤ ((1 + t ^ 2) ^ (m + 1 + 2))⁻¹ * Real.exp (2 * π * x) *
          (K * ((2 * π / (1 + t ^ 2)) ^ (m + 1 + 1))⁻¹) := by gcongr
      _ = Real.exp (2 * π * x) * K * ((2 * π) ^ (m + 1 + 1))⁻¹ * (1 + t ^ 2)⁻¹ := by
          rw [ha8, show m + 1 + 2 = (m + 1 + 1) + 1 by ring, pow_succ]; field_simp
  set C := Real.exp (2 * π * x) * K * ((2 * π) ^ (m + 1 + 1))⁻¹
  have hC : ∀ N : ℕ, ∑ n ∈ Finset.range N, ∫ t, ‖G1 m a r x n t‖ ≤ C * π := by
    intro N
    rw [← integral_finsetSum _ (fun n _ => (integrable_G1 (by omega) x n).norm)]
    calc ∫ t, ∑ n ∈ Finset.range N, ‖G1 m a r x n t‖ ≤ ∫ t, C * (1 + t ^ 2)⁻¹ := by
          refine integral_mono (integrable_finsetSum _ (fun n _ => (integrable_G1 (by omega) x n).norm))
            (integrable_inv_one_add_sq.const_mul _) (fun t => ?_)
          exact ((hpt t).1.sum_le_tsum _ (fun n _ => norm_nonneg _)).trans (hpt t).2
      _ = C * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  exact summable_of_sum_range_le (fun n => integral_nonneg fun t => norm_nonneg _) hC

/-- **The dual expansion** of the Riesz mean `W_r` (`r ≥ 5`). -/
theorem dual_W (hd : VData m a) {r : ℕ} (hr : 5 ≤ r) (x : ℝ) :
    HasSum (fun n => ac a n * kB m r n x)
      ((((2 * π) ^ r / (Nat.factorial r : ℝ)) : ℝ) * TauPartialSumsSharp.WC (ac a) r x) := by
  have hr1 : 1 ≤ r := by omega
  have h2 := hasSum_integral_of_summable_integral_norm (integrable_G1 (m := m) (a := a) hr1 x)
    (summable_G1 hd hr x)
  have h2' := h2.mul_left (sg m * ((1 / (2 * π) : ℝ) : ℂ))
  have hterm : ∀ n, sg m * ((1 / (2 * π) : ℝ) : ℂ) * ∫ t, G1 m a r x n t = ac a n * kB m r n x := by
    intro n; unfold G1 kB kE; rw [integral_const_mul]; ring
  simp_rw [hterm] at h2'
  convert h2' using 1
  have hF : ∑' n, ∫ t, F1 a r x n t = ∫ t, ∑' n, F1 a r x n t :=
    integral_tsum_of_summable_integral_norm (integrable_F1 hr1 x) (summable_F1 hd hr1 x)
  have hval : ((((2 * π) ^ r / (Nat.factorial r : ℝ)) : ℝ) : ℂ) * TauPartialSumsSharp.WC (ac a) r x =
      ((1 / (2 * π) : ℝ) : ℂ) * ∑' n, ∫ t, F1 a r x n t := by
    rw [WC_eq_tsum hd hr1, ← tsum_mul_left, ← tsum_mul_left]
    congr 1; funext n
    unfold F1
    rw [integral_const_mul, mul_left_comm, riesz_term hr1 x n]
    ring
  rw [hval, hF, ← integral_const_mul, ← integral_const_mul]
  congr 1; funext t
  rw [tsum_F1, modular_step hd]
  ring

/-! ### The kernel family -/

lemma kB_eq_kE (j n : ℕ) (x : ℝ) : kB m j n x = sg m * kE (2 * m + 1 + j) n x := rfl

lemma continuous_kB (hm : 1 ≤ m) (j n : ℕ) : Continuous (kB m j n) := by
  have e : 2 * m + 1 + j = (2 * m + j) + 1 := by omega
  have : kB m j n = fun x => sg m * kE ((2 * m + j) + 1) n x := by funext x; rw [kB_eq_kE, e]
  rw [this]
  exact continuous_const.mul (continuous_kE (by omega) n)

/-- `k_{j+1}(n, y+h) − k_{j+1}(n, y) = 2π ∫₀^h k_j(n, y+s) ds`. -/
theorem kB_rel (hm : 1 ≤ m) (j n : ℕ) (y h : ℝ) :
    kB m (j + 1) n (y + h) - kB m (j + 1) n y = 2 * π * ∫ s in (0 : ℝ)..h, kB m j n (y + s) := by
  have hd : ∀ x ∈ Set.uIcc y (y + h), HasDerivAt (kB m (j + 1) n) (2 * π * kB m j n x) x := by
    intro x _
    have : kB m (j + 1) n = fun x => sg m * kE ((2 * m + 1 + j) + 1) n x := by
      funext x; rw [kB_eq_kE]; rfl
    rw [this]
    have := (hasDerivAt_kE (m := 2 * m + 1 + j) (by omega) n x).const_mul (sg m)
    convert this using 1
    rw [kB_eq_kE]; ring
  have hc : Continuous fun x => 2 * π * kB m j n x := continuous_const.mul (continuous_kB hm j n)
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_comp_add_left (fun x => kB m j n x) y]
  simp

/-- **Scaling**: `k_j(n,x) = (−1)^m (x/n)^{(2m+j)/2} I_{2m+j}(2π√(nx))`. -/
theorem kB_eq_Ik (hm : 1 ≤ m) (j : ℕ) {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    kB m j n x = sg m * (((√(x / n)) ^ (2 * m + j) * Ik (2 * m + j) (2 * π * √(n * x)) : ℝ) : ℂ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set c := √(x / n) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  set L := 2 * π * √(n * x) with hL
  have hLc : L * c = 2 * π * x := by rw [hL, mul_assoc, sqrt_mul_sqrt_div hn0 hx]
  have hLn : L = 2 * π * n * c := by rw [hL, sqrt_mul_eq hn0 hx]; ring
  have hline := lineInt_eq_Ik (ν := 2 * m + j) (by omega) (L := L) (by positivity) hc0
  unfold LineInt at hline
  set g : ℝ → ℂ := fun u => fk (2 * m + j) L ((c : ℂ) + u * I) with hg
  have hsub := Measure.integral_comp_mul_left g c
  have hgc : ∀ t : ℝ, g (c * t) = ((c ^ (2 * m + 1 + j) : ℝ) : ℂ)⁻¹ * gE (2 * m + 1 + j) n x t := by
    intro t
    simp only [hg, fk, gE, zl]
    have hz : (1 : ℂ) + t * I ≠ 0 := zl_ne_zero t
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    have e1 : (c : ℂ) + ((c * t : ℝ) : ℂ) * I = (c : ℂ) * (1 + t * I) := by push_cast; ring
    rw [e1]
    have e2 : (L : ℂ) * ((c : ℂ) * (1 + t * I) - ((c : ℂ) * (1 + t * I))⁻¹) =
        2 * π * ((x : ℂ) * (1 + t * I) - (n : ℂ) * (1 + t * I)⁻¹) := by
      have h1 : (L : ℂ) * c = 2 * π * x := by exact_mod_cast hLc
      have h2 : (L : ℂ) = 2 * π * n * c := by exact_mod_cast hLn
      have h3 : (L : ℂ) * (c : ℂ)⁻¹ = 2 * π * n := by rw [h2]; field_simp
      calc (L : ℂ) * ((c : ℂ) * (1 + t * I) - ((c : ℂ) * (1 + t * I))⁻¹)
          = ((L : ℂ) * c) * (1 + t * I) - ((L : ℂ) * (c : ℂ)⁻¹) * (1 + t * I)⁻¹ := by
            rw [mul_inv]; ring
        _ = _ := by rw [h1, h3]; ring
    rw [e2, show 2 * m + j + 1 = 2 * m + 1 + j by ring, mul_pow]
    push_cast
    rw [mul_inv]; ring
  have hint : ∫ t, g (c * t) = ((c ^ (2 * m + 1 + j) : ℝ) : ℂ)⁻¹ * ∫ t, gE (2 * m + 1 + j) n x t := by
    simp_rw [hgc]; rw [integral_const_mul]
  rw [hint, abs_inv, abs_of_pos hc0, Complex.real_smul] at hsub
  rw [kB_eq_kE]
  unfold kE
  have hci : ((c ^ (2 * m + 1 + j) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hc0 _).ne'
  have hint2 : ∫ t, gE (2 * m + 1 + j) n x t =
      ((c ^ (2 * m + 1 + j) : ℝ) : ℂ) * (((c⁻¹ : ℝ) : ℂ) * ∫ u, g u) := by
    rw [← hsub]; field_simp
  have hl : ((1 / (2 * π) : ℝ) : ℂ) * ∫ u, g u = (Ik (2 * m + j) L : ℂ) := hline
  rw [hint2]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  congr 1
  calc ((1 / (2 * π) : ℝ) : ℂ) * (((c ^ (2 * m + 1 + j) : ℝ) : ℂ) * (((c⁻¹ : ℝ) : ℂ) * ∫ u, g u))
      = ((c ^ (2 * m + 1 + j) : ℝ) : ℂ) * ((c⁻¹ : ℝ) : ℂ) * (((1 / (2 * π) : ℝ) : ℂ) * ∫ u, g u) := by ring
    _ = _ := by
        rw [hl]; push_cast
        rw [show 2 * m + 1 + j = (2 * m + j) + 1 by omega, pow_succ]
        field_simp

/-! ### The smoothed partial sum -/

/-- `Δ_h^r k_r(n,·)(x) = (2π)^r It_h^r k_0(n,·)(x)`. -/
theorem DkC_kB (hm : 1 ≤ m) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) : ∀ (r : ℕ) (x : ℝ), 0 < x →
    TauPartialSumsSharp.DkC h r (kB m r n) x = (2 * π : ℂ) ^ r * It h r (kB m 0 n) x := by
  intro r
  induction r with
  | zero => intro x _; simp [TauPartialSumsSharp.DkC, It]
  | succ r ih =>
    intro x hx
    simp only [TauPartialSumsSharp.DkC]
    have e : (fun y => kB m (r + 1) n (y + h) - kB m (r + 1) n y) =
        fun y => (2 * π : ℂ) * ∫ s in (0 : ℝ)..h, kB m r n (y + s) := by
      funext y; exact kB_rel hm r n y h
    rw [e, TauPartialSumsSharp.DkC_const_mul,
      TauPartialSumsSharp.DkC_integral_on h hh r _ (continuous_kB hm r n).continuousOn x hx]
    have e2 : ∫ s in (0 : ℝ)..h, TauPartialSumsSharp.DkC h r (kB m r n) (x + s) =
        ∫ s in (0 : ℝ)..h, (2 * π : ℂ) ^ r * It h r (kB m 0 n) (x + s) := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [uIcc_of_le hh] at hs
      exact ih (x + s) (by linarith [hs.1])
    rw [e2, intervalIntegral.integral_const_mul]
    show _ = (2 * π : ℂ) ^ (r + 1) * ∫ s in (0 : ℝ)..h, It h r (kB m 0 n) (x + s)
    ring

/-- **The smoothed partial sum**: `Δ_h^r W_r(x) = r! Σ_n a(n) It_h^r k_0(n,·)(x)`. -/
theorem DkC_WC_eq (hd : VData m a) {r : ℕ} (hr : 5 ≤ r) {h : ℝ} (hh : 0 ≤ h) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n => ac a n * It h r (kB m 0 n) x)
      (((Nat.factorial r : ℝ) : ℂ)⁻¹ * TauPartialSumsSharp.DkC h r (TauPartialSumsSharp.WC (ac a) r) x) := by
  set c : ℂ := ((((2 * π) ^ r / (Nat.factorial r : ℝ)) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact Complex.ofReal_ne_zero.2 (div_pos (pow_pos (by positivity) r)
      (by exact_mod_cast Nat.factorial_pos r)).ne'
  have hW : TauPartialSumsSharp.WC (ac a) r = fun y => c⁻¹ * ∑' n, ac a n * kB m r n y := by
    funext y
    rw [(dual_W hd hr y).tsum_eq, ← hc]; field_simp
  have hs : ∀ y, Summable fun n => ac a n * kB m r n y := fun y => (dual_W hd hr y).summable
  rw [hW, TauPartialSumsSharp.DkC_const_mul,
    TauPartialSumsSharp.DkC_tsum_on h hh r _ x (fun y _ => hs y)]
  have hsum : Summable fun n => TauPartialSumsSharp.DkC h r (fun y => ac a n * kB m r n y) x :=
    DkC_summable h hh r _ x (fun y _ => hs y)
  have e : ∀ n, TauPartialSumsSharp.DkC h r (fun y => ac a n * kB m r n y) x =
      (2 * π : ℂ) ^ r * (ac a n * It h r (kB m 0 n) x) := by
    intro n
    rw [TauPartialSumsSharp.DkC_const_mul, DkC_kB hd.one_le hh n r x hx]; ring
  simp_rw [e] at hsum ⊢
  have hpi : (2 * π : ℂ) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0))
  have hsum' : Summable fun n => ac a n * It h r (kB m 0 n) x := by
    have := hsum.mul_left ((2 * π : ℂ) ^ r)⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ hpi] using this
  rw [tsum_mul_left]
  have e3 : ((Nat.factorial r : ℝ) : ℂ)⁻¹ * (c⁻¹ * ((2 * π : ℂ) ^ r * ∑' n, ac a n * It h r (kB m 0 n) x)) =
      ∑' n, ac a n * It h r (kB m 0 n) x := by
    have hf' : ((Nat.factorial r : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
    rw [hc]; push_cast; field_simp
  rw [e3]; exact hsum'.hasSum

end RamanujanTau.VoronoiTruncGeneral
