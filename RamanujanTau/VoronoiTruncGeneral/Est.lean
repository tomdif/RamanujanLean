/-
# Estimates feeding the `L²` assembly (weight `2m`)

* `Ik_asymp_even`: `|(−1)^m I_{2m}(L) − cos(2L − π/4)/√(πL)| ≤ C_{2m}/(πL)` — the phase:
  `i^{−(2m+1)}(−1+i) = (−1)^m(1+i)`, so the sign `(−1)^m` of the Bessel asymptotic
  `J_{2m}(2L) ~ cos(2L − mπ − π/4)/√(πL)` cancels the sign `(−1)^m = i^{−2m}` of the modular relation;
* `kB_zero_sub_main`: `|k₀(n,y) − y^{m−1/4} n^{−(m+1/4)} cos(4π√n√y − π/4)/(π√2)| ≤ C y^{m−1/2} n^{−(m+1/2)}`;
* `norm_kB_top_le`: `‖k₁₂(n,y)‖ ≤ C y^{m+6} n^{−(m+6)} (ny)^{−1/4}`;
* Rankin-trick sums for `Σ|a(n)| n^{−α}`; a Lipschitz bound for the main term;
* `integral_short_sq_le`: `∫_X^{2X} (Σ_{x<n≤x+H} |a(n)|)² ≤ (H+1) H Σ_{n≤3X} a(n)²`.
-/
import RamanujanTau.VoronoiTruncGeneral.Dual
import RamanujanTau.VoronoiTruncGeneral.MeanValue

set_option autoImplicit false

namespace RamanujanTau.VoronoiTruncGeneral

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.VoronoiTrunc (Ik Ak Ck Ck_nonneg Ak_asymp Ik_bound sqrt_identity)

variable {m : ℕ} {a : ℕ → ℝ}

/-! ### The phase for even index -/

lemma lead_even (m : ℕ) (L : ℝ) :
    (-1 + I) * (I ^ (2 * m + 1))⁻¹ * cexp (2 * I * L) =
      (((-1 : ℝ) ^ m : ℝ) : ℂ) * ((1 + I) * cexp (2 * I * L)) := by
  have : I ^ (2 * m + 1) = (-1 : ℂ) ^ m * I := by rw [pow_succ, pow_mul, I_sq]
  rw [this, mul_inv, inv_I]
  have h1 : ((-1 : ℂ) ^ m)⁻¹ = (-1 : ℂ) ^ m := by
    rw [← inv_pow, inv_neg, inv_one]
  rw [h1]; push_cast
  ring_nf; rw [I_sq]; ring

/-- **Phase asymptotic for even index**: `|(−1)^m I_{2m}(L) − cos(2L − π/4)/√(πL)| ≤ C_{2m}/(πL)`. -/
theorem Ik_asymp_even (hm : 1 ≤ m) {L : ℝ} (hL : 0 < L) :
    |(-1 : ℝ) ^ m * Ik (2 * m) L - Real.cos (2 * L - π / 4) / √(π * L)| ≤ Ck (2 * m) / (π * L) := by
  have h := Ak_asymp (ν := 2 * m) (by omega) hL
  rw [lead_even] at h
  set ε : ℝ := (-1 : ℝ) ^ m with hε
  have hεε : ε * ε = 1 := by rw [hε, ← mul_pow]; norm_num
  have hεn : ‖(ε : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, hε, abs_pow, abs_neg, abs_one, one_pow]
  set M : ℂ := (1 + I) * cexp (2 * I * L) * (√(π / (2 * L)) : ℂ)
  have hMim : M.im / π = Real.cos (2 * L - π / 4) / √(π * L) := by
    have hM : M.im = (Real.cos (2 * L) + Real.sin (2 * L)) * √(π / (2 * L)) := by
      simp only [M]
      rw [show (2 * I * (L : ℂ)) = ((2 * L : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
      simp only [mul_im, mul_re, add_re, add_im, one_re, one_im, I_re, I_im, ofReal_re, ofReal_im,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    rw [hM, mul_div_assoc, sqrt_identity hL, Real.cos_sub, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    ring
  have hIk : ε * Ik (2 * m) L - Real.cos (2 * L - π / 4) / √(π * L) =
      ((ε : ℂ) * Ak (2 * m) L - M).im / π := by
    unfold Ik; rw [← hMim, sub_im, sub_div, Complex.im_ofReal_mul]
    ring
  have hnorm : ‖(ε : ℂ) * Ak (2 * m) L - M‖ =
      ‖Ak (2 * m) L - (ε : ℂ) * ((1 + I) * cexp (2 * I * L)) * (√(π / (2 * L)) : ℂ)‖ := by
    have e : (ε : ℂ) * Ak (2 * m) L - M =
        (ε : ℂ) * (Ak (2 * m) L - (ε : ℂ) * ((1 + I) * cexp (2 * I * L)) * (√(π / (2 * L)) : ℂ)) := by
      have hεc : (ε : ℂ) * (ε : ℂ) = 1 := by exact_mod_cast hεε
      simp only [M]
      linear_combination ((1 + I) * cexp (2 * I * L) * (√(π / (2 * L)) : ℂ)) * hεc
    rw [e, norm_mul, hεn, one_mul]
  rw [hIk, abs_div, abs_of_pos Real.pi_pos, div_le_div_iff₀ Real.pi_pos (by positivity)]
  have := (abs_im_le_norm ((ε : ℂ) * Ak (2 * m) L - M)).trans (hnorm ▸ h)
  have hp := Real.pi_pos
  calc |((ε : ℂ) * Ak (2 * m) L - M).im| * (π * L) ≤ Ck (2 * m) / L * (π * L) := by gcongr
    _ = Ck (2 * m) * π := by field_simp

/-! ### The main term -/

/-- The main term `m(n,y) = y^{m−1/4} n^{−(m+1/4)} cos(4π√n√y − π/4)/(π√2)`. -/
noncomputable def mK (m n : ℕ) (y : ℝ) : ℝ :=
  y ^ ((m : ℝ) - 1 / 4) * (n : ℝ) ^ (-((m : ℝ) + 1 / 4)) / (π * √2) * Real.cos (th n y)

lemma continuous_mK (hm : 1 ≤ m) (n : ℕ) : Continuous (mK m n) := by
  unfold mK th
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have : Continuous fun y : ℝ => y ^ ((m : ℝ) - 1 / 4) := Real.continuous_rpow_const (by linarith)
  fun_prop

/-- `(y/n)^m / √(π · 2π√(ny)) = y^{m−1/4} n^{−(m+1/4)}/(π√2)`. -/
lemma rpow_identity (m : ℕ) {n y : ℝ} (hn : 0 < n) (hy : 0 < y) :
    (y / n) ^ m / √(π * (2 * π * √(n * y))) =
      y ^ ((m : ℝ) - 1 / 4) * n ^ (-((m : ℝ) + 1 / 4)) / (π * √2) := by
  have hp := Real.pi_pos
  have e1 : √(π * (2 * π * √(n * y))) = π * √2 * (n ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ)) := by
    rw [show π * (2 * π * √(n * y)) = (π * √2) ^ 2 * √(n * y) by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity),
      Real.mul_rpow hn.le hy.le]
    norm_num
  rw [e1]
  have h1 : y ^ ((m : ℝ) - 1 / 4) = y ^ (m : ℝ) * (y ^ (1 / 4 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hy.le, ← Real.rpow_add hy]; ring_nf
  have h2 : n ^ (-((m : ℝ) + 1 / 4)) = (n ^ (m : ℝ))⁻¹ * (n ^ (1 / 4 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hn.le, ← Real.rpow_neg hn.le, ← Real.rpow_add hn]; ring_nf
  rw [h1, h2, div_pow, Real.rpow_natCast, Real.rpow_natCast]
  have : 0 < n ^ (1 / 4 : ℝ) := by positivity
  have : 0 < y ^ (1 / 4 : ℝ) := by positivity
  have : 0 < n ^ m := by positivity
  have : (0 : ℝ) < √2 := by positivity
  field_simp

lemma sqrt_mul_nat (n : ℕ) (y : ℝ) : √((n : ℝ) * y) = √(n : ℝ) * √y :=
  Real.sqrt_mul (Nat.cast_nonneg n) y

/-- The constant in `kB_zero_sub_main`. -/
noncomputable def CK (m : ℕ) : ℝ := Ck (2 * m) / (2 * π ^ 2)

lemma CK_nonneg (m : ℕ) : 0 ≤ CK m := by unfold CK; have := Ck_nonneg (2 * m); positivity

lemma sg_eq_real (m : ℕ) : sg m = (((-1 : ℝ) ^ m : ℝ) : ℂ) := by unfold sg; push_cast; rfl

/-- **Kernel → main term**: `‖k₀(n,y) − m(n,y)‖ ≤ C_K y^{m−1/2} n^{−(m+1/2)}`. -/
theorem kB_zero_sub_main (hm : 1 ≤ m) {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : 1 ≤ y) :
    ‖kB m 0 n y - (mK m n y : ℂ)‖ ≤ CK m * y ^ ((m : ℝ) - 1 / 2) * (n : ℝ) ^ (-((m : ℝ) + 1 / 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hy0 : 0 < y := by linarith
  rw [kB_eq_Ik hm 0 hn hy0, sg_eq_real, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  set L := 2 * π * √((n : ℝ) * y) with hL
  have hL0 : 0 < L := by positivity
  have hA := Ik_asymp_even hm hL0
  have h12 : (√(y / n)) ^ (2 * m + 0) = (y / n) ^ m := by
    rw [add_zero, pow_mul, Real.sq_sqrt (by positivity)]
  rw [h12]
  simp only [add_zero]
  have hth : th n y = 2 * L - π / 4 := by unfold th; rw [hL, sqrt_mul_nat]; ring
  have hmain : mK m n y = (y / n) ^ m * (Real.cos (2 * L - π / 4) / √(π * L)) := by
    unfold mK
    rw [hth, ← rpow_identity m hn0 hy0, ← hL]; ring
  rw [hmain, show (-1 : ℝ) ^ m * ((y / n) ^ m * Ik (2 * m) L) -
      (y / n) ^ m * (Real.cos (2 * L - π / 4) / √(π * L)) =
      (y / n) ^ m * ((-1 : ℝ) ^ m * Ik (2 * m) L - Real.cos (2 * L - π / 4) / √(π * L)) by ring,
    abs_mul, abs_of_nonneg (by positivity)]
  calc (y / n) ^ m * |(-1 : ℝ) ^ m * Ik (2 * m) L - Real.cos (2 * L - π / 4) / √(π * L)|
      ≤ (y / n) ^ m * (Ck (2 * m) / (π * L)) := by gcongr
    _ = CK m * y ^ ((m : ℝ) - 1 / 2) * (n : ℝ) ^ (-((m : ℝ) + 1 / 2)) := by
        unfold CK
        rw [hL, Real.sqrt_mul hn0.le]
        have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
        have hsy : 0 < √y := Real.sqrt_pos.2 hy0
        have e1 : y ^ ((m : ℝ) - 1 / 2) = y ^ m / √y := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_sub hy0]
        have e2 : (n : ℝ) ^ (-((m : ℝ) + 1 / 2)) = 1 / ((n : ℝ) ^ m * √(n : ℝ)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hn0, Real.rpow_neg hn0.le]
          rw [one_div]; norm_num
        rw [e1, e2, div_pow]
        field_simp

/-- The constant in `norm_kB_top_le`. -/
noncomputable def CT (m : ℕ) : ℝ := (2 * √π + Ck (2 * m + 12)) / √(2 * π)

lemma CT_nonneg (m : ℕ) : 0 ≤ CT m := by unfold CT; have := Ck_nonneg (2 * m + 12); positivity

/-- **Top kernel bound** (`r = 12`): `‖k₁₂(n,y)‖ ≤ C_T y^{m+6} n^{−(m+6)} (ny)^{−1/4}`. -/
theorem norm_kB_top_le (hm : 1 ≤ m) {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : 1 ≤ y) :
    ‖kB m 12 n y‖ ≤ CT m * y ^ (m + 6) * ((n : ℝ) ^ (m + 6))⁻¹ * ((n : ℝ) * y) ^ (-(1 / 4) : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hy0 : 0 < y := by linarith
  rw [kB_eq_Ik hm 12 hn hy0, norm_mul, norm_sg, one_mul, Complex.norm_real, Real.norm_eq_abs]
  set L := 2 * π * √((n : ℝ) * y) with hL
  have hny : 1 ≤ (n : ℝ) * y := by nlinarith [(by exact_mod_cast hn : (1 : ℝ) ≤ n)]
  have hL1 : 1 ≤ L := by
    have : 1 ≤ √((n : ℝ) * y) := by rw [Real.le_sqrt (by norm_num) (by positivity)]; simpa using hny
    nlinarith [Real.two_le_pi]
  have hB := Ik_bound (ν := 2 * m + 12) (by omega) hL1
  have h24 : (√(y / n)) ^ (2 * m + 12) = (y / n) ^ (m + 6) := by
    rw [show 2 * m + 12 = 2 * (m + 6) by ring, pow_mul, Real.sq_sqrt (by positivity)]
  rw [abs_mul, h24, abs_of_nonneg (by positivity)]
  have hsL : √L = √(2 * π) * ((n : ℝ) * y) ^ (1 / 4 : ℝ) := by
    rw [hL, Real.sqrt_mul (by positivity)]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    norm_num
  calc (y / n) ^ (m + 6) * |Ik (2 * m + 12) L| ≤ (y / n) ^ (m + 6) * ((2 * √π + Ck (2 * m + 12)) / √L) := by
        gcongr
    _ = CT m * y ^ (m + 6) * ((n : ℝ) ^ (m + 6))⁻¹ * ((n : ℝ) * y) ^ (-(1 / 4) : ℝ) := by
        unfold CT
        rw [hsL, Real.rpow_neg (by positivity), div_pow]
        have : 0 < ((n : ℝ) * y) ^ (1 / 4 : ℝ) := by positivity
        have : 0 < √(2 * π) := by positivity
        field_simp


/-! ### Rankin-trick sums -/

/-- `St β = Σ |a(n)| n^{−β}`. -/
noncomputable def St (a : ℕ → ℝ) (β : ℝ) : ℝ := ∑' n : ℕ, |a n| / (n : ℝ) ^ β

lemma St_nonneg (β : ℝ) : 0 ≤ St a β := tsum_nonneg fun n => by positivity

/-- Head: `Σ_{n≤M} |a(n)| n^{−γ} ≤ M^{β−γ} St(β)` for `γ ≤ β`, `β > m + 1/2`. -/
lemma head_sum_le (hd : VData m a) {β γ : ℝ} (hβ : (m : ℝ) + 1 / 2 < β) (hγ : γ ≤ β) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, |a n| * (n : ℝ) ^ (-γ) ≤ (M : ℝ) ^ (β - γ) * St a β := by
  have hs := hd.summable_abs_div hβ
  have h1 : ∀ n ∈ Finset.Icc 1 M, |a n| * (n : ℝ) ^ (-γ) ≤
      (M : ℝ) ^ (β - γ) * (|a n| / (n : ℝ) ^ β) := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hnM : (n : ℝ) ≤ M := by exact_mod_cast h2
    have e : (n : ℝ) ^ (-γ) = (n : ℝ) ^ (β - γ) * ((n : ℝ) ^ β)⁻¹ := by
      rw [← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]; congr 1; ring
    rw [e, div_eq_mul_inv]
    have : (n : ℝ) ^ (β - γ) ≤ (M : ℝ) ^ (β - γ) := Real.rpow_le_rpow hn0.le hnM (by linarith)
    have h0 : 0 ≤ |a n| * ((n : ℝ) ^ β)⁻¹ := by positivity
    nlinarith
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact hs.sum_le_tsum _ fun n _ => by positivity

lemma rpow_trick {c x M1 α β : ℝ} (hc : 0 ≤ c) (hM1 : 0 < M1) (hx : M1 ≤ x) (hαβ : β ≤ α) :
    c * x ^ (-α) ≤ M1 ^ (β - α) * (c / x ^ β) := by
  have hx0 : 0 < x := lt_of_lt_of_le hM1 hx
  have e : x ^ (-α) = x ^ (β - α) * (x ^ β)⁻¹ := by
    rw [← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]; congr 1; ring
  rw [e, div_eq_mul_inv]
  have : x ^ (β - α) ≤ M1 ^ (β - α) := Real.rpow_le_rpow_of_nonpos hM1 hx (by linarith)
  have h0 : 0 ≤ c * (x ^ β)⁻¹ := by positivity
  nlinarith

/-- Tail: `Σ_{n>M} |a(n)| n^{−α} ≤ (M+1)^{β−α} St(β)` for `m + 1/2 < β ≤ α`. -/
lemma tail_sum_le (hd : VData m a) {α β : ℝ} (hβ : (m : ℝ) + 1 / 2 < β) (hαβ : β ≤ α) (M : ℕ) :
    Summable (fun k : ℕ => |a (k + (M + 1))| * ((k + (M + 1) : ℕ) : ℝ) ^ (-α)) ∧
    ∑' k : ℕ, |a (k + (M + 1))| * ((k + (M + 1) : ℕ) : ℝ) ^ (-α) ≤
      ((M : ℝ) + 1) ^ (β - α) * St a β := by
  have hs := hd.summable_abs_div hβ
  have hs' := (summable_nat_add_iff (M + 1)).2 hs
  have hb : ∀ k : ℕ, |a (k + (M + 1))| * ((k + (M + 1) : ℕ) : ℝ) ^ (-α) ≤
      ((M : ℝ) + 1) ^ (β - α) * (|a (k + (M + 1))| / ((k + (M + 1) : ℕ) : ℝ) ^ β) := by
    intro k
    have hnM : (M : ℝ) + 1 ≤ ((k + (M + 1) : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
    exact rpow_trick (abs_nonneg _) (by positivity) hnM hαβ
  have hsum : Summable fun k : ℕ => ((M : ℝ) + 1) ^ (β - α) *
      (|a (k + (M + 1))| / ((k + (M + 1) : ℕ) : ℝ) ^ β) :=
    hs'.mul_left (((M : ℝ) + 1) ^ (β - α))
  refine ⟨Summable.of_nonneg_of_le (fun k => by positivity) hb hsum, ?_⟩
  refine (Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun k => by positivity) hb hsum) hsum).trans ?_
  rw [tsum_mul_left]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := (hs.sum_add_tsum_nat_add (M + 1)).symm
  have h0 : 0 ≤ ∑ n ∈ Finset.range (M + 1), |a n| / (n : ℝ) ^ β :=
    Finset.sum_nonneg fun n _ => by positivity
  unfold St
  linarith

/-! ### A Lipschitz bound for the main term -/

lemma hasDerivAt_main (m n : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => y ^ ((m : ℝ) - 1 / 4) * Real.cos (th n y))
      (((m : ℝ) - 1 / 4) * y ^ ((m : ℝ) - 1 / 4 - 1) * Real.cos (th n y) -
        y ^ ((m : ℝ) - 1 / 4) * (Real.sin (th n y) * (4 * π * √(n : ℝ) * (1 / (2 * √y))))) y := by
  have h1 := Real.hasDerivAt_rpow_const (x := y) (p := (m : ℝ) - 1 / 4) (Or.inl hy.ne')
  have hs : HasDerivAt (fun y => √y) (1 / (2 * √y)) y := by
    have := Real.hasDerivAt_sqrt hy.ne'; simpa using this
  have h2 : HasDerivAt (th n) (4 * π * √(n : ℝ) * (1 / (2 * √y))) y := by
    unfold th
    exact (hs.const_mul (4 * π * √(n : ℝ))).sub_const (π / 4)
  have h3 := h1.mul h2.cos
  convert h3 using 1; ring

lemma abs_main_sub_le (hm : 1 ≤ m) (n : ℕ) {x x' Y : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ x') (h3 : x' ≤ Y) :
    |x' ^ ((m : ℝ) - 1 / 4) * Real.cos (th n x') - x ^ ((m : ℝ) - 1 / 4) * Real.cos (th n x)| ≤
      ((m : ℝ) + 2 * π * √(n : ℝ)) * Y ^ ((m : ℝ) - 3 / 4) * (x' - x) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hY : 1 ≤ Y := by linarith
  have hd : ∀ y ∈ Icc x x', HasDerivWithinAt (fun y => y ^ ((m : ℝ) - 1 / 4) * Real.cos (th n y))
      (((m : ℝ) - 1 / 4) * y ^ ((m : ℝ) - 1 / 4 - 1) * Real.cos (th n y) -
        y ^ ((m : ℝ) - 1 / 4) * (Real.sin (th n y) * (4 * π * √(n : ℝ) * (1 / (2 * √y))))) (Icc x x') y :=
    fun y hy => (hasDerivAt_main m n (by linarith [hy.1])).hasDerivWithinAt
  have hb : ∀ y ∈ Ico x x', ‖((m : ℝ) - 1 / 4) * y ^ ((m : ℝ) - 1 / 4 - 1) * Real.cos (th n y) -
      y ^ ((m : ℝ) - 1 / 4) * (Real.sin (th n y) * (4 * π * √(n : ℝ) * (1 / (2 * √y))))‖ ≤
      ((m : ℝ) + 2 * π * √(n : ℝ)) * Y ^ ((m : ℝ) - 3 / 4) := by
    intro y hy
    have hy1 : 1 ≤ y := le_trans h1 hy.1
    have hyY : y ≤ Y := by linarith [hy.2]
    have hy0 : 0 < y := by linarith
    have hsy : 0 < √y := Real.sqrt_pos.2 hy0
    rw [Real.norm_eq_abs]
    have hA : |((m : ℝ) - 1 / 4) * y ^ ((m : ℝ) - 1 / 4 - 1) * Real.cos (th n y)| ≤ m * Y ^ ((m : ℝ) - 3 / 4) := by
      rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < (m : ℝ) - 1 / 4), abs_of_pos (by positivity)]
      have hc := Real.abs_cos_le_one (th n y)
      have : y ^ ((m : ℝ) - 1 / 4 - 1) ≤ Y ^ ((m : ℝ) - 3 / 4) := by
        calc y ^ ((m : ℝ) - 1 / 4 - 1) ≤ y ^ ((m : ℝ) - 3 / 4) :=
              Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
          _ ≤ Y ^ ((m : ℝ) - 3 / 4) := Real.rpow_le_rpow hy0.le hyY (by linarith)
      have hp : 0 ≤ y ^ ((m : ℝ) - 1 / 4 - 1) := by positivity
      have hq : 0 ≤ Y ^ ((m : ℝ) - 3 / 4) := by positivity
      calc ((m : ℝ) - 1 / 4) * y ^ ((m : ℝ) - 1 / 4 - 1) * |Real.cos (th n y)|
          ≤ ((m : ℝ) - 1 / 4) * y ^ ((m : ℝ) - 1 / 4 - 1) * 1 :=
            mul_le_mul_of_nonneg_left hc (by nlinarith)
        _ ≤ m * Y ^ ((m : ℝ) - 3 / 4) := by
            rw [mul_one]; exact mul_le_mul (by linarith) this hp (by linarith)
    have hB : |y ^ ((m : ℝ) - 1 / 4) * (Real.sin (th n y) * (4 * π * √(n : ℝ) * (1 / (2 * √y))))| ≤
        2 * π * √(n : ℝ) * Y ^ ((m : ℝ) - 3 / 4) := by
      have e : y ^ ((m : ℝ) - 1 / 4) * (1 / (2 * √y)) = y ^ ((m : ℝ) - 3 / 4) / 2 := by
        rw [Real.sqrt_eq_rpow]
        have : y ^ ((m : ℝ) - 1 / 4) = y ^ ((m : ℝ) - 3 / 4) * y ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hy0]; congr 1; ring
        rw [this]; field_simp
      have e2 : y ^ ((m : ℝ) - 1 / 4) * (Real.sin (th n y) * (4 * π * √(n : ℝ) * (1 / (2 * √y)))) =
          Real.sin (th n y) * (2 * π * √(n : ℝ)) * y ^ ((m : ℝ) - 3 / 4) := by
        rw [show y ^ ((m : ℝ) - 1 / 4) * (Real.sin (th n y) * (4 * π * √(n : ℝ) * (1 / (2 * √y)))) =
          Real.sin (th n y) * (4 * π * √(n : ℝ)) * (y ^ ((m : ℝ) - 1 / 4) * (1 / (2 * √y))) by ring, e]
        ring
      rw [e2, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * π * √(n : ℝ)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ y ^ ((m : ℝ) - 3 / 4))]
      have hs := Real.abs_sin_le_one (th n y)
      have : y ^ ((m : ℝ) - 3 / 4) ≤ Y ^ ((m : ℝ) - 3 / 4) :=
        Real.rpow_le_rpow hy0.le hyY (by linarith)
      have hp : 0 ≤ 2 * π * √(n : ℝ) := by positivity
      have hq : 0 ≤ y ^ ((m : ℝ) - 3 / 4) := by positivity
      nlinarith [abs_nonneg (Real.sin (th n y)), mul_le_mul hs this hq zero_le_one]
    calc _ ≤ |((m : ℝ) - 1 / 4) * y ^ ((m : ℝ) - 1 / 4 - 1) * Real.cos (th n y)| +
          |y ^ ((m : ℝ) - 1 / 4) * (Real.sin (th n y) * (4 * π * √(n : ℝ) * (1 / (2 * √y))))| := abs_sub _ _
      _ ≤ m * Y ^ ((m : ℝ) - 3 / 4) + 2 * π * √(n : ℝ) * Y ^ ((m : ℝ) - 3 / 4) := add_le_add hA hB
      _ = ((m : ℝ) + 2 * π * √(n : ℝ)) * Y ^ ((m : ℝ) - 3 / 4) := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb x' ⟨h2, le_rfl⟩
  rwa [Real.norm_eq_abs] at this

/-! ### Short sums in mean square -/

lemma card_Ioc_floor_le {x H : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H) :
    ((Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℝ) ≤ H + 1 := by
  rw [Nat.card_Ioc]
  have hle : ⌊x⌋₊ ≤ ⌊x + H⌋₊ := Nat.floor_le_floor (by linarith)
  rw [Nat.cast_sub hle]
  have h1 : (⌊x + H⌋₊ : ℝ) ≤ x + H := Nat.floor_le (by linarith)
  have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  linarith

lemma short_sq_pointwise {X H x : ℝ} (hX : 0 < X) (hH : 0 ≤ H) (hHX : H ≤ X)
    (hx : x ∈ Ioc X (2 * X)) :
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, |a n|) ^ 2 ≤
      (H + 1) * ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊,
        a n ^ 2 * (Ico ((n : ℝ) - H) n).indicator 1 x := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊)
    (f := fun n => |a n|)
  simp only [sq_abs] at hcs
  refine hcs.trans ?_
  have hsub : Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ ⊆ Finset.Icc 1 ⌊3 * X⌋₊ := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hn
    refine Finset.mem_Icc.2 ⟨by omega, h2.trans (Nat.floor_le_floor (by linarith [hx.2]))⟩
  have hind : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, (Ico ((n : ℝ) - H) n).indicator 1 x = (1 : ℝ) := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hn
    have hxn : x < n := (Nat.floor_lt hx0).1 h1
    have hnx : (n : ℝ) ≤ x + H := by
      have := (Nat.le_floor_iff (by linarith)).1 h2; exact this
    rw [Set.indicator_of_mem (by constructor <;> linarith)]; rfl
  have hS : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, a n ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊, a n ^ 2 * (Ico ((n : ℝ) - H) n).indicator 1 x := by
    calc ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, a n ^ 2
        = ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, a n ^ 2 * (Ico ((n : ℝ) - H) n).indicator 1 x :=
          Finset.sum_congr rfl fun n hn => by rw [hind n hn, mul_one]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by
          have : 0 ≤ (Ico ((n : ℝ) - H) n).indicator (1 : ℝ → ℝ) x :=
            Set.indicator_nonneg (fun _ _ => zero_le_one) x
          positivity)
  have hc := card_Ioc_floor_le hx0 hH
  have h0 : 0 ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, a n ^ 2 :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  calc ((Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℝ) * ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, a n ^ 2
      ≤ (H + 1) * ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, a n ^ 2 := by gcongr
    _ ≤ _ := by gcongr

/-- **Short sums in mean square**: `∫_X^{2X} (Σ_{x<n≤x+H} |a(n)|)² ≤ (H+1) H Σ_{n≤3X} a(n)²`. -/
theorem integral_short_sq_le {X H : ℝ} (hX : 0 < X) (hH : 0 ≤ H) (hHX : H ≤ X) :
    ∫ x in Ioc X (2 * X), (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, |a n|) ^ 2 ≤
      (H + 1) * H * ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊, a n ^ 2 := by
  set g : ℝ → ℝ := fun x => (H + 1) * ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊,
    a n ^ 2 * (Ico ((n : ℝ) - H) n).indicator 1 x with hg
  have hfin : ∀ n : ℕ, (volume.restrict (Ioc X (2 * X))) (Ico ((n : ℝ) - H) n) ≠ ⊤ := by
    intro n
    rw [Measure.restrict_apply measurableSet_Ico]
    exact ((measure_mono inter_subset_left).trans_lt measure_Ico_lt_top).ne
  have hgi : IntegrableOn g (Ioc X (2 * X)) := by
    refine Integrable.const_mul (integrable_finsetSum _ fun n _ => ?_) _
    refine Integrable.const_mul ?_ _
    exact (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (hfin n) (by simp))
  have h1 := integral_mono_of_nonneg (μ := volume.restrict (Ioc X (2 * X)))
    (Eventually.of_forall fun x => sq_nonneg (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, |a n|)) hgi
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx =>
      short_sq_pointwise hX hH hHX hx))
  refine h1.trans ?_
  rw [hg, integral_const_mul, integral_finsetSum _ (fun n _ => Integrable.const_mul
    ((integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (hfin n) (by simp))) _),
    mul_assoc]
  gcongr
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [integral_const_mul, integral_indicator_one measurableSet_Ico,
    measureReal_restrict_apply measurableSet_Ico]
  have : volume.real (Ico ((n : ℝ) - H) n ∩ Ioc X (2 * X)) ≤ H := by
    calc volume.real (Ico ((n : ℝ) - H) n ∩ Ioc X (2 * X)) ≤ volume.real (Ico ((n : ℝ) - H) n) :=
          measureReal_mono inter_subset_left (by simp)
      _ = H := by rw [Real.volume_real_Ico_of_le (by linarith)]; ring
  rw [mul_comm H]
  exact mul_le_mul_of_nonneg_left this (sq_nonneg _)

end RamanujanTau.VoronoiTruncGeneral
