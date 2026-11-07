/-
# `SvStripD` step 2: the twisted local factors `γ^z_p` and the complex `L1–L3` (`[DeligneBound]`)

For `s = 1 − iz` (`z ∈ ℂ`, written `1 − z·I`), `x = p^{−s}` and `ω = p^{−iz}` (so `ωx = 1/p`), the
twisted local factor of `Γ^z_d(u₁,u₂)` is (`docs/SKQF_PROOF.md` §4 item 4: the `u₁` side carries
`J_z`, the `u₂` side `J_0`)

    γ^z(e;i,j) = Σ_{a≤i,b≤j} α(p^a) · α(p^b)ω^b · L_p(a+b, e; x) · Fi_s(p^{i−a}) · Fi(p^{j−b}),

`Fi_s(p^k) = recF gRm(p^k) x^k` (the inverse of `fR(m)m^{−s}`), `Fi(p^k) = recF gRm(p^k)/p^k`,
`L_p = SvStripA.LcC` (the complex Cholesky columns).  With `X = ‖x‖ = p^{−1−Im z}`:

* `normX_le`, `normX_ge`: on `−1/4 ≤ Im z ≤ 0`, `1/p ≤ X ≤ 3/5`.
* **First-order cancellation** (exact): `γz_010 : γ^z(0;1,0) = λ²x²/(2(1+x))`,
  `γz_001 : γ^z(0;0,1) = (λ²/(2p)) x/(1+x)`, `γz_110 = −λ/2`, `γz_101 = −λω/2`.
* **L1z** `Tz_zero_le`: `T^z(p,0,N) ≤ 1 + 23914855 X²`;
* **L2z** `Tz_one_le`:  `T^z(p,1,N) ≤ |λ(p)| + 23914845 X`;
* **L3z** `Tz_le`:      `T^z(p,e,N) ≤ 10628820 (e+1)^6`;
  all uniform in the truncation `N`.
* Pivots: `norm_W1_le : ‖W_p(1)‖ ≤ X + 25X²`, `norm_We_le : ‖W_p(e)‖ ≤ 56 X^e`.
Level 2 (on `[DeligneBound]`).
-/
import RamanujanTau.SvStripD.Generic
import RamanujanTau.SvStripA.Decomp

set_option autoImplicit false

namespace RamanujanTau.SvStripD

open Complex Finset
open RamanujanTau.SvStripA (xs LcC WcK qqK rhoPx rhoPx_one norm_rhoPx_le LcC_zero_zero)
open RamanujanTau.HafnerBridge (lam lam_one)
open RamanujanTau.SelbergCoeffs (alpha alpha_one)
open RamanujanTau.QFProof3 (Fi gRm Xp)
open RamanujanTau.SelbergDelange3 (recF recF_one)

/-! ### The twisted local data -/

/-- `ω = p^{−iz}`. -/
noncomputable def ωz (p : ℕ) (z : ℂ) : ℂ := (p : ℂ) ^ (-(z * I))

/-- `x = p^{−s}`, `s = 1 − iz`. -/
noncomputable abbrev xz (p : ℕ) (z : ℂ) : ℂ := xs p (1 - z * I)

noncomputable def A1z (p a : ℕ) : ℂ := (alpha (p ^ a) : ℂ)
noncomputable def A2z (p : ℕ) (z : ℂ) (b : ℕ) : ℂ := (alpha (p ^ b) : ℂ) * ωz p z ^ b
noncomputable def F1z (p : ℕ) (z : ℂ) (k : ℕ) : ℂ := (recF gRm (p ^ k) : ℂ) * xz p z ^ k
noncomputable def F2z (p k : ℕ) : ℂ := (Fi (p ^ k) : ℂ)
noncomputable def Lz (p : ℕ) (z : ℂ) (n e : ℕ) : ℂ := LcC (1 - z * I) p n e

/-- **The twisted local factor** `γ^z_p(e;i,j)`. -/
noncomputable def γz (p : ℕ) (z : ℂ) (e i j : ℕ) : ℂ :=
  γC (A1z p) (A2z p z) (F1z p z) (F2z p) (Lz p z) e i j

/-- **The twisted local mass** `T^z_p(e,N) = Σ_{i,j≤N} ‖γ^z_p(e;i,j)‖`. -/
noncomputable def Tz (p : ℕ) (z : ℂ) (e N : ℕ) : ℝ :=
  TC (A1z p) (A2z p z) (F1z p z) (F2z p) (Lz p z) e N

lemma Tz_nonneg (p : ℕ) (z : ℂ) (e N : ℕ) : 0 ≤ Tz p z e N := TC_nonneg _ _ _ _ _ _ _

/-! ### Sizes of `x` and `ω` -/

lemma normX_eq {p : ℕ} (hp : p.Prime) (z : ℂ) : ‖xz p z‖ = (p : ℝ) ^ (-1 - z.im) := by
  rw [xz, xs, norm_natCast_cpow_of_pos hp.pos]
  congr 1; simp; ring

lemma normX_pos {p : ℕ} (hp : p.Prime) (z : ℂ) : 0 < ‖xz p z‖ := by
  rw [normX_eq hp]; exact Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _

lemma normX_le {p : ℕ} (hp : p.Prime) {z : ℂ} (h1 : -1 / 4 ≤ z.im) : ‖xz p z‖ ≤ 3 / 5 := by
  rw [normX_eq hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have e1 : (p : ℝ) ^ (-1 - z.im) ≤ (2 : ℝ) ^ (-1 - z.im) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
  have e2 : (2 : ℝ) ^ (-1 - z.im) ≤ (2 : ℝ) ^ (-3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have e3 : (2 : ℝ) ^ (-3 / 4 : ℝ) ≤ 3 / 5 := by
    have h4 : ((2 : ℝ) ^ (-3 / 4 : ℝ)) ^ (4 : ℕ) = 1 / 8 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have hpos : 0 ≤ (2 : ℝ) ^ (-3 / 4 : ℝ) := by positivity
    by_contra hc
    push Not at hc
    have := pow_lt_pow_left₀ hc (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
    rw [h4] at this; norm_num at this
  linarith

lemma normX_ge {p : ℕ} (hp : p.Prime) {z : ℂ} (h2 : z.im ≤ 0) : (p : ℝ)⁻¹ ≤ ‖xz p z‖ := by
  rw [normX_eq hp]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have := Real.rpow_le_rpow_of_exponent_le hp1 (show (-1 : ℝ) ≤ -1 - z.im by linarith)
  rwa [Real.rpow_neg_one] at this

lemma normω_le {p : ℕ} (hp : p.Prime) {z : ℂ} (h2 : z.im ≤ 0) : ‖ωz p z‖ ≤ 1 := by
  rw [ωz, norm_natCast_cpow_of_pos hp.pos]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  refine Real.rpow_le_one_of_one_le_of_nonpos hp1 ?_
  simp; linarith

lemma ω_mul_x {p : ℕ} (hp : p.Prime) (z : ℂ) : ωz p z * xz p z = ((p : ℝ)⁻¹ : ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [ωz, xz, xs, ← cpow_add _ _ hp0]
  rw [show -(z * I) + -(1 - z * I) = -1 by ring, cpow_neg_one]
  push_cast; rfl

/-! ### The concrete hypotheses of the generic bounds -/

lemma hLz0 (p : ℕ) (z : ℂ) (n e : ℕ) (h : n < e) : Lz p z n e = 0 := by
  simp [Lz, LcC, h]


section Deligne

variable [DeligneBound]

lemma hA1z (p a : ℕ) : ‖A1z p a‖ ≤ 1 := by
  rw [A1z, Complex.norm_real, Real.norm_eq_abs]
  exact RamanujanTau.SelbergCoeffs.abs_alpha_le_one _

lemma hA2z {p : ℕ} (hp : p.Prime) {z : ℂ} (h2 : z.im ≤ 0) (b : ℕ) : ‖A2z p z b‖ ≤ 1 := by
  rw [A2z, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have h1 := RamanujanTau.SelbergCoeffs.abs_alpha_le_one (p ^ b)
  have h3 : ‖ωz p z‖ ^ b ≤ 1 := pow_le_one₀ (norm_nonneg _) (normω_le hp h2)
  have := mul_le_mul h1 h3 (by positivity) zero_le_one
  linarith

lemma hF1z {p : ℕ} (hp : p.Prime) (z : ℂ) (k : ℕ) : ‖F1z p z k‖ ≤ ck k * ‖xz p z‖ ^ k := by
  rw [F1z, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have := RamanujanTau.QFProof4.abs_recF_gRm_ppow hp k
  exact mul_le_mul_of_nonneg_right this (by positivity)

lemma hF2z {p : ℕ} (hp : p.Prime) {z : ℂ} (h2 : z.im ≤ 0) (k : ℕ) :
    ‖F2z p k‖ ≤ ck k * ‖xz p z‖ ^ k := by
  rw [F2z, Complex.norm_real, Real.norm_eq_abs]
  refine (RamanujanTau.QFProof5.abs_Fi_le hp k).trans ?_
  have h := normX_ge hp h2
  have hX0 : 0 ≤ Xp p := by unfold Xp; positivity
  have : Xp p ^ k ≤ ‖xz p z‖ ^ k := pow_le_pow_left₀ hX0 h k
  exact mul_le_mul_of_nonneg_left this (ck_nonneg k)

lemma hLz {p : ℕ} (hp : p.Prime) {z : ℂ} (h1 : -1 / 4 ≤ z.im) (n e : ℕ) :
    ‖Lz p z n e‖ ≤ 5 * (((n : ℝ) + 1) ^ 2 * ‖xz p z‖ ^ (n - e)) := by
  have hX := normX_le hp h1
  have hX0 := (normX_pos hp z).le
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hsq : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  unfold Lz LcC
  split_ifs with h0 he
  · simp; positivity
  · subst he
    rw [norm_mul, norm_pow, Nat.sub_zero, mul_comm (‖xs p (1 - z * I)‖ ^ n)]
    have hr := norm_rhoPx_le p n (x := xs p (1 - z * I)) hX
    have hl1 := RamanujanTau.QFProof5.abs_lam_pp_le hp n
    have hl2 := RamanujanTau.QFProof5.abs_lam_pp_le hp (n - 2)
    have hn2 : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
    have : ‖rhoPx p n (xs p (1 - z * I))‖ ≤ 5 * ((n : ℝ) + 1) ^ 2 := by
      refine hr.trans ?_
      nlinarith
    calc ‖rhoPx p n (xs p (1 - z * I))‖ * ‖xs p (1 - z * I)‖ ^ n
        ≤ 5 * ((n : ℝ) + 1) ^ 2 * ‖xs p (1 - z * I)‖ ^ n :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    have hl := RamanujanTau.QFProof5.abs_lam_pp_le hp (n - e)
    have hne : ((n - e : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n e
    have : |lam (p ^ (n - e))| ≤ 5 * ((n : ℝ) + 1) ^ 2 := by nlinarith
    calc |lam (p ^ (n - e))| * ‖xs p (1 - z * I)‖ ^ (n - e)
        ≤ 5 * ((n : ℝ) + 1) ^ 2 * ‖xs p (1 - z * I)‖ ^ (n - e) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring

end Deligne

/-! ### The lowest terms (exact) -/

lemma A1z_zero (p : ℕ) : A1z p 0 = 1 := by simp [A1z, alpha_one]
lemma A2z_zero (p : ℕ) (z : ℂ) : A2z p z 0 = 1 := by simp [A2z, alpha_one]
lemma F1z_zero (p : ℕ) (z : ℂ) : F1z p z 0 = 1 := by simp [F1z, recF_one]
lemma F2z_zero (p : ℕ) : F2z p 0 = 1 := by simp [F2z, RamanujanTau.QFProof4.Fi_one]
lemma Lz_00 (p : ℕ) (z : ℂ) : Lz p z 0 0 = 1 := LcC_zero_zero _ _
lemma Lz_01 (p : ℕ) (z : ℂ) : Lz p z 0 1 = 0 := hLz0 p z 0 1 one_pos
lemma Lz_10 (p : ℕ) (z : ℂ) : Lz p z 1 0 = xz p z * ((lam p : ℂ) / (1 + xz p z)) := by
  simp [Lz, LcC, rhoPx_one]
lemma Lz_11 (p : ℕ) (z : ℂ) : Lz p z 1 1 = 1 := by simp [Lz, LcC, lam_one]

lemma γz_000 (p : ℕ) (z : ℂ) : γz p z 0 0 0 = 1 := by
  simp [γz, γC_00, A1z_zero, A2z_zero, F1z_zero, F2z_zero, Lz_00]

lemma γz_100 (p : ℕ) (z : ℂ) : γz p z 1 0 0 = 0 := by
  simp [γz, γC_00, Lz_01]

section Deligne

variable [DeligneBound]

lemma alphaC {p : ℕ} (hp : p.Prime) : (alpha p : ℂ) = -(lam p : ℂ) / 2 := by
  rw [RamanujanTau.QFProof5.alpha_prime' hp]; push_cast; ring

omit [DeligneBound] in
lemma recFC {p : ℕ} (hp : p.Prime) : (recF gRm p : ℂ) = (lam p : ℂ) ^ 2 / 2 := by
  rw [RamanujanTau.QFProof4.recF_gRm_prime hp, ← RamanujanTau.QFProof5.lam_prime_eq hp]; push_cast; ring

/-- **First-order cancellation, `u₁` side**: `γ^z(0;1,0) = λ²x²/(2(1+x))`. -/
theorem γz_010 {p : ℕ} (hp : p.Prime) (z : ℂ) (h1 : 1 + xz p z ≠ 0) :
    γz p z 0 1 0 = (lam p : ℂ) ^ 2 * xz p z ^ 2 / (2 * (1 + xz p z)) := by
  rw [γz, γC_10, A1z_zero, A2z_zero, F1z_zero, F2z_zero, Lz_00, Lz_10]
  simp only [A1z, F1z, pow_one]
  rw [alphaC hp, recFC hp]
  field_simp; ring

/-- **First-order cancellation, `u₂` side**: `γ^z(0;0,1) = (λ²/(2p)) x/(1+x)`. -/
theorem γz_001 {p : ℕ} (hp : p.Prime) (z : ℂ) (h1 : 1 + xz p z ≠ 0) :
    γz p z 0 0 1 = (lam p : ℂ) ^ 2 * ((p : ℝ)⁻¹ : ℂ) * xz p z / (2 * (1 + xz p z)) := by
  rw [γz, γC_01, A1z_zero, A2z_zero, F1z_zero, F2z_zero, Lz_00, Lz_10]
  simp only [A2z, F2z, pow_one]
  have hF : (Fi p : ℂ) = (lam p : ℂ) ^ 2 * ((p : ℝ)⁻¹ : ℂ) / 2 := by
    rw [RamanujanTau.QFProof5.Fi_prime hp]; push_cast; ring
  rw [alphaC hp, hF, ← ω_mul_x hp z]
  field_simp; ring

theorem γz_110 {p : ℕ} (hp : p.Prime) (z : ℂ) : γz p z 1 1 0 = -(lam p : ℂ) / 2 := by
  rw [γz, γC_10, Lz_01, Lz_11, A1z_zero, A2z_zero, F1z_zero, F2z_zero]
  simp only [A1z, pow_one]
  rw [alphaC hp]; ring

theorem γz_101 {p : ℕ} (hp : p.Prime) (z : ℂ) : γz p z 1 0 1 = -(lam p : ℂ) / 2 * ωz p z := by
  rw [γz, γC_01, Lz_01, Lz_11, A1z_zero, A2z_zero, F1z_zero, F2z_zero]
  simp only [A2z, pow_one]
  rw [alphaC hp]; ring

/-! ### L1z–L3z -/

omit [DeligneBound] in
lemma norm_one_add_x {p : ℕ} (hp : p.Prime) {z : ℂ} (h1 : -1 / 4 ≤ z.im) : 2 / 5 ≤ ‖1 + xz p z‖ :=
  RamanujanTau.SvStripA.norm_one_add_ge (normX_le hp h1)

/-- **L1z**: `T^z(p,0,N) ≤ 1 + 23914855 X²`, `X = ‖p^{−s}‖`, uniformly in `N`. -/
theorem Tz_zero_le {p : ℕ} (hp : p.Prime) {z : ℂ} (h1 : -1 / 4 ≤ z.im) (h2 : z.im ≤ 0) (N : ℕ) :
    Tz p z 0 N ≤ 1 + 23914855 * ‖xz p z‖ ^ 2 := by
  set X := ‖xz p z‖ with hXd
  have hX0 : 0 < X := normX_pos hp z
  have hX1 : X ≤ 3 / 5 := normX_le hp h1
  have h1x := norm_one_add_x hp h1
  have h1x0 : 1 + xz p z ≠ 0 := norm_pos_iff.1 (by linarith)
  have hs := TC_zero_split hX0 (by norm_num : (0 : ℝ) ≤ 5) (hLz hp h1) (hA1z p) (hA2z hp h2)
    (hF1z hp z) (hF2z hp h2) (by linarith) N
  have hl := RamanujanTau.QFProof5.lam_sq_le hp
  have e00 : ‖γC (A1z p) (A2z p z) (F1z p z) (F2z p) (Lz p z) 0 0 0‖ = 1 := by
    rw [← γz, γz_000, norm_one]
  have hq : 0 < 2 * ‖1 + xz p z‖ := by linarith
  have e10 : ‖γC (A1z p) (A2z p z) (F1z p z) (F2z p) (Lz p z) 0 1 0‖ ≤ 5 * X ^ 2 := by
    rw [← γz, γz_010 hp z h1x0]
    have en : ‖(lam p : ℂ) ^ 2 * xz p z ^ 2 / (2 * (1 + xz p z))‖ =
        lam p ^ 2 * X ^ 2 / (2 * ‖1 + xz p z‖) := by
      simp [norm_pow, sq_abs, hXd]
    rw [en, div_le_iff₀ hq]
    nlinarith [sq_nonneg X, mul_nonneg (sq_nonneg X) (sq_nonneg (lam p))]
  have e01 : ‖γC (A1z p) (A2z p z) (F1z p z) (F2z p) (Lz p z) 0 0 1‖ ≤ 5 * X ^ 2 := by
    have hpX := normX_ge hp h2
    have hpi : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    rw [← γz, γz_001 hp z h1x0]
    have en : ‖(lam p : ℂ) ^ 2 * ((p : ℝ)⁻¹ : ℂ) * xz p z / (2 * (1 + xz p z))‖ =
        lam p ^ 2 * (p : ℝ)⁻¹ * X / (2 * ‖1 + xz p z‖) := by
      simp [norm_pow, sq_abs, hXd]
    rw [en, div_le_iff₀ hq]
    have : lam p ^ 2 * (p : ℝ)⁻¹ * X ≤ 4 * X * X := by
      have := mul_le_mul hl hpX hpi (by norm_num)
      nlinarith
    nlinarith [sq_nonneg X]
  unfold Tz
  rw [e00] at hs
  linarith

/-- **L2z**: `T^z(p,1,N) ≤ |λ(p)| + 23914845 X`. -/
theorem Tz_one_le {p : ℕ} (hp : p.Prime) {z : ℂ} (h1 : -1 / 4 ≤ z.im) (h2 : z.im ≤ 0) (N : ℕ) :
    Tz p z 1 N ≤ |lam p| + 23914845 * ‖xz p z‖ := by
  set X := ‖xz p z‖ with hXd
  have hX0 : 0 < X := normX_pos hp z
  have hX1 : X ≤ 3 / 5 := normX_le hp h1
  have hs := TC_one_split hX0 (by norm_num : (0 : ℝ) ≤ 5) (hLz hp h1) (hLz0 p z) (hA1z p)
    (hA2z hp h2) (hF1z hp z) (hF2z hp h2) (by linarith) N
  have e00 : ‖γC (A1z p) (A2z p z) (F1z p z) (F2z p) (Lz p z) 1 0 0‖ = 0 := by
    rw [← γz, γz_100, norm_zero]
  have e10 : ‖γC (A1z p) (A2z p z) (F1z p z) (F2z p) (Lz p z) 1 1 0‖ = |lam p| / 2 := by
    rw [← γz, γz_110 hp, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs]; norm_num
  have e01 : ‖γC (A1z p) (A2z p z) (F1z p z) (F2z p) (Lz p z) 1 0 1‖ ≤ |lam p| / 2 := by
    rw [← γz, γz_101 hp, norm_mul, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have := normω_le hp h2
    norm_num
    nlinarith [abs_nonneg (lam p), norm_nonneg (ωz p z)]
  unfold Tz
  rw [e00, e10] at hs
  linarith

/-- **L3z**: `T^z(p,e,N) ≤ 10628820 (e+1)^6`. -/
theorem Tz_le {p : ℕ} (hp : p.Prime) {z : ℂ} (h1 : -1 / 4 ≤ z.im) (h2 : z.im ≤ 0) (e N : ℕ) :
    Tz p z e N ≤ 10628820 * ((e : ℝ) + 1) ^ 6 := by
  have h := TC_le_gen (normX_pos hp z) (by norm_num : (0 : ℝ) ≤ 5) (hLz hp h1) (hLz0 p z) (hA1z p)
    (hA2z hp h2) (hF1z hp z) (hF2z hp h2) (by linarith [normX_le hp h1]) e N
  unfold Tz
  linarith

end Deligne

/-! ### Pivots -/

/-- `‖W_p(1)‖ ≤ X + 25X²` (`W_1 = x − λ²x²/(1+x)²`). -/
theorem norm_W1_le {p : ℕ} (hp : p.Prime) {z : ℂ} (h1 : -1 / 4 ≤ z.im) {l : ℝ} (hl : l ^ 2 ≤ 4) :
    ‖WcK (l : ℂ) (xz p z) 1‖ ≤ ‖xz p z‖ + 25 * ‖xz p z‖ ^ 2 := by
  have h1x := norm_one_add_x hp h1
  have h1x0 : 1 + xz p z ≠ 0 := norm_pos_iff.1 (by linarith)
  have e : WcK (l : ℂ) (xz p z) 1 = xz p z - (l : ℂ) ^ 2 * xz p z ^ 2 / (1 + xz p z) ^ 2 := by
    simp only [WcK, qqK]; field_simp
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hq : (2 / 5 : ℝ) ^ 2 ≤ ‖1 + xz p z‖ ^ 2 := pow_le_pow_left₀ (by norm_num) h1x 2
  have : l ^ 2 * ‖xz p z‖ ^ 2 / ‖1 + xz p z‖ ^ 2 ≤ 25 * ‖xz p z‖ ^ 2 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith [sq_nonneg ‖xz p z‖, mul_nonneg (sq_nonneg ‖xz p z‖) (sq_nonneg l)]
  linarith

/-- `‖W_p(e)‖ ≤ 56 X^e`. -/
theorem norm_We_le {p : ℕ} (hp : p.Prime) {z : ℂ} (h1 : -1 / 4 ≤ z.im) {l : ℝ} (hl : l ^ 2 ≤ 4)
    (e : ℕ) : ‖WcK (l : ℂ) (xz p z) e‖ ≤ 56 * ‖xz p z‖ ^ e := by
  refine (RamanujanTau.SvStripA.norm_WcK_le (l : ℂ) (normX_le hp h1) e).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have : 0 ≤ ‖xz p z‖ ^ e := by positivity
  nlinarith

end RamanujanTau.SvStripD
