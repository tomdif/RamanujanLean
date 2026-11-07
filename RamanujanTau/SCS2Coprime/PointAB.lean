/-
# Item 3 (part 3): the pointwise bound for `G_{a,b,ℓ}` and for the Laplace transform of `cR`

* `cfAB_sub_le`: Lipschitz control of the horocycle coefficient on the box (the Laplace variable is
  `bW`; the extra factor `b` from `‖bW − bW₀‖` is cancelled by `Σ n|c_n|e^{−nbσ} ≪ (bσ)^{−1}(…)`);
* `norm_G0_leAB`: division by the prefactor `|Y(i − ζ̄₀)|¹² ≥ (YA/2)¹²`;
* **`pointwise_parAB`**: `‖G_{a,b,ℓ}(W₀)‖ ≤ K ℓ^{1/21} A t⁹⁹ Y^{−12}` with `K` **independent of
  `a, b`** (Hölder gives `M (ab)^{−6} · (ab)²`, the trivial bounds are uniform in `a, b ≥ 1`);
* **`pointwise_Gc`**: `‖Gc (cR a b ℓ) (σ + iv)‖ ≤ K ℓ^{1/21} (|2v/σ|+3) b¹² σ^{−11901/1000}`
  for `ℓ ≥ 1`, `0 < σ ≤ b`, `ℓσ ≤ b`.
-/
import RamanujanTau.SCS2Coprime.GboundsAB
import RamanujanTau.SCSSharp2.Point21

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open MeasureTheory Set Complex Function CongruenceSubgroup
open UpperHalfPlane hiding I
open RamanujanTau.SCSProof RamanujanTau.SCSSharp
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par) (a b : ℕ+)

lemma re_natCast_mul (n : ℕ) (W : ℂ) : ((n : ℂ) * W).re = n * W.re := by simp [Complex.mul_re]

set_option maxHeartbeats 4000000 in
theorem cfAB_sub_le (hhσ : P.h * (4 * π * P.Y) ≤ 1)
    (hS1 : Summable (fun n : ℕ => n * |cR a b P.h n| * Real.exp (-n * (b * (2 * π * P.Y)))))
    (hT1 : Summable (fun n : ℕ => |cR a b P.h n| * Real.exp (-n * (b * (2 * π * P.Y)))))
    (hT0 : Summable (fun n : ℕ => |cR a b P.h n| * Real.exp (-n * (b * (4 * π * P.Y))))) :
    ∀ y ∈ Icc P.Y (P.Y * (1 + P.ε)), ∀ ζ : ℍ, inB P (ζ : ℂ) →
      ‖cfAB P a b y ζ - cfAB P a b P.Y (zeta0 P)‖ ≤
        (2 * P.Y * Aθ P) ^ 12 * (2 * π * P.Y * P.ε * (Aθ P + 2)) *
            (b * ∑' n : ℕ, n * |cR a b P.h n| * Real.exp (-n * (b * (2 * π * P.Y)))) +
          13 * (2 * P.Y * Aθ P) ^ 12 * P.ε *
            ∑' n : ℕ, |cR a b P.h n| * Real.exp (-n * (b * (4 * π * P.Y))) := by
  intro y hy ζ hζ
  have hY := P.hY; have hε := P.hε; have hε1 := P.hε1
  have hA := Aθ_ge P
  have hbpos : (0 : ℝ) < b := by exact_mod_cast b.pos
  have hy0 : 0 < y := hY.trans_le hy.1
  have hy2 : y ≤ 2 * P.Y := hy.2.trans (Y_mul_le P)
  have hyY : |y - P.Y| ≤ P.Y * P.ε := by
    rw [abs_of_nonneg (by linarith [hy.1])]; nlinarith [hy.2]
  obtain ⟨hb1, hb2, hb3⟩ := inB_bounds P hζ
  set c := cR a b P.h
  set S1 := ∑' n : ℕ, n * |c n| * Real.exp (-n * (b * (2 * π * P.Y)))
  set T0 := ∑' n : ℕ, |c n| * Real.exp (-n * (b * (4 * π * P.Y)))
  have hS1n : 0 ≤ S1 := tsum_nonneg fun n =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le
  have hT0n : 0 ≤ T0 := tsum_nonneg fun n => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  set u : ℂ := (y : ℂ) * (I - conj (ζ : ℂ))
  set u0 : ℂ := (P.Y : ℂ) * (I - conj ((zeta0 P : ℍ) : ℂ))
  set Wv : ℂ := 2 * π * y * (1 + I * conj (ζ : ℂ))
  set W0 : ℂ := 2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ))
  set e : ℝ := Real.exp (-2 * π * P.h * y)
  set e0 : ℝ := Real.exp (-2 * π * P.h * P.Y)
  have hcf : cfAB P a b y ζ = u ^ 12 * (e : ℂ) * Gc c ((b : ℂ) * Wv) := by
    unfold cfAB; rw [GAB_eq]
  have hc0 : cfAB P a b P.Y (zeta0 P) = u0 ^ 12 * (e0 : ℂ) * Gc c ((b : ℂ) * W0) := by
    unfold cfAB; rw [GAB_eq]
  have hu : ‖u‖ ≤ 2 * P.Y * Aθ P := by
    simp only [u]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hy0.le]
    calc y * ‖I - conj (ζ : ℂ)‖ ≤ (2 * P.Y) * Aθ P := by
          gcongr; exact norm_I_sub_conj P hζ
      _ = _ := by ring
  have hu0 : ‖u0‖ ≤ 2 * P.Y * Aθ P := by
    simp only [u0]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hY.le]
    calc P.Y * ‖I - conj ((zeta0 P : ℍ) : ℂ)‖ ≤ (2 * P.Y) * Aθ P := by
          gcongr
          · linarith
          · exact norm_I_sub_conj P (inB_zeta0 P)
      _ = _ := by ring
  have huu : ‖u - u0‖ ≤ P.Y * P.ε * (Aθ P + 2) := by
    have e1 : u - u0 = ((y - P.Y : ℝ) : ℂ) * (I - conj (ζ : ℂ)) +
        (P.Y : ℂ) * conj ((zeta0 P : ℍ) - (ζ : ℂ)) := by
      simp only [u, u0, map_sub]; push_cast; ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_conj,
      Real.norm_eq_abs, Real.norm_of_nonneg hY.le]
    have h1 := norm_I_sub_conj P hζ
    have h2 : ‖((zeta0 P : ℍ) : ℂ) - (ζ : ℂ)‖ ≤ 2 * P.ε := by
      rw [norm_sub_rev]; exact norm_sub_zeta0 P hζ
    calc |y - P.Y| * ‖I - conj (ζ : ℂ)‖ + P.Y * ‖((zeta0 P : ℍ) : ℂ) - (ζ : ℂ)‖
        ≤ (P.Y * P.ε) * Aθ P + P.Y * (2 * P.ε) := by gcongr
      _ = _ := by ring
  have hWW : ‖Wv - W0‖ ≤ 2 * π * P.Y * P.ε * (Aθ P + 2) := by
    have e1 : Wv - W0 = 2 * π * ((((y - P.Y : ℝ) : ℂ) * (1 + I * conj (ζ : ℂ))) +
        (P.Y : ℂ) * (I * conj ((ζ : ℂ) - (zeta0 P : ℂ)))) := by
      simp only [Wv, W0, map_sub]; push_cast; ring
    rw [e1, norm_mul]
    have h2π : ‖(2 * π : ℂ)‖ = 2 * π := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [h2π]
    have : ‖((y - P.Y : ℝ) : ℂ) * (1 + I * conj (ζ : ℂ)) + (P.Y : ℂ) * (I * conj ((ζ : ℂ) -
        (zeta0 P : ℂ)))‖ ≤ P.Y * P.ε * (Aθ P + 2) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I,
        Complex.norm_conj, Real.norm_eq_abs, Real.norm_of_nonneg hY.le, one_mul]
      have h1 := norm_one_add_I_conj P hζ
      have h2 := norm_sub_zeta0 P hζ
      calc |y - P.Y| * ‖1 + I * conj (ζ : ℂ)‖ + P.Y * ‖(ζ : ℂ) - (zeta0 P : ℂ)‖
          ≤ (P.Y * P.ε) * Aθ P + P.Y * (2 * P.ε) := by gcongr
        _ = _ := by ring
    calc 2 * π * ‖_‖ ≤ 2 * π * (P.Y * P.ε * (Aθ P + 2)) := by gcongr
      _ = _ := by ring
  have hReW : b * (2 * π * P.Y) ≤ ((b : ℂ) * Wv).re := by
    rw [re_natCast_mul]
    simp only [Wv]; rw [re_W]
    have : 2 * π * P.Y * 1 ≤ 2 * π * y * (1 + (ζ : ℂ).im) := by
      gcongr
      · linarith [hy.1]
      · linarith
    nlinarith
  have hReW0' : W0.re = 4 * π * P.Y := by
    simp only [W0]; rw [re_W, coe_zeta0]; simp; ring
  have hReW0 : ((b : ℂ) * W0).re = b * (4 * π * P.Y) := by rw [re_natCast_mul, hReW0']
  have hG := norm_Gc_sub_le c (by positivity : 0 < (b : ℝ) * (2 * π * P.Y)) hReW
    (by rw [hReW0]; have := Real.pi_pos; exact mul_le_mul_of_nonneg_left (by nlinarith) hbpos.le)
    hS1 hT1
  have hbW : ‖(b : ℂ) * Wv - (b : ℂ) * W0‖ = b * ‖Wv - W0‖ := by
    rw [← mul_sub, norm_mul, Complex.norm_natCast]
  rw [hbW] at hG
  have hG0 : ‖Gc c ((b : ℂ) * W0)‖ ≤ T0 := by
    have := norm_Gc_le c ((b : ℂ) * W0) (by rw [hReW0]; exact hT0)
    rwa [hReW0] at this
  have he1 : e ≤ 1 := Real.exp_le_one_iff.2 (by
    have hh : (0 : ℝ) ≤ P.h := Nat.cast_nonneg _
    have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * π) hh) hy0.le
    linarith)
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hee : |e - e0| ≤ P.ε / 2 := by
    have hh : (0 : ℝ) ≤ P.h := Nat.cast_nonneg _
    have := real_exp_sub_le (a := 2 * π * P.h * y) (b := 2 * π * P.h * P.Y) (by positivity)
      (by positivity)
    simp only [e, e0]
    rw [show -2 * π * P.h * y = -(2 * π * P.h * y) by ring,
      show -2 * π * P.h * P.Y = -(2 * π * P.h * P.Y) by ring]
    refine this.trans ?_
    rw [show 2 * π * P.h * y - 2 * π * P.h * P.Y = 2 * π * P.h * (y - P.Y) by ring, abs_mul,
      abs_of_nonneg (by positivity)]
    calc 2 * π * P.h * |y - P.Y| ≤ 2 * π * P.h * (P.Y * P.ε) := by gcongr
      _ = (P.h * (4 * π * P.Y)) * (P.ε / 2) := by ring
      _ ≤ 1 * (P.ε / 2) := by gcongr
      _ = _ := one_mul _
  rw [hcf, hc0]
  have hsplit : u ^ 12 * (e : ℂ) * Gc c ((b : ℂ) * Wv) - u0 ^ 12 * (e0 : ℂ) * Gc c ((b : ℂ) * W0) =
      u ^ 12 * (e : ℂ) * (Gc c ((b : ℂ) * Wv) - Gc c ((b : ℂ) * W0)) +
        ((u ^ 12 - u0 ^ 12) * (e : ℂ) + u0 ^ 12 * ((e - e0 : ℝ) : ℂ)) * Gc c ((b : ℂ) * W0) := by
    push_cast; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hm : 0 ≤ 2 * P.Y * Aθ P := by positivity
  have hpow := pow12_sub_le u u0 hu hu0
  have t1 : ‖u ^ 12 * (e : ℂ) * (Gc c ((b : ℂ) * Wv) - Gc c ((b : ℂ) * W0))‖ ≤
      (2 * P.Y * Aθ P) ^ 12 * (2 * π * P.Y * P.ε * (Aθ P + 2)) * (b * S1) := by
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg he0]
    calc ‖u‖ ^ 12 * e * ‖Gc c ((b : ℂ) * Wv) - Gc c ((b : ℂ) * W0)‖ ≤ (2 * P.Y * Aθ P) ^ 12 * 1 *
          (b * ‖Wv - W0‖ * S1) := by gcongr
      _ ≤ (2 * P.Y * Aθ P) ^ 12 * 1 * (b * (2 * π * P.Y * P.ε * (Aθ P + 2)) * S1) := by gcongr
      _ = _ := by ring
  have t2 : ‖((u ^ 12 - u0 ^ 12) * (e : ℂ) + u0 ^ 12 * ((e - e0 : ℝ) : ℂ)) * Gc c ((b : ℂ) * W0)‖ ≤
      13 * (2 * P.Y * Aθ P) ^ 12 * P.ε * T0 := by
    rw [norm_mul]
    have hin : ‖(u ^ 12 - u0 ^ 12) * (e : ℂ) + u0 ^ 12 * ((e - e0 : ℝ) : ℂ)‖ ≤
        13 * (2 * P.Y * Aθ P) ^ 12 * P.ε := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg he0, Real.norm_eq_abs]
      have hk : 12 * (2 * P.Y * Aθ P) ^ 11 * ‖u - u0‖ ≤ 12 * (2 * P.Y * Aθ P) ^ 12 * P.ε := by
        calc 12 * (2 * P.Y * Aθ P) ^ 11 * ‖u - u0‖
            ≤ 12 * (2 * P.Y * Aθ P) ^ 11 * (P.Y * P.ε * (Aθ P + 2)) := by gcongr
          _ ≤ 12 * (2 * P.Y * Aθ P) ^ 11 * ((2 * P.Y * Aθ P) * P.ε) := by
              have : P.Y * P.ε * (Aθ P + 2) ≤ (2 * P.Y * Aθ P) * P.ε := by
                nlinarith [mul_pos hY hε]
              exact mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := by ring
      calc ‖u ^ 12 - u0 ^ 12‖ * e + ‖u0‖ ^ 12 * |e - e0|
          ≤ (12 * (2 * P.Y * Aθ P) ^ 11 * ‖u - u0‖) * 1 + (2 * P.Y * Aθ P) ^ 12 * (P.ε / 2) := by
            gcongr
        _ ≤ 12 * (2 * P.Y * Aθ P) ^ 12 * P.ε + (2 * P.Y * Aθ P) ^ 12 * P.ε := by
            have : 0 ≤ (2 * P.Y * Aθ P) ^ 12 * P.ε := by positivity
            nlinarith
        _ = 13 * (2 * P.Y * Aθ P) ^ 12 * P.ε := by ring
    calc _ ≤ 13 * (2 * P.Y * Aθ P) ^ 12 * P.ε * T0 := by gcongr
      _ = _ := rfl
  linarith

/-- **Division by the prefactor.** -/
theorem norm_G0_leAB (hh : P.h * (4 * π * P.Y) ≤ 1) :
    ‖GAB a b P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ)))‖ ≤
      2 ^ 13 / (P.Y * Aθ P) ^ 12 * ‖cfAB P a b P.Y (zeta0 P)‖ := by
  have hY := P.hY
  have hA := Aθ_ge P
  set u0 : ℂ := (P.Y : ℂ) * (I - conj ((zeta0 P : ℍ) : ℂ))
  set e0 : ℝ := Real.exp (-2 * π * P.h * P.Y)
  have hcf : cfAB P a b P.Y (zeta0 P) = u0 ^ 12 * (e0 : ℂ) *
      GAB a b P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ))) := rfl
  have he0 : 1 / 2 ≤ e0 := by
    have h1 : -(1 / 2 : ℝ) ≤ -2 * π * P.h * P.Y := by nlinarith
    have h2 : Real.exp (-(1 / 2 : ℝ)) ≤ e0 := Real.exp_le_exp.2 h1
    have h3 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
      have := Real.add_one_le_exp (-(1 / 2 : ℝ)); linarith
    linarith
  have hu : P.Y * Aθ P / 2 ≤ ‖u0‖ := by
    simp only [u0]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hY.le]
    have := norm_I_sub_conj_zeta0_ge P
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left this hY.le
  have hpos : 0 < (P.Y * Aθ P) ^ 12 := by positivity
  rw [hcf, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  set G := ‖GAB a b P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ)))‖
  have hG : 0 ≤ G := norm_nonneg _
  have hp : (P.Y * Aθ P / 2) ^ 12 * (1 / 2) ≤ ‖u0‖ ^ 12 * e0 := by
    have : 0 ≤ P.Y * Aθ P / 2 := by positivity
    gcongr
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  have e : (P.Y * Aθ P / 2) ^ 12 * (1 / 2) = (P.Y * Aθ P) ^ 12 / 2 ^ 13 := by ring
  rw [e] at hp
  have : (P.Y * Aθ P) ^ 12 * G ≤ 2 ^ 13 * (‖u0‖ ^ 12 * e0 * G) := by
    have h2 : (P.Y * Aθ P) ^ 12 ≤ 2 ^ 13 * (‖u0‖ ^ 12 * e0) := by
      rw [div_le_iff₀ (by norm_num)] at hp; linarith
    nlinarith
  linarith

lemma rpow_neg12 {x : ℝ} (hx : 0 < x) : x ^ (-(12 : ℝ)) = 1 / x ^ 12 := by
  rw [Real.rpow_neg hx.le, one_div]; norm_cast

/-- The trivial bound in the form used below: `Σ |cR n| e^{−n bs} ≤ 2C₀ s^{−12}` if `ℓ s ≤ 1`. -/
lemma laplace_cR_le {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (hℓs : ℓ * s ≤ 1)
    (hb : ∑' n : ℕ, |cR a b ℓ n| * Real.exp (-n * (b * s)) ≤
      (C₀ * (b * s) ^ (-(12 : ℝ)) + Real.exp ((ℓ : ℤ) * (b * s) / b) *
        (C₀ * (a * (b * s) / b) ^ (-(12 : ℝ)))) / 2) :
    ∑' n : ℕ, |cR a b ℓ n| * Real.exp (-n * (b * s)) ≤ 2 * C₀ * (1 / s ^ 12) := by
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast a.one_le
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast b.one_le
  refine hb.trans ?_
  have he : Real.exp ((ℓ : ℤ) * (b * s) / b) ≤ 3 := by
    have e : ((ℓ : ℤ) : ℝ) * (b * s) / b = ℓ * s := by push_cast; field_simp
    rw [e]
    calc Real.exp (ℓ * s) ≤ Real.exp 1 := Real.exp_le_exp.2 hℓs
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have e2 : (a : ℝ) * (b * s) / b = a * s := by field_simp
  rw [e2, rpow_neg12 (by positivity), rpow_neg12 (by positivity)]
  have h1 : 1 / ((b : ℝ) * s) ^ 12 ≤ 1 / s ^ 12 := by
    gcongr; nlinarith
  have h2 : 1 / ((a : ℝ) * s) ^ 12 ≤ 1 / s ^ 12 := by
    gcongr; nlinarith
  have h0 : 0 ≤ C₀ * (1 / ((a : ℝ) * s) ^ 12) := by positivity
  have h3 : Real.exp ((ℓ : ℤ) * (b * s) / b) * (C₀ * (1 / ((a : ℝ) * s) ^ 12)) ≤
      3 * (C₀ * (1 / s ^ 12)) := by
    have : 0 ≤ Real.exp ((ℓ : ℤ) * (b * s) / b) := (Real.exp_pos _).le
    calc _ ≤ 3 * (C₀ * (1 / ((a : ℝ) * s) ^ 12)) := by gcongr
      _ ≤ _ := by gcongr
  have h4 : C₀ * (1 / ((b : ℝ) * s) ^ 12) ≤ C₀ * (1 / s ^ 12) := by gcongr
  linarith

set_option maxHeartbeats 4000000 in
/-- **Pointwise bound for `G_{a,b,ℓ}`** at `W₀ = 2πY(1 + iζ̄₀)`, uniform in `a, b`. -/
theorem pointwise_parAB : ∃ K : ℝ, 0 ≤ K ∧ ∀ (a b : ℕ+) (P : Par), 1 ≤ P.h →
    P.ε = (P.Y ^ (1 / 1000 : ℝ)) ^ 99 / 2 → P.h * (4 * π * P.Y) ≤ 1 →
      ‖GAB a b P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ)))‖ ≤
        K * (P.h : ℝ) ^ (1 / 21 : ℝ) * Aθ P * (P.Y ^ (1 / 1000 : ℝ)) ^ 99 * (1 / P.Y ^ 12) := by
  obtain ⟨M, hM0, hM⟩ := norm_PsiAB_le
  obtain ⟨CB, hCB0, hCB⟩ := norm_tsum_Gamma0_Iγ_le (1 / 400) (2 / 21) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨C₀, hC₀, hT⟩ := cR_laplace
  refine ⟨2 ^ 24 * M * Real.sqrt CB + 2 ^ 28 * C₀, by positivity, fun a b P hh hεt hhY => ?_⟩
  have hY := P.hY; have hY1 := P.hY1; have hε := P.hε
  have hbpos : (0 : ℝ) < b := by exact_mod_cast b.pos
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast a.one_le
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast b.one_le
  set t := P.Y ^ (1 / 1000 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hY _
  have ht1 : t ≤ 1 := Real.rpow_le_one hY.le hY1 (by norm_num)
  have hYt : P.Y = t ^ 1000 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hY.le]; norm_num
  have hhR : (1 : ℝ) ≤ P.h := by exact_mod_cast hh
  have hA := Aθ_ge P
  set A := Aθ P
  set R := Rθ P
  have hRA : R = 2 * A ^ 2 := by simp only [R, A, Rθ, Aθ]
  set q : ℕ := ((a * b : ℕ+) : ℕ)
  have hqab : (q : ℝ) = (a : ℝ) * b := by simp [q]
  -- `‖Σ I(h)‖` over `Γ₀(q)`
  have hSig := hCB P q hh
  have hYpow : P.Y ^ (-(3 / 2 : ℝ) - 2 * (1 / 400)) = 1 / t ^ 1505 := by
    rw [hYt, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    have e : ((1000 : ℕ) : ℝ) * (-(3 / 2) - 2 * (1 / 400)) = -((1505 : ℕ) : ℝ) := by norm_num
    rw [e, Real.rpow_neg ht0.le, Real.rpow_natCast, one_div]
  rw [hYpow, hεt] at hSig
  have hb : 2 * ‖∑' h : Gamma0 q, Iγ P h‖ ≤ CB * (P.h : ℝ) ^ (2 / 21 : ℝ) / (4 * t ^ 1208) := by
    have e : CB * (P.h : ℝ) ^ (2 / 21 : ℝ) * ((t ^ 99 / 2) ^ 3) * (1 / t ^ 1505) =
        CB * (P.h : ℝ) ^ (2 / 21 : ℝ) / (8 * t ^ 1208) := by
      field_simp; ring
    rw [e] at hSig
    have : CB * (P.h : ℝ) ^ (2 / 21 : ℝ) / (4 * t ^ 1208) =
        2 * (CB * (P.h : ℝ) ^ (2 / 21 : ℝ) / (8 * t ^ 1208)) := by ring
    linarith
  -- `‖Q‖`
  have hQ0 := norm_QAB_le P hM0 (hM a b)
  have hsa : Real.sqrt ((M / ((a : ℝ) * b) ^ 6 * R ^ 6) ^ 2 * (q : ℝ) ^ 4 * (8 * R)) ≤
      2 ^ 8 * M * A ^ 13 := by
    rw [hqab]
    set X : ℝ := (a : ℝ) * b
    have hX : 1 ≤ X := by nlinarith
    have e : (M / X ^ 6 * R ^ 6) ^ 2 * X ^ 4 * (8 * R) = (2 ^ 8 * M * A ^ 13) ^ 2 / X ^ 8 := by
      rw [hRA]; field_simp; ring
    rw [e]
    calc Real.sqrt ((2 ^ 8 * M * A ^ 13) ^ 2 / X ^ 8) ≤ Real.sqrt ((2 ^ 8 * M * A ^ 13) ^ 2) :=
          Real.sqrt_le_sqrt (div_le_self (sq_nonneg _) (one_le_pow₀ hX))
      _ = _ := Real.sqrt_sq (by positivity)
  have hsb : Real.sqrt (2 * ‖∑' h : Gamma0 q, Iγ P h‖) ≤
      Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) / (2 * t ^ 604) := by
    have e : CB * (P.h : ℝ) ^ (2 / 21 : ℝ) / (4 * t ^ 1208) =
        (Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) / (2 * t ^ 604)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by positivity)]; ring
    rw [e] at hb
    refine (Real.sqrt_le_sqrt hb).trans (le_of_eq ?_)
    exact Real.sqrt_sq (by positivity)
  have hQ : ‖∫ p, PsiAB a b p.1 p.2 * conj (ft P p)‖ ≤
      2 ^ 6 * M * A ^ 13 * Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) / t ^ 604 := by
    refine hQ0.trans ?_
    calc 1 / 2 * Real.sqrt ((M / ((a : ℝ) * b) ^ 6 * R ^ 6) ^ 2 * (q : ℝ) ^ 4 * (8 * R)) *
          Real.sqrt (2 * ‖∑' h : Gamma0 q, Iγ P h‖)
        ≤ 1 / 2 * (2 ^ 8 * M * A ^ 13) *
            (Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) / (2 * t ^ 604)) := by gcongr
      _ = _ := by field_simp
  -- `W`
  have hmI := mI_ge P
  have hmB := mB_ge P
  have hW : 1 / (32 * t ^ 703) ≤ mI P * mB P := by
    have h1 : P.ε / (4 * P.Y) * P.ε ^ 2 ≤ mI P * mB P := by
      have : 0 ≤ P.ε / (4 * P.Y) := by positivity
      exact mul_le_mul hmI hmB (by positivity) (le_trans this hmI)
    have e : P.ε / (4 * P.Y) * P.ε ^ 2 = 1 / (32 * t ^ 703) := by
      rw [hεt, hYt]; field_simp; ring
    linarith
  have hWpos : 0 < mI P * mB P := lt_of_lt_of_le (by positivity) hW
  -- the Lipschitz error
  have hsπ : 0 < π * P.Y := by positivity
  obtain ⟨hs1, hb1'⟩ := hT a b P.h (b * (π * P.Y)) (by positivity)
  obtain ⟨hs2, -⟩ := hT a b P.h (b * (2 * π * P.Y)) (by positivity)
  obtain ⟨hs4, hb4⟩ := hT a b P.h (b * (4 * π * P.Y)) (by positivity)
  have hhs1 : (P.h : ℝ) * (π * P.Y) ≤ 1 := by nlinarith [Real.pi_pos]
  have hT1 := laplace_cR_le a b hC₀ P.h hsπ hhs1 hb1'
  have hT4 := laplace_cR_le a b hC₀ P.h (by positivity) hhY hb4
  have hs1' : Summable (fun n : ℕ => |cR a b P.h n| * Real.exp (-n * ((b * (2 * π * P.Y)) / 2))) := by
    have e : (b : ℝ) * (2 * π * P.Y) / 2 = b * (π * P.Y) := by ring
    rw [e]; exact hs1
  obtain ⟨hnS, hnB⟩ := n_laplace_c (cR a b P.h) (by positivity : 0 < (b : ℝ) * (2 * π * P.Y)) hs1'
  have hE := cfAB_sub_le P a b hhY hnS hs2 hs4
  set S1 := (b : ℝ) * ∑' n : ℕ, n * |cR a b P.h n| * Real.exp (-n * (b * (2 * π * P.Y)))
  set T0 := ∑' n : ℕ, |cR a b P.h n| * Real.exp (-n * (b * (4 * π * P.Y)))
  have hS1b : S1 ≤ 2 / (2 * π * P.Y) * (2 * C₀ * (1 / (π * P.Y) ^ 12)) := by
    have e : (b : ℝ) * (2 * π * P.Y) / 2 = b * (π * P.Y) := by ring
    rw [e] at hnB
    have : S1 ≤ b * (2 / (b * (2 * π * P.Y)) * (2 * C₀ * (1 / (π * P.Y) ^ 12))) := by
      simp only [S1]; gcongr; exact hnB.trans (by gcongr)
    refine this.trans (le_of_eq ?_)
    field_simp
  have hT0b : T0 ≤ 2 * C₀ * (1 / (π * P.Y) ^ 12) := by
    refine hT4.trans ?_
    gcongr; nlinarith
  set E := (2 * P.Y * A) ^ 12 * (2 * π * P.Y * P.ε * (A + 2)) * S1 +
    13 * (2 * P.Y * A) ^ 12 * P.ε * T0
  have hEb : E ≤ (2 * P.Y * A) ^ 12 * P.ε * C₀ * (1 / (π * P.Y) ^ 12) * (16 * A) := by
    have k1 : (2 * π * P.Y * P.ε * (A + 2)) * S1 ≤
        P.ε * (A + 2) * (4 * C₀ * (1 / (π * P.Y) ^ 12)) := by
      calc (2 * π * P.Y * P.ε * (A + 2)) * S1
          ≤ (2 * π * P.Y * P.ε * (A + 2)) * (2 / (2 * π * P.Y) * (2 * C₀ * (1 / (π * P.Y) ^ 12))) := by
            gcongr
        _ = P.ε * (A + 2) * (4 * C₀ * (1 / (π * P.Y) ^ 12)) := by field_simp; ring
    have hpos : 0 ≤ (2 * P.Y * A) ^ 12 := by positivity
    have hq : 0 ≤ C₀ * (1 / (π * P.Y) ^ 12) := by positivity
    calc E = (2 * P.Y * A) ^ 12 * ((2 * π * P.Y * P.ε * (A + 2)) * S1) +
          13 * (2 * P.Y * A) ^ 12 * P.ε * T0 := by
          show (2 * P.Y * A) ^ 12 * (2 * π * P.Y * P.ε * (A + 2)) * S1 +
            13 * (2 * P.Y * A) ^ 12 * P.ε * T0 = _
          ring
      _ ≤ (2 * P.Y * A) ^ 12 * (P.ε * (A + 2) * (4 * C₀ * (1 / (π * P.Y) ^ 12))) +
          13 * (2 * P.Y * A) ^ 12 * P.ε * (2 * C₀ * (1 / (π * P.Y) ^ 12)) := by gcongr
      _ = (2 * P.Y * A) ^ 12 * P.ε * (C₀ * (1 / (π * P.Y) ^ 12)) * (4 * A + 34) := by ring
      _ ≤ (2 * P.Y * A) ^ 12 * P.ε * (C₀ * (1 / (π * P.Y) ^ 12)) * (16 * A) := by
          gcongr; linarith
      _ = _ := by ring
  -- main-term comparison
  have hmain := main_term_leAB P a b (by positivity) (hM a b) (cfAB P a b P.Y (zeta0 P)) E hE
  have hc0 : ‖cfAB P a b P.Y (zeta0 P)‖ ≤
      ‖∫ p, PsiAB a b p.1 p.2 * conj (ft P p)‖ / (mI P * mB P) + E := by
    have : ‖cfAB P a b P.Y (zeta0 P)‖ * (mI P * mB P) ≤
        (‖∫ p, PsiAB a b p.1 p.2 * conj (ft P p)‖ / (mI P * mB P) + E) * (mI P * mB P) := by
      rw [add_mul, div_mul_cancel₀ _ hWpos.ne']; linarith
    exact le_of_mul_le_mul_right this hWpos
  have hG := norm_G0_leAB P a b hhY
  have hQW : ‖∫ p, PsiAB a b p.1 p.2 * conj (ft P p)‖ / (mI P * mB P) ≤
      2 ^ 11 * M * A ^ 13 * Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) * t ^ 99 := by
    rw [div_le_iff₀ hWpos]
    refine hQ.trans ?_
    have hX : 0 ≤ 2 ^ 11 * M * A ^ 13 * Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) * t ^ 99 := by
      positivity
    calc 2 ^ 6 * M * A ^ 13 * Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) / t ^ 604
        = 2 ^ 11 * M * A ^ 13 * Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) * t ^ 99 *
            (1 / (32 * t ^ 703)) := by
          field_simp; ring
      _ ≤ _ := by gcongr
  have hfinal : ‖GAB a b P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ)))‖ ≤
      2 ^ 13 / (P.Y * A) ^ 12 * (2 ^ 11 * M * A ^ 13 * Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) *
        t ^ 99 + (2 * P.Y * A) ^ 12 * P.ε * C₀ * (1 / (π * P.Y) ^ 12) * (16 * A)) := by
    refine hG.trans ?_
    gcongr
    linarith
  refine hfinal.trans ?_
  have hpi : (1 : ℝ) ≤ π ^ 12 := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hsq : Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) =
      Real.sqrt CB * (P.h : ℝ) ^ (1 / 21 : ℝ) := by
    rw [Real.sqrt_mul hCB0, Real.sqrt_eq_rpow ((P.h : ℝ) ^ (2 / 21 : ℝ)),
      ← Real.rpow_mul (by positivity)]
    norm_num
  have hsh : (1 : ℝ) ≤ (P.h : ℝ) ^ (1 / 21 : ℝ) := Real.one_le_rpow hhR (by norm_num)
  have e1 : 2 ^ 13 / (P.Y * A) ^ 12 * (2 ^ 11 * M * A ^ 13 *
      Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) * t ^ 99) =
      2 ^ 24 * M * Real.sqrt CB * (P.h : ℝ) ^ (1 / 21 : ℝ) * A * t ^ 99 * (1 / P.Y ^ 12) := by
    rw [hsq]; field_simp
  have e2 : 2 ^ 13 / (P.Y * A) ^ 12 * ((2 * P.Y * A) ^ 12 * P.ε * C₀ * (1 / (π * P.Y) ^ 12) *
      (16 * A)) = 2 ^ 28 * C₀ * A * t ^ 99 / π ^ 12 * (1 / P.Y ^ 12) := by
    rw [hεt]; field_simp; ring
  rw [mul_add, e1, e2]
  have hY12 : 0 < 1 / P.Y ^ 12 := by positivity
  have k2 : 2 ^ 28 * C₀ * A * t ^ 99 / π ^ 12 ≤
      2 ^ 28 * C₀ * (P.h : ℝ) ^ (1 / 21 : ℝ) * A * t ^ 99 := by
    rw [div_le_iff₀ (by positivity)]
    have h0 : 0 ≤ 2 ^ 28 * C₀ * A * t ^ 99 := by positivity
    calc 2 ^ 28 * C₀ * A * t ^ 99 = 2 ^ 28 * C₀ * A * t ^ 99 * 1 * 1 := by ring
      _ ≤ 2 ^ 28 * C₀ * A * t ^ 99 * (P.h : ℝ) ^ (1 / 21 : ℝ) * π ^ 12 := by gcongr
      _ = _ := by ring
  have := add_le_add_right (mul_le_mul_of_nonneg_right k2 hY12.le)
    (2 ^ 24 * M * Real.sqrt CB * (P.h : ℝ) ^ (1 / 21 : ℝ) * A * t ^ 99 * (1 / P.Y ^ 12))
  calc _ ≤ _ := this
    _ = (2 ^ 24 * M * Real.sqrt CB + 2 ^ 28 * C₀) * (P.h : ℝ) ^ (1 / 21 : ℝ) * A * t ^ 99 *
          (1 / P.Y ^ 12) := by ring

/-- **Pointwise bound for the Laplace transform of `cR a b ℓ`**:
`‖Gc (cR a b ℓ) (σ+iv)‖ ≤ K ℓ^{1/21} (|2v/σ|+3) b¹² σ^{−11901/1000}` for `ℓ ≥ 1`, `0 < σ ≤ b`,
`ℓσ ≤ b`. -/
theorem pointwise_Gc : ∃ K : ℝ, 0 ≤ K ∧ ∀ (a b : ℕ+) (ℓ : ℕ), 1 ≤ ℓ → ∀ σ v : ℝ, 0 < σ →
    σ ≤ b → (ℓ : ℝ) * σ ≤ b →
      ‖Gc (cR a b ℓ) ((σ : ℂ) + v * I)‖ ≤
        K * (ℓ : ℝ) ^ (1 / 21 : ℝ) * (|2 * v / σ| + 3) * (b : ℝ) ^ 12 *
          σ ^ (-(11901 / 1000 : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := pointwise_parAB
  refine ⟨K * (4 * π) ^ (11901 / 1000 : ℝ), by positivity, fun a b ℓ hℓ σ v hσ hσb hℓσ => ?_⟩
  have hbpos : (0 : ℝ) < b := by exact_mod_cast b.pos
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast b.one_le
  set Y := σ / (4 * π * b) with hYdef
  have hY : 0 < Y := by positivity
  have hY1 : Y ≤ 1 := by
    rw [hYdef, div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  set t := Y ^ (1 / 1000 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hY _
  have ht1 : t ≤ 1 := Real.rpow_le_one hY.le hY1 (by norm_num)
  let P : Par := ⟨ℓ, Y, t ^ 99 / 2, 2 * v / σ, hY, hY1, by positivity, by
    have : t ^ 99 ≤ 1 := pow_le_one₀ ht0.le ht1
    linarith⟩
  have hPh : P.h * (4 * π * P.Y) ≤ 1 := by
    show (ℓ : ℝ) * (4 * π * (σ / (4 * π * b))) ≤ 1
    rw [show 4 * π * (σ / (4 * π * b)) = σ / b by field_simp, mul_div_assoc', div_le_one hbpos]
    exact hℓσ
  have hb := hK a b P hℓ rfl hPh
  have hW : (b : ℂ) * (2 * π * P.Y * (1 + I * conj ((zeta0 P : UpperHalfPlane) : ℂ))) =
      (σ : ℂ) + v * I := by
    rw [W0_eq]
    show (b : ℂ) * ((((4 * π * (σ / (4 * π * b)) : ℝ)) : ℂ) +
      ((2 * π * (σ / (4 * π * b)) * (2 * v / σ) : ℝ) : ℂ) * I) = _
    have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hbpos.ne'
    have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
    ring
  rw [GAB_eq, hW] at hb
  refine hb.trans ?_
  show K * (ℓ : ℝ) ^ (1 / 21 : ℝ) * (|2 * v / σ| + 3) * t ^ 99 * (1 / Y ^ 12) ≤ _
  have e1 : t ^ 99 * (1 / Y ^ 12) = Y ^ (-(11901 / 1000 : ℝ)) := by
    have h1 : t ^ 99 = Y ^ (99 / 1000 : ℝ) := by
      rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hY.le]; norm_num
    have h2 : (1 / Y ^ 12 : ℝ) = Y ^ (-(12 : ℝ)) := by
      rw [Real.rpow_neg hY.le, one_div]; norm_cast
    rw [h1, h2, ← Real.rpow_add hY]
    norm_num
  have e2 : Y ^ (-(11901 / 1000 : ℝ)) =
      (4 * π) ^ (11901 / 1000 : ℝ) * (b : ℝ) ^ (11901 / 1000 : ℝ) * σ ^ (-(11901 / 1000 : ℝ)) := by
    have hp1 : 0 < (4 * π) ^ (11901 / 1000 : ℝ) := by positivity
    have hp2 : 0 < (b : ℝ) ^ (11901 / 1000 : ℝ) := by positivity
    rw [hYdef, Real.div_rpow hσ.le (by positivity), Real.mul_rpow (by positivity) hbpos.le,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 * π), Real.rpow_neg hbpos.le]
    field_simp
  have hb12 : (b : ℝ) ^ (11901 / 1000 : ℝ) ≤ (b : ℝ) ^ 12 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
  rw [mul_assoc (K * (ℓ : ℝ) ^ (1 / 21 : ℝ) * _), e1, e2]
  have h0 : 0 ≤ K * (ℓ : ℝ) ^ (1 / 21 : ℝ) * (|2 * v / σ| + 3) := by positivity
  have h1 : 0 ≤ (4 * π) ^ (11901 / 1000 : ℝ) * σ ^ (-(11901 / 1000 : ℝ)) := by positivity
  calc K * (ℓ : ℝ) ^ (1 / 21 : ℝ) * (|2 * v / σ| + 3) * ((4 * π) ^ (11901 / 1000 : ℝ) *
        (b : ℝ) ^ (11901 / 1000 : ℝ) * σ ^ (-(11901 / 1000 : ℝ)))
      = K * (ℓ : ℝ) ^ (1 / 21 : ℝ) * (|2 * v / σ| + 3) *
          ((4 * π) ^ (11901 / 1000 : ℝ) * σ ^ (-(11901 / 1000 : ℝ))) *
          (b : ℝ) ^ (11901 / 1000 : ℝ) := by ring
    _ ≤ K * (ℓ : ℝ) ^ (1 / 21 : ℝ) * (|2 * v / σ| + 3) *
          ((4 * π) ^ (11901 / 1000 : ℝ) * σ ^ (-(11901 / 1000 : ℝ))) * (b : ℝ) ^ 12 := by
        gcongr
    _ = _ := by ring

end RamanujanTau.SCS2Coprime
