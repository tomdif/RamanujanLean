/-
# The main-term inequality for log-concavity

With `f(u) = (u−1)/(2u³)` and `g(u) = e^{−u/2}`: if `U ≥ 60`, `u₊² = U² + γ`, `u₋² = U² − γ` with
`γ ∈ [6.5, 6.7]` (in the application `γ = 2π²/3`), then

  `e^{u₊+u₋−2U} (f(u₊) + g(u₊)) (f(u₋) + g(u₋)) < (f(U) − g(U))²`   and   `g(U) < f(U)`.

The proof is elementary, writing `P = u₊u₋` and `S = u₊ + u₋`. Then `P² = U⁴ − γ²` and `S² = 2U² + 2P`, so
`σ = 2U − S ≥ γ²/(4U³)` (strict concavity of `√`) and `f(u₊)f(u₋) = (P − S + 1)/(4P³)`. The saving `e^{−σ}`
beats the loss from `P < U²` by a margin `γ²/(64U⁷)`, and the `g` terms are at most
`2²⁰·20!/(U−1)²⁰` by `x²⁰/20! ≤ eˣ`.
-/
import Mathlib

set_option autoImplicit false

namespace LogConcave
open Real

noncomputable section

def ff (u : ℝ) : ℝ := (u - 1) / (2 * u ^ 3)
def gg (u : ℝ) : ℝ := exp (-(u / 2))

/-- `ε = 2²⁰·20!/(U−1)²⁰`. -/
def eps (U : ℝ) : ℝ := 2 ^ 20 * (Nat.factorial 20 : ℝ) / (U - 1) ^ 20

lemma gg_le {U u : ℝ} (hU : 2 ≤ U) (hu : U - 1 ≤ u) : gg u ≤ eps U := by
  have hW : 0 < U - 1 := by linarith
  have h1 := pow_div_factorial_le_exp (x := u / 2) (by linarith) 20
  have h2 : ((U - 1) / 2) ^ 20 / (Nat.factorial 20 : ℝ) ≤ (u / 2) ^ 20 / (Nat.factorial 20 : ℝ) := by
    gcongr
  have hpos : 0 < ((U - 1) / 2) ^ 20 / (Nat.factorial 20 : ℝ) := by positivity
  have h3 : ((U - 1) / 2) ^ 20 / (Nat.factorial 20 : ℝ) ≤ exp (u / 2) := h2.trans h1
  rw [gg, Real.exp_neg, eps]
  rw [inv_le_comm₀ (exp_pos _) (by positivity)]
  refine le_trans (le_of_eq ?_) h3
  field_simp

lemma ff_nonneg {u : ℝ} (hu : 1 ≤ u) : 0 ≤ ff u := by
  unfold ff
  have : 0 < u := by linarith
  have : 0 ≤ u - 1 := by linarith
  positivity

lemma ff_le {u : ℝ} (hu : 1 ≤ u) : ff u ≤ 1 / (2 * u ^ 2) := by
  unfold ff
  have : 0 < u := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h : (u - 1) * (2 * u ^ 2) ≤ 1 * (2 * u ^ 3) := by
    have : (u - 1) * (2 * u ^ 2) = 2 * u ^ 3 - 2 * u ^ 2 := by ring
    rw [this]; nlinarith [pow_pos (by linarith : (0:ℝ) < u) 2]
  linarith

lemma ff_ge {u : ℝ} (hu : 2 ≤ u) : 1 / (4 * u ^ 2) ≤ ff u := by
  unfold ff
  have hu0 : 0 < u := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 1 * (2 * u ^ 3) = 2 * u * u ^ 2 := by ring
  have h2 : (u - 1) * (4 * u ^ 2) = (4 * u - 4) * u ^ 2 := by ring
  rw [this, h2]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

def Cc : ℝ := 2 ^ 20 * (Nat.factorial 20 : ℝ)

lemma Cc_pos : 0 < Cc := by unfold Cc; positivity

/-- the numeric core: `3ε/(U−1)² < γ²/(64U⁷)` and `ε ≤ 1/(U−1)²` for `U ≥ 60`, `γ² ≥ 42`. -/
lemma eps_small {U : ℝ} (hU : 60 ≤ U) (γ2 : ℝ) (hγ : 42 ≤ γ2) :
    3 * eps U / (U - 1) ^ 2 < γ2 / (64 * U ^ 7) ∧ eps U ≤ 1 / (U - 1) ^ 2 := by
  have hW59 : (59 : ℝ) ≤ U - 1 := by linarith
  have hWp : 0 < U - 1 := by linarith
  have hUp : 0 < U := by linarith
  have hU7 : U ^ 7 ≤ (60 / 59) ^ 7 * (U - 1) ^ 7 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hUp.le (by linarith) 7
  have hW15 : (59 : ℝ) ^ 15 ≤ (U - 1) ^ 15 := pow_le_pow_left₀ (by norm_num) hW59 15
  have hC : 192 * Cc * (60 / 59) ^ 7 < 42 * 59 ^ 15 := by unfold Cc; norm_num [Nat.factorial]
  have hCp := Cc_pos
  have heps : eps U = Cc / (U - 1) ^ 20 := rfl
  constructor
  · have e : 3 * eps U / (U - 1) ^ 2 = 3 * Cc / ((U - 1) ^ 7 * (U - 1) ^ 15) := by
      rw [heps]; field_simp
    rw [e, div_lt_div_iff₀ (by positivity) (by positivity)]
    have h1 : 3 * Cc * (64 * U ^ 7) ≤ 192 * Cc * (60 / 59) ^ 7 * (U - 1) ^ 7 := by
      have := mul_le_mul_of_nonneg_left hU7 (by positivity : (0 : ℝ) ≤ 192 * Cc)
      linarith
    have h2 : 192 * Cc * (60 / 59) ^ 7 * (U - 1) ^ 7 < 42 * 59 ^ 15 * (U - 1) ^ 7 :=
      mul_lt_mul_of_pos_right hC (by positivity)
    have h3 : 42 * 59 ^ 15 * (U - 1) ^ 7 ≤ γ2 * ((U - 1) ^ 7 * (U - 1) ^ 15) := by
      have h4 : (42 : ℝ) * 59 ^ 15 ≤ γ2 * (U - 1) ^ 15 :=
        mul_le_mul hγ hW15 (by positivity) (by linarith)
      have := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ (U - 1) ^ 7)
      linarith
    linarith
  · rw [heps, div_le_div_iff₀ (by positivity) (by positivity)]
    have h18 : (59 : ℝ) ^ 18 ≤ (U - 1) ^ 18 := pow_le_pow_left₀ (by norm_num) hW59 18
    have hc : Cc ≤ 59 ^ 18 := by unfold Cc; norm_num [Nat.factorial]
    have : Cc * (U - 1) ^ 2 ≤ (U - 1) ^ 18 * (U - 1) ^ 2 :=
      mul_le_mul_of_nonneg_right (hc.trans h18) (by positivity)
    have e : (U - 1) ^ 18 * (U - 1) ^ 2 = 1 * (U - 1) ^ 20 := by ring
    linarith

/-- the algebraic heart: `(A+σ)/((1+σ)P³) ≤ (U−1)²/U⁶ − γ²/(16U⁷)`. -/
lemma core {U P σ γ2 : ℝ} (hU : 60 ≤ U) (hγ : 0 ≤ γ2) (hγ' : γ2 ≤ 45) (hP0 : 0 < P) (hPU : P ≤ U ^ 2)
    (hd : (U ^ 2 - P) * U ^ 2 ≤ γ2) (hσ1 : γ2 / (4 * U ^ 3) ≤ σ) (hσ2 : σ ≤ 1) :
    (P - 2 * U + 1 + σ) / ((1 + σ) * P ^ 3) ≤ (U - 1) ^ 2 / U ^ 6 - γ2 / (16 * U ^ 7) := by
  have hUp : 0 < U := by linarith
  have hU2 : 3600 ≤ U ^ 2 := by nlinarith
  set d := U ^ 2 - P with hd_def
  have hd0 : 0 ≤ d := by linarith
  have hd1 : d ≤ 1 := by
    by_contra h
    push Not at h
    have : U ^ 2 < d * U ^ 2 := by nlinarith
    linarith
  have hPd : P = U ^ 2 - d := by rw [hd_def]; ring
  set A := P - 2 * U + 1 with hA
  have hAeq : A = (U - 1) ^ 2 - d := by rw [hA, hPd]; ring
  have hA1 : 1 ≤ A := by rw [hAeq]; nlinarith
  have hσ0 : 0 ≤ σ := le_trans (by positivity) hσ1
  have step1 : (A + σ) / (1 + σ) ≤ A - σ * (A - 1) / 2 := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_nonneg (mul_nonneg (sub_nonneg.mpr hA1) (sub_nonneg.mpr hσ2)) hσ0
    nlinarith
  have hP3 : 0 < P ^ 3 := by positivity
  have hlhs : (A + σ) / ((1 + σ) * P ^ 3) ≤ (A - σ * (A - 1) / 2) / P ^ 3 := by
    rw [← div_div]; exact div_le_div_of_nonneg_right step1 hP3.le
  refine hlhs.trans ?_
  have hP3lo : U ^ 6 - 3 * d * U ^ 4 ≤ P ^ 3 := by
    have e : P ^ 3 - (U ^ 6 - 3 * d * U ^ 4) = d ^ 2 * (3 * U ^ 2 - d) := by rw [hPd]; ring
    have : 0 ≤ d ^ 2 * (3 * U ^ 2 - d) := mul_nonneg (sq_nonneg d) (by linarith)
    linarith
  have hP3hi : P ^ 3 ≤ U ^ 6 := by
    have := pow_le_pow_left₀ hP0.le hPU 3
    have e : (U ^ 2) ^ 3 = U ^ 6 := by ring
    linarith
  have hσA : γ2 / (4 * U ^ 3) * (U ^ 2 - 2 * U - 1) ≤ σ * (A - 1) := by
    have : U ^ 2 - 2 * U - 1 ≤ A - 1 := by rw [hAeq]; nlinarith
    have h0 : 0 ≤ U ^ 2 - 2 * U - 1 := by nlinarith
    exact mul_le_mul hσ1 this h0 hσ0
  rw [div_le_iff₀ hP3]
  have hU7 : 0 < 16 * U ^ 7 := by positivity
  -- F1
  have F1 : 2 * γ2 * U ^ 4 * (U ^ 2 - 2 * U - 1) ≤ 8 * U ^ 7 * (σ * (A - 1)) := by
    have := mul_le_mul_of_nonneg_left hσA (by positivity : (0 : ℝ) ≤ 8 * U ^ 7)
    have e : 8 * U ^ 7 * (γ2 / (4 * U ^ 3) * (U ^ 2 - 2 * U - 1)) = 2 * γ2 * U ^ 4 * (U ^ 2 - 2 * U - 1) := by
      field_simp; ring
    linarith
  -- F2
  have F2 : 16 * U * (U - 1) ^ 2 * (U ^ 6 - 3 * d * U ^ 4) - γ2 * U ^ 6 ≤
      (16 * U * (U - 1) ^ 2 - γ2) * P ^ 3 := by
    have h1 := mul_le_mul_of_nonneg_left hP3lo (by positivity : (0 : ℝ) ≤ 16 * U * (U - 1) ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hP3hi hγ
    nlinarith
  have hq1 : 16 * d * U ^ 5 * (3 * (U - 1) ^ 2 - U ^ 2) ≤ 16 * d * U ^ 5 * (2 * U ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have hq2 : 32 * d * U ^ 7 ≤ 32 * γ2 * U ^ 5 := by
    have := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 32 * U ^ 5)
    have e : 32 * U ^ 5 * ((U ^ 2 - P) * U ^ 2) = 32 * d * U ^ 7 := by rw [hd_def]; ring
    linarith
  have hq3 : 32 * γ2 * U ^ 5 ≤ γ2 * U ^ 4 * (U ^ 2 - 4 * U - 2) := by
    have h0 : 0 ≤ U ^ 2 - 36 * U - 2 := by nlinarith
    have := mul_nonneg (mul_nonneg hγ (by positivity : (0 : ℝ) ≤ U ^ 4)) h0
    nlinarith
  have key : 16 * U ^ 7 * (A - σ * (A - 1) / 2) ≤ (16 * U * (U - 1) ^ 2 - γ2) * P ^ 3 := by
    rw [hAeq] at F1 ⊢
    nlinarith
  have e1 : 16 * U ^ 7 * (((U - 1) ^ 2 / U ^ 6 - γ2 / (16 * U ^ 7)) * P ^ 3) =
      (16 * U * (U - 1) ^ 2 - γ2) * P ^ 3 := by field_simp
  rw [← e1] at key
  exact le_of_mul_le_mul_left key hU7

set_option maxHeartbeats 1600000 in
/-- **the main-term inequality**. -/
theorem main_ineq {U up um γ : ℝ} (hU : 60 ≤ U) (hγ1 : 6.5 ≤ γ) (hγ2 : γ ≤ 6.7) (hup : 0 < up) (hum : 0 < um)
    (hup2 : up ^ 2 = U ^ 2 + γ) (hum2 : um ^ 2 = U ^ 2 - γ) :
    exp (up + um - 2 * U) * (ff up + gg up) * (ff um + gg um) < (ff U - gg U) ^ 2 ∧ gg U < ff U := by
  have hUp : 0 < U := by linarith
  have hU2 : 3600 ≤ U ^ 2 := by nlinarith
  have hγsq : 42 ≤ γ ^ 2 := by nlinarith
  have hγsq' : γ ^ 2 ≤ 45 := by nlinarith
  have hup1 : U - 1 ≤ up := by
    refine (pow_le_pow_iff_left₀ (by linarith) hup.le two_ne_zero).mp ?_
    rw [hup2]; nlinarith
  have hum1 : U - 1 ≤ um := by
    refine (pow_le_pow_iff_left₀ (by linarith) hum.le two_ne_zero).mp ?_
    rw [hum2]; nlinarith
  set P := up * um with hPdef
  set S := up + um with hSdef
  have hP0 : 0 < P := mul_pos hup hum
  have hP2 : P ^ 2 = U ^ 4 - γ ^ 2 := by
    rw [hPdef, mul_pow, hup2, hum2]; ring
  have hfac : (U ^ 2 - P) * (U ^ 2 + P) = γ ^ 2 := by
    have : (U ^ 2 - P) * (U ^ 2 + P) = U ^ 4 - P ^ 2 := by ring
    rw [this, hP2]; ring
  have hPU : P ≤ U ^ 2 := by
    by_contra h
    push Not at h
    have : (U ^ 2 - P) * (U ^ 2 + P) < 0 := mul_neg_of_neg_of_pos (by linarith) (by positivity)
    nlinarith
  have hd : (U ^ 2 - P) * U ^ 2 ≤ γ ^ 2 := by
    have := mul_le_mul_of_nonneg_left (by linarith : U ^ 2 ≤ U ^ 2 + P) (by linarith : 0 ≤ U ^ 2 - P)
    linarith
  have hS2 : S ^ 2 = 2 * U ^ 2 + 2 * P := by
    have : S ^ 2 = up ^ 2 + um ^ 2 + 2 * P := by rw [hSdef, hPdef]; ring
    rw [this, hup2, hum2]; ring
  have hS0 : 0 < S := by positivity
  have hSU : S ≤ 2 * U := by
    by_contra h
    push Not at h
    have : (S - 2 * U) * (S + 2 * U) > 0 := mul_pos (by linarith) (by linarith)
    nlinarith
  set σ := 2 * U - S with hσdef
  have hσ0 : 0 ≤ σ := by linarith
  have e1 : σ * (2 * U + S) = 2 * (U ^ 2 - P) := by rw [hσdef]; linear_combination (-1 : ℝ) * hS2
  have hσ1 : γ ^ 2 / (4 * U ^ 3) ≤ σ := by
    have h1 : σ * (2 * U + S) * (U ^ 2 + P) = 2 * γ ^ 2 := by rw [e1]; linear_combination 2 * hfac
    have h2 : σ * (2 * U + S) * (U ^ 2 + P) ≤ σ * (4 * U) * (2 * U ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hσ0) (by linarith) (by positivity) (by positivity)
    rw [div_le_iff₀ (by positivity)]
    have e : σ * (4 * U) * (2 * U ^ 2) = 2 * (σ * (4 * U ^ 3)) := by ring
    linarith
  have hσ2 : σ ≤ 1 := by
    have hUP : U ^ 2 - P ≤ 1 := by
      by_contra h
      push Not at h
      have : U ^ 2 < (U ^ 2 - P) * U ^ 2 := by nlinarith
      linarith
    have : σ * (2 * U) ≤ σ * (2 * U + S) := mul_le_mul_of_nonneg_left (by linarith) hσ0
    have : σ * (2 * U) ≤ 2 := by linarith
    nlinarith
  have hff : ff up * ff um = (P - 2 * U + 1 + σ) / (4 * P ^ 3) := by
    have hS' : P - 2 * U + 1 + σ = P - S + 1 := by rw [hσdef]; ring
    rw [hS']
    unfold ff; rw [hPdef, hSdef]; field_simp; ring
  have hcore := core hU (sq_nonneg γ) hγsq' hP0 hPU hd hσ1 hσ2
  have hfmain : exp (-σ) * (ff up * ff um) ≤ ff U ^ 2 - γ ^ 2 / (64 * U ^ 7) := by
    have he : exp (-σ) ≤ 1 / (1 + σ) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp σ])
    have hnn : 0 ≤ ff up * ff um := mul_nonneg (ff_nonneg (by linarith)) (ff_nonneg (by linarith))
    have e2 : 1 / (1 + σ) * (ff up * ff um) = (P - 2 * U + 1 + σ) / ((1 + σ) * P ^ 3) / 4 := by
      rw [hff]; field_simp
    have e3 : ((U - 1) ^ 2 / U ^ 6 - γ ^ 2 / (16 * U ^ 7)) / 4 = ff U ^ 2 - γ ^ 2 / (64 * U ^ 7) := by
      unfold ff; field_simp; ring
    have := mul_le_mul_of_nonneg_right he hnn
    rw [e2] at this
    linarith
  -- the g's and f's at the three points
  have hU2' : (2 : ℝ) ≤ U := by linarith
  have gp := gg_le hU2' hup1
  have gm := gg_le hU2' hum1
  have g0 := gg_le hU2' (by linarith : U - 1 ≤ U)
  have gpn : 0 ≤ gg up := (exp_pos _).le
  have gmn : 0 ≤ gg um := (exp_pos _).le
  have g0n : 0 ≤ gg U := (exp_pos _).le
  have hW : 0 < U - 1 := by linarith
  set B := 1 / (2 * (U - 1) ^ 2) with hB
  have hBn : 0 ≤ B := by positivity
  have fle : ∀ u, U - 1 ≤ u → ff u ≤ B := by
    intro u hu
    have h1 : (1 : ℝ) ≤ u := by linarith
    refine (ff_le h1).trans (one_div_le_one_div_of_le (by positivity) ?_)
    have : (U - 1) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hW.le hu 2
    linarith
  have fp1 := fle up hup1
  have fm1 := fle um hum1
  have f01 := fle U (by linarith)
  have fpn := ff_nonneg (by linarith : (1 : ℝ) ≤ up)
  have fmn := ff_nonneg (by linarith : (1 : ℝ) ≤ um)
  obtain ⟨he1, he2⟩ := eps_small hU (γ ^ 2) hγsq
  set ε := eps U with hεdef
  have hepsn : 0 ≤ ε := g0n.trans g0
  have hεB : ε ≤ 2 * B := by
    have : 2 * B = 1 / (U - 1) ^ 2 := by rw [hB]; field_simp
    linarith
  have h3ε : 3 * ε * (2 * B) < γ ^ 2 / (64 * U ^ 7) := by
    have : 3 * ε * (2 * B) = 3 * ε / (U - 1) ^ 2 := by rw [hB]; field_simp
    linarith
  have hexp1 : exp (-σ) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hexpn : 0 ≤ exp (-σ) := (exp_pos _).le
  have hS : up + um - 2 * U = -σ := by rw [hσdef, hSdef]; ring
  rw [hS]
  constructor
  · have hcr : ff up * gg um + gg up * ff um + gg up * gg um ≤ B * ε + ε * B + ε * ε := by
      have h1 := mul_le_mul fp1 gm gmn hBn
      have h2 := mul_le_mul gp fm1 fmn hepsn
      have h3 := mul_le_mul gp gm gmn hepsn
      linarith
    have hnn : 0 ≤ ff up * gg um + gg up * ff um + gg up * gg um := by positivity
    have hcross : exp (-σ) * (ff up * gg um + gg up * ff um + gg up * gg um) ≤ 2 * B * ε + ε * ε := by
      have := mul_le_mul_of_nonneg_right hexp1 hnn
      linarith
    have hexpand : exp (-σ) * (ff up + gg up) * (ff um + gg um) =
        exp (-σ) * (ff up * ff um) + exp (-σ) * (ff up * gg um + gg up * ff um + gg up * gg um) := by ring
    have hlhs : ff U ^ 2 - 2 * B * ε ≤ (ff U - gg U) ^ 2 := by
      have h1 := mul_le_mul f01 g0 g0n hBn
      have e : (ff U - gg U) ^ 2 = ff U ^ 2 - 2 * (ff U * gg U) + gg U ^ 2 := by ring
      linarith only [h1, e, sq_nonneg (gg U)]
    have hεε : ε * ε ≤ ε * (2 * B) := mul_le_mul_of_nonneg_left hεB hepsn
    rw [hexpand]
    linarith only [hfmain, hcross, hlhs, hεε, h3ε]
  · have hf0lo := ff_ge hU2'
    have hk : 3 * ε * (64 * U ^ 7) < γ ^ 2 * (U - 1) ^ 2 := by
      rwa [div_lt_div_iff₀ (by positivity) (by positivity)] at he1
    have hW2 : (U - 1) ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ hW.le (by linarith) 2
    have hk2 : ε * (192 * U ^ 7) < 45 * U ^ 2 := by
      have h45 := mul_le_mul hγsq' hW2 (by positivity) (by norm_num)
      linarith only [hk, h45]
    have hlt : ε < 1 / (4 * U ^ 2) := by
      rw [lt_div_iff₀ (by positivity)]
      by_contra h
      push Not at h
      have h5 : (1 : ℝ) ≤ U ^ 3 := one_le_pow₀ (by linarith)
      have : 48 * U ^ 5 ≤ ε * (4 * U ^ 2) * (48 * U ^ 5) := by
        have h48 := mul_le_mul_of_nonneg_right h (by positivity : (0 : ℝ) ≤ 48 * U ^ 5)
        linarith only [h48]
      have e : ε * (4 * U ^ 2) * (48 * U ^ 5) = ε * (192 * U ^ 7) := by ring
      have h455 : 45 * U ^ 2 ≤ 48 * U ^ 5 := by
        have e5 : U ^ 5 = U ^ 3 * U ^ 2 := by ring
        have := mul_le_mul_of_nonneg_right h5 (sq_nonneg U)
        rw [e5]; linarith only [this, sq_nonneg U]
      linarith only [this, e, h455, hk2]
    linarith only [hlt, hf0lo, g0]

end

end LogConcave
