/-
# The pointwise formula with the smoothing tied to the cut-off: `h = √(x/N)/6`

`pointwise_simple`: for `0 < δ ≤ 23/4` there is `C` with, for `x ≥ 1`, `1 ≤ N ≤ x`,

    |S(x) − V_N(x)| ≤ Σ_{x<n≤x+2√(x/N)} |τ(n)| + C x^{23/4} N^{1/4+δ}.

Also `abs_Vth_le`: `|V_N(x)| ≤ x^{23/4}/(π√2) · N^{β−25/4} St β`.
-/
import RamanujanTau.VoronoiPointwise.Formula

set_option autoImplicit false

namespace RamanujanTau.VoronoiPointwise

open Real
open RamanujanTau.VoronoiTrunc

lemma rpow_x_identity {x : ℝ} (hx : 0 < x) :
    x ^ 12 * x ^ (-(1 / 4) : ℝ) / x ^ 6 = x ^ (23 / 4 : ℝ) := by
  rw [← Real.rpow_natCast x 12, ← Real.rpow_natCast x 6, ← Real.rpow_add hx, ← Real.rpow_sub hx]
  norm_num

lemma rpow_N_tail {N δ : ℝ} (hN : 1 ≤ N) (hδ : δ ≤ 23 / 4) :
    N ^ 6 * (N + 1) ^ (δ - 23 / 4) ≤ N ^ (1 / 4 + δ) := by
  have hN0 : 0 < N := by linarith
  have h1 : (N + 1) ^ (δ - 23 / 4) ≤ N ^ (δ - 23 / 4) :=
    Real.rpow_le_rpow_of_nonpos hN0 (by linarith) (by linarith)
  calc N ^ 6 * (N + 1) ^ (δ - 23 / 4) ≤ N ^ 6 * N ^ (δ - 23 / 4) := by gcongr
    _ = N ^ (1 / 4 + δ) := by
        rw [← Real.rpow_natCast N 6, ← Real.rpow_add hN0]; congr 1; push_cast; ring

lemma rpow_lip_identity {x N δ : ℝ} (hx : 0 < x) (hN : 0 < N) :
    N ^ (3 / 4 + δ) * x ^ (21 / 4 : ℝ) * √(x / N) = x ^ (23 / 4 : ℝ) * N ^ (1 / 4 + δ) := by
  rw [Real.sqrt_eq_rpow, Real.div_rpow hx.le hN.le]
  have e1 : x ^ (21 / 4 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ (23 / 4 : ℝ) := by
    rw [← Real.rpow_add hx]; norm_num
  have e2 : N ^ (3 / 4 + δ) / N ^ (1 / 2 : ℝ) = N ^ (1 / 4 + δ) := by
    rw [← Real.rpow_sub hN]; congr 1; ring
  rw [← e1, ← e2]
  field_simp

lemma sqrt_div_le {x N : ℝ} (hx : 1 ≤ x) (hN : 1 ≤ N) : √(x / N) ≤ x := by
  have hN0 : 0 < N := by linarith
  have hu : x / N ≤ x := div_le_self (by linarith) hN
  have hu1 : 0 ≤ x / N := div_nonneg (by linarith) hN0.le
  calc √(x / N) ≤ √x := Real.sqrt_le_sqrt hu
    _ ≤ x := by
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith

lemma one_le_sqrt_div {x N : ℝ} (hN : 0 < N) (hNx : N ≤ x) : 1 ≤ √(x / N) := by
  rw [Real.le_sqrt (by norm_num) (div_nonneg (by linarith) hN.le), one_pow, le_div_iff₀ hN]; linarith

/-- **Pointwise truncated Voronoi, simple form** (unconditional). -/
theorem pointwise_simple {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 23 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ x →
      |Sre x - Vth N x| ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + 2 * √(x / N)⌋₊, |((tau n : ℤ) : ℝ)| +
        C * (x ^ (23 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 + δ)) := by
  set β : ℝ := 13 / 2 + δ with hβdef
  have hβ : 13 / 2 < β := by rw [hβdef]; linarith
  have hβ' : β ≤ 49 / 4 := by rw [hβdef]; linarith
  have hS := St_nonneg β
  have hCK : 0 ≤ CK := by unfold CK; have := Ck_nonneg 12; positivity
  have hCT : 0 ≤ CT := by unfold CT; have := Ck_nonneg 24; positivity
  set C1 : ℝ := CK * 3 ^ (11 / 2 : ℝ) * St β
  set C2 : ℝ := 6 ^ 12 * (CT / π ^ 12) * 3 ^ 12 * St β
  set C3 : ℝ := 1 / (π * √2) * (6 + 2 * π) * St β * 3 ^ (21 / 4 : ℝ) * 2
  have hC1 : 0 ≤ C1 := by positivity
  have hC2 : 0 ≤ C2 := by positivity
  have hC3 : 0 ≤ C3 := by positivity
  refine ⟨C1 + C2 + C3, by positivity, fun x hx N hN hNx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set u : ℝ := √(x / N) with hu
  have hu1 : 1 ≤ u := one_le_sqrt_div hN0 hNx
  have hux : u ≤ x := sqrt_div_le hx hN1
  set h : ℝ := u / 6 with hhdef
  have hh : 0 < h := by rw [hhdef]; linarith
  have h6 : 6 * h ≤ x := by rw [hhdef]; linarith
  have key := pointwise_core hβ hβ' hx hh h6 N
  have e12 : 12 * h = 2 * u := by rw [hhdef]; ring
  rw [e12] at key
  refine key.trans (add_le_add_right ?_ _)
  set P : ℝ := x ^ (23 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 + δ) with hP
  -- term 1
  have t1 : CK * (3 * x) ^ (11 / 2 : ℝ) * ((N : ℝ) ^ (β - 13 / 2) * St β) ≤ C1 * P := by
    rw [Real.mul_rpow (by norm_num) hx0.le]
    have a1 : x ^ (11 / 2 : ℝ) ≤ x ^ (23 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    have a2 : (N : ℝ) ^ (β - 13 / 2) ≤ (N : ℝ) ^ (1 / 4 + δ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by rw [hβdef]; linarith)
    calc CK * (3 ^ (11 / 2 : ℝ) * x ^ (11 / 2 : ℝ)) * ((N : ℝ) ^ (β - 13 / 2) * St β)
        = CK * 3 ^ (11 / 2 : ℝ) * St β * (x ^ (11 / 2 : ℝ) * (N : ℝ) ^ (β - 13 / 2)) := by ring
      _ ≤ CK * 3 ^ (11 / 2 : ℝ) * St β * (x ^ (23 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 + δ)) := by gcongr
      _ = C1 * P := rfl
  -- term 2
  have t2 : (h ^ 12)⁻¹ * (CT / π ^ 12 * (3 * x) ^ 12 * x ^ (-(1 / 4) : ℝ) *
      (((N : ℝ) + 1) ^ (β - 49 / 4) * St β)) ≤ C2 * P := by
    have hh12 : h ^ 12 = x ^ 6 / (N : ℝ) ^ 6 / 6 ^ 12 := by
      rw [hhdef, div_pow, hu, show (12 : ℕ) = 2 * 6 by rfl, pow_mul, Real.sq_sqrt (by positivity),
        div_pow]
    have hinv : (h ^ 12)⁻¹ = 6 ^ 12 * (N : ℝ) ^ 6 / x ^ 6 := by
      rw [hh12]; field_simp
    rw [hinv, mul_pow]
    have a2 := rpow_N_tail (N := (N : ℝ)) (δ := δ) hN1 hδ'
    have eβ : β - 49 / 4 = δ - 23 / 4 := by rw [hβdef]; ring
    rw [eβ]
    have ex := rpow_x_identity hx0
    calc 6 ^ 12 * (N : ℝ) ^ 6 / x ^ 6 * (CT / π ^ 12 * (3 ^ 12 * x ^ 12) * x ^ (-(1 / 4) : ℝ) *
          (((N : ℝ) + 1) ^ (δ - 23 / 4) * St β))
        = 6 ^ 12 * (CT / π ^ 12) * 3 ^ 12 * St β * (x ^ 12 * x ^ (-(1 / 4) : ℝ) / x ^ 6) *
          ((N : ℝ) ^ 6 * ((N : ℝ) + 1) ^ (δ - 23 / 4)) := by ring
      _ ≤ 6 ^ 12 * (CT / π ^ 12) * 3 ^ 12 * St β * (x ^ 12 * x ^ (-(1 / 4) : ℝ) / x ^ 6) *
          (N : ℝ) ^ (1 / 4 + δ) := by gcongr
      _ = C2 * P := by
          rw [ex]
          show _ = (6 ^ 12 * (CT / π ^ 12) * 3 ^ 12 * St β) * (x ^ (23 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 + δ))
          ring
  -- term 3
  have t3 : 1 / (π * √2) * ((6 + 2 * π) * ((N : ℝ) ^ (β - 23 / 4) * St β)) * (3 * x) ^ (21 / 4 : ℝ) *
      (12 * h) ≤ C3 * P := by
    rw [Real.mul_rpow (by norm_num) hx0.le, e12]
    have eβ : β - 23 / 4 = 3 / 4 + δ := by rw [hβdef]; ring
    rw [eβ]
    have el := rpow_lip_identity (δ := δ) hx0 hN0
    apply le_of_eq
    calc 1 / (π * √2) * ((6 + 2 * π) * ((N : ℝ) ^ (3 / 4 + δ) * St β)) *
          (3 ^ (21 / 4 : ℝ) * x ^ (21 / 4 : ℝ)) * (2 * u)
        = 1 / (π * √2) * (6 + 2 * π) * St β * 3 ^ (21 / 4 : ℝ) * 2 *
          ((N : ℝ) ^ (3 / 4 + δ) * x ^ (21 / 4 : ℝ) * √(x / N)) := by rw [hu]; ring
      _ = C3 * P := by
          rw [el]
  unfold Bpw
  linarith

/-- `|V_N(x)| ≤ x^{23/4}/(π√2) · N^{β−25/4} St β`. -/
lemma abs_Vth_le {β : ℝ} (hβ : 13 / 2 < β) {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    |Vth N x| ≤ x ^ (23 / 4 : ℝ) / (π * √2) * ((N : ℝ) ^ (β - 25 / 4) * St β) := by
  unfold Vth
  rw [abs_mul, abs_of_nonneg (by positivity)]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans ?_ (head_sum_le (β := β) (γ := 25 / 4) hβ (by linarith) N)
  refine Finset.sum_le_sum fun n _ => ?_
  unfold bco
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (-(25 / 4) : ℝ))]
  have := Real.abs_cos_le_one (th n x)
  have : 0 ≤ |((tau n : ℤ) : ℝ)| * (n : ℝ) ^ (-(25 / 4) : ℝ) := by positivity
  nlinarith

end RamanujanTau.VoronoiPointwise
