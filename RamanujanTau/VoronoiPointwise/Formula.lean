/-
# The pointwise truncated Voronoi decomposition (sharp cut-off `N`, smoothing `h`)

For `x ≥ 1`, `0 < h`, `6h ≤ x` and any `N` (all with Riesz order `r = 12`):

    S(x) − V_N(x) = [S − S_h] + h^{−12}[It_h^{12} E_N] + h^{−12}[tail n > N] + [h^{−12} It_h^{12} V_N − V_N],

where `S_h = h^{−12} Σ τ(n) It_h^{12} k₀(n,·)` is the smoothed sum, `E_N` the kernel error of the
head `n ≤ N`. Compared with `VoronoiTrunc.pointwise_bound` there is no mean-value block: the head is
cut at `N` itself, the tail `n > N` is killed by the 12-fold smoothing (`‖Δ_h^{12}k₁₂‖ ≤ 2^{12}sup‖k₁₂‖`),
and the Rankin-trick exponents are kept free (`β > 13/2`).

`pointwise_core`:
`|S(x) − V_N(x)| ≤ Σ_{x<n≤x+12h}|τ(n)| + C_K(3x)^{11/2}N^{β−13/2}St β
   + h^{−12}(C_T/π^{12})(3x)^{12}x^{−1/4}(N+1)^{β−49/4}St β + (6+2π)/(π√2) N^{β−23/4} St β (3x)^{21/4} 12h`.
-/
import RamanujanTau.VoronoiTrunc.Assembly

set_option autoImplicit false

namespace RamanujanTau.VoronoiPointwise

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.VoronoiTrunc

/-- Kernel error of the head, free Rankin exponent. -/
lemma norm_EM_le' {β : ℝ} (hβ : 13 / 2 < β) {X : ℝ} (hX : 1 ≤ X) (M : ℕ) {y : ℝ} (hy1 : X ≤ y)
    (hy2 : y ≤ 3 * X) :
    ‖∑ n ∈ Finset.Icc 1 M, tauC n * (kB 0 n y - (mK n y : ℂ))‖ ≤
      CK * (3 * X) ^ (11 / 2 : ℝ) * ((M : ℝ) ^ (β - 13 / 2) * St β) := by
  have hy : 1 ≤ y := le_trans hX hy1
  have hCK : 0 ≤ CK := by unfold CK; have := Ck_nonneg 12; positivity
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ n ∈ Finset.Icc 1 M, ‖tauC n * (kB 0 n y - (mK n y : ℂ))‖ ≤
      CK * (3 * X) ^ (11 / 2 : ℝ) * (|((tau n : ℤ) : ℝ)| * (n : ℝ) ^ (-(13 / 2) : ℝ)) := by
    intro n hn
    rw [norm_mul, norm_tauC]
    have h1 := kB_zero_sub_main (Finset.mem_Icc.1 hn).1 hy
    have h2 : y ^ (11 / 2 : ℝ) ≤ (3 * X) ^ (11 / 2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hy2 (by norm_num)
    have h3 : 0 ≤ (n : ℝ) ^ (-(13 / 2) : ℝ) := by positivity
    calc |((tau n : ℤ) : ℝ)| * ‖kB 0 n y - (mK n y : ℂ)‖
        ≤ |((tau n : ℤ) : ℝ)| * (CK * y ^ (11 / 2 : ℝ) * (n : ℝ) ^ (-(13 / 2) : ℝ)) := by gcongr
      _ ≤ |((tau n : ℤ) : ℝ)| * (CK * (3 * X) ^ (11 / 2 : ℝ) * (n : ℝ) ^ (-(13 / 2) : ℝ)) := by gcongr
      _ = _ := by ring
  refine (Finset.sum_le_sum hb).trans ?_
  rw [← Finset.mul_sum]
  gcongr
  exact head_sum_le (β := β) (γ := 13 / 2) hβ hβ.le M

/-- The tail `n > M`, free Rankin exponent. -/
lemma norm_tail_le' {β : ℝ} (hβ : 13 / 2 < β) (hβ' : β ≤ 49 / 4) {X h : ℝ} (hX : 1 ≤ X) (hh : 0 < h)
    (M : ℕ) {x : ℝ} (hx1 : X ≤ x) (hx2 : x + 12 * h ≤ 3 * X) :
    ‖∑' k, tauC (k + (M + 1)) * It h 12 (kB 0 (k + (M + 1))) x‖ ≤
      CT / π ^ 12 * (3 * X) ^ 12 * X ^ (-(1 / 4) : ℝ) *
        (((M : ℝ) + 1) ^ (β - 49 / 4) * St β) := by
  have hCT : 0 ≤ CT := by unfold CT; have := Ck_nonneg 24; positivity
  have hK : 0 ≤ CT / π ^ 12 * (3 * X) ^ 12 * X ^ (-(1 / 4) : ℝ) := by
    have : 0 < X := by linarith
    positivity
  have hb : ∀ k : ℕ, ‖tauC (k + (M + 1)) * It h 12 (kB 0 (k + (M + 1))) x‖ ≤
      CT / π ^ 12 * (3 * X) ^ 12 * X ^ (-(1 / 4) : ℝ) *
        (|((tau (k + (M + 1)) : ℤ) : ℝ)| * ((k + (M + 1) : ℕ) : ℝ) ^ (-(49 / 4) : ℝ)) :=
    fun k => norm_tail_term_le hX hh hx1 hx2 (by omega)
  obtain ⟨hs, hle⟩ := tail_sum_le (α := 49 / 4) (β := β) hβ hβ' M
  have hsK := hs.mul_left (CT / π ^ 12 * (3 * X) ^ 12 * X ^ (-(1 / 4) : ℝ))
  have hsn : Summable fun k : ℕ => ‖tauC (k + (M + 1)) * It h 12 (kB 0 (k + (M + 1))) x‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hb hsK
  calc _ ≤ ∑' k, ‖tauC (k + (M + 1)) * It h 12 (kB 0 (k + (M + 1))) x‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ _ := hsn.tsum_le_tsum hb hsK
    _ = CT / π ^ 12 * (3 * X) ^ 12 * X ^ (-(1 / 4) : ℝ) *
        ∑' k : ℕ, |((tau (k + (M + 1)) : ℤ) : ℝ)| * ((k + (M + 1) : ℕ) : ℝ) ^ (-(49 / 4) : ℝ) :=
        tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hle hK

/-- Lipschitz bound for `V_N`, free Rankin exponent. -/
lemma abs_Vth_sub_le' {β : ℝ} (hβ : 13 / 2 < β) {X : ℝ} (hX : 1 ≤ X) (N : ℕ) {x y : ℝ}
    (h1 : X ≤ x) (h2 : x ≤ y) (h3 : y ≤ 3 * X) :
    |Vth N y - Vth N x| ≤ 1 / (π * √2) * ((6 + 2 * π) * ((N : ℝ) ^ (β - 23 / 4) * St β)) *
      (3 * X) ^ (21 / 4 : ℝ) * (y - x) := by
  have hx1 : 1 ≤ x := le_trans hX h1
  have hV : ∀ z, Vth N z = 1 / (π * √2) * ∑ n ∈ Finset.Icc 1 N, bco n * (z ^ (23 / 4 : ℝ) * Real.cos (th n z)) := by
    intro z; unfold Vth; rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_; ring
  rw [hV, hV, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity)]
  have hb : ∀ n ∈ Finset.Icc 1 N, |bco n * (y ^ (23 / 4 : ℝ) * Real.cos (th n y)) -
      bco n * (x ^ (23 / 4 : ℝ) * Real.cos (th n x))| ≤
      (6 + 2 * π) * (|((tau n : ℤ) : ℝ)| * (n : ℝ) ^ (-(23 / 4) : ℝ)) * (3 * X) ^ (21 / 4 : ℝ) * (y - x) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    have hn0 : (0 : ℝ) < n := by linarith
    rw [← mul_sub, abs_mul]
    have hl := abs_main_sub_le n hx1 h2 h3
    have hsn : 1 ≤ √(n : ℝ) := by rw [Real.le_sqrt (by norm_num) (by positivity)]; simpa using hn1
    have hb1 : |bco n| * (6 + 2 * π * √(n : ℝ)) ≤ (6 + 2 * π) * (|((tau n : ℤ) : ℝ)| * (n : ℝ) ^ (-(23 / 4) : ℝ)) := by
      unfold bco
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ (-(25 / 4) : ℝ))]
      have e : (n : ℝ) ^ (-(23 / 4) : ℝ) = (n : ℝ) ^ (-(25 / 4) : ℝ) * √(n : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]; norm_num
      rw [e]
      have : 0 ≤ |((tau n : ℤ) : ℝ)| * (n : ℝ) ^ (-(25 / 4) : ℝ) := by positivity
      have : 6 + 2 * π * √(n : ℝ) ≤ (6 + 2 * π) * √(n : ℝ) := by nlinarith [Real.pi_pos]
      nlinarith
    have hy0 : 0 ≤ y - x := by linarith
    calc |bco n| * |y ^ (23 / 4 : ℝ) * Real.cos (th n y) - x ^ (23 / 4 : ℝ) * Real.cos (th n x)|
        ≤ |bco n| * ((6 + 2 * π * √(n : ℝ)) * (3 * X) ^ (21 / 4 : ℝ) * (y - x)) := by gcongr
      _ = (|bco n| * (6 + 2 * π * √(n : ℝ))) * ((3 * X) ^ (21 / 4 : ℝ) * (y - x)) := by ring
      _ ≤ ((6 + 2 * π) * (|((tau n : ℤ) : ℝ)| * (n : ℝ) ^ (-(23 / 4) : ℝ))) *
          ((3 * X) ^ (21 / 4 : ℝ) * (y - x)) := by gcongr
      _ = _ := by ring
  have hsum := head_sum_le (β := β) (γ := 23 / 4) hβ (by linarith) N
  calc 1 / (π * √2) * |∑ n ∈ Finset.Icc 1 N, (bco n * (y ^ (23 / 4 : ℝ) * Real.cos (th n y)) -
        bco n * (x ^ (23 / 4 : ℝ) * Real.cos (th n x)))|
      ≤ 1 / (π * √2) * ∑ n ∈ Finset.Icc 1 N, (6 + 2 * π) * (|((tau n : ℤ) : ℝ)| * (n : ℝ) ^ (-(23 / 4) : ℝ)) *
          (3 * X) ^ (21 / 4 : ℝ) * (y - x) := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb)
    _ = 1 / (π * √2) * ((6 + 2 * π) * ∑ n ∈ Finset.Icc 1 N, |((tau n : ℤ) : ℝ)| * (n : ℝ) ^ (-(23 / 4) : ℝ)) *
          (3 * X) ^ (21 / 4 : ℝ) * (y - x) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]; ring
    _ ≤ _ := by
        have : 0 ≤ y - x := by linarith
        gcongr

/-- The error majorant of `pointwise_core`. -/
noncomputable def Bpw (β x h : ℝ) (N : ℕ) : ℝ :=
  CK * (3 * x) ^ (11 / 2 : ℝ) * ((N : ℝ) ^ (β - 13 / 2) * St β) +
    (h ^ 12)⁻¹ * (CT / π ^ 12 * (3 * x) ^ 12 * x ^ (-(1 / 4) : ℝ) *
      (((N : ℝ) + 1) ^ (β - 49 / 4) * St β)) +
    1 / (π * √2) * ((6 + 2 * π) * ((N : ℝ) ^ (β - 23 / 4) * St β)) * (3 * x) ^ (21 / 4 : ℝ) * (12 * h)

/-- **Pointwise truncated Voronoi decomposition** (unconditional, explicit constants). -/
theorem pointwise_core {β : ℝ} (hβ : 13 / 2 < β) (hβ' : β ≤ 49 / 4) {x h : ℝ} (hx : 1 ≤ x)
    (hh : 0 < h) (h6 : 6 * h ≤ x) (N : ℕ) :
    |Sre x - Vth N x| ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + 12 * h⌋₊, |((tau n : ℤ) : ℝ)| + Bpw β x h N := by
  have hx0 : 0 < x := by linarith
  have hx3 : x + 12 * h ≤ 3 * x := by linarith
  have hh12 : (0 : ℝ) < h ^ 12 := pow_pos hh 12
  set VN : ℝ → ℂ := fun y => ((Vth N y : ℝ) : ℂ) with hVN
  set EN : ℝ → ℂ := fun y => ∑ n ∈ Finset.Icc 1 N, tauC n * (kB 0 n y - (mK n y : ℂ)) with hEN
  have hVNc : Continuous VN := continuous_ofReal.comp (continuous_Vth N)
  have hENc : Continuous EN := continuous_EM N
  have hhead : (fun y => ∑ n ∈ Finset.Icc 1 N, tauC n * kB 0 n y) = fun y => VN y + EN y := by
    funext y
    simp only [VN, EN]
    rw [← sum_tau_mK]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [tauC_eq]; push_cast; ring
  have hIt : It h 12 (fun y => VN y + EN y) x = It h 12 VN x + It h 12 EN x := by
    rw [It_add 12 VN EN hVNc hENc]
  set T := ∑' k, tauC (k + (N + 1)) * It h 12 (kB 0 (k + (N + 1))) x
  have hsplit := Sh_split hh hx0 N
  rw [hhead, hIt] at hsplit
  have hdec : ((Sre x - Vth N x : ℝ) : ℂ) =
      ((Sre x : ℂ) - Sh h x) + (((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 EN x + (((h ^ 12 : ℝ) : ℂ))⁻¹ * T +
      ((((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 VN x - VN x) := by
    rw [hsplit]; simp only [VN]; push_cast; ring
  have hb1 := norm_S_sub_Sh_le hh hx0
  have hbE : ‖(((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 EN x‖ ≤
      CK * (3 * x) ^ (11 / 2 : ℝ) * ((N : ℝ) ^ (β - 13 / 2) * St β) := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh12, inv_mul_le_iff₀ hh12]
    refine norm_It_le hh.le 12 EN x _ (fun y hy => ?_)
    exact norm_EM_le' hβ hx N (by linarith [hy.1]) (by push_cast at hy; linarith [hy.2])
  have hbT : ‖(((h ^ 12 : ℝ) : ℂ))⁻¹ * T‖ ≤ (h ^ 12)⁻¹ * (CT / π ^ 12 * (3 * x) ^ 12 * x ^ (-(1 / 4) : ℝ) *
      (((N : ℝ) + 1) ^ (β - 49 / 4) * St β)) := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh12]
    exact mul_le_mul_of_nonneg_left (norm_tail_le' hβ hβ' hx hh N le_rfl hx3) (by positivity)
  have hb4 : ‖(((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 VN x - VN x‖ ≤
      1 / (π * √2) * ((6 + 2 * π) * ((N : ℝ) ^ (β - 23 / 4) * St β)) * (3 * x) ^ (21 / 4 : ℝ) * (12 * h) := by
    have hε : ∀ y ∈ Icc x (x + (12 : ℕ) * h), ‖VN y - VN x‖ ≤
        1 / (π * √2) * ((6 + 2 * π) * ((N : ℝ) ^ (β - 23 / 4) * St β)) * (3 * x) ^ (21 / 4 : ℝ) * (12 * h) := by
      intro y hy
      simp only [VN]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hy3 : y ≤ 3 * x := by push_cast at hy; linarith [hy.2]
      refine (abs_Vth_sub_le' hβ hx N le_rfl hy.1 hy3).trans ?_
      have : y - x ≤ 12 * h := by push_cast at hy; linarith [hy.2]
      have : 0 ≤ 1 / (π * √2) * ((6 + 2 * π) * ((N : ℝ) ^ (β - 23 / 4) * St β)) * (3 * x) ^ (21 / 4 : ℝ) := by
        have := St_nonneg β; positivity
      gcongr
    have := norm_It_sub_le hh.le 12 hVNc x _ hε
    have e : (((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 VN x - VN x =
        (((h ^ 12 : ℝ) : ℂ))⁻¹ * (It h 12 VN x - (h : ℂ) ^ 12 * VN x) := by
      have : (((h ^ 12 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hh12.ne'
      field_simp; push_cast; ring
    rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh12, inv_mul_le_iff₀ hh12]
    exact this
  have hnorm : |Sre x - Vth N x| = ‖((Sre x - Vth N x : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, hdec]
  unfold Bpw
  set a := (Sre x : ℂ) - Sh h x
  set b := (((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 EN x
  set c := (((h ^ 12 : ℝ) : ℂ))⁻¹ * T
  set d := (((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 VN x - VN x
  have t : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ :=
    (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  linarith

end RamanujanTau.VoronoiPointwise
