/-
# Sharp pointwise bound for `G_h(W)` at complex `W`

`pointwise_G'`: `‖G_h(σ+iv)‖ ≤ K √h (|2v/σ| + 3) σ^{−12 + 12/125}` for `h ≥ 1`, `0 < σ ≤ 1`, `hσ ≤ 1`.

Changes against `SCSProof.pointwise_G` (`K h (|2v/σ|+3)³² σ^{−12+3/40}`):
* Cauchy–Schwarz is used as `√a √b` (no AM–GM), so the Weil saving enters as a square root;
* the sharp ball bound `8R` (`norm_Q_le'`) instead of `8R⁴`;
* the prefactor `|Y(i − ζ̄₀)|¹² ≥ (Y A/2)¹²`, `A = |θ|+3`, is divided out (it cancels the `R⁶ = (2A²)⁶`
  growth of `Ψ`), leaving a *linear* loss `A`;
* box size `ε = Y^{12/125}/2` balances `ε^{−3/2} Y^{1/4−δ}` (Weil, `δ = 1/100`) against `ε` (Lipschitz).
-/
import RamanujanTau.SCSSharp.NormQ

set_option autoImplicit false

namespace RamanujanTau.SCSSharp

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open RamanujanTau.SCSProof
open scoped MatrixGroups ENNReal Real ComplexConjugate

lemma norm_I_sub_conj_zeta0_ge (P : Par) :
    Aθ P / 2 ≤ ‖I - conj ((zeta0 P : ℍ) : ℂ)‖ := by
  rw [coe_zeta0]
  have e : I - conj ((P.θ : ℂ) + I) = ((-P.θ : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * I := by
    simp only [map_add, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
  rw [e]
  have hn : ‖((-P.θ : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * I‖ ^ 2 = P.θ ^ 2 + 4 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]; ring
  have h0 := norm_nonneg (((-P.θ : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * I)
  unfold Aθ
  have hsq : ((|P.θ| + 3) / 2) ^ 2 ≤ P.θ ^ 2 + 4 := by
    have := sq_abs P.θ
    nlinarith [sq_nonneg (|P.θ| - 1), abs_nonneg P.θ]
  nlinarith [abs_nonneg P.θ]

/-- **Division by the prefactor**, keeping the `A¹²` gain. -/
theorem norm_G0_le' (P : Par) (hh : P.h * (4 * π * P.Y) ≤ 1) :
    ‖Gh P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ)))‖ ≤
      2 ^ 13 / (P.Y * Aθ P) ^ 12 * ‖cf P P.Y (zeta0 P)‖ := by
  have hY := P.hY
  have hA := Aθ_ge P
  set u0 : ℂ := (P.Y : ℂ) * (I - conj ((zeta0 P : ℍ) : ℂ))
  set e0 : ℝ := Real.exp (-2 * π * P.h * P.Y)
  have hcf : cf P P.Y (zeta0 P) = u0 ^ 12 * (e0 : ℂ) *
      Gh P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ))) := rfl
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
  set G := ‖Gh P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ)))‖
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

set_option maxHeartbeats 4000000 in
/-- **Sharp pointwise bound** for `ε = t⁴⁸/2`, `t = Y^{1/500}`. -/
theorem pointwise_par' : ∃ K : ℝ, 0 ≤ K ∧ ∀ P : Par, 1 ≤ P.h →
    P.ε = (P.Y ^ (1 / 500 : ℝ)) ^ 48 / 2 → P.h * (4 * π * P.Y) ≤ 1 →
      ‖Gh P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ)))‖ ≤
        K * Real.sqrt P.h * Aθ P * (P.Y ^ (1 / 500 : ℝ)) ^ 48 * (1 / P.Y ^ 12) := by
  obtain ⟨M, hM0, hM⟩ := norm_Psi_le
  obtain ⟨CB, hCB0, hCB⟩ := norm_tsum_Iγ_le (1 / 100) (by norm_num) (by norm_num)
  obtain ⟨C₀, hC₀, hT⟩ := abs_laplace_le
  refine ⟨2 ^ 24 * M * Real.sqrt CB + 2 ^ 28 * C₀, by positivity, fun P hh hεt hhY => ?_⟩
  have hY := P.hY; have hY1 := P.hY1; have hε := P.hε
  set t := P.Y ^ (1 / 500 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hY _
  have ht1 : t ≤ 1 := Real.rpow_le_one hY.le hY1 (by norm_num)
  have hYt : P.Y = t ^ 500 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hY.le]; norm_num
  have hhR : (1 : ℝ) ≤ P.h := by exact_mod_cast hh
  have hA := Aθ_ge P
  set A := Aθ P
  set R := Rθ P
  have hRA : R = 2 * A ^ 2 := by simp only [R, A, Rθ, Aθ]
  -- `‖Σ I(γ)‖`
  have hSig := hCB P hh
  have hYpow : P.Y ^ (-(3 / 2 : ℝ) - 2 * (1 / 100)) = 1 / t ^ 760 := by
    rw [hYt, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    have e : ((500 : ℕ) : ℝ) * (-(3 / 2) - 2 * (1 / 100)) = -((760 : ℕ) : ℝ) := by norm_num
    rw [e, Real.rpow_neg ht0.le, Real.rpow_natCast, one_div]
  rw [hYpow, hεt] at hSig
  have hb : 2 * ‖∑' γ, Iγ P γ‖ ≤ CB * P.h / (4 * t ^ 616) := by
    have e : CB * P.h * ((t ^ 48 / 2) ^ 3) * (1 / t ^ 760) = CB * P.h / (8 * t ^ 616) := by
      field_simp; ring
    rw [e] at hSig
    have : CB * P.h / (4 * t ^ 616) = 2 * (CB * P.h / (8 * t ^ 616)) := by ring
    linarith
  -- `‖Q‖`
  have hQ0 := norm_Q_le' P hM0 hM
  have hsa : Real.sqrt ((M * R ^ 6) ^ 2 * (8 * R)) = 2 ^ 8 * M * A ^ 13 := by
    rw [hRA]
    have e : (M * (2 * A ^ 2) ^ 6) ^ 2 * (8 * (2 * A ^ 2)) = (2 ^ 8 * M * A ^ 13) ^ 2 := by ring
    rw [e, Real.sqrt_sq (by positivity)]
  have hsb : Real.sqrt (2 * ‖∑' γ, Iγ P γ‖) ≤ Real.sqrt (CB * P.h) / (2 * t ^ 308) := by
    have e : CB * P.h / (4 * t ^ 616) = (Real.sqrt (CB * P.h) / (2 * t ^ 308)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by positivity)]; ring
    rw [e] at hb
    refine (Real.sqrt_le_sqrt hb).trans (le_of_eq ?_)
    exact Real.sqrt_sq (by positivity)
  have hQ : ‖∫ p, Psi p.1 p.2 * conj (ft P p)‖ ≤
      2 ^ 6 * M * A ^ 13 * Real.sqrt (CB * P.h) / t ^ 308 := by
    refine hQ0.trans ?_
    rw [hsa]
    calc 1 / 2 * (2 ^ 8 * M * A ^ 13) * Real.sqrt (2 * ‖∑' γ, Iγ P γ‖)
        ≤ 1 / 2 * (2 ^ 8 * M * A ^ 13) * (Real.sqrt (CB * P.h) / (2 * t ^ 308)) := by gcongr
      _ = _ := by field_simp
  -- `W`
  have hmI := mI_ge P
  have hmB := mB_ge P
  have hW : 1 / (32 * t ^ 356) ≤ mI P * mB P := by
    have h1 : P.ε / (4 * P.Y) * P.ε ^ 2 ≤ mI P * mB P := by
      have : 0 ≤ P.ε / (4 * P.Y) := by positivity
      exact mul_le_mul hmI hmB (by positivity) (le_trans this hmI)
    have e : P.ε / (4 * P.Y) * P.ε ^ 2 = 1 / (32 * t ^ 356) := by
      rw [hεt, hYt]; field_simp; ring
    linarith
  have hWpos : 0 < mI P * mB P := lt_of_lt_of_le (by positivity) hW
  -- the Lipschitz error (as in `SCSProof.pointwise_par`)
  have hsπ : 0 < π * P.Y := by positivity
  obtain ⟨hs1, hb1⟩ := hT P.h (π * P.Y) hsπ
  obtain ⟨hs2, hb2⟩ := hT P.h (2 * π * P.Y) (by positivity)
  obtain ⟨hs4, hb4⟩ := hT P.h (4 * π * P.Y) (by positivity)
  have hhs1 : (P.h : ℝ) * (π * P.Y) ≤ 1 := by nlinarith [Real.pi_pos]
  have hhs4 : (P.h : ℝ) * (4 * π * P.Y) ≤ 1 := hhY
  have hT1 := laplace_le_of hC₀ P.h hsπ hhs1 hb1
  have hT4 := laplace_le_of hC₀ P.h (by positivity) hhs4 hb4
  have hs1' : Summable (fun n : ℕ => aabs P.h n * Real.exp (-n * ((2 * π * P.Y) / 2))) := by
    have e : (2 * π * P.Y) / 2 = π * P.Y := by ring
    rw [e]; exact hs1
  obtain ⟨hnS, hnB⟩ := n_laplace P.h (by positivity : 0 < 2 * π * P.Y) hs1'
  have hE := cf_sub_le P hhY hnS hs2 hs4
  set S1 := ∑' n : ℕ, n * aabs P.h n * Real.exp (-n * (2 * π * P.Y))
  set T0 := ∑' n : ℕ, aabs P.h n * Real.exp (-n * (4 * π * P.Y))
  have hS1b : S1 ≤ 2 / (2 * π * P.Y) * (2 * C₀ * (1 / (π * P.Y) ^ 12)) := by
    refine hnB.trans ?_
    have e : (2 * π * P.Y) / 2 = π * P.Y := by ring
    rw [e]; gcongr
  have hT0b : T0 ≤ 2 * C₀ * (1 / (π * P.Y) ^ 12) := by
    refine hT4.trans ?_
    gcongr; nlinarith
  set E := (2 * P.Y * A) ^ 12 * (2 * π * P.Y * P.ε * (A + 2)) * S1 +
    13 * (2 * P.Y * A) ^ 12 * P.ε * T0
  have hEb : E ≤ (2 * P.Y * A) ^ 12 * P.ε * C₀ * (1 / (π * P.Y) ^ 12) * (16 * A) := by
    have hS1n : 0 ≤ S1 := tsum_nonneg fun n =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (aabs_nonneg _ _)) (Real.exp_pos _).le
    have k1 : (2 * π * P.Y * P.ε * (A + 2)) * S1 ≤ P.ε * (A + 2) * (4 * C₀ * (1 / (π * P.Y) ^ 12)) := by
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
  have hmain := main_term_le P hM0 hM (cf P P.Y (zeta0 P)) E hE
  have hc0 : ‖cf P P.Y (zeta0 P)‖ ≤ ‖∫ p, Psi p.1 p.2 * conj (ft P p)‖ / (mI P * mB P) + E := by
    have : ‖cf P P.Y (zeta0 P)‖ * (mI P * mB P) ≤
        (‖∫ p, Psi p.1 p.2 * conj (ft P p)‖ / (mI P * mB P) + E) * (mI P * mB P) := by
      rw [add_mul, div_mul_cancel₀ _ hWpos.ne']; linarith
    exact le_of_mul_le_mul_right this hWpos
  have hG := norm_G0_le' P hhY
  have hQW : ‖∫ p, Psi p.1 p.2 * conj (ft P p)‖ / (mI P * mB P) ≤
      2 ^ 11 * M * A ^ 13 * Real.sqrt (CB * P.h) * t ^ 48 := by
    rw [div_le_iff₀ hWpos]
    refine hQ.trans ?_
    have hX : 0 ≤ 2 ^ 11 * M * A ^ 13 * Real.sqrt (CB * P.h) * t ^ 48 := by positivity
    calc 2 ^ 6 * M * A ^ 13 * Real.sqrt (CB * P.h) / t ^ 308
        = 2 ^ 11 * M * A ^ 13 * Real.sqrt (CB * P.h) * t ^ 48 * (1 / (32 * t ^ 356)) := by
          field_simp; ring
      _ ≤ _ := by gcongr
  have hfinal : ‖Gh P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ)))‖ ≤
      2 ^ 13 / (P.Y * A) ^ 12 * (2 ^ 11 * M * A ^ 13 * Real.sqrt (CB * P.h) * t ^ 48 +
        (2 * P.Y * A) ^ 12 * P.ε * C₀ * (1 / (π * P.Y) ^ 12) * (16 * A)) := by
    refine hG.trans ?_
    gcongr
    linarith
  refine hfinal.trans ?_
  have hpi : (1 : ℝ) ≤ π ^ 12 := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hsq : Real.sqrt (CB * P.h) = Real.sqrt CB * Real.sqrt P.h := Real.sqrt_mul hCB0 _
  have hsh : (1 : ℝ) ≤ Real.sqrt P.h := by rw [Real.one_le_sqrt]; exact hhR
  have e1 : 2 ^ 13 / (P.Y * A) ^ 12 * (2 ^ 11 * M * A ^ 13 * Real.sqrt (CB * P.h) * t ^ 48) =
      2 ^ 24 * M * Real.sqrt CB * Real.sqrt P.h * A * t ^ 48 * (1 / P.Y ^ 12) := by
    rw [hsq]; field_simp
  have e2 : 2 ^ 13 / (P.Y * A) ^ 12 * ((2 * P.Y * A) ^ 12 * P.ε * C₀ * (1 / (π * P.Y) ^ 12) *
      (16 * A)) = 2 ^ 28 * C₀ * A * t ^ 48 / π ^ 12 * (1 / P.Y ^ 12) := by
    rw [hεt]; field_simp; ring
  rw [mul_add, e1, e2]
  have hY12 : 0 < 1 / P.Y ^ 12 := by positivity
  have k2 : 2 ^ 28 * C₀ * A * t ^ 48 / π ^ 12 ≤ 2 ^ 28 * C₀ * Real.sqrt P.h * A * t ^ 48 := by
    rw [div_le_iff₀ (by positivity)]
    have h0 : 0 ≤ 2 ^ 28 * C₀ * A * t ^ 48 := by positivity
    calc 2 ^ 28 * C₀ * A * t ^ 48 = 2 ^ 28 * C₀ * A * t ^ 48 * 1 * 1 := by ring
      _ ≤ 2 ^ 28 * C₀ * A * t ^ 48 * Real.sqrt P.h * π ^ 12 := by gcongr
      _ = _ := by ring
  have := add_le_add_right (mul_le_mul_of_nonneg_right k2 hY12.le)
    (2 ^ 24 * M * Real.sqrt CB * Real.sqrt P.h * A * t ^ 48 * (1 / P.Y ^ 12))
  calc _ ≤ _ := this
    _ = (2 ^ 24 * M * Real.sqrt CB + 2 ^ 28 * C₀) * Real.sqrt P.h * A * t ^ 48 *
          (1 / P.Y ^ 12) := by ring

/-- **Sharp pointwise bound** `‖G_h(σ+iv)‖ ≤ K √h (|2v/σ|+3) σ^{−(12 − 12/125)}`. -/
theorem pointwise_G' : ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 →
    (h : ℝ) * σ ≤ 1 →
      ‖Gh h ((σ : ℂ) + v * I)‖ ≤
        K * Real.sqrt h * (|2 * v / σ| + 3) * σ ^ (-(1488 / 125 : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := pointwise_par'
  refine ⟨K * (4 * π) ^ (1488 / 125 : ℝ), by positivity, fun h hh σ v hσ hσ1 hhσ => ?_⟩
  set Y := σ / (4 * π) with hYdef
  have hY : 0 < Y := by positivity
  have hY1 : Y ≤ 1 := by
    rw [hYdef, div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  set t := Y ^ (1 / 500 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hY _
  have ht1 : t ≤ 1 := Real.rpow_le_one hY.le hY1 (by norm_num)
  let P : Par := ⟨h, Y, t ^ 48 / 2, 2 * v / σ, hY, hY1, by positivity, by
    have : t ^ 48 ≤ 1 := pow_le_one₀ ht0.le ht1
    linarith⟩
  have hPh : P.h * (4 * π * P.Y) ≤ 1 := by
    show (h : ℝ) * (4 * π * (σ / (4 * π))) ≤ 1
    rw [show 4 * π * (σ / (4 * π)) = σ by field_simp]; exact hhσ
  have hb := hK P hh rfl hPh
  have hW : 2 * π * P.Y * (1 + I * conj ((zeta0 P : UpperHalfPlane) : ℂ)) = (σ : ℂ) + v * I := by
    rw [W0_eq]
    show (((4 * π * (σ / (4 * π)) : ℝ)) : ℂ) + ((2 * π * (σ / (4 * π)) * (2 * v / σ) : ℝ) : ℂ) * I = _
    congr 2
    · congr 1; field_simp
    · congr 1; field_simp; ring
  rw [hW] at hb
  refine hb.trans (le_of_eq ?_)
  show K * Real.sqrt h * (|2 * v / σ| + 3) * t ^ 48 * (1 / Y ^ 12) = _
  have e1 : t ^ 48 * (1 / Y ^ 12) = Y ^ (-(1488 / 125 : ℝ)) := by
    have h1 : t ^ 48 = Y ^ (12 / 125 : ℝ) := by
      rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hY.le]; norm_num
    have h2 : (1 / Y ^ 12 : ℝ) = Y ^ (-(12 : ℝ)) := by
      rw [Real.rpow_neg hY.le, one_div]; norm_cast
    rw [h1, h2, ← Real.rpow_add hY]
    norm_num
  have e2 : Y ^ (-(1488 / 125 : ℝ)) = (4 * π) ^ (1488 / 125 : ℝ) * σ ^ (-(1488 / 125 : ℝ)) := by
    rw [hYdef, Real.div_rpow hσ.le (by positivity), Real.rpow_neg (by positivity : (0:ℝ) ≤ 4 * π),
      div_eq_mul_inv, inv_inv]
    ring
  rw [mul_assoc (K * Real.sqrt h * _), e1, e2]
  ring

end RamanujanTau.SCSSharp
