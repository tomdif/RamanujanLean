/-
# Weight-`k` pointwise bound with gcd-Kloosterman and `δ_W = 1/400` (copy of `SCSSharp2.Point21`)

`pointwise_GF21`: `‖G^f_h(σ+iv)‖ ≤ K h^{1/21} (|2v/σ| + 3) σ^{−k + 99/1000}` (even `k`).
Obtained from `SubconvexGeneral2.pointwise_GF` by the same edits that turn `SCSSharp.Point` into
`SCSSharp2.Point21`: `norm_tsum_Iγ_le_gcd (1/400) (2/21)`, `t = Y^{1/1000}`, `ε = t⁹⁹/2`.
-/
import RamanujanTau.SubconvexGeneral2.GeoPoint
import RamanujanTau.SCSSharp2.KloostGcd

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral3

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open RamanujanTau.SCSProof RamanujanTau.SCSSharp RamanujanTau.SCSSharp2 RamanujanTau.SubconvexGeneral
open RamanujanTau.SubconvexGeneral2
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ))

set_option maxHeartbeats 4000000 in
/-- **Sharp pointwise bound**, weight `k = 2m`, for `ε = t⁹⁹/2`, `t = Y^{1/500}`. -/
theorem pointwise_parF21 (m : ℕ) (hkm : k = 2 * m) : ∃ K : ℝ, 0 ≤ K ∧ ∀ P : Par, 1 ≤ P.h →
    P.ε = (P.Y ^ (1 / 1000 : ℝ)) ^ 99 / 2 → P.h * (4 * π * P.Y) ≤ 1 →
      ‖GhF f P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ)))‖ ≤
        K * (P.h : ℝ) ^ (1 / 21 : ℝ) * Aθ P * (P.Y ^ (1 / 1000 : ℝ)) ^ 99 * (1 / P.Y ^ k) := by
  subst hkm
  obtain ⟨M, hM0, hM'⟩ := norm_PsiF_le f
  have hM : ∀ z w : ℍ, ‖PsiF f z w‖ ≤
      M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ m := by
    intro z w
    have e : (((2 * m : ℕ) : ℝ) / 2) = ((m : ℕ) : ℝ) := by push_cast; ring
    have := hM' z w
    rwa [e, Real.rpow_natCast] at this
  obtain ⟨CB, hCB0, hCB⟩ := norm_tsum_Iγ_le_gcd (1 / 400) (2 / 21) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C₀, hC₀, hT⟩ := abs_laplace_leF f
  refine ⟨2 ^ (3 * m + 6) * M * Real.sqrt CB + 2 ^ (2 * (2 * m)) * C₀ * (2 * ((2 * m : ℕ) : ℝ) + 14),
    by positivity, fun P hh hεt hhY => ?_⟩
  have hY := P.hY; have hY1 := P.hY1; have hε := P.hε
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
  -- `‖Σ I(γ)‖`
  have hSig := hCB P hh
  have hYpow : P.Y ^ (-(3 / 2 : ℝ) - 2 * (1 / 400)) = 1 / t ^ 1505 := by
    rw [hYt, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    have e : ((1000 : ℕ) : ℝ) * (-(3 / 2) - 2 * (1 / 400)) = -((1505 : ℕ) : ℝ) := by norm_num
    rw [e, Real.rpow_neg ht0.le, Real.rpow_natCast, one_div]
  rw [hYpow, hεt] at hSig
  have hb : 2 * ‖∑' γ, Iγ P γ‖ ≤ CB * (P.h : ℝ) ^ (2 / 21 : ℝ) / (4 * t ^ 1208) := by
    have e : CB * (P.h : ℝ) ^ (2 / 21 : ℝ) * ((t ^ 99 / 2) ^ 3) * (1 / t ^ 1505) = CB * (P.h : ℝ) ^ (2 / 21 : ℝ) / (8 * t ^ 1208) := by
      field_simp; ring
    rw [e] at hSig
    have : CB * (P.h : ℝ) ^ (2 / 21 : ℝ) / (4 * t ^ 1208) = 2 * (CB * (P.h : ℝ) ^ (2 / 21 : ℝ) / (8 * t ^ 1208)) := by ring
    linarith
  -- `‖Q‖`
  have hQ0 := norm_QF_le' f P hM0 hM
  have hsa : Real.sqrt ((M * R ^ m) ^ 2 * (8 * R)) = 2 ^ (m + 2) * M * A ^ (2 * m + 1) := by
    rw [hRA]
    have e : (M * (2 * A ^ 2) ^ m) ^ 2 * (8 * (2 * A ^ 2)) =
        (2 ^ (m + 2) * M * A ^ (2 * m + 1)) ^ 2 := by ring
    rw [e, Real.sqrt_sq (by positivity)]
  have hsb : Real.sqrt (2 * ‖∑' γ, Iγ P γ‖) ≤ Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) / (2 * t ^ 604) := by
    have e : CB * (P.h : ℝ) ^ (2 / 21 : ℝ) / (4 * t ^ 1208) = (Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) / (2 * t ^ 604)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by positivity)]; ring
    rw [e] at hb
    refine (Real.sqrt_le_sqrt hb).trans (le_of_eq ?_)
    exact Real.sqrt_sq (by positivity)
  have hQ : ‖∫ p, PsiF f p.1 p.2 * conj (ft P p)‖ ≤
      2 ^ m * M * A ^ (2 * m + 1) * Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) / t ^ 604 := by
    refine hQ0.trans ?_
    rw [hsa]
    calc 1 / 2 * (2 ^ (m + 2) * M * A ^ (2 * m + 1)) * Real.sqrt (2 * ‖∑' γ, Iγ P γ‖)
        ≤ 1 / 2 * (2 ^ (m + 2) * M * A ^ (2 * m + 1)) *
            (Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) / (2 * t ^ 604)) := by gcongr
      _ = _ := by rw [pow_add]; field_simp
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
  obtain ⟨hs1, hb1⟩ := hT P.h (π * P.Y) hsπ
  obtain ⟨hs2, hb2⟩ := hT P.h (2 * π * P.Y) (by positivity)
  obtain ⟨hs4, hb4⟩ := hT P.h (4 * π * P.Y) (by positivity)
  have hhs1 : (P.h : ℝ) * (π * P.Y) ≤ 1 := by nlinarith [Real.pi_pos]
  have hhs4 : (P.h : ℝ) * (4 * π * P.Y) ≤ 1 := hhY
  have hT1 := laplace_le_ofF f hC₀ P.h hsπ hhs1 hb1
  have hT4 := laplace_le_ofF f hC₀ P.h (by positivity) hhs4 hb4
  have hs1' : Summable (fun n : ℕ => aabsF f P.h n * Real.exp (-n * ((2 * π * P.Y) / 2))) := by
    have e : (2 * π * P.Y) / 2 = π * P.Y := by ring
    rw [e]; exact hs1
  obtain ⟨hnS, hnB⟩ := n_laplaceF f P.h (by positivity : 0 < 2 * π * P.Y) hs1'
  have hE := cfF_sub_le f P hhY hnS hs2 hs4
  set S1 := ∑' n : ℕ, n * aabsF f P.h n * Real.exp (-n * (2 * π * P.Y))
  set T0 := ∑' n : ℕ, aabsF f P.h n * Real.exp (-n * (4 * π * P.Y))
  have hS1b : S1 ≤ 2 / (2 * π * P.Y) * (2 * C₀ * (1 / (π * P.Y) ^ (2 * m))) := by
    refine hnB.trans ?_
    have e : (2 * π * P.Y) / 2 = π * P.Y := by ring
    rw [e]; gcongr
  have hT0b : T0 ≤ 2 * C₀ * (1 / (π * P.Y) ^ (2 * m)) := by
    refine hT4.trans ?_
    gcongr; nlinarith
  set E := (2 * P.Y * A) ^ (2 * m) * (2 * π * P.Y * P.ε * (A + 2)) * S1 +
    (((2 * m : ℕ) : ℝ) + 1) * (2 * P.Y * A) ^ (2 * m) * P.ε * T0
  have hk0 : (0 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlin : 4 * A + 2 * ((2 * m : ℕ) : ℝ) + 10 ≤ (2 * ((2 * m : ℕ) : ℝ) + 14) * A := by nlinarith
  have hEb : E ≤ (2 * P.Y * A) ^ (2 * m) * P.ε * C₀ * (1 / (π * P.Y) ^ (2 * m)) *
      ((2 * ((2 * m : ℕ) : ℝ) + 14) * A) := by
    have hS1n : 0 ≤ S1 := tsum_nonneg fun n =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (aabsF_nonneg f _ _)) (Real.exp_pos _).le
    have k1 : (2 * π * P.Y * P.ε * (A + 2)) * S1 ≤
        P.ε * (A + 2) * (4 * C₀ * (1 / (π * P.Y) ^ (2 * m))) := by
      calc (2 * π * P.Y * P.ε * (A + 2)) * S1
          ≤ (2 * π * P.Y * P.ε * (A + 2)) *
              (2 / (2 * π * P.Y) * (2 * C₀ * (1 / (π * P.Y) ^ (2 * m)))) := by
            gcongr
        _ = P.ε * (A + 2) * (4 * C₀ * (1 / (π * P.Y) ^ (2 * m))) := by field_simp; ring
    have hpos : 0 ≤ (2 * P.Y * A) ^ (2 * m) := by positivity
    have hq : 0 ≤ C₀ * (1 / (π * P.Y) ^ (2 * m)) := by positivity
    have hk1 : 0 ≤ (((2 * m : ℕ) : ℝ) + 1) := by positivity
    calc E = (2 * P.Y * A) ^ (2 * m) * ((2 * π * P.Y * P.ε * (A + 2)) * S1) +
          (((2 * m : ℕ) : ℝ) + 1) * (2 * P.Y * A) ^ (2 * m) * P.ε * T0 := by
          show (2 * P.Y * A) ^ (2 * m) * (2 * π * P.Y * P.ε * (A + 2)) * S1 +
            (((2 * m : ℕ) : ℝ) + 1) * (2 * P.Y * A) ^ (2 * m) * P.ε * T0 = _
          ring
      _ ≤ (2 * P.Y * A) ^ (2 * m) * (P.ε * (A + 2) * (4 * C₀ * (1 / (π * P.Y) ^ (2 * m)))) +
          (((2 * m : ℕ) : ℝ) + 1) * (2 * P.Y * A) ^ (2 * m) * P.ε * (2 * C₀ * (1 / (π * P.Y) ^ (2 * m))) := by
          gcongr
      _ = (2 * P.Y * A) ^ (2 * m) * P.ε * (C₀ * (1 / (π * P.Y) ^ (2 * m))) *
          (4 * A + 2 * ((2 * m : ℕ) : ℝ) + 10) := by ring
      _ ≤ (2 * P.Y * A) ^ (2 * m) * P.ε * (C₀ * (1 / (π * P.Y) ^ (2 * m))) *
          ((2 * ((2 * m : ℕ) : ℝ) + 14) * A) := by
          gcongr
      _ = _ := by ring
  -- main-term comparison
  have hmain := main_term_leF f P hM0 hM (cfF f P P.Y (zeta0 P)) E hE
  have hc0 : ‖cfF f P P.Y (zeta0 P)‖ ≤
      ‖∫ p, PsiF f p.1 p.2 * conj (ft P p)‖ / (mI P * mB P) + E := by
    have : ‖cfF f P P.Y (zeta0 P)‖ * (mI P * mB P) ≤
        (‖∫ p, PsiF f p.1 p.2 * conj (ft P p)‖ / (mI P * mB P) + E) * (mI P * mB P) := by
      rw [add_mul, div_mul_cancel₀ _ hWpos.ne']; linarith
    exact le_of_mul_le_mul_right this hWpos
  have hG := norm_G0_leF f P hhY
  have hQW : ‖∫ p, PsiF f p.1 p.2 * conj (ft P p)‖ / (mI P * mB P) ≤
      2 ^ (m + 5) * M * A ^ (2 * m + 1) * Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) * t ^ 99 := by
    rw [div_le_iff₀ hWpos]
    refine hQ.trans ?_
    have hX : 0 ≤ 2 ^ (m + 5) * M * A ^ (2 * m + 1) * Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) * t ^ 99 := by
      positivity
    calc 2 ^ m * M * A ^ (2 * m + 1) * Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) / t ^ 604
        = 2 ^ (m + 5) * M * A ^ (2 * m + 1) * Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) * t ^ 99 *
            (1 / (32 * t ^ 703)) := by
          rw [pow_add]; field_simp; ring
      _ ≤ _ := by gcongr
  have hfinal : ‖GhF f P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ)))‖ ≤
      2 ^ (2 * m + 1) / (P.Y * A) ^ (2 * m) *
        (2 ^ (m + 5) * M * A ^ (2 * m + 1) * Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) * t ^ 99 +
          (2 * P.Y * A) ^ (2 * m) * P.ε * C₀ * (1 / (π * P.Y) ^ (2 * m)) * ((2 * ((2 * m : ℕ) : ℝ) + 14) * A)) := by
    refine hG.trans ?_
    gcongr
    linarith
  refine hfinal.trans ?_
  have hpi : (1 : ℝ) ≤ π ^ (2 * m) := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hsq : Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) = Real.sqrt CB * (P.h : ℝ) ^ (1 / 21 : ℝ) := by
    rw [Real.sqrt_mul hCB0, Real.sqrt_eq_rpow ((P.h : ℝ) ^ (2 / 21 : ℝ)), ← Real.rpow_mul (by positivity)]
    norm_num
  have hsh : (1 : ℝ) ≤ (P.h : ℝ) ^ (1 / 21 : ℝ) := Real.one_le_rpow hhR (by norm_num)
  have hA0 : 0 < A := by linarith
  have e1 : 2 ^ (2 * m + 1) / (P.Y * A) ^ (2 * m) *
      (2 ^ (m + 5) * M * A ^ (2 * m + 1) * Real.sqrt (CB * (P.h : ℝ) ^ (2 / 21 : ℝ)) * t ^ 99) =
      2 ^ (3 * m + 6) * M * Real.sqrt CB * (P.h : ℝ) ^ (1 / 21 : ℝ) * A * t ^ 99 * (1 / P.Y ^ (2 * m)) := by
    rw [hsq]
    have e3 : (2 : ℝ) ^ (2 * m + 1) * 2 ^ (m + 5) = 2 ^ (3 * m + 6) := by
      rw [← pow_add]; congr 1; ring
    have e4 : A ^ (2 * m + 1) = A ^ (2 * m) * A := pow_succ _ _
    rw [← e3, e4, mul_pow]
    field_simp
  have e2 : 2 ^ (2 * m + 1) / (P.Y * A) ^ (2 * m) * ((2 * P.Y * A) ^ (2 * m) * P.ε * C₀ *
      (1 / (π * P.Y) ^ (2 * m)) * ((2 * ((2 * m : ℕ) : ℝ) + 14) * A)) =
      2 ^ (2 * (2 * m)) * C₀ * (2 * ((2 * m : ℕ) : ℝ) + 14) * A * t ^ 99 / π ^ (2 * m) * (1 / P.Y ^ (2 * m)) := by
    rw [hεt]
    have e3 : (2 : ℝ) ^ (2 * (2 * m)) = 2 ^ (2 * m) * 2 ^ (2 * m) := by rw [two_mul (2 * m), pow_add]
    rw [e3, pow_succ, mul_pow, mul_pow, mul_pow, mul_pow]
    field_simp
  rw [mul_add, e1, e2]
  have hY12 : 0 < 1 / P.Y ^ (2 * m) := by positivity
  have k2 : 2 ^ (2 * (2 * m)) * C₀ * (2 * ((2 * m : ℕ) : ℝ) + 14) * A * t ^ 99 / π ^ (2 * m) ≤
      2 ^ (2 * (2 * m)) * C₀ * (2 * ((2 * m : ℕ) : ℝ) + 14) * (P.h : ℝ) ^ (1 / 21 : ℝ) * A * t ^ 99 := by
    rw [div_le_iff₀ (by positivity)]
    have h0 : 0 ≤ 2 ^ (2 * (2 * m)) * C₀ * (2 * ((2 * m : ℕ) : ℝ) + 14) * A * t ^ 99 := by positivity
    calc 2 ^ (2 * (2 * m)) * C₀ * (2 * ((2 * m : ℕ) : ℝ) + 14) * A * t ^ 99 =
          2 ^ (2 * (2 * m)) * C₀ * (2 * ((2 * m : ℕ) : ℝ) + 14) * A * t ^ 99 * 1 * 1 := by ring
      _ ≤ 2 ^ (2 * (2 * m)) * C₀ * (2 * ((2 * m : ℕ) : ℝ) + 14) * A * t ^ 99 * (P.h : ℝ) ^ (1 / 21 : ℝ) * π ^ (2 * m) := by
          gcongr
      _ = _ := by ring
  have := add_le_add_right (mul_le_mul_of_nonneg_right k2 hY12.le)
    (2 ^ (3 * m + 6) * M * Real.sqrt CB * (P.h : ℝ) ^ (1 / 21 : ℝ) * A * t ^ 99 * (1 / P.Y ^ (2 * m)))
  calc _ ≤ _ := this
    _ = (2 ^ (3 * m + 6) * M * Real.sqrt CB + 2 ^ (2 * (2 * m)) * C₀ * (2 * ((2 * m : ℕ) : ℝ) + 14)) *
          (P.h : ℝ) ^ (1 / 21 : ℝ) * A * t ^ 99 * (1 / P.Y ^ (2 * m)) := by ring

/-- **Sharp pointwise bound, weight `k`**:
`‖G^f_h(σ+iv)‖ ≤ K √h (|2v/σ|+3) σ^{−k + 12/125}`. -/
theorem pointwise_GF21 {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) (hev : Even k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 → (h : ℝ) * σ ≤ 1 →
      ‖RamanujanTau.SubconvexGeneral.GhF f h ((σ : ℂ) + v * I)‖ ≤
        K * (h : ℝ) ^ (1 / 21 : ℝ) * (|2 * v / σ| + 3) * σ ^ (-(k : ℝ) + 99 / 1000) := by
  obtain ⟨m, hm⟩ := hev
  obtain ⟨K, hK0, hK⟩ := pointwise_parF21 f m (by omega)
  refine ⟨K * (4 * π) ^ ((k : ℝ) - 99 / 1000), by positivity,
    fun h hh σ v hσ hσ1 hhσ => ?_⟩
  set Y := σ / (4 * π) with hYdef
  have hY : 0 < Y := by positivity
  have hY1 : Y ≤ 1 := by
    rw [hYdef, div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  set t := Y ^ (1 / 1000 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hY _
  have ht1 : t ≤ 1 := Real.rpow_le_one hY.le hY1 (by norm_num)
  let P : Par := ⟨h, Y, t ^ 99 / 2, 2 * v / σ, hY, hY1, by positivity, by
    have : t ^ 99 ≤ 1 := pow_le_one₀ ht0.le ht1
    linarith⟩
  have hPh : P.h * (4 * π * P.Y) ≤ 1 := by
    show (h : ℝ) * (4 * π * (σ / (4 * π))) ≤ 1
    rw [show 4 * π * (σ / (4 * π)) = σ by field_simp]; exact hhσ
  have hb := hK P hh rfl hPh
  have hW : 2 * π * P.Y * (1 + I * conj ((zeta0 P : UpperHalfPlane) : ℂ)) =
      (σ : ℂ) + v * I := by
    rw [W0_eq]
    show (((4 * π * (σ / (4 * π)) : ℝ)) : ℂ) +
      ((2 * π * (σ / (4 * π)) * (2 * v / σ) : ℝ) : ℂ) * I = _
    congr 2
    · congr 1; field_simp
    · congr 1; field_simp; ring
  rw [hW] at hb
  refine hb.trans (le_of_eq ?_)
  show K * (h : ℝ) ^ (1 / 21 : ℝ) * (|2 * v / σ| + 3) * t ^ 99 * (1 / Y ^ k) = _
  have e1 : t ^ 99 * (1 / Y ^ k) = Y ^ (-(k : ℝ) + 99 / 1000) := by
    have h1 : t ^ 99 = Y ^ (99 / 1000 : ℝ) := by
      rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hY.le]; norm_num
    have h2 : (1 / Y ^ k : ℝ) = Y ^ (-(k : ℝ)) := by
      rw [Real.rpow_neg hY.le, one_div, Real.rpow_natCast]
    rw [h1, h2, ← Real.rpow_add hY]
    ring_nf
  have e2 : Y ^ (-(k : ℝ) + 99 / 1000) =
      (4 * π) ^ ((k : ℝ) - 99 / 1000) * σ ^ (-(k : ℝ) + 99 / 1000) := by
    rw [hYdef, Real.div_rpow hσ.le (by positivity), div_eq_mul_inv,
      ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 * π)]
    rw [show -(-(k : ℝ) + 99 / 1000) = (k : ℝ) - 99 / 1000 by ring]
    ring
  rw [mul_assoc (K * (h : ℝ) ^ (1 / 21 : ℝ) * _), e1, e2]
  ring

end RamanujanTau.SubconvexGeneral3
