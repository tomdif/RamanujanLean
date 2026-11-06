/-
# Conditional subconvexity: `SCS(η,B)` ⇒ `|L(Δ, 6+it)| ≪ (1+|t|)^{1/2 − η/(10B+24)}`

* `rpoly_bound`: the smoothed Dirichlet polynomial of length `X = T^{1+4δ}` is `≪ T^{1/2−δ}`.
* `tauL_subconvex_of_SCS`: combine with the one-sided Riesz–Perron approximation
  `MeanSquare.approx_tauL` (error `≪ X^{−1/2} T^{1+δ} = T^{1/2−δ}`), conjugation symmetry and
  the convexity bound for `|t| ≤ 1`.
-/
import RamanujanTau.SubconvexityCond.Assembly
import RamanujanTau.HeckeZeros.Zeros

set_option autoImplicit false

namespace RamanujanTau.SubconvexityCond

open Real Finset

set_option maxHeartbeats 800000 in
/-- **Conditional bound for the smoothed Dirichlet polynomial of length `T^{1+4δ}`.** -/
theorem rpoly_bound {η B : ℝ} [hS : ShiftedConvolutionBound η B] (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ T : ℝ, 1 ≤ T →
      ‖rpoly (fun n => lam n * gX (T ^ (1 + 4 * subconvexDelta η B)) n)
        ⌊T ^ (1 + 4 * subconvexDelta η B)⌋₊ T‖ ≤ c * T ^ (1 / 2 - subconvexDelta η B) := by
  obtain ⟨C, hC0, hC⟩ := hS.bound
  have hδ0 : 0 < subconvexDelta η B := subconvexDelta_pos hη0 hB
  have hδ1 : subconvexDelta η B ≤ 1 / 24 := by
    rw [subconvexDelta, div_le_iff₀ (by positivity)]; nlinarith
  have hηδ : η = 2 * subconvexDelta η B * (5 * B + 12) := by
    rw [subconvexDelta]; field_simp; ring
  set δ := subconvexDelta η B with hδdef
  obtain ⟨M1, hM10, hM1⟩ := exp_poly_bound ((9 + 2 * B) / (2 * δ))
  set RS0 := RamanujanTau.MeanSquare.RS (12 + δ / 4)
  have hRS0 : 0 ≤ RS0 := RamanujanTau.MeanSquare.RS_nonneg _
  set cL : ℝ := 1 + 16 / δ with hcL
  have hcL1 : 1 ≤ cL := by
    have : 0 ≤ 16 / δ := by positivity
    linarith
  set cB : ℝ := RS0 + 16 * C * M1 + 16 * C * cL with hcB
  have hcB0 : 0 ≤ cB := by positivity
  set c5 : ℝ := Real.sqrt π * 64 * cL ^ 2 * cB with hc5
  have hc50 : 0 ≤ c5 := by positivity
  refine ⟨Real.sqrt (4 * Real.exp 1 * c5), Real.sqrt_nonneg _, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hdiag := diag_bound hT hδ0 hδ1
  have hR1 := region1_bound hT hδ0 hδ1 hB hC0 hM1
  have hR2 := region2_bound hT hδ0 hδ1 hB hη1 hηδ
  have hρ1 : 1 ≤ T ^ (2 * δ) := Real.one_le_rpow hT (by positivity)
  have hX1 : 1 ≤ T ^ (1 + 4 * δ) := Real.one_le_rpow hT (by linarith)
  have hH1 : 1 ≤ T ^ (1 - 4 * δ) := Real.one_le_rpow hT (by linarith)
  have hρH : T ^ (2 * δ) ≤ T ^ (1 - 4 * δ) := tpow_le hT (by linarith)
  have hHe : T ^ (1 - 4 * δ) * T ^ (δ / 4) * T ^ (δ / 2) = T ^ (1 - 4 * δ + δ / 4 + δ / 2) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
  have hlogX : Real.log (T ^ (1 + 4 * δ)) = (1 + 4 * δ) * Real.log T := Real.log_rpow hT0 _
  set ρ := T ^ (2 * δ) with hρdef
  set X := T ^ (1 + 4 * δ) with hXdef
  set H := T ^ (1 - 4 * δ) with hHdef
  set N := ⌊X⌋₊ with hNdef
  have hX0 : 0 < X := by linarith
  have hH0 : 0 < H := by linarith
  -- logarithms
  set L : ℝ := 1 + Real.log X with hLdef
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hL1 : 1 ≤ L := by rw [hLdef, hlogX]; nlinarith
  have hTd8 : 1 ≤ T ^ (δ / 8) := Real.one_le_rpow hT (by positivity)
  have hL : L ≤ cL * T ^ (δ / 8) := by
    have h1 := Real.log_le_rpow_div hT0.le (show 0 < δ / 8 by positivity)
    have e : T ^ (δ / 8) / (δ / 8) = 8 / δ * T ^ (δ / 8) := by field_simp
    rw [e] at h1
    rw [hLdef, hlogX, hcL]
    have : (1 + 4 * δ) * Real.log T ≤ 2 * Real.log T := by nlinarith
    have h16 : 0 ≤ 16 / δ := by positivity
    have : 2 * (8 / δ * T ^ (δ / 8)) = 16 / δ * T ^ (δ / 8) := by ring
    nlinarith
  -- the two weights
  set K' : ℝ := 4 * Real.log (X + 1) + 4 with hK'
  have hK'4 : 4 ≤ K' := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ X + 1 by linarith); rw [hK']; linarith
  have hK'L : K' ≤ 8 * L := by
    have h1 : Real.log (X + 1) ≤ Real.log (2 * X) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hX0.ne'] at h1
    have := Real.log_two_lt_d9
    rw [hK', hLdef]; nlinarith
  have hg1 : GBound (gX X) K' N := (gBound_gX hX1).mono hK'4
  have hg2 : GBound (fun n => gX X n * Real.log n) K' N := gBound_gX_log hX1
  have hA : ∀ h n : ℕ, 1 ≤ h → |shiftSum h n| ≤ C * ((n : ℝ) + h) ^ (1 - η) * (h : ℝ) ^ B :=
    fun h n hh => hC h n hh
  have hMV1 := mean_value_bound (T := T) hη0.le hη1 hB hC0 hρ1 hρH hg1 hA
  have hMV2 := mean_value_bound (T := T) hη0.le hη1 hB hC0 hρ1 hρH hg2 hA
  have hPW := norm_sq_le_window hH1 (fun n => lam n * gX X n) N T
  have e2 : (fun n => (fun n => lam n * gX X n) n * Real.log n) =
      fun n => lam n * (fun n => gX X n * Real.log n) n := by funext n; simp only; ring
  rw [e2] at hPW
  -- the bracket
  set Br : ℝ := ∑ n ∈ Icc 1 N, lam n ^ 2 / n +
        4 * C * (N : ℝ) ^ 3 * (N : ℝ) ^ B * (3 + |T| * N) * Real.exp (-ρ ^ 2 / 64) +
        4 * C * ((N : ℝ) * ρ / H) * ((N : ℝ) * ρ / H) ^ B * (H / ρ) ^ (-η) *
          ((2 + |T| * ρ / H) * (1 + Real.log N) + 1) with hBr
  have hTd2 : 1 ≤ T ^ (δ / 2) := Real.one_le_rpow hT (by positivity)
  have hBr' : Br ≤ cB * T ^ (δ / 2) := by
    have hLT : L ≤ cL * T ^ (δ / 2) :=
      hL.trans (mul_le_mul_of_nonneg_left (tpow_le hT (by linarith)) (by linarith))
    have h4 := mul_le_mul_of_nonneg_left hR2 (show 0 ≤ 4 * C by positivity)
    have h1 : 16 * C * L ≤ 16 * C * cL * T ^ (δ / 2) := by
      have := mul_le_mul_of_nonneg_left hLT (show 0 ≤ 16 * C by positivity); linarith
    have h2 : 16 * C * M1 ≤ 16 * C * M1 * T ^ (δ / 2) := by
      have : 0 ≤ 16 * C * M1 := by positivity
      nlinarith
    rw [hBr, hcB]
    have e4 : 4 * C * ((N : ℝ) * ρ / H) * ((N : ℝ) * ρ / H) ^ B * (H / ρ) ^ (-η) *
        ((2 + |T| * ρ / H) * (1 + Real.log N) + 1) =
        4 * C * (((N : ℝ) * ρ / H) * ((N : ℝ) * ρ / H) ^ B * (H / ρ) ^ (-η) *
        ((2 + |T| * ρ / H) * (1 + Real.log N) + 1)) := by ring
    rw [e4]
    linarith
  have hK'2 : K' ^ 2 ≤ 64 * cL ^ 2 * T ^ (δ / 4) := by
    have h1 : K' ^ 2 ≤ (8 * L) ^ 2 := pow_le_pow_left₀ (by linarith) hK'L 2
    have h2 : L ^ 2 ≤ (cL * T ^ (δ / 8)) ^ 2 := pow_le_pow_left₀ (by linarith) hL 2
    have e : (T ^ (δ / 8)) ^ 2 = T ^ (δ / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; ring_nf
    calc K' ^ 2 ≤ (8 * L) ^ 2 := h1
      _ = 64 * L ^ 2 := by ring
      _ ≤ 64 * (cL * T ^ (δ / 8)) ^ 2 := by linarith
      _ = 64 * cL ^ 2 * (T ^ (δ / 8)) ^ 2 := by ring
      _ = 64 * cL ^ 2 * T ^ (δ / 4) := by rw [e]
  have hBr0 : 0 ≤ Br := by
    rw [hBr]
    have : (1 : ℝ) ≤ N := by
      have h1 : 1 ≤ N := Nat.le_floor (by simpa using hX1)
      exact_mod_cast h1
    have := Real.log_nonneg this
    have : 0 ≤ ∑ n ∈ Icc 1 N, lam n ^ 2 / n := sum_nonneg fun n _ => by positivity
    positivity
  have hM : H * Real.sqrt π * K' ^ 2 * Br ≤ c5 * T ^ (1 - 2 * δ) := by
    have hle : T ^ (1 - 4 * δ + δ / 4 + δ / 2) ≤ T ^ (1 - 2 * δ) := tpow_le hT (by linarith)
    calc H * Real.sqrt π * K' ^ 2 * Br ≤ H * Real.sqrt π * (64 * cL ^ 2 * T ^ (δ / 4)) *
          (cB * T ^ (δ / 2)) := by gcongr
      _ = c5 * (H * T ^ (δ / 4) * T ^ (δ / 2)) := by rw [hc5]; ring
      _ ≤ c5 * T ^ (1 - 2 * δ) := by rw [hHe]; exact mul_le_mul_of_nonneg_left hle hc50
  have hsq : ‖rpoly (fun n => lam n * gX X n) N T‖ ^ 2 ≤
      4 * Real.exp 1 * c5 * T ^ (1 - 2 * δ) := by
    have he := Real.exp_pos 1
    calc ‖rpoly (fun n => lam n * gX X n) N T‖ ^ 2 ≤ 2 * Real.exp 1 *
          (H * Real.sqrt π * K' ^ 2 * Br + H * Real.sqrt π * K' ^ 2 * Br) := by
          refine hPW.trans ?_
          gcongr
      _ = 4 * Real.exp 1 * (H * Real.sqrt π * K' ^ 2 * Br) := by ring
      _ ≤ 4 * Real.exp 1 * (c5 * T ^ (1 - 2 * δ)) := by gcongr
      _ = 4 * Real.exp 1 * c5 * T ^ (1 - 2 * δ) := by ring
  have hroot : Real.sqrt (T ^ (1 - 2 * δ)) = T ^ (1 / 2 - δ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le]; ring_nf
  calc ‖rpoly (fun n => lam n * gX X n) N T‖ =
      Real.sqrt (‖rpoly (fun n => lam n * gX X n) N T‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (4 * Real.exp 1 * c5 * T ^ (1 - 2 * δ)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (4 * Real.exp 1 * c5) * T ^ (1 / 2 - δ) := by
        rw [Real.sqrt_mul (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le) hc50), hroot]

open Complex in
set_option maxHeartbeats 800000 in
/-- **Conditional subconvexity for `L(Δ,s)` in the `t`-aspect.**  Under the shifted-convolution
hypothesis `SCS(η, B)` (`0 < η ≤ 1`, `B ≥ 0`), with `δ = η/(10B+24)`:
`‖L(Δ, 6+it)‖ ≤ C (1+|t|)^{1/2−δ}` for all real `t`. -/
theorem tauL_subconvex_of_SCS {η B : ℝ} [ShiftedConvolutionBound η B] (hη0 : 0 < η)
    (hη1 : η ≤ 1) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖RamanujanTau.HeckeL.tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - subconvexDelta η B) := by
  have hδ0 : 0 < subconvexDelta η B := subconvexDelta_pos hη0 hB
  have hδ1 : subconvexDelta η B ≤ 1 / 24 := by
    rw [subconvexDelta, div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨c, hc0, hc⟩ := rpoly_bound (η := η) (B := B) hη0 hη1 hB
  set δ := subconvexDelta η B with hδdef
  obtain ⟨Ca, hCa0, hCa⟩ := RamanujanTau.MeanSquare.approx_tauL (σ := 6) (δ := 1 / 2) (ε := δ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hδ0 (by linarith)
  obtain ⟨C0, hC00, hC0⟩ := RamanujanTau.HeckeConvex.tauL_convexity (ε := 1 / 2) (by norm_num)
  -- the bound for `T ≥ 1`
  have hpos : ∀ T : ℝ, 1 ≤ T →
      ‖RamanujanTau.HeckeL.tauL (6 + T * I)‖ ≤ (c + 4 * Ca) * T ^ (1 / 2 - δ) := by
    intro T hT
    have hT0 : 0 < T := by linarith
    have hX1 : 1 ≤ T ^ (1 + 4 * δ) := Real.one_le_rpow hT (by linarith)
    have h1 := hCa (T ^ (1 + 4 * δ)) hX1 T
    have h2 := hc T hT
    rw [← dpoly_bsm_eq] at h2
    have e6 : ((6 : ℝ) : ℂ) + T * I = 6 + T * I := by push_cast; rfl
    rw [e6] at h1
    have herr : (T ^ (1 + 4 * δ)) ^ (-(1 / 2 : ℝ)) * (1 + |T|) ^ (13 / 2 - 6 + 1 / 2 + δ) ≤
        4 * T ^ (1 / 2 - δ) := by
      rw [abs_of_pos hT0, show (13 / 2 - 6 + 1 / 2 + δ : ℝ) = 1 + δ by ring]
      have hA : (1 + T) ^ (1 + δ) ≤ 4 * T ^ (1 + δ) := by
        calc (1 + T) ^ (1 + δ) ≤ (2 * T) ^ (1 + δ) :=
              Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
          _ = 2 ^ (1 + δ) * T ^ (1 + δ) := Real.mul_rpow (by norm_num) hT0.le
          _ ≤ 4 * T ^ (1 + δ) := by
              gcongr
              calc (2 : ℝ) ^ (1 + δ) ≤ 2 ^ (2 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                _ = 4 := by norm_num
      have hX : (T ^ (1 + 4 * δ)) ^ (-(1 / 2 : ℝ)) * T ^ (1 + δ) = T ^ (1 / 2 - δ) := by
        rw [← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]; ring_nf
      have hp : 0 ≤ (T ^ (1 + 4 * δ)) ^ (-(1 / 2 : ℝ)) := by positivity
      calc (T ^ (1 + 4 * δ)) ^ (-(1 / 2 : ℝ)) * (1 + T) ^ (1 + δ) ≤
          (T ^ (1 + 4 * δ)) ^ (-(1 / 2 : ℝ)) * (4 * T ^ (1 + δ)) :=
            mul_le_mul_of_nonneg_left hA hp
        _ = 4 * T ^ (1 / 2 - δ) := by rw [← hX]; ring
    have h3 := norm_sub_norm_le (RamanujanTau.HeckeL.tauL (6 + T * I))
      (RamanujanTau.MeanSquare.dpoly (RamanujanTau.MeanSquare.bsm 6 (T ^ (1 + 4 * δ)))
        ⌊T ^ (1 + 4 * δ)⌋₊ T)
    have h4 : Ca * (T ^ (1 + 4 * δ)) ^ (-(1 / 2 : ℝ)) * (1 + |T|) ^ (13 / 2 - 6 + 1 / 2 + δ) ≤
        Ca * (4 * T ^ (1 / 2 - δ)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left herr hCa0
    linarith
  refine ⟨c + 4 * Ca + 2 * C0, by positivity, fun t => ?_⟩
  have hδh : 0 ≤ 1 / 2 - δ := by linarith
  have hb1 : 1 ≤ (1 + |t|) ^ (1 / 2 - δ) := Real.one_le_rpow (by linarith [abs_nonneg t]) hδh
  rcases le_or_gt |t| 1 with ht | ht
  · have h := hC0 t
    rw [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] at h
    have : C0 * (1 + |t|) ≤ 2 * C0 := by nlinarith
    have : 0 ≤ (c + 4 * Ca) * (1 + |t|) ^ (1 / 2 - δ) := by positivity
    nlinarith
  · have key : ‖RamanujanTau.HeckeL.tauL (6 + t * I)‖ = ‖RamanujanTau.HeckeL.tauL (6 + |t| * I)‖ := by
      rcases le_or_gt 0 t with h0 | h0
      · rw [abs_of_nonneg h0]
      · rw [abs_of_neg h0]
        have e : (6 : ℂ) + t * I = (starRingEnd ℂ) (6 + ((-t : ℝ) : ℂ) * I) := by
          apply Complex.ext <;> simp
        rw [e, RamanujanTau.HeckeZeros.tauL_conj, Complex.norm_conj]
    rw [key]
    have h := hpos |t| ht.le
    have hmono : |t| ^ (1 / 2 - δ) ≤ (1 + |t|) ^ (1 / 2 - δ) :=
      Real.rpow_le_rpow (abs_nonneg t) (by linarith) hδh
    have : 0 ≤ c + 4 * Ca := by positivity
    have := mul_le_mul_of_nonneg_left hmono this
    have : 0 ≤ 2 * C0 * (1 + |t|) ^ (1 / 2 - δ) := by positivity
    nlinarith

open Complex in
/-- **Any power saving in the shifted sums gives a power saving over convexity.** -/
theorem exists_subconvex_of_SCS {η B : ℝ} (h : ShiftedConvolutionBound η B) (hη0 : 0 < η)
    (hB : 0 ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖RamanujanTau.HeckeL.tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - δ) := by
  have h' : ShiftedConvolutionBound (min η 1) B := h.mono (min_le_left _ _) le_rfl
  refine ⟨subconvexDelta (min η 1) B, subconvexDelta_pos (lt_min hη0 one_pos) hB, ?_⟩
  exact tauL_subconvex_of_SCS (lt_min hη0 one_pos) (min_le_right _ _) hB

end RamanujanTau.SubconvexityCond
