/-
# The weight-`k` reduction: `SCS_f(η,B)` ⇒ `|L(f, k/2+it)| ≪ (1+|t|)^{1/2 − δ₂(η,B,u)}`

Weight-parametric copy of `SCSSharp2.rpoly_bound2` / `tauL_subconvex_of_SCS2`, with the **same**
exponent `δ₂(η,B,u) = η/((1+u)(4B+6+2η))` (`SCSSharp2.subconvexDelta2`).  The only changes:

* `λ = τ(n)n^{−11/2}` ↦ `λ_f = nlam f`; `shiftSum` ↦ `shS (nlam f)`;
* diagonal `Σλ²/n`: `MeanSquare.sum_tau_sq_rpow_le` ↦ Abel summation of Rankin's bound
  (`sum_nlam_sq_div_le`, `≤ A(2 + log N)`), absorbed in the same `T^{v/2}` slack;
* approximation `approx_tauL` at `σ = 6` ↦ `approx_fL` at `σ = k/2`;
* conjugation `tauL_conj` ↦ `EigenformEdge.fL_conj` (needs real coefficients);
* convexity for `|t| ≤ 1`: `HeckeConvexGeneral.fL_convexity`.

So after normalization the reduction is literally weight-independent.
-/
import RamanujanTau.SubconvexGeneral.Approx

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral

open Real Finset
open RamanujanTau.SubconvexityCond RamanujanTau.SCSSharp2 RamanujanTau.HeckeConvexGeneral
open RamanujanTau.EigenformEdge
open scoped MatrixGroups

variable {k : ℕ}

/-- `n^{−k/2} = 1/(√n^{k−1} √n)`. -/
lemma rpow_neg_half_eq (hk : 1 ≤ k) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (-((k : ℝ) / 2)) = 1 / (nrm k n * Real.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : nrm k n * Real.sqrt n = Real.sqrt n ^ k := by
    rw [nrm, ← pow_succ]; congr 1; omega
  rw [e1, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le, Real.rpow_neg hn0.le,
    one_div]
  congr 2; ring

/-- The general smoothed polynomial at `σ = k/2` is `rpoly (λ_f · g_X)` (real coefficients). -/
lemma dpoly_bsmF_eq (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (hreal : ∀ n, (coef f n).im = 0)
    (X : ℝ) (N : ℕ) (t : ℝ) :
    RamanujanTau.MeanSquare.dpoly (bsmF f ((k : ℝ) / 2) X) N t =
      rpoly (fun n => nlam f n * gX X n) N t := by
  unfold rpoly
  congr 1
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [bsmF, nlam, coef_zero]
  have hc : coef f n = ((coef f n).re : ℂ) := Complex.ext (by simp) (by simp [hreal n])
  rw [bsmF, hc, rpow_neg_half_eq hk hn]
  simp only [nlam, gX]
  push_cast
  field_simp

set_option maxHeartbeats 4000000 in
/-- **Smoothed Dirichlet polynomial of length `T^{1+11δ/5}` is `≪ T^{1/2−δ}`**, `δ = η/(5B+8)`. -/
theorem rpoly_boundF (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {η B : ℝ} [hS : SCSf f η B] (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 2) (hB : 0 ≤ B) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ T : ℝ, 1 ≤ T →
      ‖rpoly (fun n => nlam f n * gX (T ^ (1 + 2 * subconvexDelta2 η B u + 2 * (subconvexDelta2 η B u * u))) n)
        ⌊T ^ (1 + 2 * subconvexDelta2 η B u + 2 * (subconvexDelta2 η B u * u))⌋₊ T‖ ≤ c * T ^ (1 / 2 - subconvexDelta2 η B u) := by
  obtain ⟨C, hC0, hC⟩ := hS.bound
  obtain ⟨hδ0, hδ1, hηδ⟩ := delta2_facts hη0 hη1 hB hu0 hu1
  set δ := subconvexDelta2 η B u with hδdef
  set v := δ * u with hvdef
  have hv0 : 0 < v := by positivity
  have hvδ : v ≤ δ := by nlinarith
  obtain ⟨M1, hM10, hM1⟩ := exp_poly_bound ((9 + 2 * B) / (v))
  obtain ⟨A0, hA00, hA0⟩ := sum_nlam_sq_div_le f hk
  set cL : ℝ := 1 + 16 / v with hcL
  have hcL1 : 1 ≤ cL := by
    have : 0 ≤ 16 / v := by positivity
    linarith
  set RS0 : ℝ := A0 * (1 + cL) with hRS0def
  have hRS0 : 0 ≤ RS0 := by positivity
  set cB : ℝ := RS0 + 16 * C * M1 + 16 * C * cL with hcB
  have hcB0 : 0 ≤ cB := by positivity
  set c5 : ℝ := Real.sqrt π * 64 * cL ^ 2 * cB with hc5
  have hc50 : 0 ≤ c5 := by positivity
  refine ⟨Real.sqrt (4 * Real.exp 1 * c5), Real.sqrt_nonneg _, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hR1 := region1_bound2 hT hδ0 hδ1 hv0 hvδ hB hC0 hM1
  have hR2 := region2_bound2 hT hδ0 hδ1 hv0 hvδ hB hη1 hηδ
  have hρ1 : 1 ≤ T ^ (v) := Real.one_le_rpow hT (by positivity)
  have hX1 : 1 ≤ T ^ (1 + 2 * δ + 2 * v) := Real.one_le_rpow hT (by linarith)
  have hH1 : 1 ≤ T ^ (1 - 2 * δ - v) := Real.one_le_rpow hT (by linarith)
  have hρH : T ^ (v) ≤ T ^ (1 - 2 * δ - v) := tpow_le hT (by linarith)
  have hHe : T ^ (1 - 2 * δ - v) * T ^ (v / 4) * T ^ (v / 2) =
      T ^ (1 - 2 * δ - v + v / 4 + v / 2) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
  have hlogX : Real.log (T ^ (1 + 2 * δ + 2 * v)) = (1 + 2 * δ + 2 * v) * Real.log T := Real.log_rpow hT0 _
  set ρ := T ^ (v) with hρdef
  set X := T ^ (1 + 2 * δ + 2 * v) with hXdef
  set H := T ^ (1 - 2 * δ - v) with hHdef
  set N := ⌊X⌋₊ with hNdef
  have hX0 : 0 < X := by linarith
  have hH0 : 0 < H := by linarith
  -- logarithms
  set L : ℝ := 1 + Real.log X with hLdef
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hL1 : 1 ≤ L := by rw [hLdef, hlogX]; nlinarith
  have hTd8 : 1 ≤ T ^ (v / 8) := Real.one_le_rpow hT (by positivity)
  have hL : L ≤ cL * T ^ (v / 8) := by
    have h1 := Real.log_le_rpow_div hT0.le (show 0 < v / 8 by positivity)
    have e : T ^ (v / 8) / (v / 8) = 8 / v * T ^ (v / 8) := by field_simp
    rw [e] at h1
    rw [hLdef, hlogX, hcL]
    have : (1 + 2 * δ + 2 * v) * Real.log T ≤ 2 * Real.log T := by nlinarith
    have h16 : 0 ≤ 16 / v := by positivity
    have : 2 * (8 / v * T ^ (v / 8)) = 16 / v * T ^ (v / 8) := by ring
    nlinarith
  have hdiag : ∑ n ∈ Icc 1 N, nlam f n ^ 2 / n ≤ RS0 * T ^ (v / 2) := by
    have h1 := hA0 N
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      have : 1 ≤ N := Nat.le_floor (by simpa using hX1)
      exact_mod_cast this
    have hlogN : Real.log N ≤ Real.log X := Real.log_le_log (by linarith) (Nat.floor_le hX0.le)
    have hv8 : T ^ (v / 8) ≤ T ^ (v / 2) := tpow_le hT (by linarith)
    have hv2 : 1 ≤ T ^ (v / 2) := Real.one_le_rpow hT (by positivity)
    have h2 : 2 + Real.log N ≤ (1 + cL) * T ^ (v / 2) := by
      have : cL * T ^ (v / 8) ≤ cL * T ^ (v / 2) := mul_le_mul_of_nonneg_left hv8 (by linarith)
      nlinarith
    calc ∑ n ∈ Icc 1 N, nlam f n ^ 2 / n ≤ A0 * (2 + Real.log N) := h1
      _ ≤ A0 * ((1 + cL) * T ^ (v / 2)) := mul_le_mul_of_nonneg_left h2 hA00
      _ = RS0 * T ^ (v / 2) := by rw [hRS0def]; ring
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
  have hA : ∀ h n : ℕ, 1 ≤ h → |shS (nlam f) h n| ≤ C * ((n : ℝ) + h) ^ (1 - η) * (h : ℝ) ^ B :=
    fun h n hh => hC h n hh
  have hη1' : η ≤ 1 := by linarith
  have hMV1 := mean_value_boundG (nlam f) (T := T) hη0.le hη1' hB hC0 hρ1 hρH hg1 hA
  have hMV2 := mean_value_boundG (nlam f) (T := T) hη0.le hη1' hB hC0 hρ1 hρH hg2 hA
  have hPW := norm_sq_le_window hH1 (fun n => nlam f n * gX X n) N T
  have e2 : (fun n => (fun n => nlam f n * gX X n) n * Real.log n) =
      fun n => nlam f n * (fun n => gX X n * Real.log n) n := by funext n; simp only; ring
  rw [e2] at hPW
  -- the bracket
  set Br : ℝ := ∑ n ∈ Icc 1 N, nlam f n ^ 2 / n +
        4 * C * (N : ℝ) ^ 3 * (N : ℝ) ^ B * (3 + |T| * N) * Real.exp (-ρ ^ 2 / 64) +
        4 * C * ((N : ℝ) * ρ / H) * ((N : ℝ) * ρ / H) ^ B * (H / ρ) ^ (-η) *
          ((2 + |T| * ρ / H) * (1 + Real.log N) + 1) with hBr
  have hTd2 : 1 ≤ T ^ (v / 2) := Real.one_le_rpow hT (by positivity)
  have hBr' : Br ≤ cB * T ^ (v / 2) := by
    have hLT : L ≤ cL * T ^ (v / 2) :=
      hL.trans (mul_le_mul_of_nonneg_left (tpow_le hT (by linarith)) (by linarith))
    have h4 := mul_le_mul_of_nonneg_left hR2 (show 0 ≤ 4 * C by positivity)
    have h1 : 16 * C * L ≤ 16 * C * cL * T ^ (v / 2) := by
      have := mul_le_mul_of_nonneg_left hLT (show 0 ≤ 16 * C by positivity); linarith
    have h2 : 16 * C * M1 ≤ 16 * C * M1 * T ^ (v / 2) := by
      have : 0 ≤ 16 * C * M1 := by positivity
      nlinarith
    rw [hBr, hcB]
    have e4 : 4 * C * ((N : ℝ) * ρ / H) * ((N : ℝ) * ρ / H) ^ B * (H / ρ) ^ (-η) *
        ((2 + |T| * ρ / H) * (1 + Real.log N) + 1) =
        4 * C * (((N : ℝ) * ρ / H) * ((N : ℝ) * ρ / H) ^ B * (H / ρ) ^ (-η) *
        ((2 + |T| * ρ / H) * (1 + Real.log N) + 1)) := by ring
    rw [e4]
    linarith
  have hK'2 : K' ^ 2 ≤ 64 * cL ^ 2 * T ^ (v / 4) := by
    have h1 : K' ^ 2 ≤ (8 * L) ^ 2 := pow_le_pow_left₀ (by linarith) hK'L 2
    have h2 : L ^ 2 ≤ (cL * T ^ (v / 8)) ^ 2 := pow_le_pow_left₀ (by linarith) hL 2
    have e : (T ^ (v / 8)) ^ 2 = T ^ (v / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; ring_nf
    calc K' ^ 2 ≤ (8 * L) ^ 2 := h1
      _ = 64 * L ^ 2 := by ring
      _ ≤ 64 * (cL * T ^ (v / 8)) ^ 2 := by linarith
      _ = 64 * cL ^ 2 * (T ^ (v / 8)) ^ 2 := by ring
      _ = 64 * cL ^ 2 * T ^ (v / 4) := by rw [e]
  have hBr0 : 0 ≤ Br := by
    rw [hBr]
    have : (1 : ℝ) ≤ N := by
      have h1 : 1 ≤ N := Nat.le_floor (by simpa using hX1)
      exact_mod_cast h1
    have := Real.log_nonneg this
    have : 0 ≤ ∑ n ∈ Icc 1 N, nlam f n ^ 2 / n := sum_nonneg fun n _ => by positivity
    positivity
  have hM : H * Real.sqrt π * K' ^ 2 * Br ≤ c5 * T ^ (1 - 2 * δ) := by
    have hle : T ^ (1 - 2 * δ - v + v / 4 + v / 2) ≤ T ^ (1 - 2 * δ) := tpow_le hT (by linarith)
    calc H * Real.sqrt π * K' ^ 2 * Br ≤ H * Real.sqrt π * (64 * cL ^ 2 * T ^ (v / 4)) *
          (cB * T ^ (v / 2)) := by gcongr
      _ = c5 * (H * T ^ (v / 4) * T ^ (v / 2)) := by rw [hc5]; ring
      _ ≤ c5 * T ^ (1 - 2 * δ) := by rw [hHe]; exact mul_le_mul_of_nonneg_left hle hc50
  have hsq : ‖rpoly (fun n => nlam f n * gX X n) N T‖ ^ 2 ≤
      4 * Real.exp 1 * c5 * T ^ (1 - 2 * δ) := by
    have he := Real.exp_pos 1
    calc ‖rpoly (fun n => nlam f n * gX X n) N T‖ ^ 2 ≤ 2 * Real.exp 1 *
          (H * Real.sqrt π * K' ^ 2 * Br + H * Real.sqrt π * K' ^ 2 * Br) := by
          refine hPW.trans ?_
          gcongr
      _ = 4 * Real.exp 1 * (H * Real.sqrt π * K' ^ 2 * Br) := by ring
      _ ≤ 4 * Real.exp 1 * (c5 * T ^ (1 - 2 * δ)) := by gcongr
      _ = 4 * Real.exp 1 * c5 * T ^ (1 - 2 * δ) := by ring
  have hroot : Real.sqrt (T ^ (1 - 2 * δ)) = T ^ (1 / 2 - δ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le]; ring_nf
  calc ‖rpoly (fun n => nlam f n * gX X n) N T‖ =
      Real.sqrt (‖rpoly (fun n => nlam f n * gX X n) N T‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (4 * Real.exp 1 * c5 * T ^ (1 - 2 * δ)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (4 * Real.exp 1 * c5) * T ^ (1 / 2 - δ) := by
        rw [Real.sqrt_mul (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le) hc50), hroot]

open Complex in
set_option maxHeartbeats 4000000 in
/-- **Sharper conditional subconvexity**: under `SCS(η, B)` with `0 < η ≤ 1/2`, `B ≥ 0`,
`‖L(Δ, 6+it)‖ ≤ C (1+|t|)^{1/2 − η/(5B+8)}`. -/
theorem fL_subconvex_of_SCSf (f : CuspForm 𝒮ℒ (k : ℤ)) (hreal : ∀ n, (coef f n).im = 0)
    {η B : ℝ} [SCSf f η B] (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 2) (hB : 0 ≤ B) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - subconvexDelta2 η B u) := by
  rcases lt_or_ge k 12 with hk | hk
  · refine ⟨0, le_rfl, fun t => ?_⟩
    rw [fL_of_eq_zero (eq_zero_of_lt_twelve f hk)]; simp
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hδ0, hδ1, hηδ⟩ := delta2_facts hη0 hη1 hB hu0 hu1
  obtain ⟨c, hc0, hc⟩ := rpoly_boundF f hk1 (η := η) (B := B) hη0 hη1 hB hu0 hu1
  set δ := subconvexDelta2 η B u with hδdef
  set v := δ * u with hvdef
  have hv0 : 0 < v := by positivity
  have hvδ : v ≤ δ := by nlinarith
  obtain ⟨Ca, hCa0, hCa⟩ := approx_fL f hk (δ := 1 / 2) (ε := v) (by norm_num) le_rfl
    (by positivity) (by linarith)
  obtain ⟨C0, hC00, hC0⟩ := fL_convexity f (ε := 1 / 2) (by norm_num)
  -- the bound for `T ≥ 1`
  have hpos : ∀ T : ℝ, 1 ≤ T →
      ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + T * I)‖ ≤ (c + 4 * Ca) * T ^ (1 / 2 - δ) := by
    intro T hT
    have hT0 : 0 < T := by linarith
    have hX1 : 1 ≤ T ^ (1 + 2 * δ + 2 * v) := Real.one_le_rpow hT (by linarith)
    have h1 := hCa (T ^ (1 + 2 * δ + 2 * v)) hX1 T
    have h2 := hc T hT
    rw [← dpoly_bsmF_eq f hk1 hreal] at h2
    have herr : (T ^ (1 + 2 * δ + 2 * v)) ^ (-(1 / 2 : ℝ)) *
        (1 + |T|) ^ (1 / 2 + 1 / 2 + v) ≤ 4 * T ^ (1 / 2 - δ) := by
      rw [abs_of_pos hT0, show (1 / 2 + 1 / 2 + v : ℝ) = 1 + v by ring]
      have hA : (1 + T) ^ (1 + v) ≤ 4 * T ^ (1 + v) := by
        calc (1 + T) ^ (1 + v) ≤ (2 * T) ^ (1 + v) :=
              Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
          _ = 2 ^ (1 + v) * T ^ (1 + v) := Real.mul_rpow (by norm_num) hT0.le
          _ ≤ 4 * T ^ (1 + v) := by
              gcongr
              calc (2 : ℝ) ^ (1 + v) ≤ 2 ^ (2 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                _ = 4 := by norm_num
      have hX : (T ^ (1 + 2 * δ + 2 * v)) ^ (-(1 / 2 : ℝ)) * T ^ (1 + v) = T ^ (1 / 2 - δ) := by
        rw [← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]; ring_nf
      have hp : 0 ≤ (T ^ (1 + 2 * δ + 2 * v)) ^ (-(1 / 2 : ℝ)) := by positivity
      calc (T ^ (1 + 2 * δ + 2 * v)) ^ (-(1 / 2 : ℝ)) * (1 + T) ^ (1 + v) ≤
          (T ^ (1 + 2 * δ + 2 * v)) ^ (-(1 / 2 : ℝ)) * (4 * T ^ (1 + v)) :=
            mul_le_mul_of_nonneg_left hA hp
        _ = 4 * T ^ (1 / 2 - δ) := by rw [← hX]; ring
    have h3 := norm_sub_norm_le (fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + T * I))
      (RamanujanTau.MeanSquare.dpoly (bsmF f ((k : ℝ) / 2) (T ^ (1 + 2 * δ + 2 * v)))
        ⌊T ^ (1 + 2 * δ + 2 * v)⌋₊ T)
    have h4 : Ca * (T ^ (1 + 2 * δ + 2 * v)) ^ (-(1 / 2 : ℝ)) *
        (1 + |T|) ^ (1 / 2 + 1 / 2 + v) ≤ Ca * (4 * T ^ (1 / 2 - δ)) := by
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
  · have key : ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + t * I)‖ = ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + |t| * I)‖ := by
      rcases le_or_gt 0 t with h0 | h0
      · rw [abs_of_nonneg h0]
      · rw [abs_of_neg h0]
        have e : (((k : ℝ) / 2 : ℝ) : ℂ) + t * I =
            (starRingEnd ℂ) ((((k : ℝ) / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
          rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
          push_cast; ring
        rw [e, RamanujanTau.EigenformEdge.fL_conj f hreal, Complex.norm_conj]
    rw [key]
    have h := hpos |t| ht.le
    have hmono : |t| ^ (1 / 2 - δ) ≤ (1 + |t|) ^ (1 / 2 - δ) :=
      Real.rpow_le_rpow (abs_nonneg t) (by linarith) hδh
    have : 0 ≤ c + 4 * Ca := by positivity
    have := mul_le_mul_of_nonneg_left hmono this
    have : 0 ≤ 2 * C0 * (1 + |t|) ^ (1 / 2 - δ) := by positivity
    nlinarith

end RamanujanTau.SubconvexGeneral
