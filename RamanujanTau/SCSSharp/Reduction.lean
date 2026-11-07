/-
# A sharper reduction: `SCS(η,B)` ⇒ `|L(Δ, 6+it)| ≪ (1+|t|)^{1/2 − η/(5B+8)}` (`0 < η ≤ 1/2`)

Same proof as `SubconvexityCond.tauL_subconvex_of_SCS` (exponent `η/(10B+24)`), with re-optimized
parameters (`δ = η/(5B+8)`):

    ρ = T^{δ/10},  X = T^{1 + 11δ/5},  H = T^{1 − 21δ/10},  approximation exponent ε = δ/10.

The approximation error `X^{−1/2} T^{1+ε}` is exactly `T^{1/2−δ}`; the off-diagonal exponent is
`(22δ/5)(1+B) + 11δ/5 − (1 − 11δ/5)η = (δ/5)(11η − 7 − 3B) ≤ 0`; diagonal and logarithms cost
`T^{3δ/40}` against the slack `H T^{3δ/40} ≤ T^{1−2δ}`.  The method's limit is `η/(4B+6)`.
-/
import RamanujanTau.SubconvexityCond.Final

set_option autoImplicit false

namespace RamanujanTau.SCSSharp

open Real Finset
open RamanujanTau.SubconvexityCond

/-- The sharper exponent `δ'(η,B) = η/(5B+8)`. -/
noncomputable def subconvexDelta' (η B : ℝ) : ℝ := η / (5 * B + 8)

lemma subconvexDelta'_pos {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) : 0 < subconvexDelta' η B := by
  unfold subconvexDelta'; positivity

section params
variable {T δ : ℝ}

lemma diag_bound' (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16) :
    ∑ n ∈ Icc 1 ⌊T ^ (1 + 11 * δ / 5)⌋₊, lam n ^ 2 / n ≤
      RamanujanTau.MeanSquare.RS (12 + δ / 40) * T ^ (δ / 20) := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < T ^ (1 + 11 * δ / 5) := by positivity
  simp_rw [lam_sq_div]
  have h := RamanujanTau.MeanSquare.sum_tau_sq_rpow_le (β := 12 + δ / 40) (γ := 12)
    (by linarith) (by linarith) ⌊T ^ (1 + 11 * δ / 5)⌋₊
  rw [show 12 + δ / 40 - 12 = δ / 40 by ring] at h
  refine h.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (RamanujanTau.MeanSquare.RS_nonneg _)
  calc ((⌊T ^ (1 + 11 * δ / 5)⌋₊ : ℕ) : ℝ) ^ (δ / 40) ≤ (T ^ (1 + 11 * δ / 5)) ^ (δ / 40) :=
        Real.rpow_le_rpow (by positivity) (Nat.floor_le hX0.le) (by positivity)
    _ = T ^ ((1 + 11 * δ / 5) * (δ / 40)) := by rw [← Real.rpow_mul hT0.le]
    _ ≤ T ^ (δ / 20) := tpow_le hT (by nlinarith)

lemma region1_bound' {B C M1 : ℝ} (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16) (hB : 0 ≤ B)
    (hC0 : 0 ≤ C) (hM1 : ∀ ρ : ℝ, 1 ≤ ρ →
      ρ ^ ((9 + 2 * B) / (δ / 10)) * Real.exp (-ρ ^ 2 / 64) ≤ M1) :
    4 * C * ((⌊T ^ (1 + 11 * δ / 5)⌋₊ : ℕ) : ℝ) ^ 3 * ((⌊T ^ (1 + 11 * δ / 5)⌋₊ : ℕ) : ℝ) ^ B *
      (3 + |T| * ((⌊T ^ (1 + 11 * δ / 5)⌋₊ : ℕ) : ℝ)) * Real.exp (-(T ^ (δ / 10)) ^ 2 / 64) ≤
      16 * C * M1 := by
  have hT0 : 0 < T := by linarith
  set N : ℝ := ((⌊T ^ (1 + 11 * δ / 5)⌋₊ : ℕ) : ℝ)
  have hX0 : 0 < T ^ (1 + 11 * δ / 5) := by positivity
  have hXT : T ^ (1 + 11 * δ / 5) ≤ T ^ 2 := by
    rw [← Real.rpow_natCast]; exact tpow_le hT (by push_cast; linarith)
  have hNT : N ≤ T ^ 2 := (Nat.floor_le hX0.le).trans hXT
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hq : (T ^ (δ / 10)) ^ ((9 + 2 * B) / (δ / 10)) = T ^ (9 : ℕ) * T ^ (2 * B) := by
    rw [← Real.rpow_mul hT0.le, show δ / 10 * ((9 + 2 * B) / (δ / 10)) = ((9 : ℕ) : ℝ) + 2 * B by
      field_simp; push_cast; ring, Real.rpow_add hT0, Real.rpow_natCast]
  have hn3 : N ^ 3 ≤ T ^ 6 := by
    calc N ^ 3 ≤ (T ^ 2) ^ 3 := pow_le_pow_left₀ hN0 hNT 3
      _ = T ^ 6 := by ring
  have hnB : N ^ B ≤ T ^ (2 * B) := by
    calc N ^ B ≤ (T ^ 2) ^ B := Real.rpow_le_rpow hN0 hNT hB
      _ = T ^ (2 * B) := by
        rw [← Real.rpow_natCast T 2, ← Real.rpow_mul hT0.le]; norm_num
  have h3 : 3 + |T| * N ≤ 4 * T ^ 3 := by
    rw [abs_of_pos hT0]
    have : (1 : ℝ) ≤ T ^ 3 := one_le_pow₀ hT
    have : T * N ≤ T * T ^ 2 := mul_le_mul_of_nonneg_left hNT hT0.le
    nlinarith
  have hprod : N ^ 3 * N ^ B * (3 + |T| * N) ≤
      4 * (T ^ (δ / 10)) ^ ((9 + 2 * B) / (δ / 10)) := by
    rw [hq]
    have : 0 ≤ N ^ B := by positivity
    calc N ^ 3 * N ^ B * (3 + |T| * N) ≤ T ^ 6 * T ^ (2 * B) * (4 * T ^ 3) := by
          gcongr
      _ = 4 * (T ^ (9 : ℕ) * T ^ (2 * B)) := by ring
  have hE := Real.exp_pos (-(T ^ (δ / 10)) ^ 2 / 64)
  have hM := hM1 (T ^ (δ / 10)) (Real.one_le_rpow hT (by positivity))
  calc 4 * C * N ^ 3 * N ^ B * (3 + |T| * N) * Real.exp (-(T ^ (δ / 10)) ^ 2 / 64) =
      4 * C * (N ^ 3 * N ^ B * (3 + |T| * N)) * Real.exp (-(T ^ (δ / 10)) ^ 2 / 64) := by ring
    _ ≤ 4 * C * (4 * (T ^ (δ / 10)) ^ ((9 + 2 * B) / (δ / 10))) *
        Real.exp (-(T ^ (δ / 10)) ^ 2 / 64) := by gcongr
    _ = 16 * C * ((T ^ (δ / 10)) ^ ((9 + 2 * B) / (δ / 10)) *
        Real.exp (-(T ^ (δ / 10)) ^ 2 / 64)) := by ring
    _ ≤ 16 * C * M1 := mul_le_mul_of_nonneg_left hM (by positivity)

lemma region2_bound' {η B : ℝ} (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16) (hB : 0 ≤ B)
    (hη1 : η ≤ 1 / 2) (hηδ : η = δ * (5 * B + 8)) :
    (((⌊T ^ (1 + 11 * δ / 5)⌋₊ : ℕ) : ℝ) * T ^ (δ / 10) / T ^ (1 - 21 * δ / 10)) *
      (((⌊T ^ (1 + 11 * δ / 5)⌋₊ : ℕ) : ℝ) * T ^ (δ / 10) / T ^ (1 - 21 * δ / 10)) ^ B *
      (T ^ (1 - 21 * δ / 10) / T ^ (δ / 10)) ^ (-η) *
      ((2 + |T| * T ^ (δ / 10) / T ^ (1 - 21 * δ / 10)) *
        (1 + Real.log ((⌊T ^ (1 + 11 * δ / 5)⌋₊ : ℕ) : ℝ)) + 1) ≤
      4 * (1 + Real.log (T ^ (1 + 11 * δ / 5))) := by
  have hT0 : 0 < T := by linarith
  set X := T ^ (1 + 11 * δ / 5) with hXdef
  set N : ℝ := ((⌊X⌋₊ : ℕ) : ℝ)
  have hX0 : 0 < X := by positivity
  have hX1 : 1 ≤ X := Real.one_le_rpow hT (by linarith)
  have hNX : N ≤ X := Nat.floor_le hX0.le
  have hN1 : (1 : ℝ) ≤ N := by
    have h1 : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hX1)
    have h2 : (1 : ℝ) ≤ ((⌊X⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
    exact h2
  have hY : N * T ^ (δ / 10) / T ^ (1 - 21 * δ / 10) ≤ T ^ (22 * δ / 5) := by
    calc N * T ^ (δ / 10) / T ^ (1 - 21 * δ / 10) ≤ X * T ^ (δ / 10) / T ^ (1 - 21 * δ / 10) := by
          gcongr
      _ = T ^ (22 * δ / 5) := by
        rw [hXdef, ← Real.rpow_add hT0, ← Real.rpow_sub hT0]; ring_nf
  have hY0 : 0 ≤ N * T ^ (δ / 10) / T ^ (1 - 21 * δ / 10) := by positivity
  have hYB : (N * T ^ (δ / 10) / T ^ (1 - 21 * δ / 10)) ^ B ≤ T ^ (22 * δ / 5 * B) := by
    calc (N * T ^ (δ / 10) / T ^ (1 - 21 * δ / 10)) ^ B ≤ (T ^ (22 * δ / 5)) ^ B :=
          Real.rpow_le_rpow hY0 hY hB
      _ = T ^ (22 * δ / 5 * B) := by rw [← Real.rpow_mul hT0.le]
  have hHρ : (T ^ (1 - 21 * δ / 10) / T ^ (δ / 10)) ^ (-η) = T ^ (-(1 - 11 * δ / 5) * η) := by
    rw [← Real.rpow_sub hT0, ← Real.rpow_mul hT0.le]; ring_nf
  have hTρH : |T| * T ^ (δ / 10) / T ^ (1 - 21 * δ / 10) = T ^ (11 * δ / 5) := by
    rw [abs_of_pos hT0, div_eq_iff (by positivity), ← Real.rpow_add hT0,
      show 11 * δ / 5 + (1 - 21 * δ / 10) = 1 + δ / 10 by ring, Real.rpow_add hT0, Real.rpow_one]
  set L := 1 + Real.log X
  have hlogN : 1 + Real.log N ≤ L := by linarith [Real.log_le_log (by linarith) hNX]
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hL1 : 1 ≤ L := by linarith
  have hT6 : 1 ≤ T ^ (11 * δ / 5) := Real.one_le_rpow hT (by positivity)
  have hQ : (2 + |T| * T ^ (δ / 10) / T ^ (1 - 21 * δ / 10)) * (1 + Real.log N) + 1 ≤
      4 * T ^ (11 * δ / 5) * L := by
    rw [hTρH]
    have := mul_le_mul_of_nonneg_left hlogN (show 0 ≤ 2 + T ^ (11 * δ / 5) by positivity)
    nlinarith
  have hexp : T ^ (22 * δ / 5) * T ^ (22 * δ / 5 * B) * T ^ (-(1 - 11 * δ / 5) * η) *
      T ^ (11 * δ / 5) ≤ 1 := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
    refine Real.rpow_le_one_of_one_le_of_nonpos hT ?_
    have key : 22 * δ / 5 + 22 * δ / 5 * B + -(1 - 11 * δ / 5) * η + 11 * δ / 5 =
        δ / 5 * (11 * η - 7 - 3 * B) := by rw [hηδ]; ring
    rw [key]
    have : 11 * η - 7 - 3 * B ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
  rw [hHρ]
  have hQ0 : 0 ≤ (2 + |T| * T ^ (δ / 10) / T ^ (1 - 21 * δ / 10)) * (1 + Real.log N) + 1 := by
    positivity
  calc _ ≤ T ^ (22 * δ / 5) * T ^ (22 * δ / 5 * B) * T ^ (-(1 - 11 * δ / 5) * η) *
        (4 * T ^ (11 * δ / 5) * L) :=
        mul4_le hY0 (by positivity) (by positivity) hQ0 hY hYB le_rfl hQ
    _ = 4 * L * (T ^ (22 * δ / 5) * T ^ (22 * δ / 5 * B) * T ^ (-(1 - 11 * δ / 5) * η) *
          T ^ (11 * δ / 5)) := by ring
    _ ≤ 4 * L * 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 4 * L := mul_one _

end params

set_option maxHeartbeats 4000000 in
/-- **Smoothed Dirichlet polynomial of length `T^{1+11δ/5}` is `≪ T^{1/2−δ}`**, `δ = η/(5B+8)`. -/
theorem rpoly_bound' {η B : ℝ} [hS : ShiftedConvolutionBound η B] (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 2) (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ T : ℝ, 1 ≤ T →
      ‖rpoly (fun n => lam n * gX (T ^ (1 + 11 * subconvexDelta' η B / 5)) n)
        ⌊T ^ (1 + 11 * subconvexDelta' η B / 5)⌋₊ T‖ ≤ c * T ^ (1 / 2 - subconvexDelta' η B) := by
  obtain ⟨C, hC0, hC⟩ := hS.bound
  have hδ0 : 0 < subconvexDelta' η B := subconvexDelta'_pos hη0 hB
  have hδ1 : subconvexDelta' η B ≤ 1 / 16 := by
    rw [subconvexDelta', div_le_iff₀ (by positivity)]; nlinarith
  have hηδ : η = subconvexDelta' η B * (5 * B + 8) := by
    rw [subconvexDelta']; field_simp
  set δ := subconvexDelta' η B with hδdef
  obtain ⟨M1, hM10, hM1⟩ := exp_poly_bound ((9 + 2 * B) / (δ / 10))
  set RS0 := RamanujanTau.MeanSquare.RS (12 + δ / 40)
  have hRS0 : 0 ≤ RS0 := RamanujanTau.MeanSquare.RS_nonneg _
  set cL : ℝ := 1 + 160 / δ with hcL
  have hcL1 : 1 ≤ cL := by
    have : 0 ≤ 160 / δ := by positivity
    linarith
  set cB : ℝ := RS0 + 16 * C * M1 + 16 * C * cL with hcB
  have hcB0 : 0 ≤ cB := by positivity
  set c5 : ℝ := Real.sqrt π * 64 * cL ^ 2 * cB with hc5
  have hc50 : 0 ≤ c5 := by positivity
  refine ⟨Real.sqrt (4 * Real.exp 1 * c5), Real.sqrt_nonneg _, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hdiag := diag_bound' hT hδ0 hδ1
  have hR1 := region1_bound' hT hδ0 hδ1 hB hC0 hM1
  have hR2 := region2_bound' hT hδ0 hδ1 hB hη1 hηδ
  have hρ1 : 1 ≤ T ^ (δ / 10) := Real.one_le_rpow hT (by positivity)
  have hX1 : 1 ≤ T ^ (1 + 11 * δ / 5) := Real.one_le_rpow hT (by linarith)
  have hH1 : 1 ≤ T ^ (1 - 21 * δ / 10) := Real.one_le_rpow hT (by linarith)
  have hρH : T ^ (δ / 10) ≤ T ^ (1 - 21 * δ / 10) := tpow_le hT (by linarith)
  have hHe : T ^ (1 - 21 * δ / 10) * T ^ (δ / 40) * T ^ (δ / 20) =
      T ^ (1 - 21 * δ / 10 + δ / 40 + δ / 20) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
  have hlogX : Real.log (T ^ (1 + 11 * δ / 5)) = (1 + 11 * δ / 5) * Real.log T := Real.log_rpow hT0 _
  set ρ := T ^ (δ / 10) with hρdef
  set X := T ^ (1 + 11 * δ / 5) with hXdef
  set H := T ^ (1 - 21 * δ / 10) with hHdef
  set N := ⌊X⌋₊ with hNdef
  have hX0 : 0 < X := by linarith
  have hH0 : 0 < H := by linarith
  -- logarithms
  set L : ℝ := 1 + Real.log X with hLdef
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hL1 : 1 ≤ L := by rw [hLdef, hlogX]; nlinarith
  have hTd8 : 1 ≤ T ^ (δ / 80) := Real.one_le_rpow hT (by positivity)
  have hL : L ≤ cL * T ^ (δ / 80) := by
    have h1 := Real.log_le_rpow_div hT0.le (show 0 < δ / 80 by positivity)
    have e : T ^ (δ / 80) / (δ / 80) = 80 / δ * T ^ (δ / 80) := by field_simp
    rw [e] at h1
    rw [hLdef, hlogX, hcL]
    have : (1 + 11 * δ / 5) * Real.log T ≤ 2 * Real.log T := by nlinarith
    have h16 : 0 ≤ 160 / δ := by positivity
    have : 2 * (80 / δ * T ^ (δ / 80)) = 160 / δ * T ^ (δ / 80) := by ring
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
  have hη1' : η ≤ 1 := by linarith
  have hMV1 := mean_value_bound (T := T) hη0.le hη1' hB hC0 hρ1 hρH hg1 hA
  have hMV2 := mean_value_bound (T := T) hη0.le hη1' hB hC0 hρ1 hρH hg2 hA
  have hPW := norm_sq_le_window hH1 (fun n => lam n * gX X n) N T
  have e2 : (fun n => (fun n => lam n * gX X n) n * Real.log n) =
      fun n => lam n * (fun n => gX X n * Real.log n) n := by funext n; simp only; ring
  rw [e2] at hPW
  -- the bracket
  set Br : ℝ := ∑ n ∈ Icc 1 N, lam n ^ 2 / n +
        4 * C * (N : ℝ) ^ 3 * (N : ℝ) ^ B * (3 + |T| * N) * Real.exp (-ρ ^ 2 / 64) +
        4 * C * ((N : ℝ) * ρ / H) * ((N : ℝ) * ρ / H) ^ B * (H / ρ) ^ (-η) *
          ((2 + |T| * ρ / H) * (1 + Real.log N) + 1) with hBr
  have hTd2 : 1 ≤ T ^ (δ / 20) := Real.one_le_rpow hT (by positivity)
  have hBr' : Br ≤ cB * T ^ (δ / 20) := by
    have hLT : L ≤ cL * T ^ (δ / 20) :=
      hL.trans (mul_le_mul_of_nonneg_left (tpow_le hT (by linarith)) (by linarith))
    have h4 := mul_le_mul_of_nonneg_left hR2 (show 0 ≤ 4 * C by positivity)
    have h1 : 16 * C * L ≤ 16 * C * cL * T ^ (δ / 20) := by
      have := mul_le_mul_of_nonneg_left hLT (show 0 ≤ 16 * C by positivity); linarith
    have h2 : 16 * C * M1 ≤ 16 * C * M1 * T ^ (δ / 20) := by
      have : 0 ≤ 16 * C * M1 := by positivity
      nlinarith
    rw [hBr, hcB]
    have e4 : 4 * C * ((N : ℝ) * ρ / H) * ((N : ℝ) * ρ / H) ^ B * (H / ρ) ^ (-η) *
        ((2 + |T| * ρ / H) * (1 + Real.log N) + 1) =
        4 * C * (((N : ℝ) * ρ / H) * ((N : ℝ) * ρ / H) ^ B * (H / ρ) ^ (-η) *
        ((2 + |T| * ρ / H) * (1 + Real.log N) + 1)) := by ring
    rw [e4]
    linarith
  have hK'2 : K' ^ 2 ≤ 64 * cL ^ 2 * T ^ (δ / 40) := by
    have h1 : K' ^ 2 ≤ (8 * L) ^ 2 := pow_le_pow_left₀ (by linarith) hK'L 2
    have h2 : L ^ 2 ≤ (cL * T ^ (δ / 80)) ^ 2 := pow_le_pow_left₀ (by linarith) hL 2
    have e : (T ^ (δ / 80)) ^ 2 = T ^ (δ / 40) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; ring_nf
    calc K' ^ 2 ≤ (8 * L) ^ 2 := h1
      _ = 64 * L ^ 2 := by ring
      _ ≤ 64 * (cL * T ^ (δ / 80)) ^ 2 := by linarith
      _ = 64 * cL ^ 2 * (T ^ (δ / 80)) ^ 2 := by ring
      _ = 64 * cL ^ 2 * T ^ (δ / 40) := by rw [e]
  have hBr0 : 0 ≤ Br := by
    rw [hBr]
    have : (1 : ℝ) ≤ N := by
      have h1 : 1 ≤ N := Nat.le_floor (by simpa using hX1)
      exact_mod_cast h1
    have := Real.log_nonneg this
    have : 0 ≤ ∑ n ∈ Icc 1 N, lam n ^ 2 / n := sum_nonneg fun n _ => by positivity
    positivity
  have hM : H * Real.sqrt π * K' ^ 2 * Br ≤ c5 * T ^ (1 - 2 * δ) := by
    have hle : T ^ (1 - 21 * δ / 10 + δ / 40 + δ / 20) ≤ T ^ (1 - 2 * δ) := tpow_le hT (by linarith)
    calc H * Real.sqrt π * K' ^ 2 * Br ≤ H * Real.sqrt π * (64 * cL ^ 2 * T ^ (δ / 40)) *
          (cB * T ^ (δ / 20)) := by gcongr
      _ = c5 * (H * T ^ (δ / 40) * T ^ (δ / 20)) := by rw [hc5]; ring
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
set_option maxHeartbeats 4000000 in
/-- **Sharper conditional subconvexity**: under `SCS(η, B)` with `0 < η ≤ 1/2`, `B ≥ 0`,
`‖L(Δ, 6+it)‖ ≤ C (1+|t|)^{1/2 − η/(5B+8)}`. -/
theorem tauL_subconvex_of_SCS' {η B : ℝ} [ShiftedConvolutionBound η B] (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 2) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖RamanujanTau.HeckeL.tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - subconvexDelta' η B) := by
  have hδ0 : 0 < subconvexDelta' η B := subconvexDelta'_pos hη0 hB
  have hδ1 : subconvexDelta' η B ≤ 1 / 16 := by
    rw [subconvexDelta', div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨c, hc0, hc⟩ := rpoly_bound' (η := η) (B := B) hη0 hη1 hB
  set δ := subconvexDelta' η B with hδdef
  obtain ⟨Ca, hCa0, hCa⟩ := RamanujanTau.MeanSquare.approx_tauL (σ := 6) (δ := 1 / 2)
    (ε := δ / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) (by linarith)
  obtain ⟨C0, hC00, hC0⟩ := RamanujanTau.HeckeConvex.tauL_convexity (ε := 1 / 2) (by norm_num)
  -- the bound for `T ≥ 1`
  have hpos : ∀ T : ℝ, 1 ≤ T →
      ‖RamanujanTau.HeckeL.tauL (6 + T * I)‖ ≤ (c + 4 * Ca) * T ^ (1 / 2 - δ) := by
    intro T hT
    have hT0 : 0 < T := by linarith
    have hX1 : 1 ≤ T ^ (1 + 11 * δ / 5) := Real.one_le_rpow hT (by linarith)
    have h1 := hCa (T ^ (1 + 11 * δ / 5)) hX1 T
    have h2 := hc T hT
    rw [← dpoly_bsm_eq] at h2
    have e6 : ((6 : ℝ) : ℂ) + T * I = 6 + T * I := by push_cast; rfl
    rw [e6] at h1
    have herr : (T ^ (1 + 11 * δ / 5)) ^ (-(1 / 2 : ℝ)) *
        (1 + |T|) ^ (13 / 2 - 6 + 1 / 2 + δ / 10) ≤ 4 * T ^ (1 / 2 - δ) := by
      rw [abs_of_pos hT0, show (13 / 2 - 6 + 1 / 2 + δ / 10 : ℝ) = 1 + δ / 10 by ring]
      have hA : (1 + T) ^ (1 + δ / 10) ≤ 4 * T ^ (1 + δ / 10) := by
        calc (1 + T) ^ (1 + δ / 10) ≤ (2 * T) ^ (1 + δ / 10) :=
              Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
          _ = 2 ^ (1 + δ / 10) * T ^ (1 + δ / 10) := Real.mul_rpow (by norm_num) hT0.le
          _ ≤ 4 * T ^ (1 + δ / 10) := by
              gcongr
              calc (2 : ℝ) ^ (1 + δ / 10) ≤ 2 ^ (2 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                _ = 4 := by norm_num
      have hX : (T ^ (1 + 11 * δ / 5)) ^ (-(1 / 2 : ℝ)) * T ^ (1 + δ / 10) = T ^ (1 / 2 - δ) := by
        rw [← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]; ring_nf
      have hp : 0 ≤ (T ^ (1 + 11 * δ / 5)) ^ (-(1 / 2 : ℝ)) := by positivity
      calc (T ^ (1 + 11 * δ / 5)) ^ (-(1 / 2 : ℝ)) * (1 + T) ^ (1 + δ / 10) ≤
          (T ^ (1 + 11 * δ / 5)) ^ (-(1 / 2 : ℝ)) * (4 * T ^ (1 + δ / 10)) :=
            mul_le_mul_of_nonneg_left hA hp
        _ = 4 * T ^ (1 / 2 - δ) := by rw [← hX]; ring
    have h3 := norm_sub_norm_le (RamanujanTau.HeckeL.tauL (6 + T * I))
      (RamanujanTau.MeanSquare.dpoly (RamanujanTau.MeanSquare.bsm 6 (T ^ (1 + 11 * δ / 5)))
        ⌊T ^ (1 + 11 * δ / 5)⌋₊ T)
    have h4 : Ca * (T ^ (1 + 11 * δ / 5)) ^ (-(1 / 2 : ℝ)) *
        (1 + |T|) ^ (13 / 2 - 6 + 1 / 2 + δ / 10) ≤ Ca * (4 * T ^ (1 / 2 - δ)) := by
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

end RamanujanTau.SCSSharp
