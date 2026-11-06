/-
# Assembly: `SCS(η,B)` ⇒ `|∑_{n ≤ X} λ(n) g_X(n) n^{−iT}| ≪ T^{1/2−δ}`, `δ = η/(10B+24)`

Parameters (`T ≥ 1`, `δ = subconvexDelta η B`):
`ρ = T^{2δ}`, `X = T^{1+4δ}`, `H = T^{1−4δ}`, `N = ⌊X⌋₊`.
Then `ρ ≤ H`, `Nρ/H ≤ T^{10δ}`, `Tρ/H = T^{6δ}`, `(H/ρ)^{−η} = T^{−(1−6δ)η}` and, since
`η = 2δ(5B+12)`, the off-diagonal is `O(log T)`; the diagonal is `O(T^{δ/2})`.  With
`norm_sq_le_window` this gives `|P(T)|² ≪ H T^{3δ/4} ≤ T^{1−2δ}` (`rpoly_bound`).
-/
import RamanujanTau.SubconvexityCond.MeanValue
import RamanujanTau.SubconvexityCond.Pointwise
import RamanujanTau.SubconvexityCond.Coeff

set_option autoImplicit false

namespace RamanujanTau.SubconvexityCond

open Real Finset

/-- `ρ^q e^{−ρ²/64}` is bounded on `ρ ≥ 1`. -/
lemma exp_poly_bound (q : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ ρ : ℝ, 1 ≤ ρ →
    ρ ^ q * Real.exp (-ρ ^ 2 / 64) ≤ M := by
  set m : ℕ := ⌈q⌉₊
  refine ⟨64 ^ m * m.factorial, by positivity, fun ρ hρ => ?_⟩
  have hρ0 : 0 < ρ := by linarith
  have h1 : ρ ^ q ≤ (ρ ^ 2) ^ m := by
    calc ρ ^ q ≤ ρ ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hρ (Nat.le_ceil q)
      _ = ρ ^ m := Real.rpow_natCast ρ m
      _ ≤ (ρ ^ 2) ^ m := pow_le_pow_left₀ hρ0.le (by nlinarith) m
  have h2 := Real.pow_div_factorial_le_exp (x := ρ ^ 2 / 64) (by positivity) m
  rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h2
  have he : Real.exp (-ρ ^ 2 / 64) * Real.exp (ρ ^ 2 / 64) = 1 := by
    rw [← Real.exp_add, show -ρ ^ 2 / 64 + ρ ^ 2 / 64 = 0 by ring, Real.exp_zero]
  have hE := Real.exp_pos (-ρ ^ 2 / 64)
  calc ρ ^ q * Real.exp (-ρ ^ 2 / 64) ≤ (ρ ^ 2) ^ m * Real.exp (-ρ ^ 2 / 64) :=
        mul_le_mul_of_nonneg_right h1 hE.le
    _ ≤ (Real.exp (ρ ^ 2 / 64) * (64 ^ m * m.factorial)) * Real.exp (-ρ ^ 2 / 64) :=
        mul_le_mul_of_nonneg_right h2 hE.le
    _ = 64 ^ m * m.factorial * (Real.exp (-ρ ^ 2 / 64) * Real.exp (ρ ^ 2 / 64)) := by ring
    _ = 64 ^ m * m.factorial := by rw [he, mul_one]

lemma tpow_le {T a b : ℝ} (hT : 1 ≤ T) (h : a ≤ b) : T ^ a ≤ T ^ b :=
  Real.rpow_le_rpow_of_exponent_le hT h

lemma lam_sq_div (n : ℕ) : lam n ^ 2 / n = ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(12 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lam, tau_zero]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [lam_sq, Real.rpow_neg hn0.le, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  field_simp


section params
variable {T δ : ℝ}

lemma diag_bound (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 24) :
    ∑ n ∈ Icc 1 ⌊T ^ (1 + 4 * δ)⌋₊, lam n ^ 2 / n ≤
      RamanujanTau.MeanSquare.RS (12 + δ / 4) * T ^ (δ / 2) := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < T ^ (1 + 4 * δ) := by positivity
  simp_rw [lam_sq_div]
  have h := RamanujanTau.MeanSquare.sum_tau_sq_rpow_le (β := 12 + δ / 4) (γ := 12)
    (by linarith) (by linarith) ⌊T ^ (1 + 4 * δ)⌋₊
  rw [show 12 + δ / 4 - 12 = δ / 4 by ring] at h
  refine h.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (RamanujanTau.MeanSquare.RS_nonneg _)
  calc ((⌊T ^ (1 + 4 * δ)⌋₊ : ℕ) : ℝ) ^ (δ / 4) ≤ (T ^ (1 + 4 * δ)) ^ (δ / 4) :=
        Real.rpow_le_rpow (by positivity) (Nat.floor_le hX0.le) (by positivity)
    _ = T ^ ((1 + 4 * δ) * (δ / 4)) := by rw [← Real.rpow_mul hT0.le]
    _ ≤ T ^ (δ / 2) := tpow_le hT (by nlinarith)

lemma region1_bound {B C M1 : ℝ} (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 24) (hB : 0 ≤ B)
    (hC0 : 0 ≤ C) (hM1 : ∀ ρ : ℝ, 1 ≤ ρ →
      ρ ^ ((9 + 2 * B) / (2 * δ)) * Real.exp (-ρ ^ 2 / 64) ≤ M1) :
    4 * C * ((⌊T ^ (1 + 4 * δ)⌋₊ : ℕ) : ℝ) ^ 3 * ((⌊T ^ (1 + 4 * δ)⌋₊ : ℕ) : ℝ) ^ B *
      (3 + |T| * ((⌊T ^ (1 + 4 * δ)⌋₊ : ℕ) : ℝ)) * Real.exp (-(T ^ (2 * δ)) ^ 2 / 64) ≤
      16 * C * M1 := by
  have hT0 : 0 < T := by linarith
  set N : ℝ := ((⌊T ^ (1 + 4 * δ)⌋₊ : ℕ) : ℝ)
  have hX0 : 0 < T ^ (1 + 4 * δ) := by positivity
  have hXT : T ^ (1 + 4 * δ) ≤ T ^ 2 := by
    rw [← Real.rpow_natCast]; exact tpow_le hT (by push_cast; linarith)
  have hNT : N ≤ T ^ 2 := (Nat.floor_le hX0.le).trans hXT
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hq : (T ^ (2 * δ)) ^ ((9 + 2 * B) / (2 * δ)) = T ^ (9 : ℕ) * T ^ (2 * B) := by
    rw [← Real.rpow_mul hT0.le, show 2 * δ * ((9 + 2 * B) / (2 * δ)) = ((9 : ℕ) : ℝ) + 2 * B by
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
      4 * (T ^ (2 * δ)) ^ ((9 + 2 * B) / (2 * δ)) := by
    rw [hq]
    have : 0 ≤ N ^ B := by positivity
    calc N ^ 3 * N ^ B * (3 + |T| * N) ≤ T ^ 6 * T ^ (2 * B) * (4 * T ^ 3) := by
          gcongr
      _ = 4 * (T ^ (9 : ℕ) * T ^ (2 * B)) := by ring
  have hE := Real.exp_pos (-(T ^ (2 * δ)) ^ 2 / 64)
  have hM := hM1 (T ^ (2 * δ)) (Real.one_le_rpow hT (by positivity))
  calc 4 * C * N ^ 3 * N ^ B * (3 + |T| * N) * Real.exp (-(T ^ (2 * δ)) ^ 2 / 64) =
      4 * C * (N ^ 3 * N ^ B * (3 + |T| * N)) * Real.exp (-(T ^ (2 * δ)) ^ 2 / 64) := by ring
    _ ≤ 4 * C * (4 * (T ^ (2 * δ)) ^ ((9 + 2 * B) / (2 * δ))) *
        Real.exp (-(T ^ (2 * δ)) ^ 2 / 64) := by gcongr
    _ = 16 * C * ((T ^ (2 * δ)) ^ ((9 + 2 * B) / (2 * δ)) *
        Real.exp (-(T ^ (2 * δ)) ^ 2 / 64)) := by ring
    _ ≤ 16 * C * M1 := mul_le_mul_of_nonneg_left hM (by positivity)

lemma mul4_le {a b c d a' b' c' d' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c') (h4 : d ≤ d') :
    a * b * c * d ≤ a' * b' * c' * d' := by
  have := mul_le_mul h1 h2 hb (ha.trans h1)
  have := mul_le_mul this h3 hc (mul_nonneg (ha.trans h1) (hb.trans h2))
  exact mul_le_mul this h4 hd (mul_nonneg (mul_nonneg (ha.trans h1) (hb.trans h2)) (hc.trans h3))

lemma region2_bound {η B : ℝ} (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 24) (hB : 0 ≤ B)
    (hη1 : η ≤ 1) (hηδ : η = 2 * δ * (5 * B + 12)) :
    (((⌊T ^ (1 + 4 * δ)⌋₊ : ℕ) : ℝ) * T ^ (2 * δ) / T ^ (1 - 4 * δ)) *
      (((⌊T ^ (1 + 4 * δ)⌋₊ : ℕ) : ℝ) * T ^ (2 * δ) / T ^ (1 - 4 * δ)) ^ B *
      (T ^ (1 - 4 * δ) / T ^ (2 * δ)) ^ (-η) *
      ((2 + |T| * T ^ (2 * δ) / T ^ (1 - 4 * δ)) *
        (1 + Real.log ((⌊T ^ (1 + 4 * δ)⌋₊ : ℕ) : ℝ)) + 1) ≤
      4 * (1 + Real.log (T ^ (1 + 4 * δ))) := by
  have hT0 : 0 < T := by linarith
  set X := T ^ (1 + 4 * δ) with hXdef
  set N : ℝ := ((⌊X⌋₊ : ℕ) : ℝ)
  have hX0 : 0 < X := by positivity
  have hX1 : 1 ≤ X := Real.one_le_rpow hT (by linarith)
  have hNX : N ≤ X := Nat.floor_le hX0.le
  have hN1 : (1 : ℝ) ≤ N := by
    have h1 : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hX1)
    have h2 : (1 : ℝ) ≤ ((⌊X⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
    exact h2
  have hY : N * T ^ (2 * δ) / T ^ (1 - 4 * δ) ≤ T ^ (10 * δ) := by
    calc N * T ^ (2 * δ) / T ^ (1 - 4 * δ) ≤ X * T ^ (2 * δ) / T ^ (1 - 4 * δ) := by gcongr
      _ = T ^ (10 * δ) := by
        rw [hXdef, ← Real.rpow_add hT0, ← Real.rpow_sub hT0]; ring_nf
  have hY0 : 0 ≤ N * T ^ (2 * δ) / T ^ (1 - 4 * δ) := by positivity
  have hYB : (N * T ^ (2 * δ) / T ^ (1 - 4 * δ)) ^ B ≤ T ^ (10 * δ * B) := by
    calc (N * T ^ (2 * δ) / T ^ (1 - 4 * δ)) ^ B ≤ (T ^ (10 * δ)) ^ B :=
          Real.rpow_le_rpow hY0 hY hB
      _ = T ^ (10 * δ * B) := by rw [← Real.rpow_mul hT0.le]
  have hHρ : (T ^ (1 - 4 * δ) / T ^ (2 * δ)) ^ (-η) = T ^ (-(1 - 6 * δ) * η) := by
    rw [← Real.rpow_sub hT0, ← Real.rpow_mul hT0.le]; ring_nf
  have hTρH : |T| * T ^ (2 * δ) / T ^ (1 - 4 * δ) = T ^ (6 * δ) := by
    rw [abs_of_pos hT0, div_eq_iff (by positivity), ← Real.rpow_add hT0,
      show 6 * δ + (1 - 4 * δ) = 1 + 2 * δ by ring, Real.rpow_add hT0, Real.rpow_one]
  set L := 1 + Real.log X
  have hlogN : 1 + Real.log N ≤ L := by linarith [Real.log_le_log (by linarith) hNX]
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hL1 : 1 ≤ L := by linarith
  have hT6 : 1 ≤ T ^ (6 * δ) := Real.one_le_rpow hT (by positivity)
  have hQ : (2 + |T| * T ^ (2 * δ) / T ^ (1 - 4 * δ)) * (1 + Real.log N) + 1 ≤
      4 * T ^ (6 * δ) * L := by
    rw [hTρH]
    have := mul_le_mul_of_nonneg_left hlogN (show 0 ≤ 2 + T ^ (6 * δ) by positivity)
    nlinarith
  have hexp : T ^ (10 * δ) * T ^ (10 * δ * B) * T ^ (-(1 - 6 * δ) * η) * T ^ (6 * δ) ≤ 1 := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
    refine Real.rpow_le_one_of_one_le_of_nonpos hT ?_
    rw [hηδ]
    have : 2 * δ * (5 * B + 12) ≤ 1 := hηδ ▸ hη1
    nlinarith
  rw [hHρ]
  have hQ0 : 0 ≤ (2 + |T| * T ^ (2 * δ) / T ^ (1 - 4 * δ)) * (1 + Real.log N) + 1 := by
    positivity
  calc _ ≤ T ^ (10 * δ) * T ^ (10 * δ * B) * T ^ (-(1 - 6 * δ) * η) * (4 * T ^ (6 * δ) * L) :=
        mul4_le hY0 (by positivity) (by positivity) hQ0 hY hYB le_rfl hQ
    _ = 4 * L * (T ^ (10 * δ) * T ^ (10 * δ * B) * T ^ (-(1 - 6 * δ) * η) * T ^ (6 * δ)) := by
        ring
    _ ≤ 4 * L * 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 4 * L := mul_one _

end params
