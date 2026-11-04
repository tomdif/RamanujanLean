/-
# `f − b` is polynomially bounded near every root of unity of order `≡ 0 (mod 4)`

`fb_zero_bound`: for `K = 4T`, `(h, K) = 1`, `Re z > 0`, `Re(1/z) ≥ K/2` and `q = e^{2πi(h+iz)/K}`,

  `|f(q) − b(q)| ≤ (864 (1 + C₀) + 4) |z|^{−3/2}`.

Proof. `f − b = −4ψ(−q)` (`watson_disc2`, `bA_eq_bE`). With `Q = −q = e^{2πi(h₀+iz)/K}`, `h₀ = h + 2T` (odd),
`(Q⁴;Q⁴)_∞(ψ(Q)+1) = Σ_{n∈ℤ} (−1)ⁿ Q^{6n²+2n}/(1 − Q^{4n+1})` (`aA_rank`, `rank_disc`, `Ad_bilateral`).
The coefficients `(−1)ⁿ ζ^{6n²+2n}` are anti-periodic of period `T` (`cP_anti`, uses `h₀` odd), the phases of
`ζ^{4n+1}` stay `2π/K` from `1` (`θS_sep`), and `(A, D, T) = (6, 4, K/4)` has threshold `4π/(3K) < 2π/K`.
The Gaussian rate `π Re(1/z)/(12T)` is exactly the growth rate of `F(Q⁴) = F(e^{2πi(h₀+iz)/T})` (`F_bound`).
-/
import RamanujanTau.MockCusp.PsiAL
import RamanujanTau.MockCusp.PhiCusp

set_option autoImplicit false

namespace MockCusp
open Complex Filter Metric Set
open scoped Topology Real

noncomputable section

/-- coefficients `(−1)ⁿ ζ^{6n²+2n}`, `ζ = e^{2πih/K}`. -/
def cP (h K : ℕ) (n : ℤ) : ℂ := (-1) ^ n * cexp (2 * π * I * h * (6 * (n : ℂ) ^ 2 + 2 * n) / K)

/-- the phase of `ζ^{4n+1}`, reduced to be exactly periodic. -/
def θS (h K : ℕ) (n : ℤ) : ℝ := 2 * π * h * (((4 * n + 1) % (K : ℤ) : ℤ) : ℝ) / K

lemma cP_norm (h K : ℕ) (n : ℤ) : ‖cP h K n‖ ≤ 1 := by
  unfold cP
  rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
    show (2 * π * I * h * (6 * (n : ℂ) ^ 2 + 2 * n) / K) =
      ((2 * π * h * (6 * (n : ℝ) ^ 2 + 2 * n) / K : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

lemma cP_anti {h T K : ℕ} (hT : 0 < T) (hKT : K = 4 * T) (hh : Odd h) (n : ℤ) :
    cP h K (n + T) = -cP h K n := by
  obtain ⟨j, rfl⟩ := hh
  subst hKT
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  unfold cP
  have hs : ((-1 : ℂ) ^ (n + (T : ℤ))) = (-1) ^ n * (-1) ^ T := by
    rw [zpow_add₀ (by norm_num), zpow_natCast]
  have he : 2 * π * I * ((2 * j + 1 : ℕ) : ℂ) * (6 * (((n + (T : ℤ)) : ℤ) : ℂ) ^ 2 + 2 * (((n + (T : ℤ)) : ℤ) : ℂ)) /
      ((4 * T : ℕ) : ℂ) = 2 * π * I * ((2 * j + 1 : ℕ) : ℂ) * (6 * (n : ℂ) ^ 2 + 2 * n) / ((4 * T : ℕ) : ℂ) +
      ((3 * n * (2 * j + 1) + j * (3 * T + 1) + T : ℤ) : ℂ) * (2 * π * I) + ((T + 1 : ℕ) : ℂ) * (π * I) := by
    push_cast; field_simp; ring
  set E := cexp (2 * π * I * ((2 * j + 1 : ℕ) : ℂ) * (6 * (n : ℂ) ^ 2 + 2 * n) / ((4 * T : ℕ) : ℂ)) with hE
  rw [hs, he, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_nat_mul,
    Complex.exp_pi_mul_I, ← hE]
  rw [pow_succ]
  have : ((-1 : ℂ)) ^ T * (-1) ^ T = 1 := by rw [← mul_pow]; norm_num
  linear_combination (-(-1 : ℂ) ^ n * E) * this

lemma θS_per {h T K : ℕ} (hKT : K = 4 * T) (n : ℤ) : θS h K (n + T) = θS h K n := by
  subst hKT
  unfold θS
  rw [show (4 * (n + (T : ℤ)) + 1) % ((4 * T : ℕ) : ℤ) = (4 * n + 1) % ((4 * T : ℕ) : ℤ) by
    rw [show 4 * (n + (T : ℤ)) + 1 = 4 * n + 1 + ((4 * T : ℕ) : ℤ) by push_cast; ring, Int.add_emod_right]]

lemma θS_sep {h T K : ℕ} (hT : 0 < T) (hKT : K = 4 * T) (hh : Odd h) (n k : ℤ) :
    2 * π / K ≤ |θS h K n - 2 * π * k| := by
  have hK0 : (0 : ℝ) < K := by rw [hKT]; push_cast; positivity
  set r : ℤ := (4 * n + 1) % (K : ℤ)
  set N : ℤ := h * r - k * K
  have hN : θS h K n - 2 * π * k = 2 * π / K * N := by
    simp only [θS, N, r]; push_cast; field_simp
  have hr : r % 2 = 1 := by
    simp only [r]
    rw [Int.emod_emod_of_dvd _ (by rw [hKT]; push_cast; exact ⟨2 * T, by ring⟩)]
    omega
  have hNo : N ≠ 0 := by
    intro h0
    obtain ⟨j, hj⟩ := hh
    have hjZ : (h : ℤ) = 2 * j + 1 := by exact_mod_cast hj
    have hK2 : (K : ℤ) = 2 * (2 * T) := by rw [hKT]; push_cast; ring
    have hr' : r = 2 * (r / 2) + 1 := by omega
    have : N = 2 * (j * r + (r / 2) - k * (2 * T)) + 1 := by
      simp only [N]; rw [hjZ, hK2]; linear_combination hr'
    omega
  rw [hN, abs_mul, abs_of_pos (by positivity)]
  have : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast Int.one_le_abs hNo
  nlinarith [Real.pi_pos, div_pos (by positivity : (0 : ℝ) < 2 * π) hK0]

lemma alTerm_psi {h K : ℕ} (hK : 0 < K) (z : ℂ) (n : ℤ) :
    alTerm (αK K z) 6 2 4 1 (cP h K) (fun n => cexp (I * θS h K n)) n =
      tmL (cexp (LK h K z)) (4 * LK h K z) n := by
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold alTerm cP αK tmL LK
  have hθ : cexp (I * θS h K n) = cexp (2 * π * I * h * (4 * n + 1) / K) := by
    have hm : (4 * (n : ℂ) + 1) = (((4 * n + 1) % (K : ℤ) : ℤ) : ℂ) + K * (((4 * n + 1) / (K : ℤ) : ℤ) : ℂ) := by
      exact_mod_cast (Int.emod_add_mul_ediv (4 * n + 1) K).symm
    have : I * (θS h K n : ℂ) = 2 * π * I * h * (4 * n + 1) / K +
        (((-((h : ℤ) * ((4 * n + 1) / (K : ℤ)))) : ℤ) : ℂ) * (2 * π * I) := by
      rw [hm]
      unfold θS
      push_cast; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  beta_reduce
  rw [hθ, mul_assoc, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  · congr 2; push_cast; ring_nf; rw [I_sq]; ring
  · congr 2; push_cast; ring_nf; rw [I_sq]; ring

/-- `aA(q) = F(Q⁴) Σ_ℤ (−1)ⁿ Q^{6n²+2n}/(1 − Q^{4n+1})`, `Q = −q = e^{L}`. -/
lemma aA_eq_F {q L : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hL : cexp L = -q)
    (hden : ∀ n : ℤ, 1 - cexp L * cexp (n * (4 * L)) ≠ 0) (hs : Summable (tmL (cexp L) (4 * L))) :
    aA q = HardyRamanujan.F ((-q) ^ 4) * ∑' n, tmL (cexp L) (4 * L) n := by
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hQ4 : cexp (4 * L) = (-q) ^ 4 := by rw [← hL, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have h1 : ‖(-q) ^ 4‖ < ‖-q‖ := by
    rw [norm_pow, norm_neg]
    calc ‖q‖ ^ 4 < ‖q‖ ^ 1 := pow_lt_pow_right_of_lt_one₀ hqn hq (by norm_num)
      _ = ‖q‖ := pow_one _
  have h2 : ‖(-q) ^ 4‖ * ‖-q‖ < 1 := by
    rw [norm_pow, norm_neg, ← pow_succ]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have hR := rank_disc (neg_ne_zero.mpr hq0) h1 h2
  have hQ1 : -q ≠ 1 := by
    intro h0; have := congrArg norm h0; rw [norm_neg, norm_one] at this; linarith
  have hA := Ad_bilateral (z := cexp L) (L := 4 * L) (by rw [hL]; exact neg_ne_zero.mpr hq0) (by rw [hL]; exact hQ1)
    hden hs
  rw [hQ4, hL] at hA
  have hP := aA_rank hq0 hq
  have hq4 : (-q) ^ 4 ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_pow, norm_neg]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have hPn := HardyRamanujan.Pq_ne_zero hq4
  have h1q : (1 : ℂ) + q ≠ 0 := by
    intro h0; apply hQ1; linear_combination -h0
  have : HardyRamanujan.Pq ((-q) ^ 4) * ((1 + q) * aA q) = (1 + q) * ∑' n, tmL (-q) (4 * L) n := by
    rw [hP, hR, hA]; ring
  have h3 : (1 + q) * (HardyRamanujan.Pq ((-q) ^ 4) * aA q - ∑' n, tmL (-q) (4 * L) n) = 0 := by
    linear_combination this
  rw [HardyRamanujan.F, hL, eq_inv_mul_iff_mul_eq₀ hPn]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left h1q)

set_option maxHeartbeats 1000000 in
/-- **`ψ(−q) + 1` near a root of unity of order `K = 4T`.** -/
theorem aA_cusp_bound {T K : ℕ} (hT : 0 < T) (hKT : K = 4 * T) {h : ℕ} (hcop : Nat.Coprime h K) {z : ℂ}
    (hz : 0 < z.re) (hR : (K : ℝ) / 2 ≤ (1 / z).re) :
    ‖aA (Rademacher.qp h K z)‖ ≤ 216 * (1 + HardyRamanujan.C0) * ‖z‖ ^ (-(3 / 2 : ℝ)) := by
  have hK0 : 0 < K := by omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  have hKr4 : (K : ℝ) = 4 * T := by rw [hKT]; push_cast; ring
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK0
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr fun h0 => by rw [h0] at hz; simp at hz
  have hRpos : 0 < (1 / z).re := by linarith
  -- arithmetic of the cusp
  have hh : Odd h := by
    have h2 : Nat.Coprime h 2 := Nat.Coprime.coprime_dvd_right ⟨2 * T, by omega⟩ hcop
    exact Nat.coprime_two_right.mp h2
  set h₀ := h + 2 * T with hh₀
  have hh₀o : Odd h₀ := hh.add_even ⟨T, by ring⟩
  have hcopT : Nat.Coprime h₀ T := by
    rw [hh₀, Nat.coprime_add_mul_right_left]
    exact Nat.Coprime.coprime_dvd_right ⟨4, by omega⟩ hcop
  have hKc : (K : ℂ) = 4 * T := by rw [hKT]; push_cast; ring
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hQ : cexp (LK h₀ K z) = -Rademacher.qp h K z := by
    rw [qp_eq_LK, show LK h₀ K z = LK h K z + π * I by
      unfold LK; simp only [hh₀]; push_cast; rw [hKc]; field_simp; ring, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hQ4 : (-Rademacher.qp h K z) ^ 4 = Rademacher.qp h₀ T z := by
    rw [← hQ, ← Complex.exp_nat_mul, qp_eq_LK]; congr 1; unfold LK; push_cast; rw [hKc]; field_simp
  have hq := Rademacher.qp_mem hK0 hz (h' := h)
  have hq1 : ‖Rademacher.qp h K z‖ < 1 := by simpa using hq
  have hq0 : Rademacher.qp h K z ≠ 0 := by rw [Rademacher.qp]; exact Complex.exp_ne_zero _
  -- geometry of the region
  have hRe : z.re = (1 / z).re * ‖z‖ ^ 2 := by
    rw [one_div, inv_re, Complex.normSq_eq_norm_sq]; field_simp
  have hzle : ‖z‖ ≤ 2 / K := by
    have h1 : (1 / z).re ≤ 1 / ‖z‖ := by
      rw [one_div, inv_re, Complex.normSq_eq_norm_sq]
      rw [div_le_div_iff₀ (by positivity) hzn]
      nlinarith [Complex.re_le_norm z]
    rw [le_div_iff₀ hKr]
    have := hR.trans h1
    rw [le_div_iff₀ hzn] at this; linarith
  have hz2 : ‖z‖ ≤ 2 := hzle.trans (by rw [div_le_iff₀ hKr]; linarith)
  -- the Appell–Lerch sum
  set α := αK K z with hαd
  have hα : 0 < α.re := by
    simp only [α, αK]
    rw [show (2 * π * z / K : ℂ) = ((2 * π / K : ℝ) : ℂ) * z by push_cast; ring, re_ofReal_mul]
    positivity
  have hαR : (1 / α).re = K * (1 / z).re / (2 * π) := by
    simp only [α, αK]
    rw [show 1 / (2 * π * z / K : ℂ) = ((K / (2 * π) : ℝ) : ℂ) * (1 / z) by
      push_cast; field_simp, re_ofReal_mul]; ring
  have hαn : ‖α‖ = 2 * π * ‖z‖ / K := by
    simp only [α, αK]; rw [norm_div, norm_mul, norm_mul]; simp [abs_of_pos Real.pi_pos]
  have hαre : α.re = 2 * π * z.re / K := by
    simp only [α, αK]
    rw [show (2 * π * z / K : ℂ) = ((2 * π / K : ℝ) : ℂ) * z by push_cast; ring, re_ofReal_mul]; ring
  obtain ⟨hs, hb⟩ := al_sum_cusp (B := 2) (E := 1) hα (by norm_num : (0 : ℝ) < 6) (by norm_num : (0 : ℝ) < 4) hT
    (cP_anti hT hKT hh₀o) (cP_norm h₀ K) (θS_per hKT) (θS_sep hT hKT hh₀o) (by
      rw [hKr4, div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [Real.pi_pos])
  -- simplify the constants
  set c0 := π * (1 / z).re / (12 * T) with hc0
  have hc0' : π ^ 2 * (1 / α).re / (4 * 6 * T ^ 2) = c0 := by
    rw [hαR, hc0, hKr4]; field_simp; ring
  have hc0'' : π ^ 2 * (1 / α).re / (2 * 6 * T ^ 2) = 2 * c0 := by
    rw [hαR, hc0, hKr4]; field_simp; ring
  rw [hc0', hc0''] at hb
  have hc0lb : π / 24 ≤ c0 := by
    rw [hc0, le_div_iff₀ (by positivity)]; rw [hKr4] at hR; nlinarith [Real.pi_pos]
  -- (i) the `min` factor
  have hmin : ‖z‖ / 4 ≤ min 1 (‖α‖ * ((1 / α).re * (2 * π / K - π * 4 / (2 * T * 6)))) := by
    refine le_min (by linarith) ?_
    rw [hαn, hαR, hKr4]
    have : 2 * π * ‖z‖ / (4 * T) * (4 * T * (1 / z).re / (2 * π) * (2 * π / (4 * T) - π * 4 / (2 * T * 6))) =
        ‖z‖ * (1 / z).re * (π / (6 * T)) := by field_simp; ring
    rw [this]
    rw [hKr4] at hR
    have h1 : ‖z‖ * (2 * T) * (π / (6 * T)) ≤ ‖z‖ * (1 / z).re * (π / (6 * T)) := by
      gcongr; linarith
    have h2 : ‖z‖ * (2 * T) * (π / (6 * T)) = ‖z‖ * (π / 3) := by field_simp; ring
    nlinarith [Real.pi_gt_three]
  have hm1 : 3 / min 1 (‖α‖ * ((1 / α).re * (2 * π / K - π * 4 / (2 * T * 6)))) ≤ 12 / ‖z‖ := by
    rw [div_le_div_iff₀ (by linarith [hmin, show 0 < ‖z‖ / 4 by positivity]) hzn]; linarith
  -- (ii) the Gaussian factor
  have hg : √(π / (6 * α.re)) ≤ 1 / ‖z‖ := by
    rw [hαre, hRe]
    have : π / (6 * (2 * π * ((1 / z).re * ‖z‖ ^ 2) / K)) = K / (12 * (1 / z).re * ‖z‖ ^ 2) := by
      field_simp; ring
    rw [this, show 1 / ‖z‖ = √(1 / ‖z‖ ^ 2) by rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hzn.le,
      Real.sqrt_one]]
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ‖z‖, mul_pos hzn hzn]
  -- (iii) `e^{4a/24} ≤ 3`
  have he : Real.exp (2 ^ 2 * α.re / (4 * 6)) ≤ 3 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) (Real.exp_one_lt_d9.le.trans (by norm_num))
    rw [hαre]
    have : z.re ≤ 2 := (Complex.re_le_norm z).trans hz2
    rw [div_le_one (by norm_num)]
    have hK4 : (4 : ℝ) ≤ K := by rw [hKr4]; have : (1 : ℝ) ≤ T := by exact_mod_cast hT
                                 linarith
    have h1 : 2 * π * z.re / K ≤ π := by
      rw [div_le_iff₀ hKr]; nlinarith [Real.pi_pos]
    nlinarith [Real.pi_lt_d2]
  -- (iv) `e^{2c₀}/sinh(2c₀) ≤ 6`
  have hsh : Real.exp c0 * Real.exp c0 * (1 / Real.sinh (2 * c0)) ≤ 6 := exp_sq_div_sinh_le hc0lb
  have hsinh : 0 < Real.sinh (2 * c0) :=
    Real.sinh_pos_iff.mpr (by linarith [lt_of_lt_of_le (by positivity : (0:ℝ) < π / 24) hc0lb])
  have hminpos : 0 < min 1 (‖α‖ * ((1 / α).re * (2 * π / K - π * 4 / (2 * T * 6)))) :=
    lt_of_lt_of_le (by positivity) hmin
  have h2 : Real.exp c0 * Real.exp (2 ^ 2 * α.re / (4 * 6)) * √(π / (6 * α.re)) ≤
      3 * Real.exp c0 * (1 / ‖z‖) := by
    calc Real.exp c0 * Real.exp (2 ^ 2 * α.re / (4 * 6)) * √(π / (6 * α.re))
        ≤ Real.exp c0 * 3 * (1 / ‖z‖) := by gcongr
      _ = 3 * Real.exp c0 * (1 / ‖z‖) := by ring
  have hb' : ‖∑' n, alTerm α 6 2 4 1 (cP h₀ K) (fun n => cexp (I * θS h₀ K n)) n‖ ≤
      (12 / ‖z‖) * (3 * Real.exp c0 * (1 / ‖z‖)) * (1 / Real.sinh (2 * c0)) := by
    refine hb.trans ?_
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hm1 h2 (by positivity) (by positivity)) (by positivity)
  -- the identity `aA = F(Q⁴)·Σ`
  have e : alTerm α 6 2 4 1 (cP h₀ K) (fun n => cexp (I * θS h₀ K n)) = tmL (cexp (LK h₀ K z)) (4 * LK h₀ K z) := by
    funext n; exact alTerm_psi hK0 z n
  have hsum : Summable (tmL (cexp (LK h₀ K z)) (4 * LK h₀ K z)) := by rw [← e]; exact hs
  have hden : ∀ n : ℤ, 1 - cexp (LK h₀ K z) * cexp (n * (4 * LK h₀ K z)) ≠ 0 := by
    intro n h0
    rw [← Complex.exp_add, show LK h₀ K z + n * (4 * LK h₀ K z) = (((4 * n + 1 : ℤ) : ℝ) : ℂ) * LK h₀ K z by
      push_cast; ring] at h0
    have h1 : cexp ((((4 * n + 1 : ℤ) : ℝ) : ℂ) * LK h₀ K z) = 1 := by linear_combination -h0
    exact norm_exp_nLK_ne_one hK0 hz (x := ((4 * n + 1 : ℤ) : ℝ)) (by exact_mod_cast (by omega : 4 * n + 1 ≠ 0))
      (by rw [h1, norm_one])
  rw [aA_eq_F hq0 hq1 hQ hden hsum, norm_mul, hQ4, ← e]
  have hFb := F_bound hT hcopT hz (by rw [hKr4] at hR; linarith)
  rw [← hc0] at hFb
  have hC0 := HardyRamanujan.C0_nonneg
  calc ‖HardyRamanujan.F (Rademacher.qp h₀ T z)‖ * ‖∑' n, alTerm α 6 2 4 1 (cP h₀ K) (fun n => cexp (I * θS h₀ K n)) n‖
      ≤ ((1 + HardyRamanujan.C0) * √‖z‖ * Real.exp c0) *
          ((12 / ‖z‖) * (3 * Real.exp c0 * (1 / ‖z‖)) * (1 / Real.sinh (2 * c0))) := by gcongr
    _ = 36 * (1 + HardyRamanujan.C0) * (Real.exp c0 * Real.exp c0 * (1 / Real.sinh (2 * c0))) *
          (√‖z‖ / ‖z‖ ^ 2) := by field_simp; norm_num
    _ ≤ 36 * (1 + HardyRamanujan.C0) * 6 * (√‖z‖ / ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsh (by positivity)) (by positivity)
    _ = 216 * (1 + HardyRamanujan.C0) * ‖z‖ ^ (-(3 / 2 : ℝ)) := by
        rw [sqrt_div_sq hzn]; ring

end

end MockCusp
