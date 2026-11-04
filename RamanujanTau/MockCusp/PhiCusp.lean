/-
# Watson's `φ(q)` is polynomially bounded near every odd-order root of unity

`phi_odd_bound`: for odd `K`, `(h, K) = 1`, `Re z > 0`, `Re(1/z) ≥ K/2` and `q = e^{2πi(h+iz)/K}`,

  `|φ(q)| ≤ 432 (1 + C₀) |z|^{−3/2}`,   `φ(q) = Σ q^{n²}/(−q²;q²)_n = R(i;q)`.

Proof: `(q;q)_∞ φ(q) = (1−i) Σ_{n∈ℤ} (−1)ⁿ q^{n(3n+1)/2}/(1 − i qⁿ)` (`rank_disc` at `z = i`, `Ad_bilateral`).
The coefficients are those of `f` (anti-periodic of period `K`, `cK_anti`), and the phases of `i ζⁿ` stay
`π/(2K)` away from `1` (`θP_sep`), which beats the threshold `π/(3K)` of `al_sum_cusp`.
-/
import RamanujanTau.MockCusp.Bilateral

set_option autoImplicit false

namespace MockCusp
open Complex Filter Metric Set
open scoped Topology Real

noncomputable section

/-- the phase of `i ζⁿ`, reduced to be exactly `K`-periodic. -/
def θP (h K : ℕ) (n : ℤ) : ℝ := π / 2 + 2 * π * h * ((n % (K : ℤ) : ℤ) : ℝ) / K

lemma θP_per (h K : ℕ) (n : ℤ) : θP h K (n + K) = θP h K n := by simp [θP]

lemma θP_sep {h K : ℕ} (hK : Odd K) (n k : ℤ) : π / (2 * K) ≤ |θP h K n - 2 * π * k| := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK.pos
  set N : ℤ := K + 4 * h * (n % (K : ℤ)) - 4 * k * K
  have hN : θP h K n - 2 * π * k = π / (2 * K) * N := by
    simp only [θP, N]; push_cast; field_simp; ring
  have hNo : N ≠ 0 := by
    intro h0
    have : Odd N := by
      obtain ⟨j, hj⟩ := hK
      have hjZ : (K : ℤ) = 2 * j + 1 := by exact_mod_cast hj
      refine ⟨2 * h * (n % (K : ℤ)) - 2 * k * K + j, ?_⟩
      simp only [N]; linear_combination hjZ
    rw [h0] at this; exact (Int.not_odd_iff_even.mpr ⟨0, rfl⟩) this
  rw [hN, abs_mul, abs_of_pos (by positivity)]
  have : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast Int.one_le_abs hNo
  nlinarith [Real.pi_pos, div_pos Real.pi_pos (by positivity : (0 : ℝ) < 2 * K)]

/-- `L = 2πi(h+iz)/K`, so `q = e^L`. -/
def LK (h K : ℕ) (z : ℂ) : ℂ := 2 * π * I * ((h + I * z) / K)

lemma qp_eq_LK (h K : ℕ) (z : ℂ) : Rademacher.qp h K z = cexp (LK h K z) := by
  rw [Rademacher.qp, LK]; push_cast; rfl

lemma alTerm_phi {h K : ℕ} (hK : 0 < K) (z : ℂ) (n : ℤ) :
    alTerm (αK K z) (3 / 2) (1 / 2) 1 0 (cK h K) (fun n => cexp (I * θP h K n)) n = tmL I (LK h K z) n := by
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold alTerm cK αK tmL LK
  have hθ : cexp (I * θP h K n) = I * cexp (2 * π * I * h * n / K) := by
    have hm : (n : ℂ) = ((n % (K : ℤ) : ℤ) : ℂ) + K * ((n / (K : ℤ) : ℤ) : ℂ) := by
      exact_mod_cast (Int.emod_add_mul_ediv n K).symm
    have : I * (θP h K n : ℂ) = 2 * π * I * h * n / K + π / 2 * I +
        (((-((h : ℤ) * (n / (K : ℤ)))) : ℤ) : ℂ) * (2 * π * I) := by
      rw [hm]
      unfold θP
      push_cast; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
      Complex.exp_pi_div_two_mul_I]; ring
  beta_reduce
  rw [hθ, mul_assoc, ← Complex.exp_add]
  congr 1
  · congr 1; push_cast; ring_nf; rw [I_sq]; ring
  · rw [mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring_nf; rw [I_sq]; ring

lemma re_nLK {h K : ℕ} (hK : 0 < K) (z : ℂ) (x : ℝ) : ((x : ℂ) * LK h K z).re = -(2 * π * x * z.re / K) := by
  unfold LK
  rw [show (x : ℂ) * (2 * π * I * ((h + I * z) / K)) = ((2 * π * x / K : ℝ) : ℂ) * (I * h - z) by
    push_cast; field_simp; ring_nf; rw [I_sq]; ring, re_ofReal_mul]
  simp; ring

lemma norm_exp_nLK_ne_one {h K : ℕ} (hK : 0 < K) {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : x ≠ 0) :
    ‖cexp ((x : ℂ) * LK h K z)‖ ≠ 1 := by
  rw [Complex.norm_exp, re_nLK hK, Ne, Real.exp_eq_one_iff]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  intro h0
  have : x * (2 * π * z.re / K) = 0 := by rw [← neg_eq_zero, ← h0]; ring
  rcases mul_eq_zero.mp this with h1 | h1
  · exact hx h1
  · have : 0 < 2 * π * z.re / K := by positivity
    linarith

lemma den_phi {h K : ℕ} (hK : 0 < K) {z : ℂ} (hz : 0 < z.re) (n : ℤ) :
    1 - I * cexp (n * LK h K z) ≠ 0 := by
  intro h0
  have h1 : I * cexp (n * LK h K z) = 1 := by linear_combination -h0
  by_cases hn : n = 0
  · subst hn; simp at h1; exact absurd h1 (by simp [Complex.ext_iff])
  · have := congrArg norm h1
    rw [norm_mul, Complex.norm_I, one_mul, norm_one] at this
    exact norm_exp_nLK_ne_one hK hz (x := n) (by exact_mod_cast hn) (by exact_mod_cast this)

/-- `gA(q) = φ(−q) = R(i;−q)`. -/
lemma gA_eq_Rd (q : ℂ) : MockTheta3.Radial.gA q = Rd I (-q) := by
  rw [MockTheta3.Radial.gA_eq, Rd]
  congr 1; funext n
  rw [rT, pc, pc, mul_assoc, ← mul_inv, ← Finset.prod_mul_distrib, div_eq_mul_inv]
  congr 1
  · rw [neg_pow, ← (Nat.even_mul_pred_self n).neg_one_pow, show n ^ 2 = n + n * (n - 1) by
      rcases n with _ | n <;> simp; ring]
    rw [pow_add, pow_add]; ring_nf
    simp [(Nat.even_mul_pred_self n).neg_one_pow]
  · congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [inv_I]
    ring_nf
    rw [show ((-1 : ℂ)) ^ (i * 2) = 1 from Even.neg_one_pow ⟨i, by ring⟩]
    ring_nf; rw [I_sq]; ring

set_option maxHeartbeats 1000000 in
/-- **`φ` near an odd-order root of unity**. -/
theorem phi_odd_bound {K : ℕ} (hK : Odd K) {h : ℕ} (hcop : Nat.Coprime h K) {z : ℂ} (hz : 0 < z.re)
    (hR : (K : ℝ) / 2 ≤ (1 / z).re) :
    ‖Rd I (Rademacher.qp h K z)‖ ≤ 432 * (1 + HardyRamanujan.C0) * ‖z‖ ^ (-(3 / 2 : ℝ)) := by
  have hK0 : 0 < K := hK.pos
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK0
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr fun h0 => by rw [h0] at hz; simp at hz
  have hRpos : 0 < (1 / z).re := by linarith
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
  obtain ⟨hs, hb⟩ := al_sum_cusp (B := 1 / 2) (E := 0) hα (by norm_num : (0 : ℝ) < 3 / 2) one_pos hK0 (cK_anti hK)
    (cK_norm h K) (θP_per h K) (θP_sep hK) (by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [Real.pi_pos])
  -- simplify the constants
  set c0 := π * (1 / z).re / (12 * K) with hc0
  have hc0' : π ^ 2 * (1 / α).re / (4 * (3 / 2) * K ^ 2) = c0 := by
    rw [hαR, hc0]; field_simp; ring_nf
  have hc0'' : π ^ 2 * (1 / α).re / (2 * (3 / 2) * K ^ 2) = 2 * c0 := by
    rw [hαR, hc0]; field_simp; ring_nf
  rw [hc0', hc0''] at hb
  have hc0lb : π / 24 ≤ c0 := by
    rw [hc0, le_div_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
  -- (i) the `min` factor
  have hmin : ‖z‖ / 4 ≤ min 1 (‖α‖ * ((1 / α).re * (π / (2 * K) - π * 1 / (2 * K * (3 / 2))))) := by
    refine le_min (by linarith) ?_
    rw [hαn, hαR]
    have : 2 * π * ‖z‖ / K * (K * (1 / z).re / (2 * π) * (π / (2 * K) - π * 1 / (2 * K * (3 / 2)))) =
        ‖z‖ * (1 / z).re * (π / (6 * K)) := by field_simp; ring
    rw [this]
    have h1 : ‖z‖ * (K / 2) * (π / (6 * K)) ≤ ‖z‖ * (1 / z).re * (π / (6 * K)) := by gcongr
    have h2 : ‖z‖ * (K / 2) * (π / (6 * K)) = ‖z‖ * (π / 12) := by field_simp; ring
    nlinarith [Real.pi_gt_three]
  have hm1 : 3 / min 1 (‖α‖ * ((1 / α).re * (π / (2 * K) - π * 1 / (2 * K * (3 / 2))))) ≤ 12 / ‖z‖ := by
    rw [div_le_div_iff₀ (by linarith [hmin, show 0 < ‖z‖ / 4 by positivity]) hzn]; linarith
  -- (ii) the Gaussian factor
  have hg : √(π / (3 / 2 * α.re)) ≤ 1 / ‖z‖ := by
    rw [hαre, hRe]
    have : π / (3 / 2 * (2 * π * ((1 / z).re * ‖z‖ ^ 2) / K)) = K / (3 * (1 / z).re * ‖z‖ ^ 2) := by
      field_simp
    rw [this, show 1 / ‖z‖ = √(1 / ‖z‖ ^ 2) by rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hzn.le,
      Real.sqrt_one]]
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ‖z‖, mul_pos hzn hzn]
  -- (iii) `e^{a/24} ≤ 3`
  have he : Real.exp ((1 / 2) ^ 2 * α.re / (4 * (3 / 2))) ≤ 3 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) (Real.exp_one_lt_d9.le.trans (by norm_num))
    rw [hαre]
    have : z.re ≤ 2 := (Complex.re_le_norm z).trans hz2
    rw [div_le_one (by norm_num)]
    have h1 : 2 * π * z.re / K ≤ 2 * π * 2 := by
      rw [div_le_iff₀ hKr]; nlinarith [Real.pi_pos]
    nlinarith [Real.pi_lt_d2]
  -- (iv) `e^{2c₀}/sinh(2c₀) ≤ 6`
  have hsh : Real.exp c0 * Real.exp c0 * (1 / Real.sinh (2 * c0)) ≤ 6 := exp_sq_div_sinh_le hc0lb
  -- assemble `|G(q)|`
  have hsinh : 0 < Real.sinh (2 * c0) :=
    Real.sinh_pos_iff.mpr (by linarith [lt_of_lt_of_le (by positivity : (0:ℝ) < π / 24) hc0lb])
  have hminpos : 0 < min 1 (‖α‖ * ((1 / α).re * (π / (2 * K) - π * 1 / (2 * K * (3 / 2))))) :=
    lt_of_lt_of_le (by positivity) hmin
  have h2 : Real.exp c0 * Real.exp ((1 / 2) ^ 2 * α.re / (4 * (3 / 2))) * √(π / (3 / 2 * α.re)) ≤
      3 * Real.exp c0 * (1 / ‖z‖) := by
    calc Real.exp c0 * Real.exp ((1 / 2) ^ 2 * α.re / (4 * (3 / 2))) * √(π / (3 / 2 * α.re))
        ≤ Real.exp c0 * 3 * (1 / ‖z‖) := by gcongr
      _ = 3 * Real.exp c0 * (1 / ‖z‖) := by ring
  have hb' : ‖∑' n, alTerm α (3 / 2) (1 / 2) 1 0 (cK h K) (fun n => cexp (I * θP h K n)) n‖ ≤
      (12 / ‖z‖) * (3 * Real.exp c0 * (1 / ‖z‖)) * (1 / Real.sinh (2 * c0)) := by
    refine hb.trans ?_
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hm1 h2 (by positivity) (by positivity)) (by positivity)
  have hsum : Summable (tmL I (LK h K z)) := by
    have e : alTerm α (3 / 2) (1 / 2) 1 0 (cK h K) (fun n => cexp (I * θP h K n)) = tmL I (LK h K z) := by
      funext n; exact alTerm_phi hK0 z n
    rw [← e]; exact hs
  have hG : ‖Ad I (Rademacher.qp h K z)‖ ≤ 2 * ((12 / ‖z‖) * (3 * Real.exp c0 * (1 / ‖z‖)) *
      (1 / Real.sinh (2 * c0))) := by
    rw [qp_eq_LK, Ad_bilateral I_ne_zero (by simp [Complex.ext_iff]) (den_phi hK0 hz) hsum, norm_mul]
    have e : ∑' n, tmL I (LK h K z) n = ∑' n, alTerm α (3 / 2) (1 / 2) 1 0 (cK h K)
        (fun n => cexp (I * θP h K n)) n := tsum_congr fun n => (alTerm_phi hK0 z n).symm
    rw [e]
    have h1I : ‖(1 : ℂ) - I‖ ≤ 2 := (norm_sub_le _ _).trans (by simp; norm_num)
    exact mul_le_mul h1I hb' (norm_nonneg _) (by norm_num)
  -- `φ = F·Ad`
  have hq : Rademacher.qp h K z ∈ ball (0 : ℂ) 1 := Rademacher.qp_mem hK0 hz
  have hq1 : ‖Rademacher.qp h K z‖ < 1 := by simpa using hq
  have hfa : Rd I (Rademacher.qp h K z) =
      Ad I (Rademacher.qp h K z) * HardyRamanujan.F (Rademacher.qp h K z) := by
    rw [← rank_disc I_ne_zero (by simpa using hq1) (by simpa using hq1), HardyRamanujan.F, mul_comm,
      ← mul_assoc, inv_mul_cancel₀ (HardyRamanujan.Pq_ne_zero hq), one_mul]
  rw [hfa, norm_mul]
  have hFb := F_bound hK0 hcop hz hR
  rw [← hc0] at hFb
  have hC0 := HardyRamanujan.C0_nonneg
  calc ‖Ad I (Rademacher.qp h K z)‖ * ‖HardyRamanujan.F (Rademacher.qp h K z)‖
      ≤ (2 * ((12 / ‖z‖) * (3 * Real.exp c0 * (1 / ‖z‖)) * (1 / Real.sinh (2 * c0)))) *
          ((1 + HardyRamanujan.C0) * √‖z‖ * Real.exp c0) := by gcongr
    _ = 72 * (1 + HardyRamanujan.C0) * (Real.exp c0 * Real.exp c0 * (1 / Real.sinh (2 * c0))) *
          (√‖z‖ / ‖z‖ ^ 2) := by field_simp; norm_num
    _ ≤ 72 * (1 + HardyRamanujan.C0) * 6 * (√‖z‖ / ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsh (by positivity)) (by positivity)
    _ = 432 * (1 + HardyRamanujan.C0) * ‖z‖ ^ (-(3 / 2 : ℝ)) := by
        rw [sqrt_div_sq hzn]; ring

end

end MockCusp
