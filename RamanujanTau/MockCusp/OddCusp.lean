/-
# `f(q)` is polynomially bounded near every odd-order root of unity

`f_odd_bound`: for odd `K`, `(h, K) = 1`, `Re z > 0`, `Re(1/z) ≥ K/2` and `q = e^{2πi(h+iz)/K}`,

  `|f(q)| ≤ 216 (1 + C₀) |z|^{−3/2}`.

Proof. `f(q) = G(q)/(q;q)_∞` (`f_AL`), and `G(q) = 2 Σ_{n∈ℤ} (−1)ⁿ q^{n(3n+1)/2}/(1+qⁿ)` is an anti-periodic
Appell–Lerch sum of period `K` (`cK_anti`; this uses `K` odd), with no denominator vanishing at the root of
unity (`θK_sep`: the phases of `−ζⁿ` stay `π/K` away from `1`). `al_sum_cusp` gives
`|G(q)| ≪ |z|^{−2} e^{−π Re(1/z)/(12K)}`, and the transformation of the partition function
(`Rademacher.F_transform`) gives `|1/(q;q)_∞| ≪ |z|^{1/2} e^{π Re(1/z)/(12K)}` (`F_bound`).
-/
import RamanujanTau.MockCusp.GenCusp
import RamanujanTau.MockCusp.FAL
import RamanujanTau.Andrews66.Arc

set_option autoImplicit false

namespace MockCusp
open Complex Filter Metric Set
open scoped Topology Real

noncomputable section

/-! ### the partition function at a cusp -/

lemma exists_inv_mod {h K : ℕ} (hcop : Nat.Coprime h K) : ∃ h' : ℤ, (K : ℤ) ∣ (h : ℤ) * h' + 1 := by
  have hc : IsCoprime (h : ℤ) (K : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨u, v, huv⟩ := hc
  exact ⟨-u, ⟨v, by linear_combination -huv⟩⟩

lemma exp_neg_pi_le : Real.exp (-π) ≤ 1 / 2 := by
  rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  have := Real.add_one_le_exp π
  linarith [Real.pi_gt_three]

/-- **`1/(q;q)_∞` at a cusp**: `|F(e^{2πi(h+iz)/K})| ≤ (1+C₀)|z|^{1/2} e^{π Re(1/z)/(12K)}`. -/
theorem F_bound {K : ℕ} (hK : 0 < K) {h : ℕ} (hcop : Nat.Coprime h K) {z : ℂ} (hz : 0 < z.re)
    (hR : (K : ℝ) / 2 ≤ (1 / z).re) :
    ‖HardyRamanujan.F (Rademacher.qp h K z)‖ ≤
      (1 + HardyRamanujan.C0) * √‖z‖ * Real.exp (π * (1 / z).re / (12 * K)) := by
  obtain ⟨h', hd⟩ := exists_inv_mod hcop
  have hKz : (0 : ℤ) < (K : ℤ) := by exact_mod_cast hK
  obtain ⟨ω, hω, H⟩ := Rademacher.F_transform (h := (h : ℤ)) hKz hd
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have e1 := H z hz
  simp only [Int.cast_natCast] at e1
  have hq : Rademacher.qp h K z = cexp (2 * π * I * (((h : ℤ) : ℂ) + I * z) / K) := by
    rw [Rademacher.qp]; push_cast; ring_nf
  have hq' : cexp (2 * π * I * ((h' + I / z) / K)) = Rademacher.qp h' K (1 / z) := by
    rw [Rademacher.qp]; ring_nf
  rw [show Rademacher.qp h K z = cexp (2 * π * I * (((h : ℂ) + I * z) / K)) by rw [Rademacher.qp]; push_cast; rfl,
    e1, hq']
  have hw : ‖Rademacher.qp h' K (1 / z)‖ ≤ 1 / 2 := by
    rw [Andrews66.norm_qp' h' hK]
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_pi_le
    rw [neg_le_neg_iff, le_div_iff₀ hKr]; nlinarith [Real.pi_pos]
  have hF1 : ‖HardyRamanujan.F (Rademacher.qp h' K (1 / z))‖ ≤ 1 + HardyRamanujan.C0 := by
    have := HardyRamanujan.F_sub_one hw
    have h2 : 2 * HardyRamanujan.C0 * ‖Rademacher.qp h' K (1 / z)‖ ≤ HardyRamanujan.C0 := by
      have := HardyRamanujan.C0_nonneg; nlinarith [norm_nonneg (Rademacher.qp h' K (1 / z))]
    have := norm_le_norm_add_norm_sub' (HardyRamanujan.F (Rademacher.qp h' K (1 / z))) 1
    rw [norm_one] at this
    linarith
  rw [norm_mul, norm_mul, norm_mul, hω, one_mul, Andrews66.norm_sqrt_eq, Andrews66.norm_cexp_main]
  have he : Real.exp (π * ((1 / z).re - z.re) / (12 * K)) ≤ Real.exp (π * (1 / z).re / (12 * K)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [Real.pi_pos]
  calc √‖z‖ * Real.exp (π * ((1 / z).re - z.re) / (12 * K)) * ‖HardyRamanujan.F (Rademacher.qp h' K (1 / z))‖
      ≤ √‖z‖ * Real.exp (π * (1 / z).re / (12 * K)) * (1 + HardyRamanujan.C0) := by gcongr
    _ = _ := by ring

/-! ### the Appell–Lerch sum of `f` at an odd cusp -/

/-- coefficients `(−1)ⁿ ζ^{n(3n+1)/2}`, `ζ = e^{2πih/K}`. -/
def cK (h K : ℕ) (n : ℤ) : ℂ := (-1) ^ n * cexp (2 * π * I * h * (3 * (n : ℂ) ^ 2 + n) / (2 * K))

/-- the phase of `−ζⁿ`, reduced to be exactly `K`-periodic. -/
def θK (h K : ℕ) (n : ℤ) : ℝ := π + 2 * π * h * ((n % (K : ℤ) : ℤ) : ℝ) / K

/-- `α = 2πz/K`. -/
def αK (K : ℕ) (z : ℂ) : ℂ := 2 * π * z / K

lemma cK_norm (h K : ℕ) (n : ℤ) : ‖cK h K n‖ ≤ 1 := by
  unfold cK
  rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
    show (2 * π * I * h * (3 * (n : ℂ) ^ 2 + n) / (2 * K)) =
      ((2 * π * h * (3 * (n : ℝ) ^ 2 + n) / (2 * K) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

lemma cK_anti {h K : ℕ} (hK : Odd K) (n : ℤ) : cK h K (n + K) = -cK h K n := by
  obtain ⟨j, rfl⟩ := hK
  have hK0 : ((2 * j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * j + 1 ≠ 0)
  unfold cK
  have hs : ((-1 : ℂ) ^ (n + ((2 * j + 1 : ℕ) : ℤ))) = -(-1) ^ n := by
    rw [zpow_add₀ (by norm_num), zpow_natCast, pow_succ, pow_mul]; simp
  have he : 2 * π * I * h * (3 * ((n + ((2 * j + 1 : ℕ) : ℤ) : ℤ) : ℂ) ^ 2 + ((n + ((2 * j + 1 : ℕ) : ℤ) : ℤ) : ℂ)) /
      (2 * ((2 * j + 1 : ℕ) : ℂ)) = 2 * π * I * h * (3 * (n : ℂ) ^ 2 + n) / (2 * ((2 * j + 1 : ℕ) : ℂ)) +
      (((h : ℤ) * (3 * n + 3 * j + 2) : ℤ) : ℂ) * (2 * π * I) := by
    field_simp; push_cast; ring
  rw [hs, he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  ring

lemma θK_per (h K : ℕ) (n : ℤ) : θK h K (n + K) = θK h K n := by
  simp [θK]

lemma θK_sep {h K : ℕ} (hK : Odd K) (n k : ℤ) : π / K ≤ |θK h K n - 2 * π * k| := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK.pos
  set N : ℤ := K + 2 * h * (n % (K : ℤ)) - 2 * k * K
  have hN : θK h K n - 2 * π * k = π / K * N := by
    simp only [θK, N]; push_cast; field_simp
  have hNo : N ≠ 0 := by
    intro h0
    have : Odd N := by
      obtain ⟨j, hj⟩ := hK
      have hjZ : (K : ℤ) = 2 * j + 1 := by exact_mod_cast hj
      refine ⟨h * (n % (K : ℤ)) - k * K + j, ?_⟩
      simp only [N]; linear_combination hjZ
    rw [h0] at this; exact (Int.not_odd_iff_even.mpr ⟨0, rfl⟩) this
  rw [hN, abs_mul, abs_of_pos (by positivity)]
  have : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast Int.one_le_abs hNo
  nlinarith [Real.pi_pos, div_pos Real.pi_pos hK0]

/-- the cusp form of the terms: `alTerm(n) = (−1)ⁿ q^{n(3n+1)/2}/(1+qⁿ)` with `q^x = e^{xL}`. -/
lemma alTerm_cusp {h K : ℕ} (hK : 0 < K) (z : ℂ) (n : ℤ) :
    alTerm (αK K z) (3 / 2) (1 / 2) 1 0 (cK h K) (fun n => cexp (I * θK h K n)) n =
      (-1) ^ n * cexp ((3 * (n : ℂ) ^ 2 + n) / 2 * (2 * π * I * ((h + I * z) / K))) /
        (1 + cexp (n * (2 * π * I * ((h + I * z) / K)))) := by
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold alTerm cK αK
  have hθ : cexp (I * θK h K n) = -cexp (2 * π * I * h * n / K) := by
    have hm : (n : ℂ) = ((n % (K : ℤ) : ℤ) : ℂ) + K * ((n / (K : ℤ) : ℤ) : ℂ) := by
      exact_mod_cast (Int.emod_add_mul_ediv n K).symm
    have : I * (θK h K n : ℂ) = 2 * π * I * h * n / K + I * π +
        (((-((h : ℤ) * (n / (K : ℤ)))) : ℤ) : ℂ) * (2 * π * I) := by
      rw [hm]
      unfold θK
      push_cast; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
      show I * (π : ℂ) = π * I by ring, Complex.exp_pi_mul_I]; ring
  beta_reduce
  rw [hθ, mul_assoc, ← Complex.exp_add]
  congr 1
  · congr 1; push_cast; ring_nf; rw [I_sq]; ring
  · rw [neg_mul, sub_neg_eq_add, ← Complex.exp_add]; congr 1; push_cast; ring_nf; rw [I_sq]; ring

lemma pow_eq_cexp (L : ℂ) (m : ℕ) : cexp L ^ m = cexp (m * L) := by rw [← Complex.exp_nat_mul]

lemma alTerm_pos {h K : ℕ} (hK : 0 < K) (z : ℂ) (m : ℕ) :
    alTerm (αK K z) (3 / 2) (1 / 2) 1 0 (cK h K) (fun n => cexp (I * θK h K n)) ((m : ℤ) + 1) =
      fGt m (Rademacher.qp h K z) := by
  rw [alTerm_cusp hK, fGt, Rademacher.qp, pow_eq_cexp, pow_eq_cexp]
  have h2 : ((eN m : ℕ) : ℂ) = (3 * (((m : ℤ) + 1 : ℤ) : ℂ) ^ 2 + (((m : ℤ) + 1 : ℤ) : ℂ)) / 2 := by
    have := two_mul_eN m
    have h' : (2 : ℂ) * (eN m : ℂ) = ((m + 1) * (3 * m + 4) : ℕ) := by exact_mod_cast this
    push_cast at h' ⊢
    linear_combination h' / 2
  rw [h2, show ((-1 : ℂ) ^ (((m : ℤ) + 1 : ℤ))) = (-1) ^ (m + 1) by
    rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast], div_eq_mul_inv]
  push_cast
  ring_nf

lemma alTerm_neg {h K : ℕ} (hK : 0 < K) (z : ℂ) (hz : 0 < z.re) (n : ℤ) :
    alTerm (αK K z) (3 / 2) (1 / 2) 1 0 (cK h K) (fun n => cexp (I * θK h K n)) (-n) =
      alTerm (αK K z) (3 / 2) (1 / 2) 1 0 (cK h K) (fun n => cexp (I * θK h K n)) n := by
  rw [alTerm_cusp hK, alTerm_cusp hK]
  set L : ℂ := 2 * π * I * ((h + I * z) / K)
  have hL : cexp (n * L) ≠ -1 := by
    intro h0
    have hn := congrArg norm h0
    rw [norm_neg, norm_one, Complex.norm_exp] at hn
    have hre : (n * L).re = -(2 * π * n * z.re / K) := by
      simp only [L]; push_cast
      rw [show (n : ℂ) * (2 * π * I * ((h + I * z) / K)) = ((2 * π * n / K : ℝ) : ℂ) * (I * h - z) by
        push_cast; field_simp; ring_nf; rw [I_sq]; ring, re_ofReal_mul]
      simp; ring
    rw [hre, Real.exp_eq_one_iff] at hn
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
    have h3 : (n : ℝ) * (2 * π * z.re / K) = 0 := by rw [← neg_eq_zero, ← hn]; ring
    have : (n : ℝ) = 0 := (mul_eq_zero.mp h3).resolve_right (by positivity)
    have hn0 : n = 0 := by exact_mod_cast this
    rw [hn0] at h0; simp at h0; norm_num at h0
  have h1 : 1 + cexp (n * L) ≠ 0 := fun h0 => hL (by linear_combination h0)
  have h1' : cexp (n * L) + 1 ≠ 0 := by rw [add_comm]; exact h1
  have hE : cexp (-n * L) = (cexp (n * L))⁻¹ := by rw [neg_mul, Complex.exp_neg]
  push_cast
  rw [hE, show (3 * (-(n : ℂ)) ^ 2 + -(n : ℂ)) / 2 * L = (3 * (n : ℂ) ^ 2 + n) / 2 * L + -(n * L) by ring,
    Complex.exp_add, Complex.exp_neg, zpow_neg, ← inv_zpow, inv_neg, inv_one]
  have h2 : cexp (n * L) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  ring

/-- `G(q) = 2 Σ_{n∈ℤ} alTerm(n)`. -/
lemma fG_eq_al {h K : ℕ} (hK : 0 < K) {z : ℂ} (hz : 0 < z.re)
    (hs : Summable (alTerm (αK K z) (3 / 2) (1 / 2) 1 0 (cK h K) (fun n => cexp (I * θK h K n)))) :
    fG (Rademacher.qp h K z) = 2 * ∑' n, alTerm (αK K z) (3 / 2) (1 / 2) 1 0 (cK h K)
      (fun n => cexp (I * θK h K n)) n := by
  set a := alTerm (αK K z) (3 / 2) (1 / 2) 1 0 (cK h K) (fun n => cexp (I * θK h K n))
  have ha0 : a 0 = 1 / 2 := by
    simp only [a, alTerm, cK]; push_cast; simp
    rw [show θK h K 0 = π by simp [θK]]
    rw [show I * (π : ℂ) = π * I by ring, Complex.exp_pi_mul_I]; norm_num
  have hpos : Summable fun m : ℕ => a ((m : ℤ) + 1) :=
    hs.comp_injective (fun x y hxy => by simpa using hxy)
  have hnat := hs.hasSum.nat_add_neg
  have e : ∀ m : ℕ, a m + a (-(m : ℤ)) = 2 * a m := fun m => by simp only [a]; rw [alTerm_neg hK z hz]; ring
  simp only [e] at hnat
  have hshift := (hasSum_nat_add_iff' 1).mpr hnat
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ha0] at hshift
  have hfin : HasSum (fun m : ℕ => 2 * fGt m (Rademacher.qp h K z)) (∑' n, a n + 1 / 2 - 2 * (1 / 2)) := by
    refine hshift.congr_fun fun m => ?_
    simp only [Nat.cast_add, Nat.cast_one, a]
    rw [alTerm_pos hK]
  have ht : ∑' m, fGt m (Rademacher.qp h K z) = (∑' n, a n - 1 / 2) / 2 := by
    have := (hfin.div_const 2).tsum_eq
    simp only [mul_div_cancel_left₀ _ (two_ne_zero' ℂ)] at this
    rw [this]; ring
  unfold fG
  rw [ht]; ring

lemma sqrt_div_sq {x : ℝ} (hx : 0 < x) : √x / x ^ 2 = x ^ (-(3 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, show (-(3 / 2 : ℝ)) = 1 / 2 - 2 by norm_num, Real.rpow_sub hx]
  norm_cast

lemma exp_sq_div_sinh_le {c : ℝ} (hc : π / 24 ≤ c) : Real.exp c * Real.exp c * (1 / Real.sinh (2 * c)) ≤ 6 := by
  have hpos : 0 < c := lt_of_lt_of_le (by positivity) hc
  have hs0 : 0 < Real.sinh (2 * c) := Real.sinh_pos_iff.mpr (by linarith)
  set a := Real.exp (2 * c)
  set b := Real.exp (-(2 * c))
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  have hab : a * b = 1 := by simp only [a, b]; rw [← Real.exp_add]; simp
  have ha2 : 3 / 2 ≤ a * a := by
    simp only [a]; rw [← Real.exp_add]
    have := Real.add_one_le_exp (2 * c + 2 * c); nlinarith [Real.pi_gt_three]
  have hsh2 : Real.sinh (2 * c) = (a - b) / 2 := Real.sinh_eq _
  rw [← Real.exp_add, show c + c = 2 * c by ring, mul_one_div, div_le_iff₀ hs0, hsh2]
  nlinarith [mul_pos ha ha]

/-- **`f` near an odd-order root of unity**. -/
theorem f_odd_bound {K : ℕ} (hK : Odd K) {h : ℕ} (hcop : Nat.Coprime h K) {z : ℂ} (hz : 0 < z.re)
    (hR : (K : ℝ) / 2 ≤ (1 / z).re) :
    ‖MockTheta3.Radial.fA (Rademacher.qp h K z)‖ ≤ 216 * (1 + HardyRamanujan.C0) * ‖z‖ ^ (-(3 / 2 : ℝ)) := by
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
    (cK_norm h K) (θK_per h K) (θK_sep hK) (by
      rw [div_lt_div_iff₀ (by positivity) hKr]; nlinarith [Real.pi_pos])
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
  have hmin : ‖z‖ / 2 ≤ min 1 (‖α‖ * ((1 / α).re * (π / K - π * 1 / (2 * K * (3 / 2))))) := by
    refine le_min (by linarith) ?_
    rw [hαn, hαR]
    have : 2 * π * ‖z‖ / K * (K * (1 / z).re / (2 * π) * (π / K - π * 1 / (2 * K * (3 / 2)))) =
        ‖z‖ * (1 / z).re * (2 * π / (3 * K)) := by field_simp; norm_num
    rw [this]
    have h1 : ‖z‖ * (K / 2) * (2 * π / (3 * K)) ≤ ‖z‖ * (1 / z).re * (2 * π / (3 * K)) := by gcongr
    have h2 : ‖z‖ * (K / 2) * (2 * π / (3 * K)) = ‖z‖ * (π / 3) := by field_simp
    nlinarith [Real.pi_gt_three]
  have hm1 : 3 / min 1 (‖α‖ * ((1 / α).re * (π / K - π * 1 / (2 * K * (3 / 2))))) ≤ 6 / ‖z‖ := by
    rw [div_le_div_iff₀ (by linarith [hmin, show 0 < ‖z‖ / 2 by positivity]) hzn]; linarith
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
  have hminpos : 0 < min 1 (‖α‖ * ((1 / α).re * (π / K - π * 1 / (2 * K * (3 / 2))))) :=
    lt_of_lt_of_le (by positivity) hmin
  have h2 : Real.exp c0 * Real.exp ((1 / 2) ^ 2 * α.re / (4 * (3 / 2))) * √(π / (3 / 2 * α.re)) ≤
      3 * Real.exp c0 * (1 / ‖z‖) := by
    calc Real.exp c0 * Real.exp ((1 / 2) ^ 2 * α.re / (4 * (3 / 2))) * √(π / (3 / 2 * α.re))
        ≤ Real.exp c0 * 3 * (1 / ‖z‖) := by gcongr
      _ = 3 * Real.exp c0 * (1 / ‖z‖) := by ring
  have hb' : ‖∑' n, alTerm α (3 / 2) (1 / 2) 1 0 (cK h K) (fun n => cexp (I * θK h K n)) n‖ ≤
      (6 / ‖z‖) * (3 * Real.exp c0 * (1 / ‖z‖)) * (1 / Real.sinh (2 * c0)) := by
    refine hb.trans ?_
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hm1 h2 (by positivity) (by positivity)) (by positivity)
  have hG : ‖fG (Rademacher.qp h K z)‖ ≤ 2 * ((6 / ‖z‖) * (3 * Real.exp c0 * (1 / ‖z‖)) *
      (1 / Real.sinh (2 * c0))) := by
    rw [fG_eq_al hK0 hz hs, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
    exact mul_le_mul_of_nonneg_left hb' (by norm_num)
  -- `f = G·F`
  have hq : Rademacher.qp h K z ∈ ball (0 : ℂ) 1 := Rademacher.qp_mem hK0 hz
  have hfa : MockTheta3.Radial.fA (Rademacher.qp h K z) =
      fG (Rademacher.qp h K z) * HardyRamanujan.F (Rademacher.qp h K z) := by
    rw [← f_AL hq, HardyRamanujan.F, mul_assoc, mul_inv_cancel₀ (HardyRamanujan.Pq_ne_zero hq), mul_one]
  rw [hfa, norm_mul]
  have hFb := F_bound hK0 hcop hz hR
  rw [← hc0] at hFb
  have hC0 := HardyRamanujan.C0_nonneg
  calc ‖fG (Rademacher.qp h K z)‖ * ‖HardyRamanujan.F (Rademacher.qp h K z)‖
      ≤ (2 * ((6 / ‖z‖) * (3 * Real.exp c0 * (1 / ‖z‖)) * (1 / Real.sinh (2 * c0)))) *
          ((1 + HardyRamanujan.C0) * √‖z‖ * Real.exp c0) := by gcongr
    _ = 36 * (1 + HardyRamanujan.C0) * (Real.exp c0 * Real.exp c0 * (1 / Real.sinh (2 * c0))) *
          (√‖z‖ / ‖z‖ ^ 2) := by field_simp; norm_num
    _ ≤ 36 * (1 + HardyRamanujan.C0) * 6 * (√‖z‖ / ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsh (by positivity)) (by positivity)
    _ = 216 * (1 + HardyRamanujan.C0) * ‖z‖ ^ (-(3 / 2 : ℝ)) := by
        rw [sqrt_div_sq hzn]; ring

end

end MockCusp
