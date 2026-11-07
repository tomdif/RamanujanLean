/-
# The multiplier of `b` at `h/2k` in terms of Dedekind sums

`ω_b(h,k) = ω_{h,k}² / ω_{h,2k}³ = e^{πi(2s(h,k) − 3s(h,2k))}` (`omegaB_eq_dsum`), where `ω_{h,k} = e^{πi s(h,k)}`
is the multiplier of `1/(q;q)_∞` (`Rademacher.omega_eq_dsum`). Hence the Kloosterman sum of Andrews' theorem is

  `A_b(k,n) = Σ_{h mod 2k, (h,2k)=1} e^{πi(2s(h,k) − 3s(h,2k)) − πinh/k}`   (`Ab_eq_dedekind`).
-/
import RamanujanTau.Andrews66.Final
import RamanujanTau.Rademacher.DedekindOmega

set_option autoImplicit false

namespace Andrews66
open Complex Metric
open scoped Real

noncomputable section

lemma coprime_half {h k : ℕ} (hcop : Nat.Coprime h (2 * k)) : Nat.Coprime h k :=
  Nat.Coprime.coprime_dvd_right (Dvd.intro_left 2 rfl) hcop

/-- the transformation of `b` with the canonical `F`-multipliers. -/
lemma isMultB_omega {h k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime h (2 * k)) :
    IsMultB h k (Rademacher.omega h k ^ 2 / Rademacher.omega h (2 * k) ^ 3) := by
  have hk2 : 0 < 2 * k := by omega
  obtain ⟨hω₁, H₁⟩ := Rademacher.omega_spec hk2 hcop
  obtain ⟨hω₂, H₂⟩ := Rademacher.omega_spec hk (coprime_half hcop)
  refine ⟨by rw [norm_div, norm_pow, norm_pow, hω₁, hω₂]; norm_num, fun h' hdvd z hz => ?_⟩
  have hdvd1 : (k : ℤ) ∣ h * h' + 1 := (Int.natCast_dvd_natCast.mpr (Dvd.intro_left 2 rfl)).trans hdvd
  set ω₁ := Rademacher.omega h (2 * k)
  set ω₂ := Rademacher.omega h k
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have h1 := H₁ h' hdvd z hz
  have h2 := H₂ h' hdvd1 z hz
  simp only [qp_inv_eq] at h1 h2
  have r1 : cexp (2 * π * I * ((((h : ℕ) : ℂ) + I * z) / ((2 * k : ℕ) : ℂ))) = Rademacher.qp (h : ℤ) (2 * k) z := by
    rw [Rademacher.qp, Int.cast_natCast]
  have r2 : cexp (2 * π * I * ((((h : ℕ) : ℂ) + I * z) / (k : ℂ))) = Rademacher.qp (h : ℤ) k z := by
    rw [Rademacher.qp, Int.cast_natCast]
  rw [r1] at h1
  rw [r2] at h2
  have hω₁0 : ω₁ ≠ 0 := fun h => by rw [h, norm_zero] at hω₁; norm_num at hω₁
  have hs := sqrt_ne hz
  have hF1 := F_qp_ne (h := h') hk2 (inv_re_pos hz)
  have hF0 := F_qp_ne (h := (h : ℤ)) hk2 hz
  unfold bE
  have q1 := qp_sq (h : ℤ) k z
  have q2 := qp_sq h' k (1 / z)
  simp only [Int.cast_natCast] at q1 h1 h2 hF0 ⊢
  rw [q1, q2, h2, h1]
  push_cast
  have hE : cexp (π * (1 / z - z) / (24 * k)) =
      cexp (π * (1 / z - z) / (12 * k)) ^ 2 / cexp (π * (1 / z - z) / (12 * (2 * k))) ^ 3 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_sub]
    congr 1
    have : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast; field_simp; try ring
  rw [hE]
  have hsq := sqrt_sq' hz0
  have hs3 : Complex.sqrt z ^ 3 = z * Complex.sqrt z := by rw [pow_succ, hsq]
  have he1 : cexp (π * (1 / z - z) / (12 * (2 * k))) ≠ 0 := Complex.exp_ne_zero _
  field_simp

lemma bE_ne {h' : ℤ} {K : ℕ} (hK : 0 < K) {w : ℂ} (hw : 0 < w.re) : bE (Rademacher.qp h' K w) ≠ 0 := by
  unfold bE
  have h1 := Rademacher.F_ne_zero (sq_mem_ball (Rademacher.qp_mem (h' := h') hK hw))
  exact div_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ (F_qp_ne hK hw))

/-- uniqueness of the multiplier of `b`. -/
lemma isMultB_unique {h k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime h (2 * k)) {ω₁ ω₂ : ℂ}
    (h₁ : IsMultB h k ω₁) (h₂ : IsMultB h k ω₂) : ω₁ = ω₂ := by
  obtain ⟨a, b, hab⟩ := Rademacher.exists_inv hcop
  have hd : ((2 * k : ℕ) : ℤ) ∣ h * a + 1 := ⟨b, by linarith⟩
  have e1 := h₁.2 a hd 1 (by simp)
  have e2 := h₂.2 a hd 1 (by simp)
  have hF := bE_ne (h' := a) (by omega : 0 < 2 * k) (w := 1 / 1) (by simp)
  rw [e1] at e2
  simp only [Complex.sqrt_one, div_one, sub_self, mul_zero, zero_div, Complex.exp_zero, mul_one] at e2 hF
  exact mul_right_cancel₀ hF e2

/-- **`ω_b(h,k) = e^{πi(2s(h,k) − 3s(h,2k))}`**. -/
theorem omegaB_eq_dsum {h k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime h (2 * k)) :
    omegaB h k = cexp (π * I * (2 * Rademacher.dsum h k - 3 * Rademacher.dsum h (2 * k))) := by
  rw [isMultB_unique hk hcop (omegaB_spec hk hcop) (isMultB_omega hk hcop),
    Rademacher.omega_eq_dsum k hk h (coprime_half hcop), Rademacher.omega_eq_dsum (2 * k) (by omega) h hcop,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_sub]
  congr 1
  push_cast
  ring

/-- **the Kloosterman sum of Andrews' theorem, explicitly**:
`A_b(k,n) = Σ_{h mod 2k, (h,2k)=1} e^{πi(2s(h,k) − 3s(h,2k)) − 2πinh/(2k)}`. -/
theorem Ab_eq_dedekind {k : ℕ} (hk : 0 < k) (n : ℕ) :
    Ab k n = ∑ h ∈ (Finset.range (2 * k)).filter (fun h => Nat.Coprime h (2 * k)),
      cexp (π * I * (2 * Rademacher.dsum h k - 3 * Rademacher.dsum h (2 * k)) -
        2 * π * I * n * h / ((2 * k : ℕ) : ℂ)) := by
  unfold Ab
  refine Finset.sum_congr rfl fun h hh => ?_
  have hcop := (Finset.mem_filter.mp hh).2
  rw [show 2 * k / 2 = k by omega, omegaB_eq_dsum hk hcop, ← Complex.exp_add]
  congr 1
  try ring

/-! ### `Hb` is monotone in `D` -/

/-- `Hb` with a smaller exponent implies `Hb` with a larger one (in the region `‖z‖ ≤ 2/K ≤ 2`). -/
lemma Hb_mono {C D D' : ℝ} (hHb : Hb C D) (hC : 0 ≤ C) (hDD : D ≤ D') : Hb (C * 2 ^ (D' - D)) D' := by
  intro K hK h hcop z hz hR
  refine (hHb K hK h hcop z hz hR).trans ?_
  have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hz2 : ‖z‖ ≤ 2 := by
    have h1 : (1 / z).re ≤ ‖1 / z‖ := Complex.re_le_norm _
    rw [norm_div, norm_one] at h1
    have : (1 : ℝ) / 2 ≤ 1 / ‖z‖ := by linarith
    rw [div_le_div_iff₀ (by norm_num) hn] at this
    linarith
  have e : ‖z‖ ^ (-D) = ‖z‖ ^ (-D') * ‖z‖ ^ (D' - D) := by
    rw [← Real.rpow_add hn]; congr 1; ring
  rw [e, show C * 2 ^ (D' - D) * ‖z‖ ^ (-D') = C * (‖z‖ ^ (-D') * 2 ^ (D' - D)) by ring]
  have h2 := Real.rpow_le_rpow hn.le hz2 (sub_nonneg.mpr hDD)
  have h0 : 0 ≤ ‖z‖ ^ (-D') := by positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 h0) hC

/-- **Andrews' `O(√n log n)`**: if `Hb C D` holds for some `D ≤ 1`, then
`α(n) = Σ_{k ≤ √n/2} (−1)^k A_b(k,n) M_{2k}(n) + O(√n log n)`. -/
theorem andrews_1966_sqrt_log_of_Hb {C D : ℝ} (hHb : Hb C D) (hC : 0 ≤ C) (hD : D ≤ 1) :
    (fun n : ℕ => (Dragonette.α n : ℂ) - andrewsMain n) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log n)) := by
  have h := andrews_1966_isBigO_of_Hb (Hb_mono hHb hC hD) (by positivity) le_rfl
  norm_num at h ⊢
  exact h

end

end Andrews66
