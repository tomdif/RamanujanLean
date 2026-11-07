/-
# `σ ↦ ‖F(σ)‖` is non-increasing on `σ > 1`

`F = Fval σ t` is the positivity product of `EdgeNonvanishing`.  Its Euler factor at `p` is
`exp ℓ_p(σ)` with `ℓ_p(σ) = Σ_k (1 + A_k E_k)² p^{−kσ}/k`, a power series in `p^{−σ}` with
non-negative coefficients (`EdgeNonvanishing.Local`).  So each factor, hence `‖F(σ)‖`, is
non-increasing in `σ`.  Also: `R(s) ≠ 0` for `Re s > 1` (read off from `‖F‖ ≥ 1`).
-/
import RamanujanTau.EdgeNonvanishing.Main

set_option autoImplicit false

namespace RamanujanTau.ZeroFreeRegion

open Complex Filter Topology
open RamanujanTau.EdgeNonvanishing RamanujanTau.HeckeL

/-- The explicit exponent of the local factor (copy of `localD_inv_eq_exp`, keeping the formula). -/
theorem localD_inv_eq_exp_tsum (α β e e' : ℂ) (r μ x : ℝ) (hx : 0 ≤ x) (hab : α * β = 1)
    (hs : α + β = r) (hee : e * e' = 1) (he : e + e' = μ) (hα1 : 1 ≤ ‖α‖) (hβ : ‖β‖ ≤ 1)
    (he1 : ‖e‖ = 1) (he1' : ‖e'‖ = 1) (hαx : ‖α‖ ^ 2 * x < 1) :
    Summable (fun k : ℕ => (1 + pseq r k * pseq μ k) ^ 2 * x ^ k / k) ∧
    (localD α β e e' (x : ℂ))⁻¹ =
      ((Real.exp (∑' k : ℕ, (1 + pseq r k * pseq μ k) ^ 2 * x ^ k / k) : ℝ) : ℂ) := by
  set l := (gammas α β e e').map (fun γ => γ * (x : ℂ))
  have hA : 1 ≤ ‖α‖ ^ 2 := by nlinarith
  have hbound : ∀ γ ∈ gammas α β e e', ‖γ‖ ≤ ‖α‖ ^ 2 := by
    intro γ hγ
    have hβ2 : ‖β‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg β]
    have hα2 : ‖α‖ ≤ ‖α‖ ^ 2 := by nlinarith
    simp only [gammas, List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h <;> subst h <;>
      simp only [norm_mul, norm_pow, he1, he1', one_pow, mul_one, norm_one] <;> nlinarith
  have hl : ∀ z ∈ l, ‖z‖ < 1 := by
    intro z hz
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
    calc ‖γ‖ * x ≤ ‖α‖ ^ 2 * x := mul_le_mul_of_nonneg_right (hbound γ hγ) hx
      _ < 1 := hαx
  obtain ⟨h1, h2⟩ := list_log l hl
  set ℓC := (l.map (fun z => -log (1 - z))).sum
  set c : ℕ → ℝ := fun k => (1 + pseq r k * pseq μ k) ^ 2 * x ^ k / k
  have hc : ∀ k, (l.map (fun z => z ^ k)).sum / k = (c k : ℂ) := by
    intro k
    have : (l.map (fun z => z ^ k)).sum = ((gammas α β e e').map (fun γ => γ ^ k)).sum * (x : ℂ) ^ k := by
      simp only [l, List.map_map]
      rw [← List.sum_map_mul_right]
      congr 1
      apply List.map_congr_left
      intro γ _
      simp [mul_pow]
    rw [this, gammas_powsum α β e e' k hab hee, pow_add_pow_eq_pseq hs hab,
      pow_add_pow_eq_pseq he hee]
    simp only [c]; push_cast; ring
  simp_rw [hc] at h1
  have hsum : Summable c := Complex.summable_ofReal.mp h1.summable
  have hℓ : ℓC = ((∑' k, c k : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; exact h1.tsum_eq.symm
  refine ⟨hsum, ?_⟩
  rw [localD_eq, h2, hℓ, Complex.ofReal_exp]

/-- The Euler factor of `F` as an inverse `localD`, with σ-independent Satake parameters. -/
theorem Fp_eq_localD (t : ℝ) {p : ℕ} (hp : p.Prime) :
    ∃ α β : ℂ, α * β = 1 ∧ α + β = lam p ∧ 1 ≤ ‖α‖ ∧ ‖β‖ ≤ 1 ∧ ‖α‖ ^ 2 ≤ p ∧
      ∀ σ : ℝ, 1 < σ → Fp σ t p =
        (localD α β (ep p t) (ep p (-t)) (((p : ℝ) ^ (-σ) : ℝ) : ℂ))⁻¹ := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨α, β, hab, hs, hα1, hβ⟩ := satake (lam p)
  have hα := alpha_sq_le hp hab hs hβ
  refine ⟨α, β, hab, hs, hα1, hβ, hα, fun σ hσ => ?_⟩
  set x : ℝ := (p : ℝ) ^ (-σ)
  have hX : (p : ℂ) ^ (-(σ : ℂ)) = (x : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl
  have hZ : ∀ u : ℝ, (p : ℂ) ^ (-(sL σ u - 11 / 2)) = ep p u * x := by
    intro u
    rw [← hX, ep, ← cpow_add _ _ hp0]; congr 1; simp [sL]; ring
  have hY : ∀ u : ℝ, (p : ℂ) ^ (-(sR σ u)) = ep p u ^ 2 * x := by
    intro u
    rw [← hX, ep, sq, ← cpow_add _ _ hp0, ← cpow_add _ _ hp0]; congr 1; simp [sR]; ring
  have hR : ∀ s : ℂ, 1 < s.re → fR s p =
      ((1 - (p : ℂ) ^ (-s)) ^ 2 * (1 - α ^ 2 * (p : ℂ) ^ (-s)) * (1 - β ^ 2 * (p : ℂ) ^ (-s)))⁻¹ :=
    fun s hs' => rs_local hs' hp hab hs hα hβ
  have hR0 := hR σ (by simpa using hσ)
  have hR1 := hR (sR σ t) (by simp [sR]; linarith)
  have hR2 := hR (sR σ (-t)) (by simp [sR]; linarith)
  rw [hX] at hR0
  rw [hY t] at hR1
  rw [hY (-t)] at hR2
  have hLa := tau_local (sL σ t) hp hab hs
  have hLb := tau_local (sL σ (-t)) hp hab hs
  rw [hZ t] at hLa
  rw [hZ (-t)] at hLb
  rw [Fp, hX, hLa, hLb, hR0, hR1, hR2, localD]
  simp only [mul_inv, ← inv_pow, ← mul_assoc]
  ring

/-- Each Euler factor of `‖F(σ)‖` is non-increasing in `σ > 1`. -/
theorem norm_Fp_antitone (t : ℝ) {p : ℕ} (hp : p.Prime) {σ₁ σ₂ : ℝ} (h1 : 1 < σ₁)
    (h12 : σ₁ ≤ σ₂) : ‖Fp σ₂ t p‖ ≤ ‖Fp σ₁ t p‖ := by
  obtain ⟨α, β, hab, hs, hα1, hβ, hα, hF⟩ := Fp_eq_localD t hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hx : ∀ σ : ℝ, 1 < σ → ‖α‖ ^ 2 * (p : ℝ) ^ (-σ) < 1 := by
    intro σ hσ
    have hxp : (p : ℝ) * (p : ℝ) ^ (-σ) < 1 := by
      have : (p : ℝ) * (p : ℝ) ^ (-σ) = (p : ℝ) ^ (1 - σ) := by
        rw [Real.rpow_sub hp0, Real.rpow_one, Real.rpow_neg hp0.le, div_eq_mul_inv]
      rw [this]; exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hα (by positivity)) hxp
  have hee := ep_mul hp t
  have hreal := ep_add_real (p := p) t
  obtain ⟨hs1, he1⟩ := localD_inv_eq_exp_tsum α β (ep p t) (ep p (-t)) (lam p) (2 * (ep p t).re)
    ((p : ℝ) ^ (-σ₁)) (by positivity) hab hs hee hreal hα1 hβ (ep_norm hp t) (ep_norm hp (-t))
    (hx σ₁ h1)
  obtain ⟨hs2, he2⟩ := localD_inv_eq_exp_tsum α β (ep p t) (ep p (-t)) (lam p) (2 * (ep p t).re)
    ((p : ℝ) ^ (-σ₂)) (by positivity) hab hs hee hreal hα1 hβ (ep_norm hp t) (ep_norm hp (-t))
    (hx σ₂ (by linarith))
  rw [hF σ₁ h1, hF σ₂ (by linarith), he1, he2, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.exp_le_exp]
  have hxle : (p : ℝ) ^ (-σ₂) ≤ (p : ℝ) ^ (-σ₁) :=
    Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  refine hs2.tsum_le_tsum (fun k => ?_) hs1
  have : 0 ≤ (1 + pseq (lam p) k * pseq (2 * (ep p t).re) k) ^ 2 := sq_nonneg _
  have h0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ₂) := by positivity
  gcongr

/-- **`‖F(σ)‖` is non-increasing on `σ > 1`.** -/
theorem norm_Fval_antitone (t : ℝ) {σ₁ σ₂ : ℝ} (h1 : 1 < σ₁) (h12 : σ₁ ≤ σ₂) :
    ‖Fval σ₂ t‖ ≤ ‖Fval σ₁ t‖ := by
  have hN1 := (Fp_hasProd h1 t).norm
  have hN2 := (Fp_hasProd (lt_of_lt_of_le h1 h12) t).norm
  refine le_of_tendsto_of_tendsto' hN2 hN1 fun S => ?_
  exact Finset.prod_le_prod (fun p _ => norm_nonneg _)
    (fun p _ => norm_Fp_antitone t p.2 h1 h12)

/-- `R(s) ≠ 0` on `Re s > 1`. -/
theorem RS_ne_zero {s : ℂ} (hs : 1 < s.re) : RS s ≠ 0 := by
  have hF := one_le_norm_Fval hs (s.im / 2)
  intro h0
  have hsR : sR s.re (s.im / 2) = s := by
    apply Complex.ext <;> simp [sR]; ring
  have : Fval s.re (s.im / 2) = 0 := by
    rw [Fval, hsR, h0]; ring
  rw [this, norm_zero] at hF
  linarith

end RamanujanTau.ZeroFreeRegion
