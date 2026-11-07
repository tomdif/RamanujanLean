/-
# Global positivity: `‖F(σ)‖ ≥ 1` for `σ > 1`

`F(σ) = ζ(σ) · L(σ+it)² · L(σ−it)² · (ζ(2σ)R(σ))² · ζ(2σ+4it)R(σ+2it) · ζ(2σ−4it)R(σ−2it)`
(normalized: `L(s) = tauL(s + 11/2)`, `R` = `RS`), the Rankin–Selberg L-function of
`Π × Π̃` for `Π = 1 ⊞ Δ|·|^{it} ⊞ Δ|·|^{−it}`.  Each Euler factor is `exp ℓ_p`, `ℓ_p ≥ 0`
(`Local.localD_inv_eq_exp`), so `‖F(σ)‖ = ∏ exp ℓ_p ≥ 1`.
-/
import RamanujanTau.EdgeNonvanishing.Local
import RamanujanTau.EdgeNonvanishing.PrimeLocal
import RamanujanTau.HeckeZeros.Zeros

set_option autoImplicit false

namespace RamanujanTau.EdgeNonvanishing

open Complex Finset Filter LSeries
open RamanujanTau.HeckeL
open scoped ComplexConjugate

/-- `e_p(t) = p^{−it}`. -/
noncomputable def ep (p : ℕ) (t : ℝ) : ℂ := (p : ℂ) ^ (-((t : ℂ) * I))

lemma ep_norm {p : ℕ} (hp : p.Prime) (t : ℝ) : ‖ep p t‖ = 1 := by
  rw [ep, norm_natCast_cpow_of_pos hp.pos]; simp

lemma ep_mul {p : ℕ} (hp : p.Prime) (t : ℝ) : ep p t * ep p (-t) = 1 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [ep, ep, ← cpow_add _ _ hp0]; push_cast; ring_nf; exact cpow_zero _

lemma ep_neg_eq_conj {p : ℕ} (t : ℝ) : ep p (-t) = conj (ep p t) := by
  rw [ep, ep, show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; rfl,
    ← HeckeZeros.ofReal_cpow_conj (by positivity)]
  congr 1
  simp [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]

lemma ep_add_real {p : ℕ} (t : ℝ) : ep p t + ep p (-t) = ((2 * (ep p t).re : ℝ) : ℂ) := by
  rw [ep_neg_eq_conj, Complex.add_conj]

/-- The `ζ(2s)R(s)` Euler factor. -/
noncomputable def fR (s : ℂ) (p : ℕ) : ℂ := (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ * ∑' e, term rsB s (p ^ e)

lemma fR_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => fR s p) (riemannZeta (2 * s) * RS s) := by
  have h2 : 1 < (2 * s).re := by simp; linarith
  exact (riemannZeta_eulerProduct_hasProd h2).mul (rs_eulerProduct hs)

/-- The points. -/
noncomputable def sL (σ t : ℝ) : ℂ := (σ : ℂ) + 11 / 2 + (t : ℂ) * I
noncomputable def sR (σ t : ℝ) : ℂ := (σ : ℂ) + 2 * (t : ℂ) * I

/-- The product `F(σ)`. -/
noncomputable def Fval (σ t : ℝ) : ℂ :=
  riemannZeta σ * (tauL (sL σ t) * tauL (sL σ t)) * (tauL (sL σ (-t)) * tauL (sL σ (-t))) *
    ((riemannZeta (2 * σ) * RS σ) * (riemannZeta (2 * σ) * RS σ)) *
    (riemannZeta (2 * sR σ t) * RS (sR σ t)) * (riemannZeta (2 * sR σ (-t)) * RS (sR σ (-t)))

/-- The Euler factor of `F`. -/
noncomputable def Fp (σ t : ℝ) (p : ℕ) : ℂ :=
  (1 - (p : ℂ) ^ (-(σ : ℂ)))⁻¹ * ((HeckeZeros.localPoly (sL σ t) p)⁻¹ * (HeckeZeros.localPoly (sL σ t) p)⁻¹) *
    ((HeckeZeros.localPoly (sL σ (-t)) p)⁻¹ * (HeckeZeros.localPoly (sL σ (-t)) p)⁻¹) *
    (fR σ p * fR σ p) * fR (sR σ t) p * fR (sR σ (-t)) p

lemma Fp_hasProd {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    HasProd (fun p : Nat.Primes => Fp σ t p) (Fval σ t) := by
  have hL : ∀ u : ℝ, 13 / 2 < (sL σ u).re := fun u => by simp [sL]; linarith
  have hz := riemannZeta_eulerProduct_hasProd (s := (σ : ℂ)) (by simpa using hσ)
  have ha := HeckeZeros.tauL_eulerProduct (hL t)
  have hb := HeckeZeros.tauL_eulerProduct (hL (-t))
  have hr0 := fR_hasProd (s := (σ : ℂ)) (by simpa using hσ)
  have hr1 := fR_hasProd (s := sR σ t) (by simp [sR]; linarith)
  have hr2 := fR_hasProd (s := sR σ (-t)) (by simp [sR]; linarith)
  exact ((((hz.mul (ha.mul ha)).mul (hb.mul hb)).mul (hr0.mul hr0)).mul hr1).mul hr2

/-- **Per-prime positivity**: `Fp σ t p = exp ℓ` with `ℓ ≥ 0`. -/
theorem Fp_eq_exp {σ : ℝ} (hσ : 1 < σ) (t : ℝ) {p : ℕ} (hp : p.Prime) :
    ∃ ℓ : ℝ, 0 ≤ ℓ ∧ Fp σ t p = ((Real.exp ℓ : ℝ) : ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  obtain ⟨α, β, hab, hs, hα1, hβ⟩ := satake (lam p)
  have hα := alpha_sq_le hp hab hs hβ
  have hxp : (p : ℝ) * (p : ℝ) ^ (-σ) < 1 := by
    have : (p : ℝ) * (p : ℝ) ^ (-σ) = (p : ℝ) ^ (1 - σ) := by
      rw [Real.rpow_sub (by positivity), Real.rpow_one, Real.rpow_neg (by positivity), div_eq_mul_inv]
    rw [this]; exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  set x : ℝ := (p : ℝ) ^ (-σ)
  have hX : (p : ℂ) ^ (-(σ : ℂ)) = (x : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl
  have hx0 : 0 ≤ x := by positivity
  have hαx : ‖α‖ ^ 2 * x < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hα hx0) hxp
  -- the exponents
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
  obtain ⟨ℓ, hℓ0, hℓ⟩ := localD_inv_eq_exp α β (ep p t) (ep p (-t)) (lam p) (2 * (ep p t).re) x hx0 hab hs
    (ep_mul hp t) (ep_add_real t) hα1 hβ (ep_norm hp t) (ep_norm hp (-t)) hαx
  refine ⟨ℓ, hℓ0, ?_⟩
  rw [← hℓ, Fp, hX, hLa, hLb, hR0, hR1, hR2, localD]
  simp only [mul_inv, ← inv_pow, ← mul_assoc]
  ring

/-- **Global positivity**: `‖F(σ)‖ ≥ 1` for every `σ > 1` and every `t`. -/
theorem one_le_norm_Fval {σ : ℝ} (hσ : 1 < σ) (t : ℝ) : 1 ≤ ‖Fval σ t‖ := by
  have hloc : ∀ p : Nat.Primes, ∃ ℓ : ℝ, 0 ≤ ℓ ∧ Fp σ t p = ((Real.exp ℓ : ℝ) : ℂ) :=
    fun p => Fp_eq_exp hσ t p.2
  choose ℓ hℓ0 hℓ using hloc
  have hN := (Fp_hasProd hσ t).norm
  have hpart : ∀ S : Finset Nat.Primes, 1 ≤ ∏ p ∈ S, ‖Fp σ t p‖ := by
    intro S
    have : ∏ p ∈ S, ‖Fp σ t p‖ = Real.exp (∑ p ∈ S, ℓ p) := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [hℓ p, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [this]
    exact Real.one_le_exp (Finset.sum_nonneg fun p _ => hℓ0 p)
  exact ge_of_tendsto' hN hpart

end RamanujanTau.EdgeNonvanishing
