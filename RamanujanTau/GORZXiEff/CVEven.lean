/-
# `Φ` is even: all odd derivatives of Riemann's kernel vanish at `0`

`H(u) = e^{u/2}(2θ₀(e^{2u}) + 1)` is even by the theta functional equation `θ(t) = t^{−1/2} θ(1/t)`
(Mathlib's `evenKernel_functional_equation`), and `Φ = H''/4 − H/16`.  Hence `Φ = Phi 0` is even, the chain
`Phi i` alternates even/odd, and **`Phi_odd_zero`** : `Phi (2j+1) 0 = 0`.
-/
import RamanujanTau.GORZXiEff.CVSeries

set_option autoImplicit false

namespace GORZXiEff.CV

open Real Set Filter Topology GORZXiEff GORZXi

lemma theta_fe {t : ℝ} (ht : 0 < t) : 2 * Tth t + 1 = t ^ (-(1 / 2) : ℝ) * (2 * Tth t⁻¹ + 1) := by
  rw [Tth_eq ht, Tth_eq (inv_pos.2 ht)]
  have := HurwitzZeta.evenKernel_functional_equation 0 t
  rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero] at this
  simp only [theta0]
  rw [show (1 : ℝ) / t = t⁻¹ by ring] at this
  rw [this, Real.rpow_neg ht.le, one_div]
  ring

lemma Ser_one (u : ℝ) : Ser [1] u = rexp (u / 2) * Tth (rexp (2 * u)) := by
  unfold Ser Tth
  rw [← tsum_mul_left]
  congr 1; funext k
  simp only [tz, zk, pe_cons, pe_nil]; push_cast; ring_nf

/-- `H(u) = e^{u/2}(2θ₀(e^{2u}) + 1)`. -/
noncomputable def Hf (u : ℝ) : ℝ := rexp (u / 2) + 2 * Ser [1] u

lemma Hf_even (u : ℝ) : Hf (-u) = Hf u := by
  have ht := exp_pos (2 * u)
  have fe := theta_fe ht
  have e1 : rexp (2 * u) ^ (-(1 / 2) : ℝ) = rexp (-u) := by
    rw [← Real.exp_mul]; congr 1; ring
  have e2 : (rexp (2 * u))⁻¹ = rexp (2 * -u) := by rw [← exp_neg]; congr 1; ring
  rw [e1, e2] at fe
  simp only [Hf, Ser_one]
  have e3 : rexp (u / 2) = rexp (-u / 2) * rexp u := by rw [← exp_add]; congr 1; ring
  have e4 : rexp (-u) * rexp u = 1 := by rw [← exp_add]; simp
  calc rexp (-u / 2) + 2 * (rexp (-u / 2) * Tth (rexp (2 * -u)))
      = rexp (-u / 2) * (2 * Tth (rexp (2 * -u)) + 1) := by ring
    _ = rexp (-u / 2) * (rexp u * (rexp (-u) * (2 * Tth (rexp (2 * -u)) + 1))) := by
        rw [← mul_assoc (rexp u), mul_comm (rexp u), e4, one_mul]
    _ = rexp (u / 2) * (2 * Tth (rexp (2 * u)) + 1) := by rw [← fe, e3]; ring
    _ = _ := by ring

noncomputable def Hf1 (u : ℝ) : ℝ := (1 / 2) * rexp (u / 2) + Ser (stepZ [1]) u
noncomputable def Hf2 (u : ℝ) : ℝ := (1 / 4) * rexp (u / 2) + (1 / 2) * Ser (stepZ (stepZ [1])) u

lemma hasDerivAt_exp_half (u : ℝ) : HasDerivAt (fun u : ℝ => rexp (u / 2)) (rexp (u / 2) * (1 / 2)) u :=
  ((hasDerivAt_id u).div_const 2).exp.congr_deriv (by simp)

lemma hasDerivAt_Hf (u : ℝ) : HasDerivAt Hf (Hf1 u) u := by
  have := (hasDerivAt_exp_half u).add ((hasDerivAt_Ser [1] u).const_mul 2)
  unfold Hf Hf1
  convert this using 1; ring

lemma hasDerivAt_Hf1 (u : ℝ) : HasDerivAt Hf1 (Hf2 u) u := by
  have := ((hasDerivAt_exp_half u).const_mul (1 / 2)).add (hasDerivAt_Ser (stepZ [1]) u)
  unfold Hf1 Hf2
  convert this using 1; ring

lemma odd_of_even {f f' : ℝ → ℝ} (hf : ∀ u, f (-u) = f u) (hd : ∀ u, HasDerivAt f (f' u) u) (u : ℝ) :
    f' (-u) = -f' u := by
  have h1 : HasDerivAt (fun v => f (-v)) (f' (-u) * (-1)) u := (hd (-u)).comp u (hasDerivAt_neg u)
  have e : (fun v => f (-v)) = f := funext hf
  rw [e] at h1
  have := (hd u).unique h1
  linarith

lemma even_of_odd {f f' : ℝ → ℝ} (hf : ∀ u, f (-u) = -f u) (hd : ∀ u, HasDerivAt f (f' u) u) (u : ℝ) :
    f' (-u) = f' u := by
  have h1 : HasDerivAt (fun v => f (-v)) (f' (-u) * (-1)) u := (hd (-u)).comp u (hasDerivAt_neg u)
  have e : (fun v => f (-v)) = fun v => -f v := funext hf
  rw [e] at h1
  have := (hd u).neg.unique h1
  linarith

lemma step2_one : stepZ (stepZ [1]) = [1, -24, 16] := by decide

lemma Phi0_eq (u : ℝ) : Phi 0 u = Hf2 u / 4 - Hf u / 16 := by
  have hs : Ser (Zs 0) u = (1 / 8) * (Ser (stepZ (stepZ [1])) u - Ser [1] u) := by
    unfold Ser
    rw [← Summable.tsum_sub (summable_tz _ u) (summable_tz _ u), ← tsum_mul_left]
    congr 1; funext k
    simp only [tz, Zs, step2_one, pe_cons, pe_nil]; push_cast; ring
  simp only [Phi, pow_zero, div_one, hs, Hf2, Hf]
  ring

lemma Phi0_even (u : ℝ) : Phi 0 (-u) = Phi 0 u := by
  have h1 := odd_of_even Hf_even hasDerivAt_Hf
  have h2 := even_of_odd h1 hasDerivAt_Hf1
  rw [Phi0_eq, Phi0_eq, h2, Hf_even]

lemma Phi_parity (j : ℕ) : (∀ u, Phi (2 * j) (-u) = Phi (2 * j) u) ∧
    (∀ u, Phi (2 * j + 1) (-u) = -Phi (2 * j + 1) u) := by
  induction j with
  | zero => exact ⟨Phi0_even, odd_of_even Phi0_even (hasDerivAt_Phi 0)⟩
  | succ j ih =>
    have he : ∀ u, Phi (2 * (j + 1)) (-u) = Phi (2 * (j + 1)) u := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
      exact even_of_odd ih.2 (hasDerivAt_Phi (2 * j + 1))
    exact ⟨he, odd_of_even he (hasDerivAt_Phi _)⟩

/-- **All odd derivatives of `Φ` vanish at `0`.** -/
theorem Phi_odd_zero (j : ℕ) : Phi (2 * j + 1) 0 = 0 := by
  have := (Phi_parity j).2 0
  rw [neg_zero] at this
  linarith

end GORZXiEff.CV
