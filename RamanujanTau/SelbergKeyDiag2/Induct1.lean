/-
# M3 step 2c: the main term is stable under peeling

`Mn u v h k α = ρ(h)ρ(k)·P(α) + ρ(h,1−iv)ρ(k,1−iv)·L(v)` with `P(α) = c₀G(p)α^{−p}e^{−v²/4}/(iv)`
(the pole of `R` at `z = iv/2`) and `L(v) = −c₀/(iv) + γ_Δ − iv ε(v)`.  Then

    Σ_j g_j (p^{−(1−iv)})^j Mn(h',k)(α p^{2j}) = Mn(p^a h', k)(α)          (`hasSum_Mn_peel`)

because `(αp^{2j})^{−iv/2}(p^{−(1−iv)})^j = α^{−iv/2} p^{−j}` and `Σ g_j p^{−j} = ρ_p(a)`,
`Σ g_j p^{−j(1−iv)} = N_p(a,1−iv)/D_p(1−iv)`.  Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.Peel

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex Finset PowerSeries RamanujanTau.HafnerBridge RamanujanTau.HafnerBridge2
open RamanujanTau.SelbergKey (NpC DpC rhoC)
open RamanujanTau.GoodSecondTerm (c0 gammaD)
open scoped Real

noncomputable def Pmain (u v α : ℝ) : ℂ :=
  (c0 : ℂ) * (Gsh u (u + v) (((v / 2 : ℝ) : ℂ) * I) * (α : ℂ) ^ (-(((v / 2 : ℝ) : ℂ) * I)) *
      Real.exp (-(v / 2) ^ 2)) / ((v : ℂ) * I)

noncomputable def Lmain (v : ℝ) : ℂ := -(c0 : ℂ) / ((v : ℂ) * I) + gammaD - (v : ℂ) * I * epsv v

lemma baseMain_eq (u v α : ℝ) : baseMain u v α = Pmain u v α + Lmain v := rfl

noncomputable def Mn (u v : ℝ) (h k : ℕ) (α : ℝ) : ℂ :=
  ((rho h * rho k : ℝ) : ℂ) * Pmain u v α + rhoC h (1 - v * I) * rhoC k (1 - v * I) * Lmain v

lemma rhoC_one (s : ℂ) : rhoC 1 s = 1 := by simp [rhoC]

lemma rhoC_peel {p a m : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hm : 1 ≤ m) (hpm : ¬ p ∣ m) (s : ℂ) :
    rhoC (p ^ a * m) s = NpC p a s / DpC p s * rhoC m s := by
  unfold rhoC
  rw [pf_peel hp ha hm, Finset.prod_insert (p_notMem hpm), fact_peel_p hp hm hpm]
  refine congrArg _ (Finset.prod_congr rfl fun q hq => ?_)
  rw [fact_peel_q hp hm (fun h => p_notMem hpm (h ▸ hq))]

/-- `(αp^{2j})^{−iv/2} (p^{−(1−iv)})^j = α^{−iv/2} p^{−j}`. -/
lemma pw_identity {p : ℕ} (hp : p.Prime) {α : ℝ} (hα : 0 < α) (v : ℝ) (j : ℕ) :
    ((α * (p : ℝ) ^ (2 * j) : ℝ) : ℂ) ^ (-(((v / 2 : ℝ) : ℂ) * I)) * ((p : ℂ) ^ (-(1 - (v : ℂ) * I))) ^ j =
      (α : ℂ) ^ (-(((v / 2 : ℝ) : ℂ) * I)) * ((((p : ℝ)⁻¹) ^ j : ℝ) : ℂ) := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hreal : ((p : ℝ)⁻¹) ^ j = Real.exp (-((j : ℝ) * Real.log p)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hp0, inv_pow]
  rw [cpow_eq_exp (by positivity : (0:ℝ) < α * (p : ℝ) ^ (2 * j)), Real.log_mul hα.ne' (by positivity),
    Real.log_pow, cpow_eq_exp hα, show (p : ℂ) = ((p : ℝ) : ℂ) by norm_cast, cpow_eq_exp hp0,
    ← Complex.exp_nat_mul, hreal, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma SN_gps {p : ℕ} (hp : p.Prime) (a : ℕ) : SN ((p : ℝ)⁻¹) (gps p a) := by
  obtain ⟨C, hC1, hC⟩ := lam_bound
  exact SN_mul (SN_Ups hC1 hC hp a) (SN_eps hp)

/-- **Peeling the main term.** -/
theorem hasSum_Mn_peel (u v : ℝ) {p a h' k : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hh' : 1 ≤ h')
    (hph : ¬ p ∣ h') {α : ℝ} (hα : 0 < α) :
    HasSum (fun j : ℕ => ((gseq p a j : ℝ) : ℂ) * ((p : ℂ) ^ (-(1 - (v : ℂ) * I))) ^ j *
      Mn u v h' k (α * (p : ℝ) ^ (2 * j))) (Mn u v (p ^ a * h') k α) := by
  obtain ⟨C, hC1, hC⟩ := lam_bound
  set x : ℂ := (p : ℂ) ^ (-(1 - (v : ℂ) * I)) with hx
  have hs : (1 - (v : ℂ) * I).re = 1 := by simp
  have hxn := norm_p_cpow hp hs
  have hSN := SN_gps hp a
  -- the real series `Σ g_j p^{−j} = ρ_p(a)`
  have hA : HasSum (fun j : ℕ => (((gseq p a j * ((p : ℝ)⁻¹) ^ j) : ℝ) : ℂ)) (rhoP p a : ℂ) := by
    have h1 : HasSum (fun j : ℕ => gseq p a j * ((p : ℝ)⁻¹) ^ j) (rhoP p a) := by
      rw [← Gg_gseq hC1 hC hp a]
      exact hSN.of_norm.hasSum
    exact Complex.hasSum_ofReal.2 h1
  -- the complex series `Σ g_j p^{−j(1−iv)} = N_p/D_p`
  have hB : HasSum (fun j : ℕ => ((gseq p a j : ℝ) : ℂ) * x ^ j) (NpC p a (1 - v * I) / DpC p (1 - v * I)) := by
    rw [← (evC_gps hp a hs).2]
    exact (SNC hxn hSN).of_norm.hasSum
  have hP : ∀ j : ℕ, Pmain u v (α * (p : ℝ) ^ (2 * j)) * x ^ j = Pmain u v α * ((((p : ℝ)⁻¹) ^ j : ℝ) : ℂ) := by
    intro j
    unfold Pmain
    have := pw_identity hp hα v j
    rw [← hx] at this
    calc _ = (c0 : ℂ) * (Gsh u (u + v) (((v / 2 : ℝ) : ℂ) * I) *
          (((α * (p : ℝ) ^ (2 * j) : ℝ) : ℂ) ^ (-(((v / 2 : ℝ) : ℂ) * I)) * x ^ j) *
          Real.exp (-(v / 2) ^ 2)) / ((v : ℂ) * I) := by ring
      _ = _ := by rw [this]; ring
  have hsum := (hA.mul_left (((rho h' * rho k : ℝ) : ℂ) * Pmain u v α)).add
    (hB.mul_left (rhoC h' (1 - v * I) * rhoC k (1 - v * I) * Lmain v))
  convert hsum using 1
  · funext j
    unfold Mn
    rw [show ((gseq p a j : ℝ) : ℂ) * x ^ j * (((rho h' * rho k : ℝ) : ℂ) * Pmain u v (α * (p : ℝ) ^ (2 * j)) +
        rhoC h' (1 - v * I) * rhoC k (1 - v * I) * Lmain v) =
        ((gseq p a j : ℝ) : ℂ) * ((rho h' * rho k : ℝ) : ℂ) * (Pmain u v (α * (p : ℝ) ^ (2 * j)) * x ^ j) +
        rhoC h' (1 - v * I) * rhoC k (1 - v * I) * Lmain v * (((gseq p a j : ℝ) : ℂ) * x ^ j) by ring,
      hP j]
    push_cast; ring
  · unfold Mn
    rw [rho_peel hp ha hh' hph, rhoC_peel hp ha hh' hph]
    push_cast; ring

end RamanujanTau.SelbergKeyDiag2
