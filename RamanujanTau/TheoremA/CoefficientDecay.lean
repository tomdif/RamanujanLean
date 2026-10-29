import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic

/-!
# Exponential decay from vanishing q-coefficients

This works at any positive cusp width. The proof factors the analytic cusp
function by a power of q using its Taylor coefficients.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open UpperHalfPlane Complex Filter Asymptotics
open scoped Real Topology Manifold
local notation "𝕢" => Function.Periodic.qParam

theorem decay_of_coeff_eq_zero {f : ℍ → ℂ} {h : ℝ} (hh : 0 < h)
    (hfper : Function.Periodic (f ∘ ofComplex) h) (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f) (m : ℕ)
    (hc : ∀ n < m, (qExpansion h f).coeff n = 0) :
    f =O[atImInfty] (fun z : ℍ => Real.exp (-2 * π * z.im / h) ^ m) := by
  have ha := analyticAt_cuspFunction_zero hh hfper hfhol hfbdd
  have hd : ∀ n < m, iteratedDeriv n (cuspFunction h f) 0 = 0 := by
    intro n hn
    have he := hc n hn
    rw [qExpansion_coeff] at he
    exact (mul_eq_zero.mp he).resolve_left (inv_ne_zero (by exact_mod_cast n.factorial_ne_zero))
  obtain ⟨G, hG, he⟩ := ha.exists_eq_sum_add_pow_mul m
  have he' : cuspFunction h f = fun q => q ^ m * G q := by
    funext q
    rw [he q]
    have hs : (∑ i ∈ Finset.range m, (q ^ i / i.factorial) •
        iteratedDeriv i (cuspFunction h f) 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hd i (Finset.mem_range.mp hi), smul_zero]
    rw [hs, zero_add, smul_eq_mul]
  have hb : G =O[𝓝 0] (fun _ : ℂ => (1 : ℂ)) := hG.continuousAt.tendsto.isBigO_one ℂ
  have hp : cuspFunction h f =O[𝓝 0] (fun q : ℂ => q ^ m) := by
    rw [he']
    simpa using (isBigO_refl (fun q : ℂ => q ^ m) (𝓝 0)).mul hb
  have ht := (hp.comp_tendsto (qParam_tendsto_atImInfty hh)).norm_right
  simpa only [Function.comp_def, eq_cuspFunction _ hh.ne' hfper,
    norm_pow, Function.Periodic.norm_qParam] using ht

end RamanujanTau.TheoremA
