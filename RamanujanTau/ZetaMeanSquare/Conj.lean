/-
# Conjugation symmetry of `ζ`, and `ζ` is real on the real axis

Mathlib has no `riemannZeta (conj s) = conj (riemannZeta s)`. We prove it by the identity principle on
the connected set `ℂ ∖ {1}`: both sides are holomorphic there and agree on `Re s > 1`, where
`ζ(s) = ∑ n^{−s}` and `conj (n^{conj s}) = n^s`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.ZetaMeanSquare

open Complex Set Filter Topology

/-- **`ζ(s̄) = conj ζ(s)`** for `s ≠ 1`. -/
theorem riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannZeta s) := by
  set g : ℂ → ℂ := fun z => (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) z)) with hg
  have hgd : DifferentiableOn ℂ g {1}ᶜ := by
    intro z hz
    have hz' : (starRingEnd ℂ) z ≠ 1 := by
      intro h; apply hz
      have := congrArg (starRingEnd ℂ) h
      simpa using this
    have h := (differentiableAt_riemannZeta hz').conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  have hev : g =ᶠ[𝓝 (2 : ℂ)] riemannZeta := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hV] with z hz
    have hz : 1 < z.re := hz
    have hz' : 1 < ((starRingEnd ℂ) z).re := by simpa using hz
    simp only [hg]
    rw [zeta_eq_tsum_one_div_nat_cpow hz', zeta_eq_tsum_one_div_nat_cpow hz]
    rw [show (starRingEnd ℂ) (∑' n : ℕ, 1 / (n : ℂ) ^ ((starRingEnd ℂ) z)) =
        star (∑' n : ℕ, 1 / (n : ℂ) ^ ((starRingEnd ℂ) z)) from rfl, tsum_star]
    congr 1; funext n
    have harg : (n : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
    rw [Complex.cpow_conj _ _ harg, Complex.conj_natCast]
    change (starRingEnd ℂ) (1 / (starRingEnd ℂ) ((n : ℂ) ^ z)) = _
    rw [map_div₀, map_one, Complex.conj_conj]
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have heq := (hgd.analyticOnNhd isOpen_compl_singleton).eqOn_of_preconnected_of_eventuallyEq
    analyticOn_riemannZeta hconn h2 hev (show s ∈ ({1}ᶜ : Set ℂ) from hs)
  have := congrArg (starRingEnd ℂ) heq
  simp only [hg, Complex.conj_conj] at this
  exact this

/-- `‖ζ(σ + it)‖ = ‖ζ(σ − it)‖` (away from the pole). -/
lemma norm_riemannZeta_conj (σ t : ℝ) (h : (σ : ℂ) - t * I ≠ 1) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ = ‖riemannZeta ((σ : ℂ) - t * I)‖ := by
  have e : (starRingEnd ℂ) ((σ : ℂ) - t * I) = (σ : ℂ) + t * I := by
    simp [map_sub, Complex.conj_ofReal, Complex.conj_I]
  rw [← e, riemannZeta_conj h, Complex.norm_conj]

/-- `ζ` is real on the real axis (away from `1`). -/
lemma riemannZeta_ofReal_eq_re {p : ℝ} (hp : p ≠ 1) :
    riemannZeta (p : ℂ) = (((riemannZeta (p : ℂ)).re : ℝ) : ℂ) := by
  have hp' : (p : ℂ) ≠ 1 := by exact_mod_cast hp
  have h := riemannZeta_conj hp'
  rw [Complex.conj_ofReal] at h
  exact ((Complex.conj_eq_iff_re).1 h.symm).symm

end RamanujanTau.ZetaMeanSquare
