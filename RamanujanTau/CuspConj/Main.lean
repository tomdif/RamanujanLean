/-
# `CuspConj/`: the conjugate cusp form `f^ρ` and subconvexity for **every** level-one cusp form

Build: `nice -n 10 lake build RamanujanTau.CuspConj.Main`. See `docs/CUSP_CONJ.md`.

* `cuspConj f : CuspForm 𝒮ℒ k`, `f^ρ(z) = conj f(−z̄)`, `coef_cuspConj : a_{f^ρ}(n) = conj a_f(n)`;
* `eq_reF_add_imF : f = reF f + i • imF f` with real-coefficient `reF f`, `imF f`;
* `fL_add`, `fL_smul`: linearity of `L(f,s)` in `f`;
* **`fL_subconvex_all`**: `‖L(f, k/2+it)‖ ≤ C (1+|t|)^{1/2 − 1/134}` for every `f ∈ S_k(SL₂(ℤ))`
  (no reality hypothesis).
-/
import RamanujanTau.CuspConj.Decomp
import RamanujanTau.SubconvexGeneral3.Main

set_option autoImplicit false

namespace RamanujanTau.CuspConj

open Complex
open RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups

variable {k : ℕ}

/-- `L(f,s) = L(Re f, s) + i L(Im f, s)`. -/
theorem fL_eq_re_add_im (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (s : ℂ) :
    fL f s = fL (reF f) s + I * fL (imF f) s := by
  conv_lhs => rw [eq_reF_add_imF f]
  rw [fL_add _ _ hk, fL_smul]

/-- **Unconditional t-aspect subconvexity for every level-one cusp form** (any weight `k`,
complex coefficients allowed): `‖L(f, k/2+it)‖ ≤ C (1+|t|)^{1/2 − 1/134}`. -/
theorem fL_subconvex_all (f : CuspForm 𝒮ℒ (k : ℤ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 134 : ℝ) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · refine ⟨0, le_rfl, fun t => ?_⟩
    rw [fL_of_eq_zero (eq_zero_of_lt_twelve f (by omega))]; simp
  obtain ⟨C1, hC1, h1⟩ := RamanujanTau.SubconvexGeneral3.fL_subconvex_general134 (reF f) (reF_real f)
  obtain ⟨C2, hC2, h2⟩ := RamanujanTau.SubconvexGeneral3.fL_subconvex_general134 (imF f) (imF_real f)
  refine ⟨C1 + C2, by positivity, fun t => ?_⟩
  rw [fL_eq_re_add_im f hk]
  calc ‖fL (reF f) _ + I * fL (imF f) _‖ ≤ ‖fL (reF f) _‖ + ‖fL (imF f) _‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ C1 * (1 + |t|) ^ (1 / 2 - 1 / 134 : ℝ) + C2 * (1 + |t|) ^ (1 / 2 - 1 / 134 : ℝ) :=
        add_le_add (h1 t) (h2 t)
    _ = (C1 + C2) * (1 + |t|) ^ (1 / 2 - 1 / 134 : ℝ) := by ring

end RamanujanTau.CuspConj

#print axioms RamanujanTau.CuspConj.cuspConj
#print axioms RamanujanTau.CuspConj.coef_cuspConj
#print axioms RamanujanTau.CuspConj.eq_reF_add_imF
#print axioms RamanujanTau.CuspConj.reF_real
#print axioms RamanujanTau.CuspConj.imF_real
#print axioms RamanujanTau.CuspConj.fL_add
#print axioms RamanujanTau.CuspConj.fL_smul
#print axioms RamanujanTau.CuspConj.fL_eq_re_add_im
#print axioms RamanujanTau.CuspConj.fL_subconvex_all
