/-
# The characteristic polynomial of ψ in `ℤ⟦q⟧`

Evaluate the certified Cayley–Hamilton identity `CH = (q¹¹ − Q)·H` at `q = X` and `c_k = V(c_k)`. Since
`−c₀c₁c₂c₄c₇ = Q` and `V(Q) = X¹¹`, the factor `q¹¹ − Q` vanishes, which gives
`X⁵⁵ Ψ¹¹ + Σ_{j=1}^{11} (−1)ʲ Ẽ_j X^{5j} Ψ^{11−j} = 0` with `Ψ = E(q)/E(q¹²¹)`.
-/
import RamanujanTau.Atkin11DissectPS
import RamanujanTau.Atkin11Cert.CharPoly

set_option autoImplicit false

namespace Atkin11
open PowerSeries Atkin11Cert

/-- the evaluation point `(q, c₀, c₁, c₂, c₄, c₇) = (X, V c₀, …)`. -/
noncomputable def x6 : List PS := [X, V cP0, V cP1, V cP2, V cP4, V cP7]

/-- `Ψ = Σ_k q^k V(c_k)`; by the dissection, `E₁ = E₁₂₁ Ψ`. -/
noncomputable def Ψd : PS := V cP0 + X * V cP1 + X ^ 2 * V cP2 + X ^ 4 * V cP4 + X ^ 5 + X ^ 7 * V cP7

lemma E1_eq_Ψd : E1 = E121 * Ψd := E_dissect_PS

/-- the Laurent-free coefficients `Ẽ_j = Q⁵ e_j(ψ)` at `Q = X`. -/
noncomputable def Et (p : SPoly6.Poly) : PS := SPoly6.evalP [X, cP0, cP1, cP2, cP4, cP7] p

lemma unit_pair {u : PS} (hu : IsUnit u) : u * Ring.inverse u = 1 := Ring.mul_inverse_cancel u hu

/-- `c₀c₁c₂c₄c₇ = −Q`. -/
lemma prod_cP : cP0 * cP1 * cP2 * cP4 * cP7 = -X := by
  have h1 := unit_pair (isUnit_ηP (a := 1) le_rfl (by norm_num))
  have h2 := unit_pair (isUnit_ηP (a := 2) (by norm_num) (by norm_num))
  have h3 := unit_pair (isUnit_ηP (a := 3) (by norm_num) (by norm_num))
  have h4 := unit_pair (isUnit_ηP (a := 4) (by norm_num) (by norm_num))
  have h5 := unit_pair (isUnit_ηP (a := 5) (by norm_num) (by norm_num))
  set e1 := ηP 1 * Ring.inverse (ηP 1)
  set e2 := ηP 2 * Ring.inverse (ηP 2)
  set e3 := ηP 3 * Ring.inverse (ηP 3)
  set e4 := ηP 4 * Ring.inverse (ηP 4)
  set e5 := ηP 5 * Ring.inverse (ηP 5)
  have : cP0 * cP1 * cP2 * cP4 * cP7 = -X * (e1 * e2 * e3 * e4 * e5) := by
    simp only [cP0, cP1, cP2, cP4, cP7, e1, e2, e3, e4, e5]; ring
  rw [this]
  linear_combination (-X) * (e2 * e3 * e4 * e5 * h1 + e3 * e4 * e5 * h2 + e4 * e5 * h3 + e5 * h4 + h5)

lemma V_X' : V (X : PS) = X ^ 11 := by simp [ex]

lemma eval_Psi : SPoly6.evalP x6 CH_Psi = Ψd := by
  simp [CH_Psi, CH_Psi_0, SPoly6.ofPacked, SPoly6.decTerm, SPoly6.evalP, SPoly6.evalM, SPoly6.dec, SPoly6.evalL,
    x6, Ψd]
  ring

lemma eval_D : SPoly6.evalP x6 CH_D = 0 := by
  have h : V cP0 * V cP1 * V cP2 * V cP4 * V cP7 = -X ^ 11 := by
    simp only [← map_mul, prod_cP, map_neg, V_X']
  simp [CH_D, SPoly6.evalP, SPoly6.evalM, SPoly6.dec, SPoly6.evalL, x6]
  linear_combination h

lemma eval_H0 : SPoly6.evalP x6 CH_H0 = X ^ 55 := by
  have h : V cP0 * V cP1 * V cP2 * V cP4 * V cP7 = -X ^ 11 := by
    simp only [← map_mul, prod_cP, map_neg, V_X']
  simp [CH_H0, CH_H0_0, SPoly6.ofPacked, SPoly6.decTerm, SPoly6.evalP, SPoly6.evalM, SPoly6.dec, SPoly6.evalL, x6]
  linear_combination (-(V cP0 * V cP1 * V cP2 * V cP4 * V cP7) ^ 4 + (V cP0 * V cP1 * V cP2 * V cP4 * V cP7) ^ 3 * X ^ 11
    - (V cP0 * V cP1 * V cP2 * V cP4 * V cP7) ^ 2 * X ^ 22 + (V cP0 * V cP1 * V cP2 * V cP4 * V cP7) * X ^ 33
    - X ^ 44) * h

/-- one Horner step. -/
lemma horner (Hp Hn E : SPoly6.Poly) (k : ℕ) (s : ℤ)
    (h : SPoly6.certifyR [(Hp, CH_Psi), (E, [(k, s)])] Hn = true) (hk : k < 1024) :
    SPoly6.evalP x6 Hn = SPoly6.evalP x6 Hp * Ψd + SPoly6.evalP x6 E * ((s : PS) * X ^ k) := by
  rw [SPoly6.certifyR_sound x6 _ _ h]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [eval_Psi]
  have hd : SPoly6.dec k = [k, 0, 0, 0, 0, 0] := by
    simp only [SPoly6.dec, List.cons.injEq, and_true]; omega
  congr 1
  simp [SPoly6.evalP, SPoly6.evalM, hd, SPoly6.evalL, x6]

end Atkin11
