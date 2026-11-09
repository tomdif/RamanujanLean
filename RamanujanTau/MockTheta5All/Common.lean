/-
# Common bridges for the ten fifth-order identities

* bridges between Watson's `osum` definitions and the repository's definitions (`f1w_eq`);
* the theta quotients `ϑ₄`, `ψ(q²)` in product form;
* the map `ιq : ℤ⟦q⟧ → ℂ((q))` used to compare with the theta identities of `Theta.lean`, and a
  discharger `unit_tac` for the `IsUnit` side conditions of `Ring.inverse`.
-/
import RamanujanTau.Watson.Final
import RamanujanTau.MTC.Final1
import RamanujanTau.MockTheta5All.B1
import RamanujanTau.MockTheta5All.Theta

set_option autoImplicit false

namespace MockTheta5All
open PowerSeries Watson Finset RankProof

lemma f1w_eq : f1w = MockTheta5.JTP.f1 := by
  rw [f1w, osum_eq_mk (fun n k hk => by rw [coeff_X_pow_mul', if_neg (by nlinarith)]),
    MockTheta5.JTP.f1, MockTheta5.JTP.tsumQsqQ]
  congr 1; ext k; congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [sq]
  congr 2
  simp only [FP, MockTheta5.Bailey.mqfac]
  refine prod_congr rfl fun j _ => ?_
  simp; ring_nf

lemma th4w_eq : th4w = Pinf 1 1 * Pinf 1 1 * Ring.inverse (Pinf 2 2) := by
  have hsq := IP_sq 1 (a := 1) (b := 1) le_rfl le_rfl
  norm_num at hsq
  have u1 := uIP (-1) (show 1 ≤ 1 by rfl) (show 1 ≤ 1 by rfl)
  have u2 := uIP 1 (show 1 ≤ 2 by norm_num) (show 1 ≤ 2 by norm_num)
  rw [th4w, ← IP_eq_Pinf, ← IP_eq_Pinf, ← hsq, inv_mul' (uIP 1 le_rfl le_rfl) u1]
  have e := Ring.mul_inverse_cancel _ (uIP 1 (show 1 ≤ 1 by rfl) (show 1 ≤ 1 by rfl))
  linear_combination (IP 1 1 1 * Ring.inverse (IP (-1) 1 1)) * e.symm

lemma psi2w_eq : psi2w = Pinf 4 4 * Ring.inverse (Pinf 2 4) := by
  rw [psi2w, IP_eq_Pinf, IP_eq_Pinf]

/-- `ιq : ℤ⟦q⟧ → ℂ((q))`. -/
noncomputable abbrev ιq : PowerSeries ℤ →+* ALz.L := ALz.ιN Theta.h1

lemma ιq_inv {f : PowerSeries ℤ} (hf : IsUnit f) : ιq (Ring.inverse f) = (ιq f)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← map_mul, Ring.mul_inverse_cancel _ hf, map_one]

lemma ιq_X : ιq X = ALz.mono 1 1 := MTC.ιN_X Theta.h1

lemma ιq_injective : Function.Injective ιq := MTC.ιN_injective Theta.h1

lemma expand_Pinf' (e : ℕ) (he : e ≠ 0) (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) :
    expand e he (Pinf b a) = Pinf (e * b) (e * a) := Watson.expand_Pinf e he b a hb ha

lemma expand_inv' (e : ℕ) (he : e ≠ 0) {f : PowerSeries ℤ} (hf : IsUnit f) :
    expand e he (Ring.inverse f) = Ring.inverse (expand e he f) := expand_inverse e he hf

/-- discharger for `IsUnit (Pinf … * Pinf … ^ k)` and `1 ≤ n`. -/
macro "unit_tac" : tactic =>
  `(tactic| ((repeat' (first | apply IsUnit.mul | apply IsUnit.pow | apply RankProof.isUnit_Pinf)) <;> norm_num))

lemma two_L : (2 : ALz.L) ≠ 0 := by
  intro h
  have h' : ιq 2 = ιq 0 := by rw [map_ofNat, map_zero, h]
  exact two_ne_zero_PS (ιq_injective h')

lemma eq_of_two_mul {a b : ALz.L} (h : 2 * (a - b) = 0) : a = b :=
  sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left two_L)

end MockTheta5All
