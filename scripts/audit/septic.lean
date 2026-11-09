/-
Audit for Ramanujan's septic theta identity, Lost Notebook Entry 1.1(i)
(see docs/SEPTIC_ENTRY_1_1.md). Expected: every theorem depends only on
[propext, Classical.choice, Quot.sound].
-/
import RamanujanTau.Septic.Dissection
import RamanujanTau.Septic.ProductForm
import RamanujanTau.Septic.Page206

set_option autoImplicit false

open PowerSeries RamanujanTau.Septic

/-- Headline restated: `φ(q)/φ(q⁴⁹) = 1 + u + v + w` (Entry 1.1(i) with `q ↦ q⁷`). -/
example : phi * Ring.inverse (ramF 49 49) =
    1 + 2 * X * ramF 35 63 * Ring.inverse (ramF 49 49)
      + 2 * X ^ 4 * ramF 21 77 * Ring.inverse (ramF 49 49)
      + 2 * X ^ 9 * ramF 7 91 * Ring.inverse (ramF 49 49) :=
  septic_entry_1_1_i

/-- `φ` really is `Σ_{n∈ℤ} q^{n²}` and `f(q^α,q^β)` the full bilateral sum (no truncation). -/
example (N : ℕ) : coeff N phi = (Nat.card {n : ℤ // n * (n + 1) + n * (n - 1) = 2 * (N : ℤ)} : ℤ) := by
  rw [phi, coeff_ramF le_rfl le_rfl]; simp [ex2]

#print axioms septic_entry_1_1_i
#print axioms phi_seven_dissection
#print axioms card_sq_seven
#print axioms coeff_ramF
#print axioms ramF_product
#print axioms septic_product_forms
#print axioms rescale_Pfin

-- page 206: statement only (named Prop, unproved; see docs/SEPTIC_ENTRY_1_1.md)
#check (Page206Evaluation : Prop)
