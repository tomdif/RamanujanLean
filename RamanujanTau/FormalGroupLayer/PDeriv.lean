/-
# Partial derivatives of multivariable power series

`pd i f` has coefficients `coeff e (pd i f) = coeff (e + eᵢ) f · (eᵢ + 1)`. It is compatible with
`MvPolynomial.pderiv` on polynomials, and it is a derivation (Leibniz rule, via truncation).
-/
import Mathlib

set_option autoImplicit false

namespace MvPowerSeries
open Finsupp

variable {σ R : Type*} [CommRing R] [DecidableEq σ]
set_option linter.unusedSectionVars false

/-- the partial derivative `∂/∂Xᵢ`. -/
noncomputable def pd (i : σ) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun e => coeff (e + single i 1) f * (e i + 1)

lemma coeff_pd (i : σ) (f : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    coeff e (pd i f) = coeff (e + single i 1) f * (e i + 1) := rfl

lemma pd_add (i : σ) (f g : MvPowerSeries σ R) : pd i (f + g) = pd i f + pd i g := by
  ext e; simp [coeff_pd, add_mul]

lemma pd_sub (i : σ) (f g : MvPowerSeries σ R) : pd i (f - g) = pd i f - pd i g := by
  ext e; simp [coeff_pd, sub_mul]

lemma pd_smul (i : σ) (c : R) (f : MvPowerSeries σ R) : pd i (c • f) = c • pd i f := by
  ext e; simp [coeff_pd, mul_assoc]

/-- coefficient formula for `MvPolynomial.pderiv`. -/
lemma _root_.MvPolynomial.coeff_pderiv' (i : σ) (p : MvPolynomial σ R) (e : σ →₀ ℕ) :
    (MvPolynomial.pderiv i p).coeff e = p.coeff (e + single i 1) * (e i + 1) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hs : s = e + single i 1
    · subst hs
      simp [add_tsub_cancel_right]
    · rw [if_neg hs, zero_mul]
      split_ifs with h
      · -- `s − eᵢ = e` but `s ≠ e + eᵢ` forces `s i = 0`
        have hsi : s i = 0 := by
          by_contra hne
          apply hs
          rw [← h]; ext j
          simp only [coe_add, coe_tsub, Pi.add_apply, Pi.sub_apply, single_apply]
          split_ifs with hij
          · subst hij; omega
          · omega
        simp [hsi]
      · rfl
  | add p q hp hq => simp [hp, hq, add_mul]

lemma pd_coe (i : σ) (p : MvPolynomial σ R) : pd i (p : MvPowerSeries σ R) = (MvPolynomial.pderiv i p : _) := by
  ext e; rw [coeff_pd, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe, MvPolynomial.coeff_pderiv']

/-- a coefficient of a product only sees the coefficients of the factors below it. -/
lemma coeff_mul_congr {A A' B B' : MvPowerSeries σ R} (e : σ →₀ ℕ)
    (hA : ∀ m ≤ e, coeff m A = coeff m A') (hB : ∀ m ≤ e, coeff m B = coeff m B') :
    coeff e (A * B) = coeff e (A' * B') := by
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.mem_antidiagonal.mp hx
  rw [hA x.1 (hx' ▸ le_self_add), hB x.2 (hx' ▸ le_add_self)]

/-- **Leibniz rule**. -/
lemma pd_mul (i : σ) (f g : MvPowerSeries σ R) : pd i (f * g) = pd i f * g + f * pd i g := by
  ext e
  set n := e + single i 1 with hn_def
  set F := trunc' R n f
  set G := trunc' R n g
  have hF : ∀ m ≤ n, coeff m f = coeff m (F : MvPowerSeries σ R) := fun m hm => by
    rw [MvPolynomial.coeff_coe, coeff_trunc', if_pos hm]
  have hG : ∀ m ≤ n, coeff m g = coeff m (G : MvPowerSeries σ R) := fun m hm => by
    rw [MvPolynomial.coeff_coe, coeff_trunc', if_pos hm]
  have hen : e ≤ n := le_self_add
  have hpdF : ∀ m ≤ e, coeff m (pd i f) = coeff m (pd i (F : MvPowerSeries σ R)) := fun m hm => by
    rw [coeff_pd, coeff_pd, hF _ (by rw [hn_def]; exact add_le_add hm le_rfl)]
  have hpdG : ∀ m ≤ e, coeff m (pd i g) = coeff m (pd i (G : MvPowerSeries σ R)) := fun m hm => by
    rw [coeff_pd, coeff_pd, hG _ (by rw [hn_def]; exact add_le_add hm le_rfl)]
  have hL : coeff e (pd i (f * g)) = coeff e (pd i ((F : MvPowerSeries σ R) * (G : MvPowerSeries σ R))) := by
    rw [coeff_pd, coeff_pd, ← coeff_trunc'_mul_trunc'_eq_coeff_mul n f g le_rfl, ← MvPolynomial.coe_mul,
      MvPolynomial.coeff_coe]
  rw [hL, ← MvPolynomial.coe_mul, pd_coe, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
    MvPolynomial.coe_add, MvPolynomial.coe_mul, MvPolynomial.coe_mul, ← pd_coe, ← pd_coe, map_add, map_add]
  rw [add_comm]
  congr 1
  · rw [mul_comm (G : MvPowerSeries σ R)]
    exact (coeff_mul_congr e hpdF fun m hm => hG m (le_trans hm hen)).symm
  · exact (coeff_mul_congr e (fun m hm => hF m (le_trans hm hen)) hpdG).symm

lemma pd_X (i j : σ) : pd i (X j : MvPowerSeries σ R) = if j = i then 1 else 0 := by
  have := pd_coe (R := R) i (MvPolynomial.X j)
  rw [MvPolynomial.coe_X] at this
  rw [this, MvPolynomial.pderiv_X]
  split_ifs with h
  · subst h; simp
  · simp [Ne.symm h]

lemma pd_C (i : σ) (c : R) : pd i (C c : MvPowerSeries σ R) = 0 := by
  have := pd_coe (R := R) i (MvPolynomial.C c)
  rw [MvPolynomial.coe_C] at this
  rw [this, MvPolynomial.pderiv_C, MvPolynomial.coe_zero]

/-- `pd i` as an `R`-derivation. -/
noncomputable def pdDer (i : σ) : Derivation R (MvPowerSeries σ R) (MvPowerSeries σ R) where
  toFun := pd i
  map_add' := pd_add i
  map_smul' c f := by
    rw [RingHom.id_apply, show c • f = C c * f from (smul_eq_C_mul f c), pd_mul, pd_C, zero_mul,
      zero_add, smul_eq_C_mul]
  map_one_eq_zero' := by show pd i 1 = 0; rw [← map_one C, pd_C]
  leibniz' f g := by show pd i (f * g) = f • pd i g + g • pd i f; rw [pd_mul, smul_eq_mul, smul_eq_mul, add_comm, mul_comm f, mul_comm g]

lemma pdDer_apply (i : σ) (f : MvPowerSeries σ R) : pdDer i f = pd i f := rfl

end MvPowerSeries
