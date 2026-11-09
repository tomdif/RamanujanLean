/-
# The ten fifth-order mock theta functions as locally finite sums

Definitions in the style of `RamanujanTau/Watson/` (`osum` of a locally finite family). The repository already
has `f₀` (`MockTheta5.JTP.f0`, `Watson.f0w`), `f₁` (`MockTheta5.JTP.f1`), `F₀` (`Watson.F0w`),
`φ₀(−q)` (`Watson.P0w`) and `χ₀` (`MockTheta5.Formal.chi0`, `Watson.chiA`). This file adds the rest:

* `f1w  = Σ q^{n²+n}/(−q;q)_n`                (= `MockTheta5.JTP.f1`, see `f1w_eq`)
* `F1w  = Σ q^{2n²+2n}/(q;q²)_{n+1}`
* `phi0w = Σ q^{n²}(−q;q²)_n`,   `phi1w = Σ q^{(n+1)²}(−q;q²)_n`
* `P1w  = φ₁(−q) = Σ (−1)^{n+1} q^{(n+1)²}(q;q²)_n`
* `psi0w = Σ q^{(n+1)(n+2)/2}(−q;q)_n`,   `psi1w = Σ q^{n(n+1)/2}(−q;q)_n`
* `chi1w = Σ qⁿ/(q^{n+1};q)_{n+1}`

and the substitution `q ↦ −q` (`negQ`, i.e. `PowerSeries.rescale (−1)`), with
`negQ phi0w = P0w` and `negQ phi1w = P1w`.
-/
import RamanujanTau.Watson.F0Rel

set_option autoImplicit false

namespace MockTheta5All
open PowerSeries Watson Finset

/-- `f₁(q) = Σ q^{n²+n}/(−q;q)_n`. -/
noncomputable def f1w : PowerSeries ℤ := osum fun n => X ^ (n * n + n) * Ring.inverse (FP (-1) 1 1 n)

/-- `F₁(q) = Σ q^{2n²+2n}/(q;q²)_{n+1}`. -/
noncomputable def F1w : PowerSeries ℤ := osum fun n => X ^ (2 * (n * n + n)) * Ring.inverse (FP 1 1 2 (n + 1))

/-- `φ₀(q) = Σ q^{n²}(−q;q²)_n`. -/
noncomputable def phi0w : PowerSeries ℤ := osum fun n => X ^ (n * n) * FP (-1) 1 2 n

/-- `φ₁(q) = Σ q^{(n+1)²}(−q;q²)_n`. -/
noncomputable def phi1w : PowerSeries ℤ := osum fun n => X ^ ((n + 1) * (n + 1)) * FP (-1) 1 2 n

/-- `φ₁(−q) = Σ (−1)^{n+1} q^{(n+1)²}(q;q²)_n`. -/
noncomputable def P1w : PowerSeries ℤ :=
  osum fun n => (((-1) ^ (n + 1) : ℤ) : PowerSeries ℤ) * X ^ ((n + 1) * (n + 1)) * FP 1 1 2 n

/-- `ψ₀(q) = Σ q^{(n+1)(n+2)/2}(−q;q)_n`. -/
noncomputable def psi0w : PowerSeries ℤ := osum fun n => X ^ ((n + 2).choose 2) * FP (-1) 1 1 n

/-- `ψ₁(q) = Σ q^{n(n+1)/2}(−q;q)_n`. -/
noncomputable def psi1w : PowerSeries ℤ := osum fun n => X ^ ((n + 1).choose 2) * FP (-1) 1 1 n

/-- `χ₁(q) = Σ qⁿ/(q^{n+1};q)_{n+1}`. -/
noncomputable def chi1w : PowerSeries ℤ := osum fun n => X ^ n * Ring.inverse (FP 1 (n + 1) 1 (n + 1))

/-! ### the families are locally finite (so the `osum`s are honest sums) -/

lemma choose_succ_two (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right]

lemma choose_succ_succ_two (n : ℕ) : (n + 2).choose 2 = 1 + 2 * n + n.choose 2 := by
  rw [choose_succ_two (n + 1), choose_succ_two n]; ring

lemma LF_f1w : LF fun n => X ^ (n * n + n) * Ring.inverse (FP (-1) 1 1 n) := LF_Xpow_mul fun n => by nlinarith
lemma LF_F1w : LF fun n => X ^ (2 * (n * n + n)) * Ring.inverse (FP 1 1 2 (n + 1)) :=
  LF_Xpow_mul fun n => by nlinarith
lemma LF_phi0w : LF fun n => X ^ (n * n) * FP (-1) 1 2 n := LF_Xpow_mul fun n => by nlinarith
lemma LF_phi1w : LF fun n => X ^ ((n + 1) * (n + 1)) * FP (-1) 1 2 n := LF_Xpow_mul fun n => by nlinarith
lemma LF_psi0w : LF fun n => X ^ ((n + 2).choose 2) * FP (-1) 1 1 n :=
  LF_Xpow_mul fun n => by rw [choose_succ_succ_two]; omega
lemma LF_psi1w : LF fun n => X ^ ((n + 1).choose 2) * FP (-1) 1 1 n :=
  LF_Xpow_mul fun n => by rw [choose_succ_two]; omega
lemma LF_chi1w : LF fun n => X ^ n * Ring.inverse (FP 1 (n + 1) 1 (n + 1)) := LF_Xpow_mul fun n => le_refl n
lemma LF_P1w : LF fun n => (((-1) ^ (n + 1) : ℤ) : PowerSeries ℤ) * X ^ ((n + 1) * (n + 1)) * FP 1 1 2 n :=
  LF.of_nat fun n k hk => by
    rw [show (((-1) ^ (n + 1) : ℤ) : PowerSeries ℤ) * X ^ ((n + 1) * (n + 1)) * FP 1 1 2 n
      = X ^ ((n + 1) * (n + 1)) * ((((-1) ^ (n + 1) : ℤ) : PowerSeries ℤ) * FP 1 1 2 n) by ring,
      coeff_X_pow_mul', if_neg (by nlinarith)]

/-! ### `q ↦ −q` -/

/-- the substitution `q ↦ −q`. -/
noncomputable def negQ : PowerSeries ℤ →+* PowerSeries ℤ := rescale (-1 : ℤ)

lemma negQ_X : negQ X = -X := by simp [negQ]

lemma negQ_osum (f : ℕ → PowerSeries ℤ) : negQ (osum f) = osum fun n => negQ (f n) := by
  ext k
  simp only [negQ, coeff_rescale, coeff_osum]
  exact mul_finsum _ _

lemma negQ_FP (c : ℤ) (a b n : ℕ) (hab : Odd a ∧ Even b) : negQ (FP c a b n) = FP (-c) a b n := by
  simp only [FP, map_prod, map_sub, map_one, map_mul, map_pow, negQ_X, map_intCast]
  refine prod_congr rfl fun k _ => ?_
  have ho : Odd (a + b * k) := hab.1.add_even (hab.2.mul_right k)
  rw [ho.neg_pow]; push_cast; ring

lemma negQ_phi0w : negQ phi0w = P0w := by
  rw [phi0w, negQ_osum, P0w]
  refine osum_ext fun n => ?_
  rw [map_mul, map_pow, negQ_X, negQ_FP _ _ _ _ ⟨odd_one, even_two⟩, neg_neg, neg_pow]
  have : ((-1 : PowerSeries ℤ)) ^ (n * n) = (((-1) ^ n : ℤ) : PowerSeries ℤ) := by
    push_cast
    rcases Nat.even_or_odd n with h | h
    · rw [(h.mul_right n).neg_one_pow, h.neg_one_pow]
    · rw [(h.mul h).neg_one_pow, h.neg_one_pow]
  rw [this]

lemma negQ_phi1w : negQ phi1w = P1w := by
  rw [phi1w, negQ_osum, P1w]
  refine osum_ext fun n => ?_
  rw [map_mul, map_pow, negQ_X, negQ_FP _ _ _ _ ⟨odd_one, even_two⟩, neg_neg, neg_pow]
  have : ((-1 : PowerSeries ℤ)) ^ ((n + 1) * (n + 1)) = (((-1) ^ (n + 1) : ℤ) : PowerSeries ℤ) := by
    push_cast
    rcases Nat.even_or_odd (n + 1) with h | h
    · rw [(h.mul_right (n + 1)).neg_one_pow, h.neg_one_pow]
    · rw [(h.mul h).neg_one_pow, h.neg_one_pow]
  rw [this]

end MockTheta5All
