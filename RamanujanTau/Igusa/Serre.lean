import RamanujanTau.ModP.SwinnertonDyer

/-!
# The Serre derivation on `R[X₀,X₁]` and the two Hasse relations (Swinnerton-Dyer)

* `theta f = q df/dq` on `R⟦q⟧`; `theta_mul` (Leibniz), `map_theta`.
* `E2 R = 1 − 24 Σ σ₁(n) qⁿ`.
* `RamanujanODE`: **Ramanujan's differential equations** over `ℤ`,
    `3 θE₄ = E₂E₄ − E₆`, `2 θE₆ = E₂E₆ − E₄²`, `12 θE₂ = E₂² − E₄`.
  This classical theorem is *not* proved here; it is the one hypothesis of the Igusa layer.
* `serreD P = −4 X₁ ∂₀P − 6 X₀² ∂₁P` (the Serre derivative `12θ − kE₂` on isobaric polynomials):
  `ev_serreD`: `12 θ(P(E₄,E₆)) = k E₂ P(E₄,E₆) + (serreD P)(E₄,E₆)` for `P` of weight `k`.
* `euler`: `4X₀∂₀P + 6X₁∂₁P = kP` for `P` isobaric of weight `k`; `iso_serreD`: `serreD` raises weight by 2.
* Over `𝔽_p` (`p ≥ 5`), with `Ā = hasseBar`:
  `ev_serreD_hasseBar`: `(∂Ā)(E₄,E₆) = E₂`, and **`serreD_serreD_hasseBar`: `∂∂Ā = −X₀ Ā`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Igusa
open MvPolynomial ModP

section Theta
variable {R : Type*} [CommRing R]

/-- `θ = q d/dq`. -/
noncomputable def theta (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => (n : R) * PowerSeries.coeff n f

lemma coeff_theta (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (theta f) = (n : R) * PowerSeries.coeff n f := by
  rw [theta, PowerSeries.coeff_mk]

lemma theta_add (f g : PowerSeries R) : theta (f + g) = theta f + theta g := by
  ext n; simp [coeff_theta, mul_add]

lemma theta_mul (f g : PowerSeries R) : theta (f * g) = theta f * g + f * theta g := by
  ext n
  rw [map_add, coeff_theta, PowerSeries.coeff_mul, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [coeff_theta, coeff_theta, ← hx]
  push_cast; ring

lemma theta_C (c : R) : theta (PowerSeries.C c) = 0 := by
  ext n; rw [coeff_theta, PowerSeries.coeff_C]; split_ifs with h <;> simp [h]

lemma theta_one : theta (1 : PowerSeries R) = 0 := by
  rw [← map_one PowerSeries.C]; exact theta_C 1

lemma theta_natCast_mul (k : ℕ) (f : PowerSeries R) : theta ((k : PowerSeries R) * f) = k * theta f := by
  rw [theta_mul, ← map_natCast PowerSeries.C, theta_C]; ring

lemma map_theta {S : Type*} [CommRing S] (φ : R →+* S) (f : PowerSeries R) :
    PowerSeries.map φ (theta f) = theta (PowerSeries.map φ f) := by
  ext n; simp [coeff_theta]

end Theta

/-! ### `E₂` and Ramanujan's equations -/

/-- `E₂ = 1 − 24 Σ σ₁(n) qⁿ` over `ℤ`. -/
noncomputable def e2Z : PowerSeries ℤ :=
  1 - 24 * PowerSeries.mk (fun n => (ArithmeticFunction.sigma 1 n : ℤ))

/-- `E₂ ∈ R⟦q⟧`. -/
noncomputable def E2 (R : Type*) [CommRing R] : PowerSeries R := PowerSeries.map (Int.castRingHom R) e2Z

/-- **Ramanujan's differential equations** (formal q-series over `ℤ`). Classical; assumed. -/
def RamanujanODE : Prop :=
  3 * theta (E4 ℤ) = E2 ℤ * E4 ℤ - E6 ℤ ∧
  2 * theta (E6 ℤ) = E2 ℤ * E6 ℤ - E4 ℤ ^ 2 ∧
  12 * theta (E2 ℤ) = E2 ℤ ^ 2 - E4 ℤ

section ODE
variable {R : Type*} [CommRing R]

lemma map_E2 {S : Type*} [CommRing S] (φ : R →+* S) : PowerSeries.map φ (E2 R) = E2 S := by
  rw [E2, E2, psmap_map, show φ.comp (Int.castRingHom R) = Int.castRingHom S from RingHom.ext_int _ _]

lemma ode_map (hR : RamanujanODE) :
    3 * theta (E4 R) = E2 R * E4 R - E6 R ∧
    2 * theta (E6 R) = E2 R * E6 R - E4 R ^ 2 ∧
    12 * theta (E2 R) = E2 R ^ 2 - E4 R := by
  obtain ⟨h1, h2, h3⟩ := hR
  set φ := Int.castRingHom R
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (PowerSeries.map φ) h1
    simpa [map_theta, map_E4, map_E6, map_E2, map_ofNat] using this
  · have := congrArg (PowerSeries.map φ) h2
    simpa [map_theta, map_E4, map_E6, map_E2, map_ofNat] using this
  · have := congrArg (PowerSeries.map φ) h3
    simpa [map_theta, map_E4, map_E6, map_E2, map_ofNat] using this

/-- Chain rule for `θ ∘ ev`. -/
lemma theta_ev (P : MvPolynomial (Fin 2) R) :
    theta (ev R P) = ev R (pderiv 0 P) * theta (E4 R) + ev R (pderiv 1 P) * theta (E6 R) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [ev, aeval_C, Algebra.algebraMap_eq_smul_one, pderiv_C, map_zero, zero_mul, add_zero]
    rw [show a • (1 : PowerSeries R) = PowerSeries.C a by
      rw [Algebra.smul_def, mul_one]; rfl, theta_C]
  | add p q hp hq =>
    rw [map_add, theta_add, hp, hq, map_add, map_add, map_add, map_add]; ring
  | mul_X p i hp =>
    rw [map_mul, theta_mul, hp, Derivation.leibniz, Derivation.leibniz]
    fin_cases i
    · simp [pderiv_X]; ring
    · simp [pderiv_X]; ring

end ODE

/-! ### The Serre derivation and Euler's identity -/

section Serre
variable {R : Type*} [CommRing R]

/-- `∂P = −4 X₁ ∂P/∂X₀ − 6 X₀² ∂P/∂X₁`. -/
noncomputable def serreD (P : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  -(4 * X 1 * pderiv 0 P) - 6 * X 0 ^ 2 * pderiv 1 P

lemma map_serreD {S : Type*} [CommRing S] (φ : R →+* S) (P : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (serreD P) = serreD (MvPolynomial.map φ P) := by
  simp [serreD, pderiv_map]

lemma X_mul_pderiv_monomial (i : Fin 2) (s : Fin 2 →₀ ℕ) (a : R) :
    X i * pderiv i (monomial s a) = monomial s (a * s i) := by
  rw [pderiv_monomial]
  by_cases h : s i = 0
  · simp [h]
  · rw [X, monomial_mul, one_mul]
    rw [add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))]

lemma X_mul_pderiv_eq (i : Fin 2) (P : MvPolynomial (Fin 2) R) :
    X i * pderiv i P = ∑ s ∈ P.support, monomial s (P.coeff s * s i) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => X_mul_pderiv_monomial i s _

lemma iso_X_mul_pderiv {P : MvPolynomial (Fin 2) R} {k : ℕ} (hP : Iso P k) (i : Fin 2) :
    Iso (X i * pderiv i P) k := by
  rw [X_mul_pderiv_eq]
  apply IsWeightedHomogeneous.sum
  intro s hs
  by_cases h : P.coeff s * s i = 0
  · rw [h, monomial_zero]; exact isWeightedHomogeneous_zero _ _ _
  · exact isWeightedHomogeneous_monomial _ _ _ (hP (mem_support_iff.mp hs))

/-- **Euler's identity** for the weights `(4, 6)`. -/
theorem euler {P : MvPolynomial (Fin 2) R} {k : ℕ} (hP : Iso P k) :
    4 * (X 0 * pderiv 0 P) + 6 * (X 1 * pderiv 1 P) = (k : MvPolynomial (Fin 2) R) * P := by
  rw [X_mul_pderiv_eq, X_mul_pderiv_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  conv_rhs => rw [P.as_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hw := hP (mem_support_iff.mp hs)
  rw [weight_wt] at hw
  rw [← hw]
  simp only [← map_ofNat C, ← map_natCast C, C_mul_monomial, ← map_add]
  congr 1; push_cast; ring

lemma iso_of_X_mul {Q : MvPolynomial (Fin 2) R} {i : Fin 2} {m : ℕ} (h : Iso (X i * Q) m) :
    Iso Q (m - wt i) := by
  classical
  intro d hd
  have h1 : (X i * Q).coeff (d + Finsupp.single i 1) ≠ 0 := by
    rw [mul_comm, coeff_mul_X]; exact hd
  have := h h1
  rw [Finsupp.weight_apply] at this ⊢
  rw [Finsupp.sum_add_index' (by simp) (by intros; ring), Finsupp.sum_single_index (by simp)] at this
  rw [← this]; simp [wt]

lemma iso_mul_X_pderiv_aux {P : MvPolynomial (Fin 2) R} {k : ℕ} (hP : Iso P k) :
    Iso (X 1 * pderiv 0 P) (k + 2) ∧ Iso (X 0 ^ 2 * pderiv 1 P) (k + 2) := by
  constructor
  · have h : Iso (X 0 * (X 1 * pderiv 0 P)) (6 + k) := by
      rw [mul_left_comm]
      exact ((isWeightedHomogeneous_X R wt 1).mul (iso_X_mul_pderiv hP 0))
    have := iso_of_X_mul h
    exact iso_of_eq this (by simp [wt]; omega)
  · have h : Iso (X 1 * (X 0 ^ 2 * pderiv 1 P)) (8 + k) := by
      rw [mul_left_comm]
      exact iso_of_eq (((isWeightedHomogeneous_X R wt 0).pow 2).mul (iso_X_mul_pderiv hP 1))
        (by simp [wt])
    have := iso_of_X_mul h
    exact iso_of_eq this (by simp [wt]; omega)

/-- `∂` raises the weight by `2`. -/
theorem iso_serreD {P : MvPolynomial (Fin 2) R} {k : ℕ} (hP : Iso P k) : Iso (serreD P) (k + 2) := by
  obtain ⟨h1, h2⟩ := iso_mul_X_pderiv_aux hP
  unfold serreD
  refine iso_sub ?_ ?_
  · rw [show -(4 * X 1 * pderiv 0 P) = C (-4 : R) * (X 1 * pderiv 0 P) by
      rw [map_neg, map_ofNat]; ring]
    exact h1.C_mul _
  · rw [show 6 * X 0 ^ 2 * pderiv 1 P = C (6 : R) * (X 0 ^ 2 * pderiv 1 P) by
      rw [map_ofNat]; ring]
    exact h2.C_mul _

/-- **The Serre derivative on q-expansions.** -/
theorem ev_serreD (hR : RamanujanODE) {P : MvPolynomial (Fin 2) R} {k : ℕ} (hP : Iso P k) :
    12 * theta (ev R P) = (k : PowerSeries R) * E2 R * ev R P + ev R (serreD P) := by
  obtain ⟨h4, h6, -⟩ := ode_map (R := R) hR
  have he := congrArg (ev R) (euler hP)
  simp only [map_add, map_mul, map_ofNat, map_natCast, ev_X0, ev_X1] at he
  rw [theta_ev]
  simp only [serreD, map_sub, map_neg, map_mul, map_ofNat, map_pow, ev_X0, ev_X1]
  linear_combination (4 * ev R (pderiv 0 P)) * h4 + (6 * ev R (pderiv 1 P)) * h6 + E2 R * he

end Serre

/-! ### The two Hasse relations over `𝔽_p` -/

section Hasse
variable {p : ℕ} [hp : Fact p.Prime]

lemma natCast_p_PS : ((p : ℕ) : PowerSeries (ZMod p)) = 0 := by
  rw [← map_natCast (PowerSeries.C (R := ZMod p)), ZMod.natCast_self, map_zero]

/-- `∂Ā` (isobaric of weight `p + 1`); its q-expansion is `E₂`. -/
noncomputable def hasseB (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) : MvPolynomial (Fin 2) (ZMod p) :=
  serreD (hasseBar p hp5)

lemma iso_hasseB (hp5 : 5 ≤ p) : Iso (hasseB p hp5) (p + 1) :=
  iso_of_eq (iso_serreD (iso_hasseBar hp5)) (by omega)

theorem ev_hasseB (hR : RamanujanODE) (hp5 : 5 ≤ p) : ev (ZMod p) (hasseB p hp5) = E2 (ZMod p) := by
  have h := ev_serreD (R := ZMod p) hR (iso_hasseBar hp5)
  rw [ev_hasseBar, theta_one, mul_zero, mul_one] at h
  have hc : ((p - 1 : ℕ) : PowerSeries (ZMod p)) = -1 := by
    rw [Nat.cast_sub (by have := hp.out.two_le; omega), natCast_p_PS]; simp
  rw [hc] at h
  rw [hasseB]; linear_combination -h

/-- **Second Hasse relation:** `∂(∂Ā) = −X₀ Ā`. -/
theorem serreD_hasseB (hR : RamanujanODE) (hp5 : 5 ≤ p) :
    serreD (hasseB p hp5) = -(X 0 * hasseBar p hp5) := by
  have h := ev_serreD (R := ZMod p) hR (iso_hasseB hp5)
  obtain ⟨-, -, h2⟩ := ode_map (R := ZMod p) hR
  rw [ev_hasseB hR hp5, h2] at h
  have hc : ((p + 1 : ℕ) : PowerSeries (ZMod p)) = 1 := by
    rw [Nat.cast_add, natCast_p_PS]; simp
  rw [hc] at h
  apply ev_injOn_iso (isUnit_1728_ZMod hp5) (k := p + 3)
  · exact iso_of_eq (iso_serreD (iso_hasseB hp5)) (by omega)
  · have := (isWeightedHomogeneous_X (ZMod p) wt 0).mul (iso_hasseBar hp5)
    rw [show -(X 0 * hasseBar p hp5) = C (-1 : ZMod p) * (X 0 * hasseBar p hp5) by
      rw [map_neg, map_one]; ring]
    exact iso_of_eq (this.C_mul _) (by simp [wt]; omega)
  · rw [map_neg, map_mul, ev_hasseBar, ev_X0]
    linear_combination -h

end Hasse

end Igusa
