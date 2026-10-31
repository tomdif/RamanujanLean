import RamanujanTau.BLBound.Recurrence

/-!
# The filtration of level one forms modulo `ℓ`

The least weight of a reduction in a fixed class modulo `ℓ - 1`, and the Swinnerton-Dyer facts about it:
`θ` raises it by exactly `ℓ + 1` when `ℓ` does not divide it, and otherwise lowers `ℓ + 1` by a multiple of `ℓ - 1`.
Also division by `Δ` for isobaric polynomials, which bounds the filtration below by the order at infinity, and the
numerical analysis of a closed theta cycle starting at weight `(ℓ²-1)/2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BLBound
open MvPolynomial ModP Igusa
open MvPolynomial ModP BoylanWebb

noncomputable section

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-! ### The Hasse polynomials -/

/-- `Ā` and `B̄` have no common factor. -/
lemma hasse_relPrime (h5 : 5 ≤ ℓ) : IsRelPrime (hasseBar ℓ h5) (hasseB ℓ h5) := by
  rintro D ⟨R₁, hA⟩ ⟨R₂, hB⟩
  let K := AlgebraicClosure (ZMod ℓ)
  let φ : ZMod ℓ →+* K := ZMod.castHom (dvd_refl ℓ) K
  have hno : ∀ x y : K, (x ≠ 0 ∨ y ≠ 0) → eval ![x, y] (map φ D) ≠ 0 := by
    intro x y hxy h0
    have hAz : eval ![x, y] (Igusa.AF K ℓ h5) = 0 := by
      have e : Igusa.AF K ℓ h5 = map φ (hasseBar ℓ h5) := rfl
      rw [e, hA, map_mul, map_mul, h0, zero_mul]
    have hBz : eval ![x, y] (Igusa.BF K ℓ h5) = 0 := by
      have e : Igusa.BF K ℓ h5 = map φ (hasseB ℓ h5) := rfl
      rw [e, hB, map_mul, map_mul, h0, zero_mul]
    exact RamanujanTau.TheoremA.hasse_companion_separation h5 x y hxy hAz hBz
  obtain ⟨c, hc⟩ := const_of_no_zero _ hno
  have hinj : Function.Injective φ := φ.injective
  have hD0 : D = C (coeff 0 D) := by
    apply MvPolynomial.map_injective φ hinj
    rw [map_C, hc]
    have h0 : φ (coeff 0 D) = c := by
      have := congrArg (coeff 0) hc
      rw [coeff_map] at this
      simpa using this
    rw [h0]
  have hne : coeff 0 D ≠ 0 := by
    intro h0
    apply hasseBar_ne_zero (p := ℓ) h5
    rw [hA, hD0, h0]
    simp
  rw [hD0]
  exact (isUnit_iff_ne_zero.mpr hne).map C

/-- The numerator of `θ`, of weight `k + ℓ + 1`. -/
def thP (h5 : 5 ≤ ℓ) (k : ℕ) (P : MvPolynomial (Fin 2) (ZMod ℓ)) : MvPolynomial (Fin 2) (ZMod ℓ) :=
  C (12 : ZMod ℓ)⁻¹ * (C (k : ZMod ℓ) * hasseB ℓ h5 * P + hasseBar ℓ h5 * serreD P)

lemma iso_thP (h5 : 5 ≤ ℓ) {k : ℕ} {P : MvPolynomial (Fin 2) (ZMod ℓ)} (hP : Iso P k) :
    Iso (thP h5 k P) (k + (ℓ + 1)) := by
  have h1 : Iso (C (k : ZMod ℓ) * hasseB ℓ h5 * P) (k + (ℓ + 1)) := by
    have := ((iso_hasseB h5).C_mul (k : ZMod ℓ)).mul hP
    exact iso_of_eq this (by ring)
  have h2 : Iso (hasseBar ℓ h5 * serreD P) (k + (ℓ + 1)) := by
    have := (iso_hasseBar h5).mul (iso_serreD hP)
    refine iso_of_eq this ?_
    have := hℓ.out.two_le
    omega
  exact (h1.add h2).C_mul _

lemma ev_thP (h5 : 5 ≤ ℓ) {k : ℕ} {P : MvPolynomial (Fin 2) (ZMod ℓ)} (hP : Iso P k) :
    ev (ZMod ℓ) (thP h5 k P) = Igusa.theta (ev (ZMod ℓ) P) := by
  have hs := ev_serreD (R := ZMod ℓ) RamanujanODEProof.ramanujanODE hP
  have h12 := twelve_unit (ℓ := ℓ) h5
  have hE2 := ev_hasseB (p := ℓ) RamanujanODEProof.ramanujanODE h5
  have hunit : (PowerSeries.C (12 : ZMod ℓ)⁻¹) * (12 : PowerSeries (ZMod ℓ)) = 1 := by
    have : (12 : PowerSeries (ZMod ℓ)) = PowerSeries.C (12 : ZMod ℓ) :=
      (map_ofNat (PowerSeries.C (R := ZMod ℓ)) 12).symm
    rw [this, ← map_mul, inv_mul_cancel₀ h12, map_one]
  have hC : ∀ c : ZMod ℓ, ev (ZMod ℓ) (C c) = PowerSeries.C c := ev_C
  rw [thP, map_mul, map_add, map_mul, map_mul, map_mul, hC, hC, hE2, ev_hasseBar, one_mul]
  have e : Igusa.theta (ev (ZMod ℓ) P) = PowerSeries.C (12 : ZMod ℓ)⁻¹ *
      (12 * Igusa.theta (ev (ZMod ℓ) P)) := by
    rw [← mul_assoc, hunit, one_mul]
  rw [e, hs]
  simp

/-- If `Ā ∤ P` and `ℓ ∤ k`, then `Ā` does not divide the numerator of `θ`. -/
lemma not_hasse_dvd_thP (h5 : 5 ≤ ℓ) {k : ℕ} {P : MvPolynomial (Fin 2) (ZMod ℓ)}
    (hnd : ¬ hasseBar ℓ h5 ∣ P) (hk : (k : ZMod ℓ) ≠ 0) : ¬ hasseBar ℓ h5 ∣ thP h5 k P := by
  intro hd
  have h12 := twelve_unit (ℓ := ℓ) h5
  have h1 : hasseBar ℓ h5 ∣ C (k : ZMod ℓ) * hasseB ℓ h5 * P + hasseBar ℓ h5 * serreD P := by
    have e : C (k : ZMod ℓ) * hasseB ℓ h5 * P + hasseBar ℓ h5 * serreD P =
        C (12 : ZMod ℓ) * thP h5 k P := by
      rw [thP, ← mul_assoc, ← C_mul, mul_inv_cancel₀ h12, C_1, one_mul]
    rw [e]
    exact dvd_mul_of_dvd_right hd _
  have h2 : hasseBar ℓ h5 ∣ C (k : ZMod ℓ) * hasseB ℓ h5 * P :=
    (dvd_add_left (dvd_mul_right _ _)).mp h1
  have h3 : hasseBar ℓ h5 ∣ hasseB ℓ h5 * P := by
    have e : hasseB ℓ h5 * P = C (k : ZMod ℓ)⁻¹ * (C (k : ZMod ℓ) * hasseB ℓ h5 * P) := by
      rw [← mul_assoc, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hk, C_1, one_mul]
    rw [e]
    exact dvd_mul_of_dvd_right h2 _
  exact hnd ((hasse_relPrime h5).dvd_of_dvd_mul_left h3)

/-! ### The filtration -/

/-- The least weight of `f` in the class of `r` modulo `ℓ - 1`. -/
def filt (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (f : PowerSeries (ZMod ℓ)) : ℕ :=
  sInf {k | k % (ℓ - 1) = r % (ℓ - 1) ∧ FormBar ℓ k f}

lemma filt_le {r k : ℕ} {f : PowerSeries (ZMod ℓ)} (hm : k % (ℓ - 1) = r % (ℓ - 1)) (hf : FormBar ℓ k f) :
    filt ℓ r f ≤ k := Nat.sInf_le ⟨hm, hf⟩

lemma filt_spec {r k : ℕ} {f : PowerSeries (ZMod ℓ)} (hm : k % (ℓ - 1) = r % (ℓ - 1)) (hf : FormBar ℓ k f) :
    filt ℓ r f % (ℓ - 1) = r % (ℓ - 1) ∧ FormBar ℓ (filt ℓ r f) f := by
  change sInf {k | k % (ℓ - 1) = r % (ℓ - 1) ∧ FormBar ℓ k f} ∈
    {k | k % (ℓ - 1) = r % (ℓ - 1) ∧ FormBar ℓ k f}
  exact Nat.sInf_mem ⟨k, hm, hf⟩

lemma filt_congr {r s : ℕ} (f : PowerSeries (ZMod ℓ)) (h : r % (ℓ - 1) = s % (ℓ - 1)) :
    filt ℓ r f = filt ℓ s f := by
  simp only [filt, h]

lemma theta_class {k r : ℕ} (hℓ2 : 2 ≤ ℓ) (hm : k % (ℓ - 1) = r % (ℓ - 1)) :
    (k + (ℓ + 1)) % (ℓ - 1) = (r + 2) % (ℓ - 1) := by
  have e : k + (ℓ + 1) = k + 2 + (ℓ - 1) := by omega
  rw [e, Nat.add_mod_right, Nat.add_mod, hm, ← Nat.add_mod]

/-- `θ` lowers the filtration against `ℓ + 1` by a multiple of `ℓ - 1`. -/
theorem filt_theta_step (h5 : 5 ≤ ℓ) {r k : ℕ} {f : PowerSeries (ZMod ℓ)}
    (hm : k % (ℓ - 1) = r % (ℓ - 1)) (hf : FormBar ℓ k f) :
    ∃ d : ℕ, filt ℓ r f + (ℓ + 1) = filt ℓ (r + 2) (Igusa.theta f) + (ℓ - 1) * d := by
  obtain ⟨hmod, hrep⟩ := filt_spec hm hf
  have hnext := theta_class (by omega) hmod
  have hle := filt_le hnext (hrep.theta h5)
  have hmnext := (filt_spec hnext (hrep.theta h5)).1
  exact (Nat.modEq_iff_exists_eq_add hle).mp (hmnext.trans hnext.symm)

/-- **Away from weights divisible by `ℓ`, `θ` raises the filtration by exactly `ℓ + 1`.** -/
theorem filt_theta_eq (h5 : 5 ≤ ℓ) {r k : ℕ} {f : PowerSeries (ZMod ℓ)}
    (hm : k % (ℓ - 1) = r % (ℓ - 1)) (hf : FormBar ℓ k f) (hf0 : f ≠ 0)
    (hk : ((filt ℓ r f : ℕ) : ZMod ℓ) ≠ 0) :
    filt ℓ (r + 2) (Igusa.theta f) = filt ℓ r f + (ℓ + 1) := by
  obtain ⟨hmod, P, hP, he⟩ := filt_spec hm hf
  have hP0 : P ≠ 0 := by
    rintro rfl
    apply hf0
    rw [← he, map_zero]
  have hl1 : 1 ≤ ℓ - 1 := by omega
  have hnd : ¬ hasseBar ℓ h5 ∣ P := by
    rintro ⟨R, hR⟩
    obtain ⟨hle, R', hR', hRe⟩ := iso_quotient (iso_hasseBar h5) hP hP0 hR
    have hmod' : (filt ℓ r f - (ℓ - 1)) % (ℓ - 1) = r % (ℓ - 1) := by
      have e : filt ℓ r f - (ℓ - 1) + (ℓ - 1) = filt ℓ r f := Nat.sub_add_cancel hle
      have := Nat.add_mod_right (filt ℓ r f - (ℓ - 1)) (ℓ - 1)
      rw [e] at this
      exact this.symm.trans hmod
    have hlow := filt_le (f := f) hmod' ⟨R', hR', by
      have : ev (ZMod ℓ) P = ev (ZMod ℓ) R' := by rw [hRe, map_mul, ev_hasseBar, one_mul]
      rw [← this, he]⟩
    omega
  have hnext := theta_class (k := filt ℓ r f) (by omega) hmod
  have hT : FormBar ℓ (filt ℓ r f + (ℓ + 1)) (Igusa.theta f) :=
    ⟨thP h5 _ P, iso_thP h5 hP, by rw [ev_thP h5 hP, he]⟩
  have hle := filt_le hnext hT
  refine le_antisymm hle ?_
  by_contra hlt
  push_neg at hlt
  obtain ⟨hmod2, Q, hQ, hQe⟩ := filt_spec hnext hT
  obtain ⟨m, hm'⟩ := (Nat.modEq_iff_exists_eq_add hle).mp (hmod2.trans hnext.symm)
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  have hiso : Iso (thP h5 (filt ℓ r f) P) (filt ℓ (r + 2) (Igusa.theta f) + m * (ℓ - 1)) :=
    iso_of_eq (iso_thP h5 hP) (by rw [hm']; ring)
  have heq := eq_hasseBar_pow_mul h5 hQ hiso (by rw [hQe, ev_thP h5 hP, he])
  apply not_hasse_dvd_thP h5 hnd hk
  rw [heq]
  exact dvd_mul_of_dvd_left (dvd_pow_self _ hm0) _

/-! ### Division by `Δ` -/

/-- The discriminant polynomial. -/
abbrev disc (R : Type*) [CommRing R] : MvPolynomial (Fin 2) R := X 0 ^ 3 - X 1 ^ 2

lemma iso_disc {R : Type*} [CommRing R] : Iso (disc R) 12 := by
  refine iso_sub (iso_of_eq ?_ (by norm_num : 4 * 3 + 6 * 0 = 12)) (iso_of_eq ?_ (by norm_num : 4 * 0 + 6 * 2 = 12))
  · simpa using iso_mono (R := R) 3 0
  · simpa using iso_mono (R := R) 0 2

lemma eval_disc {R : Type*} [CommRing R] : eval (one2 : Fin 2 → R) (disc R) = 0 := by
  simp [disc, one2]

/-- A monomial is the base monomial modulo the discriminant. -/
lemma mono_reduce {R : Type*} [CommRing R] (k : ℕ) (j : ℕ) : ∀ i : ℕ, 4 * i + 6 * j = k →
    ∃ Q : MvPolynomial (Fin 2) R, Iso Q (k - 12) ∧ (k < 12 → Q = 0) ∧
      (X 0 ^ i * X 1 ^ j : MvPolynomial (Fin 2) R) = base k + disc R * Q := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i hij
    by_cases hj : j < 2
    · refine ⟨0, isWeightedHomogeneous_zero _ _ _, fun _ => rfl, ?_⟩
      have e0 : bexp0 k = i := by unfold bexp0; omega
      have e1 : bexp1 k = j := by unfold bexp1; omega
      rw [base, e0, e1, mul_zero, add_zero]
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      obtain ⟨Q, hQ, hQ0, he⟩ := ih j' (by omega) (i + 3) (by omega)
      have hmono : Iso (X 0 ^ i * X 1 ^ j' : MvPolynomial (Fin 2) R) (k - 12) :=
        iso_of_eq (iso_mono i j') (by omega)
      refine ⟨Q - X 0 ^ i * X 1 ^ j', iso_sub hQ hmono, fun h => by omega, ?_⟩
      have e : (X 0 ^ i * X 1 ^ (j' + 2) : MvPolynomial (Fin 2) R) =
          X 0 ^ (i + 3) * X 1 ^ j' - disc R * (X 0 ^ i * X 1 ^ j') := by
        simp only [disc]
        ring
      rw [e, he]
      ring

/-- **An isobaric polynomial is a multiple of the base monomial, modulo the discriminant.** -/
theorem disc_decomp {R : Type*} [CommRing R] {P : MvPolynomial (Fin 2) R} {k : ℕ} (hP : Iso P k) :
    ∃ Q : MvPolynomial (Fin 2) R, Iso Q (k - 12) ∧ (k < 12 → Q = 0) ∧
      P = C (eval one2 P) * base k + disc R * Q := by
  classical
  have hS : ∃ (c : R) (Q : MvPolynomial (Fin 2) R), Iso Q (k - 12) ∧ (k < 12 → Q = 0) ∧
      P = C c * base k + disc R * Q := by
    rw [← P.support_sum_monomial_coeff]
    refine Finset.sum_induction _ (fun T => ∃ (c : R) (Q : MvPolynomial (Fin 2) R), Iso Q (k - 12) ∧
      (k < 12 → Q = 0) ∧ T = C c * base k + disc R * Q) ?_ ?_ ?_
    · rintro _ _ ⟨c, Q, hQ, hQ0, rfl⟩ ⟨c', Q', hQ', hQ0', rfl⟩
      refine ⟨c + c', Q + Q', hQ.add hQ', fun h => by rw [hQ0 h, hQ0' h, add_zero], ?_⟩
      rw [C_add]
      ring
    · exact ⟨0, 0, isWeightedHomogeneous_zero _ _ _, fun _ => rfl, by simp⟩
    · intro d hd
      have hw : Finsupp.weight wt d = k := hP (mem_support_iff.mp hd)
      rw [weight_wt] at hw
      obtain ⟨Q, hQ, hQ0, he⟩ := mono_reduce (R := R) k (d 1) (d 0) hw
      refine ⟨coeff d P, C (coeff d P) * Q, hQ.C_mul _, fun h => by rw [hQ0 h, mul_zero], ?_⟩
      rw [monomial_eq_two, he]
      ring
  obtain ⟨c, Q, hQ, hQ0, he⟩ := hS
  have hc : eval one2 P = c := by
    rw [he, map_add, map_mul, map_mul, eval_C, eval_base, eval_disc, zero_mul, add_zero, mul_one]
  exact ⟨Q, hQ, hQ0, by rw [hc]; exact he⟩

variable (ℓ) in
/-- `Δ` modulo `ℓ`. -/
abbrev Dl : PowerSeries (ZMod ℓ) := Dq (ZMod ℓ)

/-- A reduction with no constant term is divisible by `Δ`. -/
lemma div_Delta (h5 : 5 ≤ ℓ) {P : MvPolynomial (Fin 2) (ZMod ℓ)} {k : ℕ} (hP : Iso P k)
    (h0 : PowerSeries.constantCoeff (ev (ZMod ℓ) P) = 0) (hne : ev (ZMod ℓ) P ≠ 0) :
    12 ≤ k ∧ ∃ Q : MvPolynomial (Fin 2) (ZMod ℓ), Iso Q (k - 12) ∧ ev (ZMod ℓ) P = Dl ℓ * ev (ZMod ℓ) Q := by
  obtain ⟨Q, hQ, hQ0, he⟩ := disc_decomp hP
  rw [constantCoeff_ev] at h0
  rw [h0, C_0, zero_mul, zero_add] at he
  have hk : 12 ≤ k := by
    by_contra hlt
    apply hne
    rw [he, hQ0 (by omega), mul_zero, map_zero]
  refine ⟨hk, C 1728 * Q, hQ.C_mul _, ?_⟩
  rw [he, map_mul, map_mul, ev_disc, ev_C]
  have : (PowerSeries.C (1728 : ZMod ℓ)) = (1728 : PowerSeries (ZMod ℓ)) := map_ofNat _ 1728
  rw [this]
  ring

lemma Dl_pow (d : ℕ) : Dl ℓ ^ d =
    PowerSeries.X ^ d * PowerSeries.map (Int.castRingHom (ZMod ℓ)) (MockTheta5.JTP.qfacInf ^ (24 * d)) := by
  simp only [Dl, Dq, map_mul, map_pow, PowerSeries.map_X, mul_pow, pow_mul]

lemma constantCoeff_qfac : PowerSeries.constantCoeff (MockTheta5.JTP.qfacInf : PowerSeries ℤ) = 1 := by
  have h := congrArg PowerSeries.constantCoeff qfac_mul_pgf
  rw [map_mul, map_one] at h
  have hp : PowerSeries.constantCoeff MockTheta5.JTP.partitionGF = (1 : ℤ) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, MockTheta5.JTP.coeff_partitionGF_eq_card]
    simp
  rwa [hp, mul_one] at h

/-- **Valence.** A nonzero reduction vanishing to order `d` is `Δ^d` times a reduction, and has weight at
least `12 d`. -/
theorem div_Delta_pow (h5 : 5 ≤ ℓ) (d : ℕ) {P : MvPolynomial (Fin 2) (ZMod ℓ)} {k : ℕ} (hP : Iso P k)
    (h0 : ∀ n < d, PowerSeries.coeff n (ev (ZMod ℓ) P) = 0) (hne : ev (ZMod ℓ) P ≠ 0) :
    12 * d ≤ k ∧ ∃ Q : MvPolynomial (Fin 2) (ZMod ℓ), Iso Q (k - 12 * d) ∧
      ev (ZMod ℓ) P = Dl ℓ ^ d * ev (ZMod ℓ) Q := by
  induction d with
  | zero => exact ⟨by omega, P, by simpa using hP, by simp⟩
  | succ d ih =>
    obtain ⟨hk, Q, hQ, he⟩ := ih fun n hn => h0 n (by omega)
    have hQne : ev (ZMod ℓ) Q ≠ 0 := by
      intro h
      apply hne
      rw [he, h, mul_zero]
    have hc : PowerSeries.constantCoeff (ev (ZMod ℓ) Q) = 0 := by
      have h := h0 d (by omega)
      rw [he, Dl_pow, mul_assoc, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul] at h
      have hu : PowerSeries.constantCoeff (PowerSeries.map (Int.castRingHom (ZMod ℓ))
          (MockTheta5.JTP.qfacInf ^ (24 * d))) = 1 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
          PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_qfac]
        simp
      rwa [hu, one_mul] at h
    obtain ⟨hk', Q', hQ', he'⟩ := div_Delta h5 hQ hc hQne
    refine ⟨by omega, Q', iso_of_eq hQ' (by omega), ?_⟩
    rw [he, he', pow_succ, mul_assoc]

/-! ### The numerical cycle -/

private lemma not_dvd_add {L u e : ℤ} (he : 0 < e) (heL : e < L) : ¬ L ∣ L * u + e := by
  intro h
  have h2 : L ∣ e := (Int.dvd_add_right (dvd_mul_right L u)).mp h
  have := Int.le_of_dvd he h2
  omega

/-- **The closed cycle from weight `(ℓ²-1)/2`.** With `ℓ = 2s+1` and every filtration at least the starting one, the
filtration after `s + 2` steps is four more than the starting one. -/
theorem cycle_weight_four (s : ℕ) (hs : 3 ≤ s) (K : ℤ) (hK : K = 2 * (s : ℤ) ^ 2 + 2 * s) (w d : ℕ → ℤ)
    (hw : ∀ i ≤ 2 * s, K ≤ w i) (hd : ∀ i < 2 * s, 0 ≤ d i)
    (hstep : ∀ i < 2 * s, w (i + 1) = w i + 2 * s + 2 - d i * (2 * s))
    (hdrop : ∀ i < 2 * s, ¬ (2 * (s : ℤ) + 1) ∣ w i → d i = 0)
    (hstart : w 0 = K) (hclose : w (2 * s) = K) : w (s + 2) = K + 4 := by
  have hsz : (3 : ℤ) ≤ s := by exact_mod_cast hs
  have phase1 : ∀ i ≤ s + 1, w i = K + i * (2 * s + 2) := by
    intro i
    induction i with
    | zero => intro _; simpa using hstart
    | succ i ih =>
      intro hi
      have hwi := ih (by omega)
      have hiz : (i : ℤ) ≤ s := by exact_mod_cast (by omega : i ≤ s)
      have hi0 : (0 : ℤ) ≤ i := by positivity
      have hd0 : d i = 0 := hdrop i (by omega) (by
        have e : w i = (2 * (s : ℤ) + 1) * (s + i) + (s + i) := by rw [hwi, hK]; ring
        rw [e]
        exact not_dvd_add (by omega) (by omega))
      have := hstep i (by omega)
      rw [this, hwi, hd0]
      push_cast
      ring
  have h1 := phase1 (s + 1) le_rfl
  have h2 := hstep (s + 1) (by omega)
  have h3 := hw (s + 2) (by omega)
  set D := d (s + 1) with hD
  have hD0 : 0 ≤ D := hd (s + 1) (by omega)
  have h4 : w (s + 2) = K + (s + 2) * (2 * s + 2) - D * (2 * s) := by
    rw [show s + 2 = s + 1 + 1 by ring, h2, h1]
    push_cast
    ring
  have hDle : D ≤ s + 3 := by
    by_contra hc
    have : (s : ℤ) + 4 ≤ D := by omega
    nlinarith
  by_contra hne
  have hDlt : D ≤ s + 2 := by
    by_contra hc
    apply hne
    have : D = s + 3 := by omega
    rw [h4, this]
    ring
  have phase2 : ∀ t ≤ s - 2, w (s + 2 + t) = K + (s + 2) * (2 * s + 2) - D * (2 * s) + t * (2 * s + 2) := by
    intro t
    induction t with
    | zero => intro _; simpa using h4
    | succ t ih =>
      intro ht
      have hwt := ih (by omega)
      have htz : (t : ℤ) + 3 ≤ s := by exact_mod_cast (by omega : t + 3 ≤ s)
      have ht0 : (0 : ℤ) ≤ t := by positivity
      have hd0 : d (s + 2 + t) = 0 := hdrop _ (by omega) (by
        have e : w (s + 2 + t) = (2 * (s : ℤ) + 1) * (2 * s + 3 - D + t) + (1 + t + D) := by
          rw [hwt, hK]
          ring
        rw [e]
        exact not_dvd_add (by omega) (by omega))
      have := hstep (s + 2 + t) (by omega)
      rw [show s + 2 + (t + 1) = s + 2 + t + 1 by ring, this, hwt, hd0]
      push_cast
      ring
  have h5 := phase2 (s - 2) le_rfl
  rw [show s + 2 + (s - 2) = 2 * s by omega, hclose] at h5
  have hc2 : ((s - 2 : ℕ) : ℤ) = s - 2 := by
    rw [Nat.cast_sub (by omega)]
    rfl
  rw [hc2] at h5
  nlinarith

end

end RamanujanTau.BLBound
