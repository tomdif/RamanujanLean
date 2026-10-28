import RamanujanTau.ModP.Structure

/-!
# The Hasse polynomial `Ā` and the mod-`p` q-expansion structure (Swinnerton-Dyer, single weight class)

For a prime `p ≥ 5`:
* `exists_hasse_poly` — there is an isobaric `A ∈ ℤ_[p][X₀,X₁]` of weight `p − 1` with
  `A(E₄,E₆) = E_{p−1}` (`TateCurve.EhasseZp`).
* `hasseBar p hp5 ∈ 𝔽_p[X₀,X₁]` its reduction: isobaric of weight `p − 1`, `Ā(Ē₄,Ē₆) = 1`
  (`ev_hasseBar`), and it is the *unique* isobaric polynomial of weight `p − 1` with this property.
* `iso_eq_zero_of_ev_eq_zero` (from `Formal`) — single-weight q-expansion principle over `𝔽_p`.
* `eq_hasseBar_pow_mul` — weight filtration: if `P` has weight `k`, `P'` weight `k + m(p−1)` and the same
  q-expansion, then `P' = Ā^m · P`.
* `sum_hasseBar_pow_eq_zero`, `mem_span_hasseBar_sub_one` — Swinnerton-Dyer's theorem restricted to one
  weight class: if `P = Σ_{i ≤ n} P_i`, `P_i` isobaric of weight `k₀ + i(p−1)`, has vanishing q-expansion,
  then `Σ Ā^{n−i} P_i = 0` and `P ∈ (Ā − 1)`; conversely `(Ā − 1) ⊆ ker`.
* `katz_independent` — "Katz pieces": if `P_i ∈ B_i` (weight `k₀ + i(p−1)`) where `B_i` meets
  `Ā · M_{k₀+(i−1)(p−1)}` trivially, and `Σ P_i(Ē₄,Ē₆) = 0`, then every `P_i = 0`.
-/

set_option autoImplicit false

namespace ModP
open MvPolynomial

variable {p : ℕ} [hp : Fact p.Prime]

lemma ne_zero_1728 (hp5 : 5 ≤ p) : (1728 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((1728 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have h'' : p ∣ 2 ^ 6 * 3 ^ 3 := by norm_num; exact h'
  rcases (Nat.Prime.dvd_mul hp.out).mp h'' with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) (hp.out.dvd_of_dvd_pow h2); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.out.dvd_of_dvd_pow h3); omega

lemma isUnit_1728_ZMod (hp5 : 5 ≤ p) : IsUnit (1728 : ZMod p) :=
  isUnit_iff_ne_zero.mpr (ne_zero_1728 hp5)

lemma isUnit_1728_Zp (hp5 : 5 ≤ p) : IsUnit (1728 : ℤ_[p]) := by
  by_contra hx
  have hm : (1728 : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := (IsLocalRing.mem_maximalIdeal _).mpr hx
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_ofNat] at hm
  exact ne_zero_1728 hp5 hm

lemma iso_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {P : MvPolynomial (Fin 2) R}
    {k : ℕ} (h : Iso P k) : Iso (MvPolynomial.map φ P) k := by
  intro d hd
  apply h
  intro h0
  apply hd
  rw [coeff_map, h0, map_zero]

/-- **`E_{p−1}` is an isobaric polynomial of weight `p − 1` in `E₄, E₆` with `p`-integral coefficients.** -/
theorem exists_hasse_poly (hp5 : 5 ≤ p) :
    ∃ A : MvPolynomial (Fin 2) ℤ_[p], Iso A (p - 1) ∧ ev ℤ_[p] A = TateCurve.EhasseZp p (by omega) := by
  have hk : 3 ≤ p - 1 := by omega
  have hk2 : Even (p - 1) := hp.out.even_sub_one (by omega)
  obtain ⟨P, hP, hPe⟩ := exists_poly_Eis hk hk2
  have hinj : Function.Injective (PadicInt.Coe.ringHom (p := p)) := Subtype.val_injective
  obtain ⟨A, hA, hAe⟩ := descend (PadicInt.Coe.ringHom (p := p)) hinj (isUnit_1728_Zp hp5) (p - 1)
    (MvPolynomial.map (Rat.castHom ℚ_[p]) P) (iso_map _ hP)
    ⟨TateCurve.EhasseZp p (by omega), by rw [TateCurve.map_EhasseZp, ← map_ev, hPe]⟩
  refine ⟨A, hA, PowerSeries.map_injective _ hinj ?_⟩
  rw [map_ev, hAe, TateCurve.map_EhasseZp, ← map_ev, hPe]

/-- The Hasse polynomial `A` over `ℤ_[p]`: `A(E₄,E₆) = E_{p−1}`. -/
noncomputable def hasseA (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) : MvPolynomial (Fin 2) ℤ_[p] :=
  Classical.choose (exists_hasse_poly hp5)

lemma iso_hasseA (hp5 : 5 ≤ p) : Iso (hasseA p hp5) (p - 1) :=
  (Classical.choose_spec (exists_hasse_poly hp5)).1

lemma ev_hasseA (hp5 : 5 ≤ p) : ev ℤ_[p] (hasseA p hp5) = TateCurve.EhasseZp p (by omega) :=
  (Classical.choose_spec (exists_hasse_poly hp5)).2

/-- The reduction `Ā ∈ 𝔽_p[X₀,X₁]` of the Hasse polynomial. -/
noncomputable def hasseBar (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) : MvPolynomial (Fin 2) (ZMod p) :=
  MvPolynomial.map (PadicInt.toZMod (p := p)) (hasseA p hp5)

theorem iso_hasseBar (hp5 : 5 ≤ p) : Iso (hasseBar p hp5) (p - 1) := iso_map _ (iso_hasseA hp5)

/-- **`Ā(Ē₄, Ē₆) = 1` in `𝔽_p⟦q⟧`.** -/
theorem ev_hasseBar (hp5 : 5 ≤ p) : ev (ZMod p) (hasseBar p hp5) = 1 := by
  rw [hasseBar, ← map_ev, ev_hasseA, TateCurve.map_toZMod_EhasseZp]

/-- `Ā − 1` lies in the kernel of the q-expansion map. -/
theorem ev_hasseBar_sub_one (hp5 : 5 ≤ p) : ev (ZMod p) (hasseBar p hp5 - 1) = 0 := by
  rw [map_sub, ev_hasseBar, map_one, sub_self]

/-- The ideal `(Ā − 1)` is contained in the kernel of the q-expansion map `𝔽_p[X₀,X₁] → 𝔽_p⟦q⟧`. -/
theorem span_hasseBar_sub_one_le_ker (hp5 : 5 ≤ p) :
    Ideal.span {hasseBar p hp5 - 1} ≤ RingHom.ker (ev (ZMod p)).toRingHom := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact ev_hasseBar_sub_one hp5

/-- `Ā` is the unique isobaric polynomial of weight `p − 1` over `𝔽_p` with q-expansion `1`. -/
theorem hasseBar_unique (hp5 : 5 ≤ p) {B : MvPolynomial (Fin 2) (ZMod p)} (hB : Iso B (p - 1))
    (hBe : ev (ZMod p) B = 1) : B = hasseBar p hp5 :=
  ev_injOn_iso (isUnit_1728_ZMod hp5) hB (iso_hasseBar hp5) (by rw [hBe, ev_hasseBar])

/-- **Mod-`p` q-expansion principle, single weight.** -/
theorem eq_zero_of_ev_eq_zero_modP (hp5 : 5 ≤ p) {k : ℕ} {P : MvPolynomial (Fin 2) (ZMod p)}
    (hP : Iso P k) (h : ev (ZMod p) P = 0) : P = 0 :=
  iso_eq_zero_of_ev_eq_zero (isUnit_1728_ZMod hp5) k P hP h

/-- **Weight filtration.** Same q-expansion, weights `k` and `k + m(p−1)`: then `P' = Ā^m P`. -/
theorem eq_hasseBar_pow_mul (hp5 : 5 ≤ p) {k m : ℕ} {P P' : MvPolynomial (Fin 2) (ZMod p)}
    (hP : Iso P k) (hP' : Iso P' (k + m * (p - 1))) (h : ev (ZMod p) P = ev (ZMod p) P') :
    P' = hasseBar p hp5 ^ m * P := by
  refine (ev_injOn_iso (isUnit_1728_ZMod hp5)
    (iso_of_eq (((iso_hasseBar hp5).pow m).mul hP) (by rw [smul_eq_mul]; ring)) hP' ?_).symm
  rw [map_mul, map_pow, ev_hasseBar, one_pow, one_mul, h]

lemma weight_aux {k0 n i q : ℕ} (hi : i ≤ n) : (n - i) * q + (k0 + i * q) = k0 + n * q := by
  have : (n - i) * q + i * q = n * q := by rw [← Nat.add_mul, Nat.sub_add_cancel hi]
  omega

/-- **Swinnerton-Dyer, single weight class (homogenized form).** -/
theorem sum_hasseBar_pow_eq_zero (hp5 : 5 ≤ p) (k0 n : ℕ) (P : ℕ → MvPolynomial (Fin 2) (ZMod p))
    (hP : ∀ i ≤ n, Iso (P i) (k0 + i * (p - 1)))
    (h : ∑ i ∈ Finset.range (n + 1), ev (ZMod p) (P i) = 0) :
    ∑ i ∈ Finset.range (n + 1), hasseBar p hp5 ^ (n - i) * P i = 0 := by
  apply eq_zero_of_ev_eq_zero_modP hp5 (k := k0 + n * (p - 1))
  · apply IsWeightedHomogeneous.sum
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact iso_of_eq (((iso_hasseBar hp5).pow (n - i)).mul (hP i hi'))
      (by rw [smul_eq_mul]; exact weight_aux hi')
  · rw [map_sum, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, ev_hasseBar, one_pow, one_mul]

/-- **Swinnerton-Dyer, single weight class (kernel form).** A polynomial whose isobaric pieces all have
weights `≡ k₀ (mod p − 1)` and whose q-expansion vanishes lies in the ideal `(Ā − 1)`. -/
theorem mem_span_hasseBar_sub_one (hp5 : 5 ≤ p) (k0 n : ℕ) (P : ℕ → MvPolynomial (Fin 2) (ZMod p))
    (hP : ∀ i ≤ n, Iso (P i) (k0 + i * (p - 1)))
    (h : ev (ZMod p) (∑ i ∈ Finset.range (n + 1), P i) = 0) :
    ∑ i ∈ Finset.range (n + 1), P i ∈ Ideal.span {hasseBar p hp5 - 1} := by
  rw [map_sum] at h
  have h0 := sum_hasseBar_pow_eq_zero hp5 k0 n P hP h
  have : ∑ i ∈ Finset.range (n + 1), P i =
      ∑ i ∈ Finset.range (n + 1), (1 - hasseBar p hp5 ^ (n - i)) * P i := by
    rw [← sub_zero (∑ i ∈ Finset.range (n + 1), P i), ← h0, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ?_
  rw [Ideal.mem_span_singleton]
  have := sub_dvd_pow_sub_pow (hasseBar p hp5) 1 (n - i)
  rw [one_pow] at this
  rw [show (1 : MvPolynomial (Fin 2) (ZMod p)) - hasseBar p hp5 ^ (n - i) =
    -(hasseBar p hp5 ^ (n - i) - 1) by ring]
  exact dvd_neg.mpr this

/-- **Independence of Katz pieces (mod-`p` q-expansions).** Let `B i` be subspaces of the weight
`k₀ + i(p−1)` polynomials meeting `Ā · (weight k₀ + (i−1)(p−1))` trivially. If `P i ∈ B i` and
`Σ_{i ≤ n} P i (Ē₄, Ē₆) = 0` in `𝔽_p⟦q⟧`, then all `P i = 0`. -/
theorem katz_independent (hp5 : 5 ≤ p) (k0 : ℕ) (B : ℕ → Set (MvPolynomial (Fin 2) (ZMod p)))
    (hB : ∀ i, 1 ≤ i → ∀ x ∈ B i, ∀ y : MvPolynomial (Fin 2) (ZMod p),
      Iso y (k0 + (i - 1) * (p - 1)) → x = hasseBar p hp5 * y → x = 0) :
    ∀ (n : ℕ) (P : ℕ → MvPolynomial (Fin 2) (ZMod p)), (∀ i ≤ n, Iso (P i) (k0 + i * (p - 1))) →
      (∀ i ≤ n, P i ∈ B i) → ∑ i ∈ Finset.range (n + 1), ev (ZMod p) (P i) = 0 →
      ∀ i ≤ n, P i = 0 := by
  intro n
  induction n with
  | zero =>
    intro P hP _ h i hi
    obtain rfl : i = 0 := by omega
    simp only [zero_add, Finset.range_one, Finset.sum_singleton] at h
    exact eq_zero_of_ev_eq_zero_modP hp5 (hP 0 le_rfl) h
  | succ n ih =>
    intro P hP hPB h
    have hS := sum_hasseBar_pow_eq_zero hp5 k0 (n + 1) P hP h
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul] at hS
    set y := -∑ i ∈ Finset.range (n + 1), hasseBar p hp5 ^ (n - i) * P i with hy
    have hlast : P (n + 1) = hasseBar p hp5 * y := by
      rw [hy, mul_neg, Finset.mul_sum, eq_neg_iff_add_eq_zero, add_comm, ← hS]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [← mul_assoc, ← pow_succ', show n - i + 1 = n + 1 - i by omega]
    have hyiso : Iso y (k0 + (n + 1 - 1) * (p - 1)) := by
      rw [show n + 1 - 1 = n by omega, hy]
      have : Iso (∑ i ∈ Finset.range (n + 1), hasseBar p hp5 ^ (n - i) * P i) (k0 + n * (p - 1)) := by
        apply IsWeightedHomogeneous.sum
        intro i hi
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact iso_of_eq (((iso_hasseBar hp5).pow (n - i)).mul (hP i (by omega)))
          (by rw [smul_eq_mul]; exact weight_aux hi')
      have h0 : Iso (0 : MvPolynomial (Fin 2) (ZMod p)) (k0 + n * (p - 1)) :=
        isWeightedHomogeneous_zero _ _ _
      simpa using iso_sub h0 this
    have hPn : P (n + 1) = 0 := hB (n + 1) (by omega) _ (hPB _ le_rfl) y hyiso hlast
    have h' : ∑ i ∈ Finset.range (n + 1), ev (ZMod p) (P i) = 0 := by
      rw [Finset.sum_range_succ, hPn, map_zero, add_zero] at h; exact h
    intro i hi
    rcases Nat.lt_or_ge i (n + 1) with hlt | hge
    · exact ih P (fun j hj => hP j (by omega)) (fun j hj => hPB j (by omega)) h' i (by omega)
    · obtain rfl : i = n + 1 := by omega
      exact hPn

end ModP
