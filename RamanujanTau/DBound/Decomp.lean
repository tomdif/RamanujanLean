import RamanujanTau.AtkinOBrienFinal.Transfer

/-!
# Katz decomposition of a single weight `n(ℓ−1)` (mod every `ℓ^N`)

For an isobaric `P ∈ ℤ_ℓ[X₀,X₁]` of weight `n(ℓ−1)`:

  `P(E₄,E₆)/E^n ≡ Σ_{m ≤ n} c_m(E₄,E₆)/E^m   (mod ℓ^N)`,   `c_m ∈ B_m = Kpiece m`,

for every `N` (`decompN`). This is the decomposition `M_{n(ℓ−1)} = E·M_{(n−1)(ℓ−1)} ⊕ B_n`, iterated.

* `divS`: division with remainder by `Ā` over `𝔽_ℓ` w.r.t. the leading monomial `X₀^{dA}X₁^{eA}`:
  `Q = R + Ā·Q'` with `supp R ⊆ S(w)`. (In one weight a monomial is determined by its `X₀`-degree.)
* `decompF`: hence `Q = Σ_{m ≤ n} Ā^{n−m} c̄_m`, `supp c̄_m ⊆ S(m(ℓ−1))`.
* `decomp1`: lift to `ℤ_ℓ`: `P = Σ A^{n−m} c_m + ℓ·P'`.
* `decompN`: iterate (`A(E₄,E₆) = E`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace DBound
open MvPolynomial ModP AtkinOBrienFinal AtkinOBrien

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-- `𝔽_ℓ[X₀,X₁]`. -/
abbrev PolyF (ℓ : ℕ) := MvPolynomial (Fin 2) (ZMod ℓ)

/-- monomials divisible by the leading monomial of `Ā`. -/
def Bad (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ) (t : Fin 2 →₀ ℕ) : Prop :=
  Igusa.dA ℓ hℓ ≤ t 0 ∧ Igusa.eA ℓ hℓ ≤ t 1

lemma mono_eq {s t : Fin 2 →₀ ℕ} (hw : 4 * s 0 + 6 * s 1 = 4 * t 0 + 6 * t 1) (h0 : s 0 = t 0) :
    s = t := by
  ext i; fin_cases i
  · exact h0
  · show s 1 = t 1; omega

lemma weight_of_iso {R : Type*} [CommSemiring R] {Q : MvPolynomial (Fin 2) R} {w : ℕ} (hQ : Iso Q w)
    {t : Fin 2 →₀ ℕ} (ht : t ∈ Q.support) : 4 * t 0 + 6 * t 1 = w := by
  have := hQ (mem_support_iff.mp ht); rwa [weight_wt] at this

lemma iso_of_support {R : Type*} [CommSemiring R] {Q : MvPolynomial (Fin 2) R} {w : ℕ}
    (h : (Q.support : Set (Fin 2 →₀ ℕ)) ⊆ Igusa.S ℓ hℓ w) : Iso Q w := fun d hd => by
  rw [weight_wt]; exact (h (mem_support_iff.mpr hd)).1

lemma weight_lead : 4 * Igusa.dA ℓ hℓ + 6 * Igusa.eA ℓ hℓ = ℓ - 1 := Igusa.dA_eA (p := ℓ) hℓ

/-- **Division by `Ā` with remainder in the monomial complement.** -/
theorem divS (w : ℕ) : ∀ n (Q : PolyF ℓ), Iso Q w → (∀ t ∈ Q.support, Bad ℓ hℓ t → t 0 < n) →
    ∃ R Q' : PolyF ℓ, (R.support : Set (Fin 2 →₀ ℕ)) ⊆ Igusa.S ℓ hℓ w ∧ Iso Q' (w - (ℓ - 1)) ∧
      Q = R + hasseBar ℓ hℓ * Q' := by
  obtain ⟨s₀, hs₀, h0, h1⟩ := Igusa.exists_lead (p := ℓ) hℓ
  have hu : coeff s₀ (hasseBar ℓ hℓ) ≠ 0 := mem_support_iff.mp hs₀
  have hwl := weight_lead hℓ
  intro n
  induction n with
  | zero =>
    intro Q hQ hb
    refine ⟨Q, 0, fun t ht => ⟨weight_of_iso hQ ht, fun hbt => ?_⟩, isWeightedHomogeneous_zero _ _ _,
      by rw [mul_zero, add_zero]⟩
    exact Nat.not_lt_zero _ (hb t ht hbt)
  | succ n ih =>
    intro Q hQ hb
    by_cases hex : ∃ t ∈ Q.support, Bad ℓ hℓ t ∧ t 0 = n
    swap
    · refine ih Q hQ fun t ht hbt => lt_of_le_of_ne (Nat.lt_succ_iff.mp (hb t ht hbt))
        fun h => hex ⟨t, ht, hbt, h⟩
    obtain ⟨t, ht, ⟨hbt0, hbt1⟩, htn⟩ := hex
    have hwt := weight_of_iso hQ ht
    have hle : s₀ ≤ t := by
      intro i; fin_cases i
      · show s₀ 0 ≤ t 0; omega
      · show s₀ 1 ≤ t 1; omega
    set t' := t - s₀ with ht'
    have ht'0 : t' 0 = t 0 - s₀ 0 := Finsupp.tsub_apply _ _ _
    have ht'1 : t' 1 = t 1 - s₀ 1 := Finsupp.tsub_apply _ _ _
    set c : ZMod ℓ := coeff t Q * (coeff s₀ (hasseBar ℓ hℓ))⁻¹ with hc
    set Q1 := Q - monomial t' c * hasseBar ℓ hℓ with hQ1
    have hmono : Iso (monomial t' c : PolyF ℓ) (w - (ℓ - 1)) :=
      isWeightedHomogeneous_monomial _ _ _ (by rw [weight_wt]; omega)
    have hiso1 : Iso Q1 w := by
      refine iso_sub hQ (iso_of_eq (hmono.mul (iso_hasseBar hℓ)) ?_)
      omega
    have hb1 : ∀ r ∈ Q1.support, Bad ℓ hℓ r → r 0 < n := by
      intro r hr hbr
      by_contra hcon
      push Not at hcon
      apply mem_support_iff.mp hr
      have hwr := weight_of_iso hiso1 hr
      rw [hQ1, coeff_sub, coeff_monomial_mul']
      rcases Nat.lt_or_ge n (r 0) with hgt | hge
      · have hq : coeff r Q = 0 := by
          by_contra hq
          have := hb r (mem_support_iff.mpr hq) hbr
          omega
        rw [hq]
        split_ifs with hrt
        · have : coeff (r - t') (hasseBar ℓ hℓ) = 0 := by
            by_contra hz
            have := Igusa.le_dA (p := ℓ) hℓ (mem_support_iff.mpr hz)
            rw [Finsupp.tsub_apply] at this
            omega
          rw [this, mul_zero, sub_zero]
        · rw [sub_zero]
      · have hrt : r = t := mono_eq (by omega) (by omega)
        subst hrt
        rw [if_pos (le_refl _ |>.trans' (tsub_le_self)), ht', tsub_tsub_cancel_of_le hle, hc,
          mul_assoc, inv_mul_cancel₀ hu, mul_one, sub_self]
    obtain ⟨R, Q1', hR, hQ1', he⟩ := ih Q1 hiso1 hb1
    refine ⟨R, Q1' + monomial t' c, hR, hQ1'.add hmono, ?_⟩
    have : Q = Q1 + monomial t' c * hasseBar ℓ hℓ := by rw [hQ1]; ring
    rw [this, he]; ring

/-- **Full Katz decomposition over `𝔽_ℓ`.** -/
theorem decompF (n : ℕ) : ∀ Q : PolyF ℓ, Iso Q (n * (ℓ - 1)) →
    ∃ c : ℕ → PolyF ℓ, (∀ m, ((c m).support : Set (Fin 2 →₀ ℕ)) ⊆ Igusa.S ℓ hℓ (m * (ℓ - 1))) ∧
      Q = ∑ m ∈ Finset.range (n + 1), hasseBar ℓ hℓ ^ (n - m) * c m := by
  have hwl := weight_lead hℓ
  have hl1 : 4 ≤ ℓ - 1 := by omega
  induction n with
  | zero =>
    intro Q hQ
    refine ⟨fun m => if m = 0 then Q else 0, fun m => ?_, by simp⟩
    dsimp only
    split_ifs with hm
    · subst hm
      intro t ht
      have hw := weight_of_iso hQ ht
      rw [zero_mul] at hw
      refine ⟨by rw [zero_mul]; exact hw, fun hb => ?_⟩
      unfold Bad at hb
      obtain ⟨hb0, hb1⟩ := hb
      omega
    · simp
  | succ n ih =>
    intro Q hQ
    have hb : ∀ t ∈ Q.support, Bad ℓ hℓ t → t 0 < (n + 1) * (ℓ - 1) + 1 := by
      intro t ht _
      have := weight_of_iso hQ ht
      omega
    obtain ⟨R, Q', hR, hQ', he⟩ := divS hℓ ((n + 1) * (ℓ - 1)) _ Q hQ hb
    have hw : (n + 1) * (ℓ - 1) - (ℓ - 1) = n * (ℓ - 1) := by rw [Nat.succ_mul, Nat.add_sub_cancel]
    rw [hw] at hQ'
    obtain ⟨c', hc', he'⟩ := ih Q' hQ'
    refine ⟨fun m => if m = n + 1 then R else c' m, fun m => ?_, ?_⟩
    · dsimp only
      split_ifs with hm
      · subst hm; exact hR
      · exact hc' m
    · dsimp only
      rw [Finset.sum_range_succ, if_pos rfl, Nat.sub_self, pow_zero, one_mul, he, he',
        Finset.mul_sum, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm' : m < n + 1 := Finset.mem_range.mp hm
      rw [if_neg (by omega), show n + 1 - m = (n - m) + 1 by omega, pow_succ]
      ring

/-- lift of a polynomial over `𝔽_ℓ` to `ℤ_ℓ`, coefficientwise (support-preserving). -/
noncomputable def liftP (P : PolyF ℓ) : Poly ℓ :=
  ∑ d ∈ P.support, monomial d (((P.coeff d).val : ℕ) : ℤ_[ℓ])

lemma map_liftP (P : PolyF ℓ) : MvPolynomial.map (PadicInt.toZMod (p := ℓ)) (liftP P) = P := by
  rw [liftP, map_sum]
  conv_rhs => rw [P.as_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_monomial, map_natCast, ZMod.natCast_zmod_val]

lemma support_liftP (P : PolyF ℓ) : ((liftP P).support : Set (Fin 2 →₀ ℕ)) ⊆ P.support := by
  intro d hd
  rw [Finset.mem_coe, mem_support_iff, liftP, coeff_sum] at hd
  by_contra hn
  apply hd
  refine Finset.sum_eq_zero fun e he => ?_
  rw [coeff_monomial, if_neg]
  rintro rfl; exact hn he

lemma iso_smul_cancel {P : Poly ℓ} {w : ℕ} (h : Iso ((ℓ : ℤ_[ℓ]) • P) w) : Iso P w := by
  intro d hd
  apply h
  rw [coeff_smul, smul_eq_mul]
  exact mul_ne_zero ell_ne_zero hd

/-- **One step over `ℤ_ℓ`**: `P = Σ_{m ≤ n} A^{n−m} c_m + ℓ·P'`. -/
theorem decomp1 (n : ℕ) (P : Poly ℓ) (hP : Iso P (n * (ℓ - 1))) :
    ∃ (c : ℕ → Poly ℓ) (P' : Poly ℓ), (∀ m, c m ∈ Kpiece ℓ hℓ m) ∧ Iso P' (n * (ℓ - 1)) ∧
      P = ∑ m ∈ Finset.range (n + 1), hasseA ℓ hℓ ^ (n - m) * c m + (ℓ : ℤ_[ℓ]) • P' := by
  obtain ⟨cb, hcb, he⟩ := decompF hℓ n _ (iso_map (PadicInt.toZMod (p := ℓ)) hP)
  have hK : ∀ m, liftP (cb m) ∈ Kpiece ℓ hℓ m := fun m =>
    (mem_Kpiece hℓ).mpr ((support_liftP _).trans (hcb m))
  obtain ⟨P', hP'⟩ := Poly_dvd_of_map
    (P - ∑ m ∈ Finset.range (n + 1), hasseA ℓ hℓ ^ (n - m) * liftP (cb m)) (by
      rw [map_sub, map_sum]
      conv_lhs => rw [he]
      rw [sub_eq_zero]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, map_pow, map_liftP]; rfl)
  have hl1 : 1 ≤ ℓ - 1 := by omega
  refine ⟨fun m => liftP (cb m), P', hK, iso_smul_cancel ?_, by rw [← hP']; abel⟩
  rw [← hP']
  refine iso_sub hP (IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_)
  have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  refine iso_of_eq (((iso_hasseA hℓ).pow (n - m)).mul (iso_of_support hℓ ((mem_Kpiece hℓ).mp (hK m))))
    ?_
  rw [smul_eq_mul, ← Nat.add_mul, Nat.sub_add_cancel hm']

lemma ev_hasseA_E : ModP.ev ℤ_[ℓ] (hasseA ℓ hℓ) = E ℓ hℓ := ev_hasseA hℓ

lemma E_pow_mul_Einv_pow {m n : ℕ} (h : m ≤ n) :
    E ℓ hℓ ^ (n - m) * Einv ℓ hℓ ^ n = Einv ℓ hℓ ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  rw [Nat.add_sub_cancel_left, pow_add, mul_left_comm, ← mul_pow, E_mul_Einv, one_pow, mul_one]

/-- **Katz decomposition of one weight, mod `ℓ^N`.** -/
theorem decompN (N : ℕ) : ∀ (n : ℕ) (P : Poly ℓ), Iso P (n * (ℓ - 1)) →
    ∃ c : ℕ → Poly ℓ, (∀ m, c m ∈ Kpiece ℓ hℓ m) ∧ (∀ m, n < m → c m = 0) ∧
      Dvd (ℓ : ℤ_[ℓ]) N (ModP.ev ℤ_[ℓ] P * Einv ℓ hℓ ^ n -
        ∑ m ∈ Finset.range (n + 1), ModP.ev ℤ_[ℓ] (c m) * Einv ℓ hℓ ^ m) := by
  induction N with
  | zero =>
    intro n P _
    exact ⟨0, fun m => Submodule.zero_mem _, fun _ _ => rfl, ⟨_, by rw [pow_zero, one_smul]⟩⟩
  | succ N ih =>
    intro n P hP
    obtain ⟨c, P', hc, hP', he⟩ := decomp1 hℓ n P hP
    obtain ⟨c', hc', hc'0, y, hy⟩ := ih n P' hP'
    refine ⟨fun m => if m ≤ n then c m + (ℓ : ℤ_[ℓ]) • c' m else 0, fun m => ?_, fun m hm => ?_,
      ⟨y, ?_⟩⟩
    · dsimp only
      split_ifs
      · exact Submodule.add_mem _ (hc m) (Submodule.smul_mem _ _ (hc' m))
      · exact Submodule.zero_mem _
    · dsimp only; rw [if_neg (by omega)]
    · have e1 : ModP.ev ℤ_[ℓ] P * Einv ℓ hℓ ^ n =
          ∑ m ∈ Finset.range (n + 1), ModP.ev ℤ_[ℓ] (c m) * Einv ℓ hℓ ^ m +
            (ℓ : ℤ_[ℓ]) • (ModP.ev ℤ_[ℓ] P' * Einv ℓ hℓ ^ n) := by
        have hs : ∑ m ∈ Finset.range (n + 1), ModP.ev ℤ_[ℓ] (hasseA ℓ hℓ ^ (n - m) * c m) *
            Einv ℓ hℓ ^ n = ∑ m ∈ Finset.range (n + 1), ModP.ev ℤ_[ℓ] (c m) * Einv ℓ hℓ ^ m := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [map_mul, map_pow, ev_hasseA_E, mul_comm (E ℓ hℓ ^ (n - m)), mul_assoc,
            E_pow_mul_Einv_pow hℓ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]
        conv_lhs => rw [he]
        rw [map_add, map_sum, add_mul, Finset.sum_mul, map_smul, smul_mul_assoc, hs]
      have e2 : ∑ m ∈ Finset.range (n + 1),
          ModP.ev ℤ_[ℓ] (if m ≤ n then c m + (ℓ : ℤ_[ℓ]) • c' m else 0) * Einv ℓ hℓ ^ m =
          ∑ m ∈ Finset.range (n + 1), ModP.ev ℤ_[ℓ] (c m) * Einv ℓ hℓ ^ m +
            (ℓ : ℤ_[ℓ]) • ∑ m ∈ Finset.range (n + 1), ModP.ev ℤ_[ℓ] (c' m) * Einv ℓ hℓ ^ m := by
        rw [Finset.smul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)), map_add, map_smul, add_mul,
          smul_mul_assoc]
      beta_reduce
      rw [e1, e2, add_sub_add_left_eq_sub, ← smul_sub, hy, smul_smul, ← pow_succ']

end DBound
