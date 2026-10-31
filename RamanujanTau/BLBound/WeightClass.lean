import RamanujanTau.BLBound.NoCongruence
import Mathlib.FieldTheory.KummerExtension

/-!
# Weight classes modulo `ℓ - 1` are independent

Two facts of Swinnerton-Dyer on reductions of level one forms. A nonzero series has a well defined weight modulo
`ℓ - 1` (`weight_class_eq`), because the Hasse polynomial is squarefree. And a sum of forms of even weight in distinct
classes vanishes only if each term does (`class_sep`). For the second, `u = E₆/E₄` has class `2`, its `(ℓ-1)/2`-th power
lies in the field `L` of ratios of forms of equal weight, and no smaller power does, so `1, u, …` are independent over `L`
by the Kummer argument (`kummer_free`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BLBound
open MvPolynomial ModP Igusa BoylanWebb

noncomputable section

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-! ### The weight of a series -/

lemma hasse_not_unit (h5 : 5 ≤ ℓ) : ¬ IsUnit (hasseBar ℓ h5) := by
  intro hu
  obtain ⟨R, hR⟩ := isUnit_iff_dvd_one.mp hu
  have := (iso_quotient (iso_hasseBar h5) (isWeightedHomogeneous_one (ZMod ℓ) wt) one_ne_zero hR).1
  have := hℓ.out.two_le
  omega

/-- `A^m R^n = S^n` with `A` squarefree and not a unit forces `n ∣ m`. -/
lemma dvd_of_pow_eq {A R S : MvPolynomial (Fin 2) (ZMod ℓ)} (hsq : Squarefree A) (hu : ¬ IsUnit A) (hA : A ≠ 0)
    (hR : R ≠ 0) {m n : ℕ} (hn : n ≠ 0) (h : S ^ n = A ^ m * R ^ n) : n ∣ m := by
  classical
  obtain ⟨π, hπ, hd⟩ := WfDvdMonoid.exists_irreducible_factor hu hA
  have hprime : Prime π := hπ.prime
  have hS : S ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at h
    exact (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hR)) h.symm
  have hfin : ∀ x : MvPolynomial (Fin 2) (ZMod ℓ), x ≠ 0 → FiniteMultiplicity π x := fun x hx =>
    FiniteMultiplicity.of_prime_left hprime hx
  have hA1 : emultiplicity π A = 1 := by
    obtain ⟨B, rfl⟩ := hd
    have hnd : ¬ π ∣ B := by
      intro hB
      obtain ⟨C', rfl⟩ := hB
      exact hu (by
        have := hsq π ⟨C', by ring⟩
        exact (hprime.not_unit this).elim)
    rw [emultiplicity_mul hprime, emultiplicity_eq_zero.mpr hnd, add_zero]
    exact (hfin π hprime.ne_zero).emultiplicity_self
  have h1 := congrArg (emultiplicity π) h
  rw [emultiplicity_pow hprime, emultiplicity_mul hprime, emultiplicity_pow hprime, emultiplicity_pow hprime, hA1,
    (hfin S hS).emultiplicity_eq_multiplicity, (hfin R hR).emultiplicity_eq_multiplicity] at h1
  have h2 : n * multiplicity π S = m * 1 + n * multiplicity π R := by exact_mod_cast h1
  have hdv : n ∣ m * 1 := (Nat.dvd_add_left (dvd_mul_right _ _)).mp (h2 ▸ dvd_mul_right n _)
  simpa using hdv

/-- **A nonzero series has one weight modulo `ℓ - 1`.** -/
theorem weight_class_le (h5 : 5 ≤ ℓ) {P Q : MvPolynomial (Fin 2) (ZMod ℓ)} {a b : ℕ} (hP : Iso P a) (hQ : Iso Q b)
    (hab : a ≤ b) (he : ev (ZMod ℓ) P = ev (ZMod ℓ) Q) (h0 : ev (ZMod ℓ) P ≠ 0) : (ℓ - 1) ∣ b - a := by
  have hl : ℓ - 1 ≠ 0 := by omega
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact h0 (map_zero _)
  have hPn : Iso (P ^ (ℓ - 1)) (a * (ℓ - 1)) := iso_of_eq (hP.pow (ℓ - 1)) (by rw [smul_eq_mul, mul_comm])
  have hQn : Iso (Q ^ (ℓ - 1)) (a * (ℓ - 1) + (b - a) * (ℓ - 1)) :=
    iso_of_eq (hQ.pow (ℓ - 1)) (by
      rw [smul_eq_mul, ← add_mul, Nat.add_sub_cancel' hab, mul_comm])
  have heq := eq_hasseBar_pow_mul h5 hPn hQn (by rw [map_pow, map_pow, he])
  exact dvd_of_pow_eq (hasse_squarefree h5) (hasse_not_unit h5) (hasseBar_ne_zero h5) hP0 hl heq

/-! ### The Kummer argument -/

/-- A monic divisor of a product of linear factors is a subproduct. -/
lemma monic_dvd_prod {E : Type*} [Field E] [DecidableEq E] (T : Finset E) :
    ∀ g : Polynomial E, g.Monic → g ∣ ∏ a ∈ T, (Polynomial.X - Polynomial.C a) →
      ∃ T' ⊆ T, g = ∏ a ∈ T', (Polynomial.X - Polynomial.C a) := by
  induction T using Finset.induction_on with
  | empty =>
    intro g hg hd
    refine ⟨∅, Finset.Subset.refl _, ?_⟩
    rw [Finset.prod_empty] at hd ⊢
    exact Polynomial.eq_one_of_monic_natDegree_zero hg
      (Polynomial.natDegree_eq_zero_of_isUnit (isUnit_of_dvd_one hd))
  | insert a T ha ih =>
    intro g hg hd
    rw [Finset.prod_insert ha] at hd
    by_cases hX : (Polynomial.X - Polynomial.C a) ∣ g
    · obtain ⟨g₁, rfl⟩ := hX
      have hg₁ : g₁.Monic := (Polynomial.monic_X_sub_C a).of_mul_monic_left hg
      have hd₁ := (mul_dvd_mul_iff_left (Polynomial.X_sub_C_ne_zero a)).mp hd
      obtain ⟨T', hT', rfl⟩ := ih g₁ hg₁ hd₁
      refine ⟨insert a T', Finset.insert_subset_insert a hT', ?_⟩
      rw [Finset.prod_insert (fun h => ha (hT' h))]
    · have hp := Polynomial.prime_X_sub_C (R := E) a
      have hcop : IsCoprime g (Polynomial.X - Polynomial.C a) :=
        ((Polynomial.irreducible_X_sub_C a).coprime_iff_not_dvd.mpr hX).symm
      obtain ⟨T', hT', he⟩ := ih g hg (hcop.dvd_of_dvd_mul_left hd)
      exact ⟨T', hT'.trans (Finset.subset_insert a T), he⟩

/-- **Independence of the powers of a Kummer element.** -/
theorem kummer_free {E : Type*} [Field E] (L : Subfield E) (u : E) (hu : u ≠ 0) (s : ℕ) (hs : 0 < s)
    (huL : u ^ s ∈ L) {ζ : E} (hζ : IsPrimitiveRoot ζ s) (hζL : ζ ∈ L)
    (hd : ∀ d, 0 < d → d < s → u ^ d ∉ L) (c : ℕ → L)
    (hrel : ∑ i ∈ Finset.range s, (c i : E) * u ^ i = 0) : ∀ i < s, c i = 0 := by
  classical
  haveI : NeZero s := ⟨hs.ne'⟩
  let h : Polynomial L := ∑ i ∈ Finset.range s, Polynomial.monomial i (c i)
  have hcoeff : ∀ i, h.coeff i = if i < s then c i else 0 := by
    intro i
    simp only [h, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range s) i]
    simp
  have hzero : h = 0 := by
    by_contra hne
    let α : L := ⟨u ^ s, huL⟩
    have hrootA : Polynomial.aeval u (Polynomial.X ^ s - Polynomial.C α) = 0 := by
      simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      exact sub_self (u ^ s)
    have hint : IsIntegral L u := ⟨Polynomial.X ^ s - Polynomial.C α,
      Polynomial.monic_X_pow_sub_C α hs.ne', by rw [← Polynomial.aeval_def]; exact hrootA⟩
    have hrootH : Polynomial.aeval u h = 0 := by
      simp only [h, map_sum, Polynomial.aeval_monomial]
      exact hrel
    set g := minpoly L u with hg
    have hgm : g.Monic := minpoly.monic hint
    have hgdeg : 0 < g.natDegree := minpoly.natDegree_pos hint
    have hg1 : g ∣ h := minpoly.dvd L u hrootH
    have hgH : g.natDegree ≤ h.natDegree := Polynomial.natDegree_le_of_dvd hg1 hne
    have hHdeg : h.natDegree < s := by
      have hle : h.natDegree ≤ s - 1 := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by
        rw [hcoeff, if_neg (by omega)]
      omega
    have hg2 : g ∣ Polynomial.X ^ s - Polynomial.C α := minpoly.dvd L u hrootA
    have hprod := X_pow_sub_C_eq_prod hζ hs (α := u) (a := u ^ s) rfl
    have hg3 : g.map (algebraMap L E) ∣ ∏ a ∈ (Finset.range s).image (fun i => ζ ^ i * u),
        (Polynomial.X - Polynomial.C a) := by
      have hm := Polynomial.map_dvd (algebraMap L E) hg2
      have e : (Polynomial.X ^ s - Polynomial.C α : Polynomial L).map (algebraMap L E) =
          Polynomial.X ^ s - Polynomial.C (u ^ s) := by
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
        rfl
      rw [e, hprod] at hm
      rw [Finset.prod_image (fun x hx y hy hxy => hζ.pow_inj (Finset.mem_range.mp hx) (Finset.mem_range.mp hy)
        (mul_right_cancel₀ hu hxy))]
      exact hm
    obtain ⟨T', hT', hgT⟩ := monic_dvd_prod _ _ (hgm.map _) hg3
    have hcard : T'.card = g.natDegree := by
      have := congrArg Polynomial.natDegree hgT
      rw [Polynomial.natDegree_map, Polynomial.natDegree_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a] at this
      simpa using this.symm
    have hrootsL : ∀ a ∈ T', ∃ z ∈ L, z ≠ 0 ∧ a = z * u := by
      intro a ha
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hT' ha)
      exact ⟨ζ ^ i, L.pow_mem hζL i, pow_ne_zero _ (hζ.ne_zero hs.ne'), rfl⟩
    have hprodT : ∀ T₀ ⊆ T', ∃ z ∈ L, z ≠ 0 ∧ ∏ a ∈ T₀, a = z * u ^ T₀.card := by
      intro T₀
      induction T₀ using Finset.induction_on with
      | empty => intro _; exact ⟨1, L.one_mem, one_ne_zero, by simp⟩
      | insert a T₁ ha ih =>
        intro hsub
        obtain ⟨z, hz, hz0, he⟩ := ih ((Finset.subset_insert a T₁).trans hsub)
        obtain ⟨y, hy, hy0, rfl⟩ := hrootsL a (hsub (Finset.mem_insert_self a T₁))
        refine ⟨y * z, L.mul_mem hy hz, mul_ne_zero hy0 hz0, ?_⟩
        rw [Finset.prod_insert ha, he, Finset.card_insert_of_notMem ha, pow_succ]
        ring
    obtain ⟨z, hz, hz0, hze⟩ := hprodT T' (Finset.Subset.refl _)
    have hc0 : (g.coeff 0 : E) = (-1) ^ T'.card * (z * u ^ T'.card) := by
      have h1 := congrArg (fun p => Polynomial.coeff p 0) hgT
      simp only [Polynomial.coeff_map] at h1
      rw [Polynomial.coeff_zero_eq_eval_zero (∏ a ∈ T', _), Polynomial.eval_prod] at h1
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub] at h1
      rw [Finset.prod_neg, hze] at h1
      exact h1
    apply hd g.natDegree hgdeg (lt_of_le_of_lt hgH hHdeg)
    have hmem : (-1 : E) ^ T'.card * z ∈ L := L.mul_mem (L.pow_mem (L.neg_mem L.one_mem) _) hz
    have hne1 : (-1 : E) ^ T'.card * z ≠ 0 := mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hz0
    have e : u ^ g.natDegree = ((-1 : E) ^ T'.card * z)⁻¹ * (g.coeff 0 : E) := by
      rw [hc0, hcard]
      field_simp
    rw [e]
    exact L.mul_mem (L.inv_mem hmem) (g.coeff 0).2
  intro i hi
  have := hcoeff i
  rwa [hzero, Polynomial.coeff_zero, if_pos hi, eq_comm] at this

/-! ### The field of degree zero fractions -/

variable (ℓ) in
/-- The fraction field of `𝔽_ℓ⟦q⟧`. -/
abbrev EF : Type := FractionRing (PowerSeries (ZMod ℓ))

variable (ℓ) in
/-- The inclusion in the fraction field. -/
abbrev iF : PowerSeries (ZMod ℓ) →+* EF ℓ := algebraMap _ _

lemma iF_inj : Function.Injective (iF ℓ) := IsFractionRing.injective _ _

lemma iF_ne {f : PowerSeries (ZMod ℓ)} (h : f ≠ 0) : iF ℓ f ≠ 0 := fun h0 =>
  h (iF_inj (by rw [h0, map_zero]))

/-- The ratios of forms of equal weight. -/
def LF (ℓ : ℕ) [Fact ℓ.Prime] : Subfield (EF ℓ) where
  carrier := {x | ∃ (k : ℕ) (f g : PowerSeries (ZMod ℓ)), FormBar ℓ k f ∧ FormBar ℓ k g ∧ g ≠ 0 ∧ x = iF ℓ f / iF ℓ g}
  mul_mem' := by
    rintro _ _ ⟨k, f, g, ⟨P, hP, rfl⟩, ⟨Q, hQ, rfl⟩, hg, rfl⟩ ⟨k', f', g', ⟨P', hP', rfl⟩, ⟨Q', hQ', rfl⟩, hg', rfl⟩
    refine ⟨k + k', _, _, ⟨P * P', hP.mul hP', map_mul _ _ _⟩, ⟨Q * Q', hQ.mul hQ', map_mul _ _ _⟩,
      mul_ne_zero hg hg', ?_⟩
    rw [map_mul, map_mul, div_mul_div_comm]
  one_mem' := ⟨0, 1, 1, ⟨1, isWeightedHomogeneous_one _ _, map_one _⟩, ⟨1, isWeightedHomogeneous_one _ _, map_one _⟩,
    one_ne_zero, by simp⟩
  add_mem' := by
    rintro _ _ ⟨k, f, g, ⟨P, hP, rfl⟩, ⟨Q, hQ, rfl⟩, hg, rfl⟩ ⟨k', f', g', ⟨P', hP', rfl⟩, ⟨Q', hQ', rfl⟩, hg', rfl⟩
    refine ⟨k + k', _, _, ⟨P * Q' + Q * P', (hP.mul hQ').add (hQ.mul hP'), rfl⟩, ⟨Q * Q', hQ.mul hQ', map_mul _ _ _⟩,
      mul_ne_zero hg hg', ?_⟩
    rw [map_add, map_mul, map_mul, map_add, map_mul, map_mul, map_mul]
    field_simp [iF_ne hg, iF_ne hg']
  zero_mem' := ⟨0, 0, 1, ⟨0, isWeightedHomogeneous_zero _ _ _, map_zero _⟩,
    ⟨1, isWeightedHomogeneous_one _ _, map_one _⟩, one_ne_zero, by simp⟩
  neg_mem' := by
    rintro _ ⟨k, f, g, ⟨P, hP, rfl⟩, hG, hg, rfl⟩
    refine ⟨k, _, _, ⟨-P, by simpa using iso_sub (isWeightedHomogeneous_zero (ZMod ℓ) wt k) hP, map_neg _ _⟩, hG, hg, ?_⟩
    rw [map_neg, neg_div]
  inv_mem' := by
    rintro _ ⟨k, f, g, hF, hG, hg, rfl⟩
    by_cases hf : f = 0
    · exact ⟨k, 0, g, ⟨0, isWeightedHomogeneous_zero _ _ _, map_zero _⟩, hG, hg, by simp [hf]⟩
    · exact ⟨k, g, f, hG, hF, hf, by rw [inv_div]⟩

/-- Ratios of forms in the same class lie in `L`. -/
lemma mem_LF_of_class (h5 : 5 ≤ ℓ) {a b : ℕ} {f g : PowerSeries (ZMod ℓ)} (hf : FormBar ℓ a f) (hg : FormBar ℓ b g)
    (hab : a % (ℓ - 1) = b % (ℓ - 1)) (hg0 : g ≠ 0) : iF ℓ f / iF ℓ g ∈ LF ℓ := by
  rcases le_total a b with h | h
  · obtain ⟨m, hm⟩ := (Nat.modEq_iff_exists_eq_add h).mp hab
    have := hf.up h5 m
    refine ⟨b, f, g, ?_, hg, hg0, rfl⟩
    have e : a + m * (ℓ - 1) = b := by rw [hm]; ring
    rwa [e] at this
  · obtain ⟨m, hm⟩ := (Nat.modEq_iff_exists_eq_add h).mp hab.symm
    have := hg.up h5 m
    refine ⟨a, f, g, hf, ?_, hg0, rfl⟩
    have e : b + m * (ℓ - 1) = a := by rw [hm]; ring
    rwa [e] at this

lemma exists_primitive (s : ℕ) (hs : ℓ = 2 * s + 1) (hs0 : 0 < s) : ∃ ζ : ZMod ℓ, IsPrimitiveRoot ζ s := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod ℓ)ˣ)
  have hord : orderOf g = ℓ - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hℓ.out]
  have h1 : IsPrimitiveRoot (g : ZMod ℓ) (ℓ - 1) := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hord]
    exact IsPrimitiveRoot.orderOf g
  exact ⟨_, h1.pow (by omega) (by omega : ℓ - 1 = 2 * s)⟩

/-- **Forms in distinct classes are independent.** If `fᵢ` has weight in the class of `c + 2i` for `i < (ℓ-1)/2`, with
`c` even, and `∑ fᵢ = 0`, then every `fᵢ = 0`. -/
theorem class_sep (h5 : 5 ≤ ℓ) (s : ℕ) (hs : ℓ = 2 * s + 1) (c : ℕ) (hc : c % 2 = 0)
    (f : ℕ → PowerSeries (ZMod ℓ)) (k : ℕ → ℕ) (hf : ∀ i < s, FormBar ℓ (k i) (f i))
    (hk : ∀ i < s, k i % (ℓ - 1) = (c + 2 * i) % (ℓ - 1))
    (hsum : ∑ i ∈ Finset.range s, f i = 0) : ∀ i < s, f i = 0 := by
  have hs0 : 0 < s := by omega
  have hl1 : ℓ - 1 = 2 * s := by omega
  let E₄ := E4 (ZMod ℓ)
  let E₆ := E6 (ZMod ℓ)
  have hE4 : E₄ ≠ 0 := by
    intro h
    have := constantCoeff_E4 (R := ZMod ℓ)
    rw [show E4 (ZMod ℓ) = 0 from h, map_zero] at this
    exact zero_ne_one this
  have hE6 : E₆ ≠ 0 := by
    intro h
    have := constantCoeff_E6 (R := ZMod ℓ)
    rw [show E6 (ZMod ℓ) = 0 from h, map_zero] at this
    exact zero_ne_one this
  have hF4 : ∀ d, FormBar ℓ (4 * d) (E₄ ^ d) := fun d =>
    ⟨X 0 ^ d, by simpa using iso_mono (R := ZMod ℓ) d 0, by rw [map_pow, ev_X0]⟩
  have hF6 : ∀ d, FormBar ℓ (6 * d) (E₆ ^ d) := fun d =>
    ⟨X 1 ^ d, by simpa using iso_mono (R := ZMod ℓ) 0 d, by rw [map_pow, ev_X1]⟩
  let u : EF ℓ := iF ℓ E₆ / iF ℓ E₄
  have hi4 := iF_ne hE4
  have hi6 := iF_ne hE6
  have hu : u ≠ 0 := div_ne_zero hi6 hi4
  have huk : ∀ d, u ^ d = iF ℓ (E₆ ^ d) / iF ℓ (E₄ ^ d) := fun d => by
    simp only [u, div_pow, map_pow]
  have huL : u ^ s ∈ LF ℓ := by
    rw [huk]
    refine mem_LF_of_class h5 (hF6 s) (hF4 s) ?_ (pow_ne_zero _ hE4)
    rw [hl1, show 6 * s = 4 * s + 2 * s * 1 by ring, Nat.add_mul_mod_self_left]
  obtain ⟨ζ₀, hζ₀⟩ := exists_primitive (ℓ := ℓ) s hs hs0
  let ιc : ZMod ℓ →+* EF ℓ := (iF ℓ).comp (PowerSeries.C (R := ZMod ℓ))
  have hζ : IsPrimitiveRoot (ιc ζ₀) s := hζ₀.map_of_injective ιc.injective
  have hζL : ιc ζ₀ ∈ LF ℓ :=
    ⟨0, PowerSeries.C ζ₀, 1, ⟨C ζ₀, isWeightedHomogeneous_C _ _, ev_C _⟩,
      ⟨1, isWeightedHomogeneous_one _ _, map_one _⟩, one_ne_zero, by simp [ιc]⟩
  have hd : ∀ d, 0 < d → d < s → u ^ d ∉ LF ℓ := by
    rintro d hd0 hds ⟨K, _, _, ⟨P, hP, rfl⟩, ⟨Q, hQ, rfl⟩, hQ0, he⟩
    rw [huk] at he
    have hcross : iF ℓ (E₆ ^ d * ev (ZMod ℓ) Q) = iF ℓ (ev (ZMod ℓ) P * E₄ ^ d) := by
      rw [map_mul, map_mul]
      have h4 : iF ℓ (E₄ ^ d) ≠ 0 := iF_ne (pow_ne_zero _ hE4)
      have hQ' : iF ℓ (ev (ZMod ℓ) Q) ≠ 0 := iF_ne hQ0
      rw [div_eq_div_iff h4 hQ'] at he
      exact he
    have hcross' := iF_inj hcross
    have hne : E₆ ^ d * ev (ZMod ℓ) Q ≠ 0 := mul_ne_zero (pow_ne_zero _ hE6) hQ0
    obtain ⟨A₁, hA₁, heA⟩ : FormBar ℓ (6 * d + K) (E₆ ^ d * ev (ZMod ℓ) Q) := by
      obtain ⟨R, hR, heR⟩ := hF6 d
      exact ⟨R * Q, hR.mul hQ, by rw [map_mul, heR]⟩
    obtain ⟨B₁, hB₁, heB⟩ : FormBar ℓ (4 * d + K) (ev (ZMod ℓ) P * E₄ ^ d) := by
      obtain ⟨R, hR, heR⟩ := hF4 d
      exact ⟨R * P, iso_of_eq (hR.mul hP) rfl, by rw [map_mul, heR, mul_comm]⟩
    have hw := weight_class_le h5 hB₁ hA₁ (by omega) (by rw [heA, heB, hcross']) (by rw [heB, ← hcross']; exact hne)
    rw [show 6 * d + K - (4 * d + K) = 2 * d by omega, hl1] at hw
    have := Nat.le_of_dvd (by omega) hw
    omega
  have hw : (c + 2 * (ℓ - 1)) % 2 = 0 := by omega
  let w := c + 2 * (ℓ - 1)
  have hwb : 4 * bexp0 w + 6 * bexp1 w = w := by
    have : 6 ≤ w := by
      simp only [w]
      omega
    unfold bexp0 bexp1
    omega
  let G : PowerSeries (ZMod ℓ) := ev (ZMod ℓ) (base w)
  have hG : FormBar ℓ w G := ⟨_, iso_base hwb, rfl⟩
  have hG0 : G ≠ 0 := by
    intro h
    have h1 := constantCoeff_ev (R := ZMod ℓ) (base w)
    rw [eval_base] at h1
    rw [show ev (ZMod ℓ) (base w) = 0 from h, map_zero] at h1
    exact zero_ne_one h1
  have hiG := iF_ne hG0
  have hlam : ∀ i, i < s → iF ℓ (f i * E₄ ^ i) / iF ℓ (E₆ ^ i * G) ∈ LF ℓ := by
    intro i hi
    obtain ⟨P, hP, heP⟩ := hf i hi
    obtain ⟨R, hR, heR⟩ := hF4 i
    obtain ⟨S, hS, heS⟩ := hF6 i
    obtain ⟨T, hT, heT⟩ := hG
    refine mem_LF_of_class h5 (a := k i + 4 * i) (b := 6 * i + w)
      ⟨P * R, hP.mul hR, by rw [map_mul, heP, heR]⟩ ⟨S * T, hS.mul hT, by rw [map_mul, heS, heT]⟩ ?_
      (mul_ne_zero (pow_ne_zero _ hE6) hG0)
    have h1 := hk i hi
    rw [Nat.add_mod, h1, ← Nat.add_mod]
    simp only [w]
    rw [hl1, show c + 2 * i + 4 * i = c + 6 * i by ring,
      show 6 * i + (c + 2 * (2 * s)) = c + 6 * i + 2 * s * 2 by ring, Nat.add_mul_mod_self_left]
  let lam : ℕ → LF ℓ := fun i =>
    if hi : i < s then ⟨_, hlam i hi⟩ else 0
  have hlamv : ∀ i, i < s → (lam i : EF ℓ) * u ^ i = iF ℓ (f i) / iF ℓ G := by
    intro i hi
    simp only [lam, dif_pos hi]
    rw [huk, map_mul, map_mul]
    have h6 : iF ℓ (E₆ ^ i) ≠ 0 := iF_ne (pow_ne_zero _ hE6)
    have h4 : iF ℓ (E₄ ^ i) ≠ 0 := iF_ne (pow_ne_zero _ hE4)
    field_simp
  have hrel : ∑ i ∈ Finset.range s, (lam i : EF ℓ) * u ^ i = 0 := by
    rw [Finset.sum_congr rfl fun i hi => hlamv i (Finset.mem_range.mp hi), ← Finset.sum_div, ← map_sum, hsum,
      map_zero, zero_div]
  have hfree := kummer_free (LF ℓ) u hu s hs0 huL hζ hζL hd lam hrel
  intro i hi
  have h0 := hlamv i hi
  rw [hfree i hi] at h0
  simp only [ZeroMemClass.coe_zero, zero_mul] at h0
  have h1 : iF ℓ (f i) = 0 := by
    have := h0.symm
    rwa [div_eq_zero_iff, or_iff_left hiG] at this
  exact iF_inj (by rw [h1, map_zero])

end

end RamanujanTau.BLBound
