/-
# Kloosterman's bound for prime moduli (Kloosterman 1927, fourth-moment method)

For `p` prime and any `b`:  `|S(1,b;p)|⁴ ≤ 3 p³`.

Proof: `∑_{a,b ∈ 𝔽_p} |S(a,b;p)|⁴ = p² N`, where `N` counts `(x₁,x₂,x₃,x₄) ∈ (𝔽_p^×)⁴` with
`x₁+x₂ = x₃+x₄` and `x₁⁻¹+x₂⁻¹ = x₃⁻¹+x₄⁻¹`; elementary algebra gives `N ≤ 3(p-1)²`; and
`S(a, b a⁻¹) = S(1, b)` for the `p - 1` units `a`.
-/
import RamanujanTau.TauBound.KlBasic

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Complex
open scoped Real ComplexConjugate

variable {p : ℕ} [hp : Fact p.Prime]

local notation "ψ" => (ZMod.stdAddChar (N := p))

lemma conj_stdAddChar (x : ZMod p) : conj (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv, ← Complex.inv_eq_conj (norm_stdAddChar p x)]

lemma kl_eq_field (a b : ZMod p) :
    kl p a b = ∑ u : (ZMod p)ˣ, ψ (a * (u : ZMod p) + b * (u : ZMod p)⁻¹) := by
  unfold kl; simp only [Units.val_inv_eq_inv_val]

/-- Sum and inverse-sum of a pair of units. -/
noncomputable def sP (w : (ZMod p)ˣ × (ZMod p)ˣ) : ZMod p := (w.1 : ZMod p) + w.2
/-- Inverse-sum of a pair of units. -/
noncomputable def tP (w : (ZMod p)ˣ × (ZMod p)ˣ) : ZMod p := (w.1 : ZMod p)⁻¹ + (w.2 : ZMod p)⁻¹

lemma kl_sq (a b : ZMod p) :
    kl p a b ^ 2 = ∑ w : (ZMod p)ˣ × (ZMod p)ˣ, ψ (a * sP w + b * tP w) := by
  rw [sq, kl_eq_field, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_congr _ _ (fun w => ?_)
  rw [← AddChar.map_add_eq_mul, sP, tP]
  ring_nf

lemma conj_kl_sq (a b : ZMod p) :
    conj (kl p a b ^ 2) = ∑ w : (ZMod p)ˣ × (ZMod p)ˣ, ψ (-(a * sP w + b * tP w)) := by
  rw [kl_sq, map_sum]
  simp only [conj_stdAddChar]

lemma sum_psi_mul (x : ZMod p) : ∑ a : ZMod p, ψ (a * x) = if x = 0 then (p : ℂ) else 0 := by
  rw [AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar p)]
  simp [ZMod.card]

/-- The fourth-moment identity `∑_{a,b} |S(a,b)|⁴ = p² N`. -/
theorem sum_norm_kl_pow_four :
    (∑ a : ZMod p, ∑ b : ZMod p, (‖kl p a b‖ ^ 4 : ℝ) : ℂ) =
      (p : ℂ) ^ 2 * ((Finset.univ.filter (fun ww : ((ZMod p)ˣ × (ZMod p)ˣ) ×
        ((ZMod p)ˣ × (ZMod p)ˣ) => sP ww.1 = sP ww.2 ∧ tP ww.1 = tP ww.2)).card : ℂ) := by
  have h4 : ∀ a b : ZMod p, ((‖kl p a b‖ ^ 4 : ℝ) : ℂ) = kl p a b ^ 2 * conj (kl p a b ^ 2) := by
    intro a b
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow]
    push_cast; ring
  have hterm : ∀ a b : ZMod p, kl p a b ^ 2 * conj (kl p a b ^ 2) =
      ∑ ww : ((ZMod p)ˣ × (ZMod p)ˣ) × ((ZMod p)ˣ × (ZMod p)ˣ),
        ψ (a * (sP ww.1 - sP ww.2)) * ψ (b * (tP ww.1 - tP ww.2)) := by
    intro a b
    rw [conj_kl_sq, kl_sq, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    refine Fintype.sum_congr _ _ (fun ww => ?_)
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; ring_nf
  simp_rw [h4, hterm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm), Finset.sum_comm]
  have hinner : ∀ ww : ((ZMod p)ˣ × (ZMod p)ˣ) × ((ZMod p)ˣ × (ZMod p)ˣ),
      ∑ a : ZMod p, ∑ b : ZMod p, ψ (a * (sP ww.1 - sP ww.2)) * ψ (b * (tP ww.1 - tP ww.2)) =
        if sP ww.1 = sP ww.2 ∧ tP ww.1 = tP ww.2 then (p : ℂ) ^ 2 else 0 := by
    intro ww
    rw [← Finset.sum_mul_sum, sum_psi_mul, sum_psi_mul]
    simp only [sub_eq_zero]
    split_ifs <;> simp_all [sq]
  simp_rw [hinner]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  ring

/-! ### Counting the solutions -/

/-- The three parametrised families of solutions. -/
noncomputable def solF1 (w : (ZMod p)ˣ × (ZMod p)ˣ) :
    ((ZMod p)ˣ × (ZMod p)ˣ) × ((ZMod p)ˣ × (ZMod p)ˣ) := (w, w)
/-- Second family. -/
noncomputable def solF2 (w : (ZMod p)ˣ × (ZMod p)ˣ) :
    ((ZMod p)ˣ × (ZMod p)ˣ) × ((ZMod p)ˣ × (ZMod p)ˣ) := (w, (w.2, w.1))
/-- Third family. -/
noncomputable def solF3 (w : (ZMod p)ˣ × (ZMod p)ˣ) :
    ((ZMod p)ˣ × (ZMod p)ˣ) × ((ZMod p)ˣ × (ZMod p)ˣ) := ((w.1, -w.1), (w.2, -w.2))

lemma mem_families (x1 x2 x3 x4 : (ZMod p)ˣ)
    (hs : (x1 : ZMod p) + x2 = x3 + x4)
    (ht : (x1 : ZMod p)⁻¹ + (x2 : ZMod p)⁻¹ = (x3 : ZMod p)⁻¹ + (x4 : ZMod p)⁻¹) :
    ((x1, x2), (x3, x4)) = solF1 (x1, x2) ∨ ((x1, x2), (x3, x4)) = solF2 (x1, x2) ∨
      ((x1, x2), (x3, x4)) = solF3 (x1, x3) := by
  have h1 : (x1 : ZMod p) ≠ 0 := x1.ne_zero
  have h2 : (x2 : ZMod p) ≠ 0 := x2.ne_zero
  have h3 : (x3 : ZMod p) ≠ 0 := x3.ne_zero
  have h4 : (x4 : ZMod p) ≠ 0 := x4.ne_zero
  by_cases hS : (x1 : ZMod p) + x2 = 0
  · right; right
    have e2 : x2 = -x1 := Units.ext (by simp; linear_combination hS)
    have e4 : x4 = -x3 := Units.ext (by simp; linear_combination hS - hs)
    simp [solF3, e2, e4]
  · have hprod : (x1 : ZMod p) * x2 = x3 * x4 := by
      have ht' : ((x1 : ZMod p) + x2) * (x3 * x4) = ((x3 : ZMod p) + x4) * (x1 * x2) := by
        field_simp at ht; linear_combination ht
      rw [← hs] at ht'
      have : ((x1 : ZMod p) + x2) * ((x3 : ZMod p) * x4 - x1 * x2) = 0 := by
        linear_combination ht'
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hS
      · linear_combination -h
    have hq : ((x3 : ZMod p) - x1) * ((x3 : ZMod p) - x2) = 0 := by
      linear_combination (-(x3 : ZMod p)) * hs + hprod
    rcases mul_eq_zero.mp hq with h | h
    · left
      have e3 : x3 = x1 := Units.ext (by linear_combination h)
      have e4 : x4 = x2 := Units.ext (by rw [e3] at hs; linear_combination -hs)
      simp [solF1, e3, e4]
    · right; left
      have e3 : x3 = x2 := Units.ext (by linear_combination h)
      have e4 : x4 = x1 := Units.ext (by rw [e3] at hs; linear_combination -hs)
      simp [solF2, e3, e4]

lemma card_units_prime : Fintype.card (ZMod p)ˣ = p - 1 := by
  rw [ZMod.card_units_eq_totient, Nat.totient_prime hp.out]

/-- `N ≤ 3 (p-1)²`. -/
theorem card_solutions_le :
    (Finset.univ.filter (fun ww : ((ZMod p)ˣ × (ZMod p)ˣ) × ((ZMod p)ˣ × (ZMod p)ˣ) =>
      sP ww.1 = sP ww.2 ∧ tP ww.1 = tP ww.2)).card ≤ 3 * (p - 1) ^ 2 := by
  classical
  have hsub : Finset.univ.filter (fun ww : ((ZMod p)ˣ × (ZMod p)ˣ) × ((ZMod p)ˣ × (ZMod p)ˣ) =>
      sP ww.1 = sP ww.2 ∧ tP ww.1 = tP ww.2) ⊆
      (Finset.univ.image solF1 ∪ Finset.univ.image solF2) ∪ Finset.univ.image solF3 := by
    rintro ⟨⟨x1, x2⟩, ⟨x3, x4⟩⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, sP, tP] at hmem
    rcases mem_families x1 x2 x3 x4 hmem.1 hmem.2 with h | h | h
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  have hc : ∀ f : (ZMod p)ˣ × (ZMod p)ˣ → ((ZMod p)ˣ × (ZMod p)ˣ) × ((ZMod p)ˣ × (ZMod p)ˣ),
      (Finset.univ.image f).card ≤ (p - 1) ^ 2 := by
    intro f
    refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Finset.card_univ, Fintype.card_prod, card_units_prime, sq]
  have := hc (solF1 (p := p)); have := hc (solF2 (p := p)); have := hc (solF3 (p := p))
  have := Finset.card_union_le (Finset.univ.image (solF1 (p := p)))
    (Finset.univ.image (solF2 (p := p)))
  omega

/-- **Kloosterman's bound** for prime moduli: `|S(1,b;p)|⁴ ≤ 3 p³`. -/
theorem norm_kl_prime_pow_four_le (b : ZMod p) : ‖kl p 1 b‖ ^ 4 ≤ 3 * (p : ℝ) ^ 3 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hid := sum_norm_kl_pow_four (p := p)
  have hreal : (∑ a : ZMod p, ∑ b : ZMod p, ‖kl p a b‖ ^ 4 : ℝ) =
      (p : ℝ) ^ 2 * ((Finset.univ.filter (fun ww : ((ZMod p)ˣ × (ZMod p)ˣ) ×
        ((ZMod p)ˣ × (ZMod p)ˣ) => sP ww.1 = sP ww.2 ∧ tP ww.1 = tP ww.2)).card : ℝ) := by
    exact_mod_cast hid
  have hN : ((Finset.univ.filter (fun ww : ((ZMod p)ˣ × (ZMod p)ˣ) ×
        ((ZMod p)ˣ × (ZMod p)ˣ) => sP ww.1 = sP ww.2 ∧ tP ww.1 = tP ww.2)).card : ℝ) ≤
      3 * ((p : ℝ) - 1) ^ 2 := by
    have := card_solutions_le (p := p)
    have h' : (((3 * (p - 1) ^ 2 : ℕ)) : ℝ) = 3 * ((p : ℝ) - 1) ^ 2 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
    rw [← h']; exact_mod_cast this
  -- lower bound by the orbit `a ↦ (a, b a⁻¹)`
  set K := ‖kl p 1 b‖ ^ 4
  have horbit : ∀ a : ZMod p, (if a = 0 then (0 : ℝ) else K) ≤ ∑ b' : ZMod p, ‖kl p a b'‖ ^ 4 := by
    intro a
    split_ifs with ha
    · exact Finset.sum_nonneg fun _ _ => by positivity
    · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
      have hk : kl p a (a⁻¹ * b) = kl p 1 b := by
        have := kl_unit_eq p hu.unit (a⁻¹ * b)
        simp only [IsUnit.unit_spec] at this
        rw [this, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
      have := Finset.single_le_sum (f := fun b' => ‖kl p a b'‖ ^ 4)
        (fun _ _ => by positivity) (Finset.mem_univ (a⁻¹ * b))
      simp only at this
      rwa [hk] at this
  have hsumG : (∑ a : ZMod p, (if a = 0 then (0 : ℝ) else K)) = ((p : ℝ) - 1) * K := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have : (Finset.univ.filter (fun a : ZMod p => ¬ a = 0)).card = p - 1 := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      simp [ZMod.card, Finset.filter_eq']
    rw [this]; push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
  have hmain : ((p : ℝ) - 1) * K ≤ (p : ℝ) ^ 2 * (3 * ((p : ℝ) - 1) ^ 2) := by
    rw [← hsumG]
    calc (∑ a : ZMod p, (if a = 0 then (0 : ℝ) else K))
        ≤ ∑ a : ZMod p, ∑ b' : ZMod p, ‖kl p a b'‖ ^ 4 := Finset.sum_le_sum fun a _ => horbit a
      _ = _ := hreal
      _ ≤ _ := by gcongr
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  have hK : K ≤ 3 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) := by
    have : ((p : ℝ) - 1) * K ≤ ((p : ℝ) - 1) * (3 * (p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by
      nlinarith
    exact le_of_mul_le_mul_left this hp1
  nlinarith [sq_nonneg (p : ℝ)]

end RamanujanTau.TauBound
