import RamanujanTau.KatzForms.Lift
import RamanujanTau.ModP.SwinnertonDyer

/-!
# Step (K) in the concrete model: Weierstrass test curves and the Hasse polynomial

* `K`: complete, ultrametric, algebraically closed. `φ : ℤ_[p] →+* K` with `‖φ x‖ ≤ 1` (so `K` has
  residue characteristic `p` exactly when `‖φ p‖ < 1`. That inequality is not needed below; it enters
  only through the supersingular-detection hypothesis).
* `Eh φ = map φ (hasseA p hp5)`: the Hasse polynomial, `E = E_{p−1}`, as a polynomial over `K`.
* A test object is a Weierstrass curve `W` with integral coefficients and `‖Δ(W)‖ = 1`. Its point is
  `pt W = (c₄(W), −c₆(W))`; the sign matches `c₆(Tate) = −E₆` (`TateCurve.c₆_Tate`).
* `katzPiece φ Bz i = K · φ(Bz i)`: the Katz piece `B_i ⊗ K` for a chosen `ℤ_[p]`-complement `Bz i`.

Main results:
* `katz_easy`: the `⇒` direction of (K), with no hypotheses on `b`.
* `katz_iff_weierstrass`: the full equivalence (K), assuming only `SSDetect`. That hypothesis says every
  element of `B i` attains its Gauss norm at some supersingular point of good reduction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace KatzForms
open MvPolynomial Filter Topology ModP

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-! ### Units and the Hasse polynomial over `K` -/

lemma norm_eq_one_of_mul {a b : ℝ} (ha0 : 0 ≤ a) (_hb0 : 0 ≤ b) (ha : a ≤ 1) (hb : b ≤ 1)
    (h : a * b = 1) : a = 1 := by nlinarith

section Hasse
variable {p : ℕ} [Fact p.Prime] (φ : ℤ_[p] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1)
include hφ

lemma norm_phi_unit {u : ℤ_[p]} (hu : IsUnit u) : ‖φ u‖ = 1 := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h : ‖φ u‖ * ‖φ v‖ = 1 := by rw [← norm_mul, ← map_mul, hv, map_one, norm_one]
  exact norm_eq_one_of_mul (norm_nonneg _) (norm_nonneg _) (hφ u) (hφ v) h

lemma norm_1728 (hp5 : 5 ≤ p) : ‖(1728 : K)‖ = 1 := by
  have := norm_phi_unit φ hφ (isUnit_1728_Zp hp5)
  rwa [map_ofNat] at this

lemma norm_48 (hp5 : 5 ≤ p) : ‖(48 : K)‖ = 1 :=
  norm_eq_one_of_mul (norm_nonneg _) (norm_nonneg (36 : K))
    (by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 48)
    (by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 36)
    (by rw [← norm_mul, show (48 : K) * 36 = 1728 by norm_num, norm_1728 φ hφ hp5])

lemma norm_864 (hp5 : 5 ≤ p) : ‖(864 : K)‖ = 1 :=
  norm_eq_one_of_mul (norm_nonneg _) (norm_nonneg (2 : K))
    (by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 864)
    (by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 2)
    (by rw [← norm_mul, show (864 : K) * 2 = 1728 by norm_num, norm_1728 φ hφ hp5])

omit hφ in
/-- The Hasse polynomial over `K`. -/
noncomputable def Eh (hp5 : 5 ≤ p) : MvPolynomial (Fin 2) K := MvPolynomial.map φ (hasseA p hp5)

lemma Eh_integral (hp5 : 5 ≤ p) (d : Fin 2 →₀ ℕ) : ‖(Eh φ hp5).coeff d‖ ≤ 1 := by
  rw [Eh, coeff_map]; exact hφ _

lemma Eh_unit_coeff (hp5 : 5 ≤ p) : ∃ d, ‖(Eh φ hp5).coeff d‖ = 1 := by
  have hne : hasseBar p hp5 ≠ 0 := by
    intro h
    have := ev_hasseBar hp5
    rw [h, map_zero] at this
    exact zero_ne_one this
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hne
  refine ⟨d, ?_⟩
  rw [Eh, coeff_map]
  apply norm_phi_unit φ hφ
  by_contra hu
  have hm : (hasseA p hp5).coeff d ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
    (IsLocalRing.mem_maximalIdeal _).mpr hu
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hm
  exact hd (by rw [hasseBar, coeff_map, hm])

omit hφ in
lemma Eh_uniq (hp5 : 5 ≤ p) (j : Fin 2) (d d' : Fin 2 →₀ ℕ) (hd : (Eh φ hp5).coeff d ≠ 0)
    (hd' : (Eh φ hp5).coeff d' ≠ 0) (hj : d j = d' j) : d = d' := by
  have hiso := iso_hasseA hp5
  have h1 : (hasseA p hp5).coeff d ≠ 0 := by
    intro h; apply hd; rw [Eh, coeff_map, h, map_zero]
  have h2 : (hasseA p hp5).coeff d' ≠ 0 := by
    intro h; apply hd'; rw [Eh, coeff_map, h, map_zero]
  have w1 := hiso h1
  have w2 := hiso h2
  rw [weight_wt] at w1 w2
  ext i
  fin_cases j <;> fin_cases i <;> simp at hj ⊢ <;> omega

end Hasse

/-! ### Weierstrass test curves -/

/-- Test objects: integral Weierstrass curves of good reduction. -/
def IsTest (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1 ∧ ‖W.Δ‖ = 1

/-- The point `(c₄, −c₆)` at which classical forms are evaluated (`X 0 ↦ E₄`, `X 1 ↦ E₆`). -/
noncomputable def pt (W : WeierstrassCurve K) : Fin 2 → K := ![W.c₄, -W.c₆]

/-- The closed unit ball as a subring. -/
def ball1 : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, norm_mul] at *; exact mul_le_one₀ hx (norm_nonneg _) hy
  one_mem' := by simp
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at *
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  zero_mem' := by simp
  neg_mem' {x} hx := by simpa using hx

lemma integral_pt {W : WeierstrassCurve K} (hW : IsTest W) : Integral (pt W) := by
  obtain ⟨h1, h2, h3, h4, h6, -⟩ := hW
  let W' : WeierstrassCurve (ball1 (K := K)) :=
    ⟨⟨W.a₁, h1⟩, ⟨W.a₂, h2⟩, ⟨W.a₃, h3⟩, ⟨W.a₄, h4⟩, ⟨W.a₆, h6⟩⟩
  have hmap : W'.map (ball1 (K := K)).subtype = W := rfl
  intro i
  fin_cases i
  · change ‖W.c₄‖ ≤ 1
    rw [← hmap, WeierstrassCurve.map_c₄]; exact W'.c₄.2
  · change ‖-W.c₆‖ ≤ 1
    rw [norm_neg, ← hmap, WeierstrassCurve.map_c₆]; exact W'.c₆.2

section Curves
variable {p : ℕ} [Fact p.Prime] (φ : ℤ_[p] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hp5 : 5 ≤ p)
include hφ hp5

lemma good_pt {W : WeierstrassCurve K} (hW : IsTest W) : Good (pt W) := by
  refine ⟨integral_pt hW, ?_⟩
  change ‖W.c₄ ^ 3 - (-W.c₆) ^ 2‖ = 1
  rw [neg_sq, ← W.c_relation, norm_mul, norm_1728 φ hφ hp5, hW.2.2.2.2.2, mul_one]

omit hφ hp5 in
/-- The short Weierstrass curve `y² = x³ − (x₀/48) x + x₁/864`, with `(c₄, −c₆) = (x₀, x₁)`. -/
noncomputable def ofPt (x : Fin 2 → K) : WeierstrassCurve K :=
  ⟨0, 0, 0, -(x 0 / 48), x 1 / 864⟩

lemma pt_ofPt (x : Fin 2 → K) : pt (ofPt x) = x := by
  have h48 : (48 : K) ≠ 0 := by intro h; have := norm_48 φ hφ hp5; rw [h, norm_zero] at this; simp at this
  have h864 : (864 : K) ≠ 0 := by
    intro h; have := norm_864 φ hφ hp5; rw [h, norm_zero] at this; simp at this
  ext i
  fin_cases i
  · simp [pt, ofPt, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    field_simp; ring
  · simp [pt, ofPt, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆]
    field_simp; ring

lemma isTest_ofPt {x : Fin 2 → K} (hx : Good x) : IsTest (ofPt x) := by
  have h48 := norm_48 φ hφ hp5
  have h864 := norm_864 φ hφ hp5
  refine ⟨by simp [ofPt], by simp [ofPt], by simp [ofPt], ?_, ?_, ?_⟩
  · simp only [ofPt, norm_neg, norm_div, h48, div_one]; exact hx.1 0
  · simp only [ofPt, norm_div, h864, div_one]; exact hx.1 1
  · have hrel := (ofPt x).c_relation
    have hpt := pt_ofPt φ hφ hp5 x
    have h0 : (ofPt x).c₄ = x 0 := congrFun hpt 0
    have h1 : -(ofPt x).c₆ = x 1 := congrFun hpt 1
    have : ‖(1728 : K) * (ofPt x).Δ‖ = 1 := by
      rw [hrel, h0, ← neg_sq, h1]; exact hx.2
    rwa [norm_mul, norm_1728 φ hφ hp5, one_mul] at this

end Curves

/-! ### Katz pieces and the main theorem -/

/-- `B_i ⊗ K`: the `K`-span of the image of a chosen `ℤ_[p]`-complement `Bz i`. -/
noncomputable def katzPiece {p : ℕ} [Fact p.Prime] (φ : ℤ_[p] →+* K)
    (Bz : ℕ → Set (MvPolynomial (Fin 2) ℤ_[p])) (i : ℕ) : Submodule K (MvPolynomial (Fin 2) K) :=
  Submodule.span K (MvPolynomial.map φ '' Bz i)

/-- **(K), `⇒`.** If `gnorm b_i ≤ ‖r‖^i` for all `i`, the Katz series has `‖f(W)‖ ≤ 1` at every test
curve with `‖E(W)‖ ≥ ‖r‖`. This holds for any `E`. -/
theorem katz_easy [CompleteSpace K] (E : MvPolynomial (Fin 2) K) (b : ℕ → MvPolynomial (Fin 2) K)
    {r : K} (hr0 : 0 < ‖r‖) (hcoef : ∀ i, gnorm (b i) ≤ ‖r‖ ^ i) {W : WeierstrassCurve K}
    (hW : IsTest W) (hrE : ‖r‖ ≤ ‖eval (pt W) E‖) : ‖kval E b (pt W)‖ ≤ 1 :=
  kval_le_one_of_coeff hr0 hcoef (integral_pt hW) hrE

/-- **(K) Katz expansions = sup norm, concrete model.** Fix `0 < ‖r‖ < 1` and Katz coefficients
`b_i ∈ B_i` (any `K`-subspaces) with `gnorm b_i / ‖r‖^i → 0`. Assume every element of every `B_i`
attains its Gauss norm at a supersingular point of good reduction (`SSDetect`). Then
`(∀ i, gnorm b_i ≤ ‖r‖^i) ↔ (∀ test curves W with ‖E(W)‖ ≥ ‖r‖, ‖Σ b_i(W)/E(W)^i‖ ≤ 1)`,
where `E` is the Hasse polynomial `map φ (hasseA p hp5)`. -/
theorem katz_iff_weierstrass [CompleteSpace K] [IsAlgClosed K] {p : ℕ} [Fact p.Prime]
    (φ : ℤ_[p] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hp5 : 5 ≤ p)
    (B : ℕ → Submodule K (MvPolynomial (Fin 2) K))
    (hss : ∀ i, ∀ β ∈ B i, SSDetect (Eh φ hp5) β)
    (r : K) (hr0 : 0 < ‖r‖) (hr1 : ‖r‖ < 1)
    (b : ℕ → MvPolynomial (Fin 2) K) (hbB : ∀ i, b i ∈ B i)
    (hb : Tendsto (fun i => gnorm (b i) / ‖r‖ ^ i) atTop (𝓝 0)) :
    (∀ i, gnorm (b i) ≤ ‖r‖ ^ i) ↔
      ∀ W : WeierstrassCurve K, IsTest W → ‖r‖ ≤ ‖eval (pt W) (Eh φ hp5)‖ →
        ‖kval (Eh φ hp5) b (pt W)‖ ≤ 1 := by
  set E := Eh φ hp5
  obtain ⟨d₀, hd₀⟩ := Eh_unit_coeff φ hφ hp5
  have hdet : ∀ i, DetectsNear Good E (b i) := fun i =>
    detectsNear_of_ss E (Eh_integral φ hφ hp5) hd₀ (Eh_uniq φ hp5 0) (Eh_uniq φ hp5 1) hr0 hr1
      (hss i (b i) (hbB i))
  rw [katz_iff E b r hr0 hr1 hb Good (fun x hx => hx.1) hdet]
  constructor
  · intro h W hW hrE
    exact h (pt W) (good_pt φ hφ hp5 hW) hrE
  · intro h x hx hrE
    have := h (ofPt x) (isTest_ofPt φ hφ hp5 hx) (by rwa [pt_ofPt φ hφ hp5])
    rwa [pt_ofPt φ hφ hp5] at this

end KatzForms
