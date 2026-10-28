import RamanujanTau.Igusa.Charts
import RamanujanTau.Igusa.Residue

/-!
# Discharging `SSDetect`: step (K) with an explicit monomial Katz complement

`K`: complete, ultrametric, algebraically closed, with `‖(p : K)‖ < 1` (residue characteristic `p`).
`φ : ℤ_[p] →+* K` integral. The residue field `Res K` is algebraically closed of characteristic `p`
(`Residue.lean`), and the reduction of `Eh φ hp5 = φ(A)` is `Ā ⊗ Res K` (`map_res_liftO_Eh`).

* `Bz p hp5 k₀ i`: the monomials `X₀^a X₁^b` (coefficient `1`) of weight `k₀ + i(p−1)` **not divisible by
  the leading monomial `X₀^{dA} X₁^{eA}` of `Ā`** (`Igusa.S`). Its `K`-span (`katzPiece`) consists of the
  polynomials supported on those monomials, and the Gauss norm is the max coefficient norm in this basis
  (the basis is a set of distinct monomials).
* `ssDetect_of_support`: every `β ∈ K[X₀,X₁]` supported on `S p hp5 k` satisfies `SSDetect (Eh φ hp5) β`.
* **`katz_iff_hasse`**: `KatzForms.katz_iff_weierstrass` for `B i = katzPiece φ (Bz p hp5 k₀) i`, with the
  hypothesis `hss` discharged. Remaining hypotheses: `‖(p:K)‖ < 1` and `RamanujanODE`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Igusa
open KatzForms MvPolynomial ModP Filter Topology

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪" => (ball1 (K := K))

section Red
variable (φ : ℤ_[p] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hpK : ‖(p : K)‖ < 1)

lemma res_phi (a : ℤ_[p]) :
    haveI := charP_res hp.out hpK
    res (⟨φ a, hφ a⟩ : 𝒪) = ZMod.castHom (dvd_refl p) (Res K) (PadicInt.toZMod a) := by
  haveI := charP_res hp.out hpK
  have hs := PadicInt.toZMod_spec a
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hs
  obtain ⟨b, hb⟩ := hs
  set z := PadicInt.toZMod a
  have hz : ((z.val : ℕ) : ℤ_[p]) = (z.cast : ℤ_[p]) := (ZMod.cast_eq_val z).symm
  have ha : a = (z.val : ℤ_[p]) + b * p := by rw [hz]; linear_combination -hb
  have he : (⟨φ a, hφ a⟩ : 𝒪) = (z.val : 𝒪) + ⟨φ b, hφ b⟩ * (p : 𝒪) := by
    apply Subtype.ext
    simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast]
    conv_lhs => rw [ha]
    rw [map_add, map_mul, map_natCast, map_natCast]
  rw [he, map_add, map_mul, map_natCast, map_natCast, CharP.cast_eq_zero (Res K) p, mul_zero, add_zero,
    ZMod.castHom_apply, ZMod.cast_eq_val]

lemma map_res_liftO_Eh (hp5 : 5 ≤ p) :
    haveI := charP_res hp.out hpK
    MvPolynomial.map res (liftO (Eh φ hp5) (Eh_integral φ hφ hp5)) = AF (Res K) p hp5 := by
  haveI := charP_res hp.out hpK
  ext d
  rw [coeff_map, coeff_liftO, AF, coeff_map, hasseBar, coeff_map]
  simp only [Eh, coeff_map]
  exact res_phi φ hφ hpK _

end Red

/-- Lifting a residue point. -/
lemma exists_lift_res (xb : Fin 2 → Res K) : ∃ xO : Fin 2 → 𝒪, ∀ i, res (xO i) = xb i :=
  ⟨fun i => (res_surj (xb i)).choose, fun i => (res_surj (xb i)).choose_spec⟩

lemma norm_eval_eq_one {P : MvPolynomial (Fin 2) K} (hP : ∀ d, ‖P.coeff d‖ ≤ 1) {xO : Fin 2 → 𝒪}
    (h : MvPolynomial.eval (fun i => res (xO i)) (MvPolynomial.map res (liftO P hP)) ≠ 0) :
    ‖MvPolynomial.eval (fun i => (xO i : K)) P‖ = 1 := by
  rw [← eval_liftO P hP]
  exact norm_eq_one_of_res_ne_zero (by rwa [res_eval])

lemma norm_eval_lt_one {P : MvPolynomial (Fin 2) K} (hP : ∀ d, ‖P.coeff d‖ ≤ 1) {xO : Fin 2 → 𝒪}
    (h : MvPolynomial.eval (fun i => res (xO i)) (MvPolynomial.map res (liftO P hP)) = 0) :
    ‖MvPolynomial.eval (fun i => (xO i : K)) P‖ < 1 := by
  rw [← eval_liftO P hP]
  exact res_eq_zero_iff.mp (by rwa [res_eval])

variable [IsAlgClosed K]

/-- A residue supersingular point lifts to a good point with `‖E‖ < 1`. -/
lemma good_lift (φ : ℤ_[p] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hpK : ‖(p : K)‖ < 1) (hp5 : 5 ≤ p)
    (xO : Fin 2 → 𝒪)
    (hA : haveI := charP_res hp.out hpK
      MvPolynomial.eval (fun i => res (xO i)) (AF (Res K) p hp5) = 0)
    (hD : res (xO 0) ^ 3 - res (xO 1) ^ 2 ≠ 0) :
    Good (fun i => (xO i : K)) ∧ ‖MvPolynomial.eval (fun i => (xO i : K)) (Eh φ hp5)‖ < 1 := by
  haveI := charP_res hp.out hpK
  refine ⟨⟨fun i => (xO i).2, ?_⟩, ?_⟩
  · have : res (xO 0 ^ 3 - xO 1 ^ 2) ≠ 0 := by simpa using hD
    have h := norm_eq_one_of_res_ne_zero this
    simpa using h
  · apply norm_eval_lt_one (Eh_integral φ hφ hp5)
    rw [map_res_liftO_Eh φ hφ hpK hp5]; exact hA

lemma gnorm_zero : gnorm (0 : MvPolynomial (Fin 2) K) = 0 := by simp [gnorm]

/-- **Supersingular detection for polynomials supported on the complement `S`.** -/
theorem ssDetect_of_support (φ : ℤ_[p] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hpK : ‖(p : K)‖ < 1)
    (hp5 : 5 ≤ p) (hR : RamanujanODE) {k : ℕ} {β : MvPolynomial (Fin 2) K}
    (hS : (β.support : Set (Fin 2 →₀ ℕ)) ⊆ S p hp5 k) : SSDetect (Eh φ hp5) β := by
  haveI := charP_res hp.out hpK
  by_cases hβ : β = 0
  · subst hβ
    obtain ⟨xb, hA, hD⟩ := exists_ss (F := Res K) hp5 hR
    obtain ⟨xO, hxO⟩ := exists_lift_res xb
    have hx : (fun i => res (xO i)) = xb := funext hxO
    obtain ⟨hg, hE⟩ := good_lift φ hφ hpK hp5 xO (by rw [hx]; exact hA) (by rw [hxO, hxO]; exact hD)
    exact ⟨_, hg, hE, by simp [gnorm_zero]⟩
  -- normalize
  obtain ⟨d, hd⟩ := exists_coeff_eq_gnorm β
  set c := β.coeff d
  have hc : c ≠ 0 := by
    intro h0
    apply hβ
    ext e
    have := norm_coeff_le_gnorm β e
    rw [← hd, h0, norm_zero] at this
    simpa using norm_le_zero_iff.mp this
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set β' := C c⁻¹ * β with hβ'
  have hcoef' : ∀ e, β'.coeff e = c⁻¹ * β.coeff e := fun e => by rw [hβ', coeff_C_mul]
  have hint : ∀ e, ‖β'.coeff e‖ ≤ 1 := fun e => by
    rw [hcoef', norm_mul, norm_inv, inv_mul_le_iff₀ hc0, mul_one, hd]
    exact norm_coeff_le_gnorm β e
  set βb := MvPolynomial.map res (liftO β' hint)
  have hcb : ∀ e, βb.coeff e ≠ 0 → β.coeff e ≠ 0 := by
    intro e he h0
    apply he
    rw [coeff_map, coeff_liftO]
    have : (⟨β'.coeff e, hint e⟩ : 𝒪) = 0 := Subtype.ext (by simp [hcoef', h0])
    rw [this, map_zero]
  have hβb : βb ≠ 0 := by
    intro h0
    have h1 := congrArg (coeff d) h0
    rw [coeff_map, coeff_liftO, coeff_zero] at h1
    have : (⟨β'.coeff d, hint d⟩ : 𝒪) = 1 := Subtype.ext (by simp [hcoef', inv_mul_cancel₀ hc, c])
    rw [this, map_one] at h1
    exact one_ne_zero h1
  have hSb : (βb.support : Set (Fin 2 →₀ ℕ)) ⊆ S p hp5 k := by
    intro e he
    exact hS (mem_support_iff.mpr (hcb e (mem_support_iff.mp he)))
  obtain ⟨xb, hA, hD, hB⟩ := exists_ss_nonvanishing (F := Res K) hp5 hR hβb hSb
  obtain ⟨xO, hxO⟩ := exists_lift_res xb
  have hx : (fun i => res (xO i)) = xb := funext hxO
  obtain ⟨hg, hE⟩ := good_lift φ hφ hpK hp5 xO (by rw [hx]; exact hA) (by rw [hxO, hxO]; exact hD)
  refine ⟨_, hg, hE, ?_⟩
  have h1 := norm_eval_eq_one hint (xO := xO) (by rw [hx]; exact hB)
  have hβeq : β = C c * β' := by rw [hβ', ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
  calc ‖MvPolynomial.eval (fun i => (xO i : K)) β‖
      = ‖c‖ * ‖MvPolynomial.eval (fun i => (xO i : K)) β'‖ := by
        conv_lhs => rw [hβeq]
        rw [map_mul, eval_C, norm_mul]
    _ = gnorm β := by rw [h1, mul_one, hd]

/-! ### The explicit Katz complement -/

/-- The monomial `ℤ_[p]`-basis of the Katz piece of weight `k₀ + i(p−1)`. -/
def Bz (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (k₀ i : ℕ) : Set (MvPolynomial (Fin 2) ℤ_[p]) :=
  (fun s => monomial s 1) '' S p hp5 (k₀ + i * (p - 1))

lemma support_subset_of_mem_katzPiece (φ : ℤ_[p] →+* K) (hp5 : 5 ≤ p) (k₀ i : ℕ)
    {β : MvPolynomial (Fin 2) K} (hβ : β ∈ katzPiece φ (Bz p hp5 k₀) i) :
    (β.support : Set (Fin 2 →₀ ℕ)) ⊆ S p hp5 (k₀ + i * (p - 1)) := by
  have hle : katzPiece φ (Bz p hp5 k₀) i ≤ restrictSupport K (S p hp5 (k₀ + i * (p - 1))) := by
    rw [katzPiece, Submodule.span_le]
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    rw [map_monomial, map_one]
    exact (MvPolynomial.monomial_mem_restrictSupport (R := K)).mpr (Or.inl hs)
  exact hle hβ

/-- **Step (K) with `SSDetect` discharged.** `B i = K`-span of the monomials of weight `k₀ + i(p−1)` not
divisible by the leading monomial of `Ā`. -/
theorem katz_iff_hasse [CompleteSpace K] (φ : ℤ_[p] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hpK : ‖(p : K)‖ < 1) (hp5 : 5 ≤ p) (hR : RamanujanODE) (k₀ : ℕ)
    (r : K) (hr0 : 0 < ‖r‖) (hr1 : ‖r‖ < 1)
    (b : ℕ → MvPolynomial (Fin 2) K) (hbB : ∀ i, b i ∈ katzPiece φ (Bz p hp5 k₀) i)
    (hb : Tendsto (fun i => gnorm (b i) / ‖r‖ ^ i) atTop (𝓝 0)) :
    (∀ i, gnorm (b i) ≤ ‖r‖ ^ i) ↔
      ∀ W : WeierstrassCurve K, IsTest W → ‖r‖ ≤ ‖eval (pt W) (Eh φ hp5)‖ →
        ‖kval (Eh φ hp5) b (pt W)‖ ≤ 1 :=
  katz_iff_weierstrass φ hφ hp5 (katzPiece φ (Bz p hp5 k₀))
    (fun i β hβ => ssDetect_of_support φ hφ hpK hp5 hR
      (support_subset_of_mem_katzPiece φ hp5 k₀ i hβ)) r hr0 hr1 b hbB hb

end Igusa
