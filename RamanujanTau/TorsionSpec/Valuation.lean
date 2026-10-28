import RamanujanTau.HeightEll.Kummer
import RamanujanTau.Velu.Defs

/-!
# Torsion abscissae lie in every valuation ring of residue characteristic `0`

Let `V` be a valuation subring of a field `L` containing `A, B` and all `1/n` (`n ≥ 1`), and let
`P = (x, y)` be a point of `y² = x³ + Ax + B` with `x ∉ V`. Writing `u = 1/x ∈ 𝔪_V` and
`rₙ = x(nP)/x`, the Kummer-line relations give, by induction, `rₙ ∈ V` with residue `1/n²`; in
particular `nP ≠ 0` for every `n ≥ 1` (**`nsmul_ne_zero_of_not_mem`**). Hence a torsion point has
`x(P) ∈ V` (**`xc_mem_of_nsmul_eq_zero`**).
-/

set_option autoImplicit false

namespace TorsionSpec

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

variable {L : Type*} [Field L] (V : ValuationSubring L)

/-- `z ∈ V` with residue `ρ`. -/
def Res (z : L) (ρ : ResidueField V) : Prop := ∃ hz : z ∈ V, residue V ⟨z, hz⟩ = ρ

namespace Res
variable {V}

lemma of_mem {z : L} (hz : z ∈ V) : Res V z (residue V ⟨z, hz⟩) := ⟨hz, rfl⟩

lemma add {z w : L} {ρ σ : ResidueField V} (h : Res V z ρ) (h' : Res V w σ) :
    Res V (z + w) (ρ + σ) := by
  obtain ⟨hz, rfl⟩ := h; obtain ⟨hw, rfl⟩ := h'
  exact ⟨add_mem hz hw, by rw [← map_add]; rfl⟩

lemma mul {z w : L} {ρ σ : ResidueField V} (h : Res V z ρ) (h' : Res V w σ) :
    Res V (z * w) (ρ * σ) := by
  obtain ⟨hz, rfl⟩ := h; obtain ⟨hw, rfl⟩ := h'
  exact ⟨mul_mem hz hw, by rw [← map_mul]; rfl⟩

lemma neg {z : L} {ρ : ResidueField V} (h : Res V z ρ) : Res V (-z) (-ρ) := by
  obtain ⟨hz, rfl⟩ := h
  exact ⟨neg_mem hz, by rw [← map_neg]; rfl⟩

lemma sub {z w : L} {ρ σ : ResidueField V} (h : Res V z ρ) (h' : Res V w σ) :
    Res V (z - w) (ρ - σ) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact h.add h'.neg

lemma pow {z : L} {ρ : ResidueField V} (h : Res V z ρ) (m : ℕ) : Res V (z ^ m) (ρ ^ m) := by
  induction m with
  | zero => exact ⟨by simp, by simp only [pow_zero]; rw [← map_one (residue V)]; rfl⟩
  | succ m ih => rw [pow_succ, pow_succ]; exact ih.mul h

lemma natCast (m : ℕ) : Res V (m : L) (m : ResidueField V) :=
  ⟨natCast_mem V m, by rw [← map_natCast (residue V) m]; rfl⟩

lemma one : Res V (1 : L) 1 := by simpa using natCast (V := V) 1

lemma ofNat (m : ℕ) [m.AtLeastTwo] : Res V (OfNat.ofNat m : L) (OfNat.ofNat m) := by
  simpa using natCast (V := V) m

lemma unique {z : L} {ρ σ : ResidueField V} (h : Res V z ρ) (h' : Res V z σ) : ρ = σ := by
  obtain ⟨_, rfl⟩ := h; obtain ⟨_, rfl⟩ := h'; rfl

lemma ne_zero {z : L} {ρ : ResidueField V} (h : Res V z ρ) (hρ : ρ ≠ 0) : z ≠ 0 := by
  rintro rfl
  obtain ⟨_, rfl⟩ := h
  exact hρ (by rw [show (⟨0, V.zero_mem⟩ : V) = 0 from rfl, map_zero])

lemma inv {z : L} {ρ : ResidueField V} (h : Res V z ρ) (hρ : ρ ≠ 0) : Res V z⁻¹ ρ⁻¹ := by
  obtain ⟨hz, rfl⟩ := h
  obtain ⟨w, hw⟩ := ((residue_ne_zero_iff_isUnit _).1 hρ).exists_right_inv
  have hw' : z * (w : L) = 1 := by simpa using congrArg Subtype.val hw
  have : z⁻¹ = w := (eq_inv_of_mul_eq_one_right hw').symm
  refine ⟨this ▸ w.2, ?_⟩
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul]
  have e : (⟨z⁻¹, this ▸ w.2⟩ : V) = w := Subtype.ext this
  rw [e, mul_comm, hw, map_one]

lemma div {z w : L} {ρ σ : ResidueField V} (h : Res V z ρ) (h' : Res V w σ) (hσ : σ ≠ 0) :
    Res V (z / w) (ρ / σ) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]; exact h.mul (h'.inv hσ)

lemma congr {z w : L} {ρ σ : ResidueField V} (h : Res V z ρ) (hz : z = w) (hρ : ρ = σ) :
    Res V w σ := hz ▸ hρ ▸ h

end Res

/-- `u = 1/x` has residue `0` when `x ∉ V`. -/
lemma res_inv_of_not_mem {x : L} (hx : x ∉ V) : Res V x⁻¹ 0 := by
  have hu : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hx
  refine ⟨hu, ?_⟩
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  have hw' : x⁻¹ * (w : L) = 1 := by simpa using congrArg Subtype.val hw
  have hx0 : x ≠ 0 := by rintro rfl; exact hx V.zero_mem
  have : (w : L) = x := by field_simp at hw'; exact hw'
  exact hx (this ▸ w.2)

section Torsion

open Velu

variable {V} {A B : L}

lemma short_b₂ : (short A B : WeierstrassCurve L).b₂ = 0 := by simp [WeierstrassCurve.b₂]
lemma short_b₄ : (short A B : WeierstrassCurve L).b₄ = 2 * A := by simp [WeierstrassCurve.b₄]
lemma short_b₆ : (short A B : WeierstrassCurve L).b₆ = 4 * B := by simp [WeierstrassCurve.b₆]
lemma short_b₈ : (short A B : WeierstrassCurve L).b₈ = -A ^ 2 := by
  simp [WeierstrassCurve.b₈]

lemma hxc_eq (P : (short A B).Point) : HeightEll.xc (short A B) P = Velu.xc P := by
  cases P <;> rfl

variable [DecidableEq L]

/-- **Key estimate.** If `x(P) ∉ V`, then for every `n ≥ 1`, `nP ≠ 0` and `x(nP)/x(P) ∈ V` has
residue `1/n²`. -/
theorem res_nsmul (hA : A ∈ V) (hB : B ∈ V) (hchar : ∀ m : ℕ, 0 < m → (m : ResidueField V) ≠ 0)
    {x y : L} (h : (short A B).Nonsingular x y) (hx : x ∉ V) :
    ∀ n : ℕ, 1 ≤ n → n • (Point.some x y h : (short A B).Point) ≠ 0 ∧
      Res V (Velu.xc (n • (Point.some x y h : (short A B).Point)) / x)
        ((n : ResidueField V) ^ 2)⁻¹ := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hx V.zero_mem
  have hu := res_inv_of_not_mem V hx
  have hux : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  set u := x⁻¹ with hu_def
  have hAr := Res.of_mem hA
  have hBr := Res.of_mem hB
  have h4 : (4 : ResidueField V) ≠ 0 := by exact_mod_cast hchar 4 (by norm_num)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  match n, hn with
  | 1, _ =>
    refine ⟨by rw [one_nsmul]; exact Point.some_ne_zero h, ?_⟩
    rw [one_nsmul, Velu.xc_some, div_self hx0]
    exact Res.congr Res.one rfl (by simp)
  | 2, _ =>
    -- the unit `4 + 4A u² + 4B u³`
    have hD : Res V (4 + 4 * A * u ^ 2 + 4 * B * u ^ 3) 4 :=
      Res.congr ((((Res.ofNat 4).add (((Res.ofNat 4).mul hAr).mul (hu.pow 2))).add
        (((Res.ofNat 4).mul hBr).mul (hu.pow 3)))) rfl (by simp)
    have hPsi : HeightEll.kPsi (short A B : WeierstrassCurve L) x =
        x ^ 3 * (4 + 4 * A * u ^ 2 + 4 * B * u ^ 3) := by
      rw [HeightEll.kPsi, short_b₂, short_b₄, short_b₆]
      linear_combination (-4 * A * x * (x * u + 1) - 4 * B * (x ^ 2 * u ^ 2 + x * u + 1)) * hux
    have hP2 : Point.some x y h + Point.some x y h ≠ 0 := by
      intro h0
      by_cases hy : y = (short A B).negY x y
      · have e := HeightEll.sq_eq_kPsi (short A B : WeierstrassCurve L) h
        rw [← hy, sub_self, hPsi] at e
        exact mul_ne_zero (pow_ne_zero 3 hx0) (hD.ne_zero h4) (by rw [← e]; ring)
      · rw [Point.add_self_of_Y_ne hy] at h0; exact Point.some_ne_zero _ h0
    obtain ⟨hp, hd⟩ := HeightEll.doubling (short A B : WeierstrassCurve L) h hP2
    refine ⟨by rwa [two_nsmul], ?_⟩
    rw [two_nsmul, ← hxc_eq]
    have hN : Res V (1 - 2 * A * u ^ 2 - 8 * B * u ^ 3 + A ^ 2 * u ^ 4) 1 :=
      Res.congr (((Res.one.sub (((Res.ofNat 2).mul hAr).mul (hu.pow 2))).sub
        (((Res.ofNat 8).mul hBr).mul (hu.pow 3))).add ((hAr.pow 2).mul (hu.pow 4))) rfl (by simp)
    refine Res.congr (hN.div hD h4) ?_ (by norm_num)
    have hDne := hD.ne_zero h4
    rw [hPsi] at hd
    rw [HeightEll.kPhi, short_b₄, short_b₆, short_b₈] at hd
    set X := HeightEll.xc (short A B : WeierstrassCurve L) (Point.some x y h + Point.some x y h)
    rw [div_eq_div_iff hDne hx0]
    apply mul_left_cancel₀ (pow_ne_zero 3 hx0)
    linear_combination -hd + (-2 * A * x ^ 2 * (x * u + 1) - 8 * B * x * (x ^ 2 * u ^ 2 + x * u + 1)
      + A ^ 2 * (x * u + 1) * (x ^ 2 * u ^ 2 + 1)) * hux
  | m + 3, _ =>
    obtain ⟨h2ne, r2⟩ := ih (m + 2) (by omega) (by omega)
    obtain ⟨-, r1⟩ := ih (m + 1) (by omega) (by omega)
    obtain ⟨x₁, y₁, h₁, hA1⟩ := HeightEll.eq_some_of_ne_zero (short A B : WeierstrassCurve L) h2ne
    rw [hA1, Velu.xc_some] at r2
    have k1 : ((m + 1 : ℕ) : ResidueField V) ≠ 0 := hchar _ (by omega)
    have k2 : ((m + 2 : ℕ) : ResidueField V) ≠ 0 := hchar _ (by omega)
    have k3 : ((m + 3 : ℕ) : ResidueField V) ≠ 0 := hchar _ (by omega)
    push_cast at k1 k2 k3 r1 r2 ⊢
    set ρ : ResidueField V := (((m : ResidueField V) + 2) ^ 2)⁻¹ with hρ
    have hρ1 : ρ - 1 ≠ 0 := by
      intro h0
      have e : ((m : ResidueField V) + 2) ^ 2 = 1 := by
        rw [sub_eq_zero, hρ, inv_eq_one] at h0; exact h0
      apply mul_ne_zero k1 k3
      linear_combination e
    have hxne : x₁ ≠ x := by
      rintro rfl
      rw [div_self hx0] at r2
      exact hρ1 (by rw [Res.unique r2 Res.one, sub_self])
    obtain ⟨hs, -, hk, -⟩ := HeightEll.kummer (short A B : WeierstrassCurve L) h₁ h hxne
    have e3 : Point.some x₁ y₁ h₁ + Point.some x y h = (m + 3) • (Point.some x y h : (short A B).Point) := by
      rw [← hA1, ← succ_nsmul]
    have e1 : Point.some x₁ y₁ h₁ - Point.some x y h = (m + 1) • (Point.some x y h : (short A B).Point) := by
      rw [← hA1, show m + 2 = (m + 1) + 1 from rfl, succ_nsmul, add_sub_cancel_right]
    rw [e3, e1, hxc_eq, hxc_eq] at hk
    rw [e3] at hs
    refine ⟨hs, ?_⟩
    obtain ⟨r, hr⟩ : ∃ r, x₁ / x = r := ⟨_, rfl⟩
    obtain ⟨r', hr'⟩ : ∃ r', xc ((m + 1) • (Point.some x y h : (short A B).Point)) / x = r' := ⟨_, rfl⟩
    obtain ⟨s, hs'⟩ : ∃ s, xc ((m + 3) • (Point.some x y h : (short A B).Point)) / x = s := ⟨_, rfl⟩
    rw [hr] at r2; rw [hr'] at r1; rw [hs']
    rw [div_eq_iff hx0] at hr hr' hs'
    rw [hr, hr', hs', HeightEll.kS, short_b₂, short_b₄, short_b₆] at hk
    have key : (r - 1) ^ 2 * (s + r') = 2 * r * (r + 1) + 2 * A * u ^ 2 * (r + 1) + 4 * B * u ^ 3 := by
      apply mul_left_cancel₀ (pow_ne_zero 3 hx0)
      linear_combination hk - (2 * A * x * (r + 1) * (x * u + 1) + 4 * B * (x ^ 2 * u ^ 2 + x * u + 1)) * hux
    have hE : Res V (2 * r * (r + 1) + 2 * A * u ^ 2 * (r + 1) + 4 * B * u ^ 3) (2 * ρ * (ρ + 1)) :=
      Res.congr (((((Res.ofNat 2).mul r2).mul (r2.add Res.one)).add
        ((((Res.ofNat 2).mul hAr).mul (hu.pow 2)).mul (r2.add Res.one))).add
        (((Res.ofNat 4).mul hBr).mul (hu.pow 3))) rfl (by simp)
    have hD := (r2.sub Res.one).pow 2
    have hr1 : r - 1 ≠ 0 := hD.ne_zero (pow_ne_zero 2 hρ1) |> fun h => by
      intro h0; exact h (by rw [h0]; ring)
    refine Res.congr ((hE.div hD (pow_ne_zero 2 hρ1)).sub r1) ?_ ?_
    · rw [← key]; field_simp; ring
    · have hρ' : ρ - 1 = -(((m : ResidueField V) + 1) * ((m : ResidueField V) + 3)) /
          ((m : ResidueField V) + 2) ^ 2 := by
        rw [hρ]; field_simp; ring
      rw [hρ', hρ]
      field_simp
      ring
/-- **Torsion abscissae lie in `V`.** -/
theorem xc_mem_of_nsmul_eq_zero (hA : A ∈ V) (hB : B ∈ V)
    (hchar : ∀ m : ℕ, 0 < m → (m : ResidueField V) ≠ 0) {P : (short A B).Point} {n : ℕ}
    (hn : 1 ≤ n) (hP : n • P = 0) : Velu.xc P ∈ V := by
  cases P with
  | zero => exact V.zero_mem
  | some x y h =>
    by_contra hx
    exact (res_nsmul hA hB hchar h hx n hn).1 hP

end Torsion

/-! ### Integrality -/

section Integral

open Velu

/-- In a `ℚ`-algebra base, every valuation ring containing the image has residue char `0`. -/
lemma residue_natCast_ne_zero {R : Type*} [CommRing R] [Algebra ℚ R] [Algebra R L]
    (hV : ∀ r : R, algebraMap R L r ∈ V) (m : ℕ) (hm : 0 < m) : (m : ResidueField V) ≠ 0 := by
  set c : L := algebraMap R L (algebraMap ℚ R (m⁻¹ : ℚ))
  have hc : (m : L) * c = 1 := by
    have : (m : L) = algebraMap R L (algebraMap ℚ R (m : ℚ)) := by simp
    rw [this, ← map_mul, ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hm.ne'), map_one, map_one]
  have h1 := (Res.natCast (V := V) m).mul (Res.of_mem (hV (algebraMap ℚ R (m⁻¹ : ℚ))))
  rw [hc] at h1
  have := Res.unique h1 Res.one
  intro h0; rw [h0, zero_mul] at this; exact zero_ne_one this

/-- **R1 (pointwise).** Over a `ℚ`-algebra `R`, the abscissa of a torsion point of
`y² = x³ + ax + b` (`a, b ∈ R`) over any field `L ⊇ R` is integral over `R`. -/
theorem isIntegral_xc_of_nsmul_eq_zero {R : Type*} [CommRing R] [Algebra ℚ R] [Algebra R L]
    [DecidableEq L] (a b : R) {P : (short (algebraMap R L a) (algebraMap R L b)).Point} {n : ℕ}
    (hn : 1 ≤ n) (hP : n • P = 0) : IsIntegral R (Velu.xc P) := by
  rw [← mem_integralClosure_iff]
  show Velu.xc P ∈ (integralClosure R L).toSubring
  by_contra hx
  obtain ⟨W, hW, hxW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hx
  have hR : ∀ r : R, algebraMap R L r ∈ W := fun r =>
    hW (show algebraMap R L r ∈ integralClosure R L from Subalgebra.algebraMap_mem _ r)
  exact hxW (xc_mem_of_nsmul_eq_zero (hR a) (hR b) (residue_natCast_ne_zero W hR) hn hP)

end Integral

end TorsionSpec
