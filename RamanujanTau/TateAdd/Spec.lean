/-
# Specialisations of the addition theorem

* `σμ α γ : R3 → K⟦q⟧` (`u = α`, `v = γ` constants): the identity for `x(α), x(γ), x(αγ)`
  (`chord_mu`), in terms of `tx m w = θ^m x |_{u=w}`.
* `σs α β : R3 → K⟦s⟧` (`u = s^α`, `v = s^β`, `q = s^p`, `α + β < p`): the identity for
  `x(s^α), x(s^β), x(s^{α+β})` (`chord_sub`), in terms of `tB`.

Both are stated as `Ix = Iy = 0` for the scaled data `(36 δ² X, 216 δ³ Y, δ)`, `X = x + 1/12`,
`Y = θx/2`; `chord_field` turns this into the chord formulas in a field.
-/
import RamanujanTau.TateAdd.Chord
import RamanujanTau.TateQuot.SubSeries

set_option autoImplicit false

noncomputable section

namespace TateAdd

open PowerSeries TateQuot

/-! ### Chord formulas in a field -/

section Field
variable {L : Type*} [Field L]

lemma Ix_scaled (X1 Y1 d1 X2 Y2 d2 X3 d3 : L) :
    Ix (36 * d1 ^ 2 * X1) (216 * d1 ^ 3 * Y1) d1 (36 * d2 ^ 2 * X2) (216 * d2 ^ 3 * Y2) d2
      (36 * d3 ^ 2 * X3) d3 =
      46656 * d1 ^ 6 * d2 ^ 6 * d3 ^ 2 * ((X3 + X1 + X2) * (X1 - X2) ^ 2 - (Y1 - Y2) ^ 2) := by
  simp only [Ix]; ring

lemma Iy_scaled (X1 Y1 d1 X2 Y2 d2 X3 Y3 d3 : L) :
    Iy (36 * d1 ^ 2 * X1) (216 * d1 ^ 3 * Y1) d1 (36 * d2 ^ 2 * X2) (216 * d2 ^ 3 * Y2) d2
      (36 * d3 ^ 2 * X3) (216 * d3 ^ 3 * Y3) d3 =
      7776 * d1 ^ 5 * d2 ^ 3 * d3 ^ 3 * ((Y3 + Y1) * (X1 - X2) + (Y1 - Y2) * (X3 - X1)) := by
  simp only [Iy]; ring

/-- **The chord formulas** from `Ix = Iy = 0`. -/
theorem chord_field [CharZero L] {X1 Y1 d1 X2 Y2 d2 X3 Y3 d3 : L}
    (hx : Ix (36 * d1 ^ 2 * X1) (216 * d1 ^ 3 * Y1) d1 (36 * d2 ^ 2 * X2) (216 * d2 ^ 3 * Y2) d2
      (36 * d3 ^ 2 * X3) d3 = 0)
    (hy : Iy (36 * d1 ^ 2 * X1) (216 * d1 ^ 3 * Y1) d1 (36 * d2 ^ 2 * X2) (216 * d2 ^ 3 * Y2) d2
      (36 * d3 ^ 2 * X3) (216 * d3 ^ 3 * Y3) d3 = 0)
    (h1 : d1 ≠ 0) (h2 : d2 ≠ 0) (h3 : d3 ≠ 0) (hX : X1 ≠ X2) :
    X3 = ((Y1 - Y2) / (X1 - X2)) ^ 2 - X1 - X2 ∧
      Y3 = -((Y1 - Y2) / (X1 - X2) * (X3 - X1) + Y1) := by
  rw [Ix_scaled] at hx
  rw [Iy_scaled] at hy
  have hs : X1 - X2 ≠ 0 := sub_ne_zero.mpr hX
  have ex : (X3 + X1 + X2) * (X1 - X2) ^ 2 - (Y1 - Y2) ^ 2 = 0 := by
    simpa [h1, h2, h3] using hx
  have ey : (Y3 + Y1) * (X1 - X2) + (Y1 - Y2) * (X3 - X1) = 0 := by
    simpa [h1, h2, h3] using hy
  constructor
  · field_simp; linear_combination ex
  · field_simp; linear_combination ey

end Field

/-! ### `u, v` constants -/

section Mu
variable {K : Type*} [Field K] [CharZero K]

/-- `ℚ[a][c] → K`, `a ↦ α`, `c ↦ γ`. -/
def φμ (α γ : K) : P3 →+* K :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (algebraMap ℚ K) α) γ

/-- `R3 → K⟦q⟧`: `a ↦ α`, `c ↦ γ`, `b ↦ q/(αγ)`. -/
def σμ (α γ : K) : R3 →+* PowerSeries K := (rescale (α * γ)⁻¹).comp (PowerSeries.map (φμ α γ))

lemma φμ_ja (α γ : K) (c : P) : φμ α γ (ja c) = Polynomial.eval₂ (Int.castRingHom K) α c := by
  simp only [ja, Polynomial.coe_eval₂RingHom]
  rw [Polynomial.hom_eval₂]; congr 1
  · ext n; simp
  · simp [φμ]
lemma φμ_jc (α γ : K) (c : P) : φμ α γ (jc c) = Polynomial.eval₂ (Int.castRingHom K) γ c := by
  simp only [jc, Polynomial.coe_eval₂RingHom]
  rw [Polynomial.hom_eval₂]; congr 1
  · ext n; simp
  · simp [φμ]
lemma φμ_jac (α γ : K) (c : P) :
    φμ α γ (jac c) = Polynomial.eval₂ (Int.castRingHom K) (α * γ) c := by
  simp only [jac, Polynomial.coe_eval₂RingHom]
  rw [Polynomial.hom_eval₂]; congr 1
  · ext n; simp
  · simp [φμ]

variable {α γ : K} (hα : α ≠ 0) (hγ : γ ≠ 0)
include hα hγ

lemma σμ_ιu (F : R2) : σμ α γ (ιu3 F) = evA α F := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_evA, σμ, RingHom.comp_apply, coeff_rescale, coeff_map, coeff_ιu3, map_mul, map_pow,
    φμ_ja]
  simp only [φμ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [← mul_assoc, ← mul_pow]; congr 2; field_simp
lemma σμ_ιv (F : R2) : σμ α γ (ιv3 F) = evA γ F := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_evA, σμ, RingHom.comp_apply, coeff_rescale, coeff_map, coeff_ιv3, map_mul, map_pow,
    φμ_jc]
  simp only [φμ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]
  rw [← mul_assoc, ← mul_pow]; congr 2; field_simp
lemma σμ_ιw (F : R2) : σμ α γ (ιw3 F) = evA (α * γ) F := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_evA, σμ, RingHom.comp_apply, coeff_rescale, coeff_map, coeff_ιw3, φμ_jac]

omit hα hγ in
lemma σμ_C (c : P3) : σμ α γ (C c) = C (φμ α γ c) := by
  simp [σμ, rescale_C']

/-- **Addition theorem at constant `u = α`, `v = γ`** (`α, γ, αγ ≠ 1`), cleared form in `K⟦q⟧`. -/
theorem chord_mu (h1 : α ≠ 1) (h2 : γ ≠ 1) (h3 : α * γ ≠ 1) :
    Ix (36 * (tx 0 α * C (α - 1) ^ 2) + 3 * C (α - 1) ^ 2) (108 * (tx 1 α * C (α - 1) ^ 3))
        (C (α - 1)) (36 * (tx 0 γ * C (γ - 1) ^ 2) + 3 * C (γ - 1) ^ 2)
        (108 * (tx 1 γ * C (γ - 1) ^ 3)) (C (γ - 1))
        (36 * (tx 0 (α * γ) * C (α * γ - 1) ^ 2) + 3 * C (α * γ - 1) ^ 2) (C (α * γ - 1)) = 0 ∧
    Iy (36 * (tx 0 α * C (α - 1) ^ 2) + 3 * C (α - 1) ^ 2) (108 * (tx 1 α * C (α - 1) ^ 3))
        (C (α - 1)) (36 * (tx 0 γ * C (γ - 1) ^ 2) + 3 * C (γ - 1) ^ 2)
        (108 * (tx 1 γ * C (γ - 1) ^ 3)) (C (γ - 1))
        (36 * (tx 0 (α * γ) * C (α * γ - 1) ^ 2) + 3 * C (α * γ - 1) ^ 2)
        (108 * (tx 1 (α * γ) * C (α * γ - 1) ^ 3)) (C (α * γ - 1)) = 0 := by
  obtain ⟨hx, hy⟩ := chord_R3
  have hx' := congrArg (σμ α γ) hx
  have hy' := congrArg (σμ α γ) hy
  rw [Ix_map, map_zero] at hx'
  rw [Iy_map, map_zero] at hy'
  have e1 : φμ α γ (A3 - 1) = α - 1 := by simp [φμ]
  have e2 : φμ α γ (C3 - 1) = γ - 1 := by simp [φμ]
  have e3 : φμ α γ (A3 * C3 - 1) = α * γ - 1 := by simp [φμ]
  simp only [map_add, map_mul, map_pow, map_ofNat, σμ_ιu hα hγ, σμ_ιv hα hγ, σμ_ιw hα hγ,
    σμ_C, evA_zB h1, evA_zB h2, evA_zB h3, e1, e2, e3, zero_add, Nat.reduceAdd] at hx' hy'
  exact ⟨hx', hy'⟩

end Mu

/-! ### `u = s^α`, `v = s^β`, `q = s^p` -/

section Sub
variable {K : Type*} [Field K] [CharZero K] {p : ℕ} [hp : Fact p.Prime]

/-- `ℚ[a][c] → K⟦s⟧`, `a ↦ s^α`, `c ↦ s^β`. -/
def φ3 (K : Type*) [Field K] [CharZero K] (α β : ℕ) : P3 →+* PowerSeries K :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (algebraMap ℚ (PowerSeries K)) (X ^ α)) (X ^ β)

/-- `R3 → K⟦s⟧`: `a ↦ s^α`, `c ↦ s^β`, `b ↦ s^n`. -/
def σs (K : Type*) [Field K] [CharZero K] (α β n : ℕ) : R3 →+* PowerSeries K :=
  diagHom.comp ((rescale (X ^ (n - 1) : PowerSeries K)).comp (PowerSeries.map (φ3 K α β)))

lemma φ3_comp (α β k : ℕ) (j : P →+* P3)
    (hj : φ3 K α β (j Polynomial.X) = X ^ k) : (φ3 K α β).comp j = φk K k := by
  apply Polynomial.ringHom_ext
  · intro n; simp
  · simp [hj, φk]

lemma φ3_ja (α β : ℕ) : (φ3 K α β).comp ja = φk K α :=
  φ3_comp α β α ja (by simp [ja, φ3])
lemma φ3_jc (α β : ℕ) : (φ3 K α β).comp jc = φk K β :=
  φ3_comp α β β jc (by simp [jc, φ3])
lemma φ3_jac (α β : ℕ) : (φ3 K α β).comp jac = φk K (α + β) :=
  φ3_comp α β (α + β) jac (by simp [jac, φ3, pow_add])

variable {α β : ℕ}

lemma σs_ιu (h : α + β < p) (F : R2) : σs K α β (p - α - β) (ιu3 F) = evB K α (p - α) F := by
  simp only [σs, evB, RingHom.comp_apply]
  congr 1
  refine PowerSeries.ext fun N => ?_
  rw [coeff_rescale, coeff_map, coeff_ιu3, coeff_rescale, coeff_map, map_mul, map_pow,
    ← RingHom.comp_apply (φ3 K α β) ja, φ3_ja]
  have : φ3 K α β C3 = X ^ β := by simp [φ3]
  rw [this, ← mul_assoc, ← mul_pow, ← pow_add]
  congr 3; omega
lemma σs_ιv (h : α + β < p) (F : R2) : σs K α β (p - α - β) (ιv3 F) = evB K β (p - β) F := by
  simp only [σs, evB, RingHom.comp_apply]
  congr 1
  refine PowerSeries.ext fun N => ?_
  rw [coeff_rescale, coeff_map, coeff_ιv3, coeff_rescale, coeff_map, map_mul, map_pow,
    ← RingHom.comp_apply (φ3 K α β) jc, φ3_jc]
  have : φ3 K α β A3 = X ^ α := by simp [φ3]
  rw [this, ← mul_assoc, ← mul_pow, ← pow_add]
  congr 3; omega
lemma σs_ιw (F : R2) : σs K α β (p - α - β) (ιw3 F) = evB K (α + β) (p - (α + β)) F := by
  simp only [σs, evB, RingHom.comp_apply]
  congr 1
  refine PowerSeries.ext fun N => ?_
  rw [coeff_rescale, coeff_map, coeff_ιw3, coeff_rescale, coeff_map,
    ← RingHom.comp_apply (φ3 K α β) jac, φ3_jac]
  congr 3; omega

lemma σs_C (n : ℕ) (c : P3) : σs K α β n (C c) = φ3 K α β c := by
  simp [σs, rescale_C', diagHom_apply, diag_C]

/-- **Addition theorem at `u = s^α`, `v = s^β`, `q = s^p`** (`α, β ≥ 1`, `α + β < p`), cleared. -/
theorem chord_sub (h1 : 1 ≤ α) (h2 : 1 ≤ β) (h : α + β < p) :
    Ix (36 * (tB K p 0 α * Us K α ^ 2) + 3 * Us K α ^ 2) (108 * (tB K p 1 α * Us K α ^ 3))
        (Us K α) (36 * (tB K p 0 β * Us K β ^ 2) + 3 * Us K β ^ 2)
        (108 * (tB K p 1 β * Us K β ^ 3)) (Us K β)
        (36 * (tB K p 0 (α + β) * Us K (α + β) ^ 2) + 3 * Us K (α + β) ^ 2) (Us K (α + β)) = 0 ∧
    Iy (36 * (tB K p 0 α * Us K α ^ 2) + 3 * Us K α ^ 2) (108 * (tB K p 1 α * Us K α ^ 3))
        (Us K α) (36 * (tB K p 0 β * Us K β ^ 2) + 3 * Us K β ^ 2)
        (108 * (tB K p 1 β * Us K β ^ 3)) (Us K β)
        (36 * (tB K p 0 (α + β) * Us K (α + β) ^ 2) + 3 * Us K (α + β) ^ 2)
        (108 * (tB K p 1 (α + β) * Us K (α + β) ^ 3)) (Us K (α + β)) = 0 := by
  obtain ⟨hx, hy⟩ := chord_R3
  have hx' := congrArg (σs K α β (p - α - β)) hx
  have hy' := congrArg (σs K α β (p - α - β)) hy
  rw [Ix_map, map_zero] at hx'
  rw [Iy_map, map_zero] at hy'
  have e1 : φ3 K α β (A3 - 1) = Us K α := by simp [φ3, Us]
  have e2 : φ3 K α β (C3 - 1) = Us K β := by simp [φ3, Us]
  have e3 : φ3 K α β (A3 * C3 - 1) = Us K (α + β) := by simp [φ3, Us, pow_add]
  have hab : 1 ≤ α + β := by omega
  have hap : α < p := by omega
  have hbp : β < p := by omega
  simp only [map_add, map_mul, map_pow, map_ofNat, σs_ιu h, σs_ιv h, σs_ιw, σs_C, e1, e2, e3,
    evB_zB (p := p) h1, evB_zB (p := p) h2, evB_zB (p := p) hab, zero_add, Nat.reduceAdd]
    at hx' hy'
  exact ⟨hx', hy'⟩

end Sub

end TateAdd
