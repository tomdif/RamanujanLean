import RamanujanTau.SubgroupSum.PointMap

/-!
# Scaling behaviour of the subgroup sum

For `u ≠ 0`, `(x, y) ↦ (u²x, u³y)` is a group isomorphism `short A B ≅ short (u⁴A) (u⁶B)`
(`scaleData`, inverse `scaleData u⁻¹`). It maps subgroups to subgroups, with
`A'_{uG} = u⁴ A'_G`, `B'_{uG} = u⁶ B'_G` (`aC_scale`, `bC_scale`). Hence:

* `subSum_scale` — if `f (u⁴a) (u⁶b) = u^k f a b`, then
  `subSum n f (u⁴A) (u⁶B) = u^k · subSum n f A B`;
* **`subSum_ptR_scale`** — for `P` isobaric of weight `k`,
  `Σ_G P(ptR(E_u/G)) = u^k Σ_G P(ptR(E/G))`, `E_u = short (u⁴A) (u⁶B)`.
-/

set_option autoImplicit false

namespace SubgroupSum

open Velu WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K]

omit [DecidableEq K] in
lemma short_nonsingular_iff (a b x y : K) : (short a b).Nonsingular x y ↔
    y ^ 2 = x ^ 3 + a * x + b ∧ (3 * x ^ 2 + a ≠ 0 ∨ 2 * y ≠ 0) := by
  rw [nonsingular_iff', equation_iff]
  simp only [short_a₁, short_a₂, short_a₃, short_a₄, short_a₆]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by linear_combination h1, ?_⟩
    rcases h2 with h | h
    · left; intro h'; apply h; linear_combination -h'
    · right; intro h'; apply h; linear_combination h'
  · rintro ⟨h1, h2⟩
    refine ⟨by linear_combination h1, ?_⟩
    rcases h2 with h | h
    · left; intro h'; apply h; linear_combination -h'
    · right; intro h'; apply h; linear_combination h'

omit [DecidableEq K] in
lemma short_addX (a b x₁ x₂ ℓ : K) : (short a b).addX x₁ x₂ ℓ = ℓ ^ 2 - x₁ - x₂ := by
  simp [Affine.addX]

omit [DecidableEq K] in
lemma short_addY (a b x₁ x₂ y₁ ℓ : K) :
    (short a b).addY x₁ x₂ y₁ ℓ = -(ℓ * (ℓ ^ 2 - x₁ - x₂ - x₁) + y₁) := by
  simp [Affine.addY, Affine.negAddY, Affine.negY]

variable {A B A₂ B₂ : K} {u : K}

lemma slope_scale (hu : u ≠ 0) (hA : A₂ = u ^ 4 * A) (x₁ x₂ y₁ y₂ : K) :
    (short A₂ B₂).slope (u ^ 2 * x₁) (u ^ 2 * x₂) (u ^ 3 * y₁) (u ^ 3 * y₂) =
      u * (short A B).slope x₁ x₂ y₁ y₂ := by
  have h2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have h3 : u ^ 3 ≠ 0 := pow_ne_zero 3 hu
  unfold Affine.slope
  simp only [Affine.negY, short_a₁, short_a₂, short_a₃, short_a₄, zero_mul, sub_zero, mul_zero,
    add_zero]
  by_cases hx : x₁ = x₂
  · subst hx
    rw [if_pos rfl, if_pos rfl]
    by_cases hy : y₁ = -y₂
    · rw [if_pos hy, if_pos (by rw [hy]; ring), mul_zero]
    · have hy' : ¬u ^ 3 * y₁ = -(u ^ 3 * y₂) := by
        intro h; apply hy; apply mul_left_cancel₀ h3; linear_combination h
      rw [if_neg hy, if_neg hy', hA]
      by_cases hz : y₁ - -y₁ = 0
      · have : u ^ 3 * y₁ - -(u ^ 3 * y₁) = 0 := by linear_combination u ^ 3 * hz
        rw [this, hz, div_zero, div_zero, mul_zero]
      · have hz' : u ^ 3 * y₁ - -(u ^ 3 * y₁) ≠ 0 := by
          intro h; apply hz; apply mul_left_cancel₀ h3; linear_combination h
        field_simp
  · have hx' : ¬u ^ 2 * x₁ = u ^ 2 * x₂ := fun h => hx (mul_left_cancel₀ h2 h)
    rw [if_neg hx, if_neg hx']
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
    have hd' : u ^ 2 * x₁ - u ^ 2 * x₂ ≠ 0 := sub_ne_zero.2 hx'
    field_simp

/-- The scaling `(x, y) ↦ (u²x, u³y)` from `short A B` to `short A₂ B₂`, `A₂ = u⁴A`, `B₂ = u⁶B`. -/
def scaleData (hu : u ≠ 0) (hA : A₂ = u ^ 4 * A) (hB : B₂ = u ^ 6 * B) : HomData A B A₂ B₂ where
  f x := u ^ 2 * x
  g y := u ^ 3 * y
  f_inj := mul_right_injective₀ (pow_ne_zero 2 hu)
  g_inj := mul_right_injective₀ (pow_ne_zero 3 hu)
  g_neg y := by ring
  ns x y h := by
    rw [short_nonsingular_iff] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨by rw [hA, hB]; linear_combination u ^ 6 * h1, ?_⟩
    rcases h2 with h | h
    · left; rw [hA]; intro h'; apply h; apply mul_left_cancel₀ (pow_ne_zero 4 hu)
      linear_combination h'
    · right; intro h'; apply h; apply mul_left_cancel₀ (pow_ne_zero 3 hu); linear_combination h'
  addX x₁ x₂ y₁ y₂ _ _ _ := by
    rw [slope_scale hu hA, short_addX, short_addX]; ring
  addY x₁ x₂ y₁ y₂ _ _ _ := by
    rw [slope_scale hu hA, short_addY, short_addY]; ring

lemma tSum_scale (hu : u ≠ 0) (hA : A₂ = u ^ 4 * A) (hB : B₂ = u ^ 6 * B)
    (G : Finset (short A B).Point) :
    tSum (G.image (scaleData hu hA hB).toFun) = u ^ 4 * tSum G := by
  rw [tSum, HomData.sum_image_erase, tSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [Kernel.tQ, Kernel.tQ, HomData.xc_toFun _ (Finset.ne_of_mem_erase hP)]
  simp only [scaleData, hA]; ring

lemma wSum_scale (hu : u ≠ 0) (hA : A₂ = u ^ 4 * A) (hB : B₂ = u ^ 6 * B)
    (G : Finset (short A B).Point) :
    wSum (G.image (scaleData hu hA hB).toFun) = u ^ 6 * wSum G := by
  rw [wSum, HomData.sum_image_erase, wSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [Kernel.tQ, Kernel.tQ, Kernel.uQ, Kernel.uQ, HomData.xc_toFun _ (Finset.ne_of_mem_erase hP),
    HomData.yc_toFun _ (Finset.ne_of_mem_erase hP)]
  simp only [scaleData, hA]; ring

lemma aC_scale (hu : u ≠ 0) (hA : A₂ = u ^ 4 * A) (hB : B₂ = u ^ 6 * B)
    (G : Finset (short A B).Point) :
    aC (G.image (scaleData hu hA hB).toFun) = u ^ 4 * aC G := by
  rw [aC, aC, tSum_scale, hA]; ring

lemma bC_scale (hu : u ≠ 0) (hA : A₂ = u ^ 4 * A) (hB : B₂ = u ^ 6 * B)
    (G : Finset (short A B).Point) :
    bC (G.image (scaleData hu hA hB).toFun) = u ^ 6 * bC G := by
  rw [bC, bC, wSum_scale, hB]; ring

lemma scaleData_inv_toFun (hu : u ≠ 0) (hA : A₂ = u ^ 4 * A) (hB : B₂ = u ^ 6 * B)
    (hA' : A = u⁻¹ ^ 4 * A₂) (hB' : B = u⁻¹ ^ 6 * B₂) (P : (short A B).Point) :
    (scaleData (inv_ne_zero hu) hA' hB').toFun ((scaleData hu hA hB).toFun P) = P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp only [HomData.toFun, scaleData, Point.some.injEq]
    constructor <;> field_simp

/-- **Scaling of the subgroup sum.** -/
theorem subSum_scale (hu : u ≠ 0) (hA : A₂ = u ^ 4 * A) (hB : B₂ = u ^ 6 * B) (n k : ℕ)
    (f : K → K → K) (hf : ∀ a b, f (u ^ 4 * a) (u ^ 6 * b) = u ^ k * f a b) :
    subSum n f A₂ B₂ = u ^ k * subSum n f A B := by
  classical
  have hA' : A = u⁻¹ ^ 4 * A₂ := by rw [hA]; field_simp
  have hB' : B = u⁻¹ ^ 6 * B₂ := by rw [hB]; field_simp
  set φ := scaleData hu hA hB
  set ψ := scaleData (inv_ne_zero hu) hA' hB'
  have hψφ : ∀ P, ψ.toFun (φ.toFun P) = P := scaleData_inv_toFun hu hA hB hA' hB'
  have hφψ : ∀ P, φ.toFun (ψ.toFun P) = P := by
    have := scaleData_inv_toFun (inv_ne_zero hu) hA' hB' (by rw [hA]; field_simp)
      (by rw [hB]; field_simp)
    simpa only [inv_inv] using this
  have hIψφ : ∀ G : Finset (short A B).Point, (G.image φ.toFun).image ψ.toFun = G := fun G => by
    rw [Finset.image_image]; convert G.image_id; funext P; exact hψφ P
  have hIφψ : ∀ G : Finset (short A₂ B₂).Point, (G.image ψ.toFun).image φ.toFun = G := fun G => by
    rw [Finset.image_image]; convert G.image_id; funext P; exact hφψ P
  have himg : subs A₂ B₂ n = (fun G => G.image φ.toFun) '' subs A B n := by
    ext G'
    refine ⟨fun h => ⟨G'.image ψ.toFun, ψ.image_mem_subs h, hIφψ G'⟩, ?_⟩
    rintro ⟨G, hG, rfl⟩
    exact φ.image_mem_subs hG
  have himg' : subs A B n = (fun G => G.image ψ.toFun) '' subs A₂ B₂ n := by
    ext G
    refine ⟨fun h => ⟨G.image φ.toFun, φ.image_mem_subs h, hIψφ G⟩, ?_⟩
    rintro ⟨G', hG', rfl⟩
    exact ψ.image_mem_subs hG'
  unfold subSum
  by_cases h : (subs A B n).Finite
  · have h₂ : (subs A₂ B₂ n).Finite := himg ▸ h.image _
    rw [dif_pos h, dif_pos h₂, Finset.mul_sum]
    refine Finset.sum_nbij' (fun G => G.image ψ.toFun) (fun G => G.image φ.toFun) ?_ ?_
      (fun G _ => hIφψ G) (fun G _ => hIψφ G) ?_
    · intro G hG
      simp only [Set.Finite.mem_toFinset] at hG ⊢
      exact ψ.image_mem_subs hG
    · intro G hG
      simp only [Set.Finite.mem_toFinset] at hG ⊢
      exact φ.image_mem_subs hG
    · intro G _
      conv_lhs => rw [← hIφψ G]
      rw [aC_scale, bC_scale, hf]
  · have h₂ : ¬(subs A₂ B₂ n).Finite := fun h₂ => h (himg' ▸ h₂.image _)
    rw [dif_neg h, dif_neg h₂, mul_zero]

/-- **Isobaric forms scale by `u^k` on the subgroup sum.** -/
theorem subSum_ptR_scale (hu : u ≠ 0) (A B : K) (n : ℕ) {k : ℕ} {P : MvPolynomial (Fin 2) K}
    (hP : ModP.Iso P k) :
    subSum n (fun x y => MvPolynomial.eval (HeckeQExp.ptR (short x y : WeierstrassCurve K)) P)
        (u ^ 4 * A) (u ^ 6 * B) =
      u ^ k * subSum n (fun x y => MvPolynomial.eval
        (HeckeQExp.ptR (short x y : WeierstrassCurve K)) P) A B := by
  refine subSum_scale hu rfl rfl n k _ fun a b => ?_
  have := HeckeQExp.aeval_scale hP u ![-48 * a, 864 * b]
  rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self]
    at this
  rw [ptR_short, ptR_short]
  convert this using 2
  change MvPolynomial.eval _ = MvPolynomial.eval _
  congr 1
  funext i; fin_cases i <;> simp <;> ring

end SubgroupSum
