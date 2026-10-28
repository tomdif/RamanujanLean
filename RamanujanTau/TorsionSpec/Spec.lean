import RamanujanTau.TorsionSpec.Valuation
import RamanujanTau.SubgroupSum.Basic

/-!
# Specialization of torsion points

Data (`SpecData`): fields `L, K`, a subring `O ⊆ L` closed under square roots in `L`, a ring map
`ψ : O → K`, short curves `E : y² = x³ + Ax + B` over `L` (`A, B ∈ O`) and `Ē : y² = x³ + ax + b` over
`K` with `ψ A = a`, `ψ B = b`, `4a³ + 27b² ≠ 0`, and such that the abscissae of torsion points of `E`
lie in `O`.

Then `sp : E(L) → Ē(K)`, `(x, y) ↦ (ψ x, ψ y)`, is, on torsion points,
* injective (**`sp_inj`**): two distinct torsion points with the same reduction would give a common
  root of `x³ + ax + b` and `x⁴ − 2ax² − 8bx + a²`, forcing `4a³ + 27b² = 0`;
* additive (**`sp_add`**).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TorsionSpec

open Velu SubgroupSum WeierstrassCurve WeierstrassCurve.Affine

/-- A common root of `x³ + ax + b` and `x⁴ − 2ax² − 8bx + a²` forces the discriminant to vanish. -/
lemma disc_eq_zero_of_common_root {K : Type*} [Field K] {a b ξ : K} (h1 : ξ ^ 3 + a * ξ + b = 0)
    (h2 : ξ ^ 4 - 2 * a * ξ ^ 2 - 8 * b * ξ + a ^ 2 = 0) : 4 * a ^ 3 + 27 * b ^ 2 = 0 := by
  linear_combination (27 * b + 5 * a * ξ - 3 * ξ ^ 3) * h1 + (4 * a + 3 * ξ ^ 2) * h2

/-- Every point of a nonsingular short curve in characteristic `≠ 2` is nonsingular. -/
lemma ns_of_eq {K : Type*} [Field K] {a b x y : K} (h2 : (2 : K) ≠ 0)
    (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (h : y ^ 2 = x ^ 3 + a * x + b) :
    (short a b).Nonsingular x y := by
  rw [nonsingular_iff']
  refine ⟨(short_equation_iff a b x y).2 h, ?_⟩
  simp only [short_a₁, short_a₂, short_a₃, short_a₄, zero_mul, zero_sub, mul_zero, add_zero]
  by_contra hc
  push Not at hc
  obtain ⟨hc1, hc2⟩ := hc
  have hy : y = 0 := by
    rcases mul_eq_zero.1 hc2 with h | h
    · exact absurd h h2
    · exact h
  have ha : a = -3 * x ^ 2 := by linear_combination -hc1
  subst hy
  apply hΔ
  have hb : b = 2 * x ^ 3 := by rw [ha] at h; linear_combination -h
  rw [ha, hb]; ring

/-- Torsion points. -/
def IsTors {K : Type*} [Field K] [DecidableEq K] {A B : K} (P : (short A B).Point) : Prop :=
  ∃ n : ℕ, 0 < n ∧ n • P = 0

namespace IsTors
variable {K : Type*} [Field K] [DecidableEq K] {A B : K}

lemma zero : IsTors (0 : (short A B).Point) := ⟨1, one_pos, by simp⟩

lemma add {P Q : (short A B).Point} (hP : IsTors P) (hQ : IsTors Q) : IsTors (P + Q) := by
  obtain ⟨m, hm, hmP⟩ := hP
  obtain ⟨n, hn, hnQ⟩ := hQ
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [nsmul_add, mul_nsmul, hmP, nsmul_zero, mul_nsmul', hnQ, nsmul_zero, add_zero]

lemma neg {P : (short A B).Point} (hP : IsTors P) : IsTors (-P) := by
  obtain ⟨m, hm, hmP⟩ := hP
  exact ⟨m, hm, by rw [neg_nsmul, hmP, neg_zero]⟩

lemma sub {P Q : (short A B).Point} (hP : IsTors P) (hQ : IsTors Q) : IsTors (P - Q) := by
  rw [sub_eq_add_neg]; exact hP.add hQ.neg

end IsTors

/-- Specialization data. -/
structure SpecData (L K : Type*) [Field L] [Field K] [DecidableEq L] (A B : L) (a b : K) where
  O : Subring L
  ψ : O →+* K
  hA : A ∈ O
  hB : B ∈ O
  ψA : ψ ⟨A, hA⟩ = a
  ψB : ψ ⟨B, hB⟩ = b
  sq : ∀ z : L, z ^ 2 ∈ O → z ∈ O
  tors : ∀ P : (short A B).Point, IsTors P → xc P ∈ O
  hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0

namespace SpecData

variable {L K : Type*} [Field L] [Field K] [DecidableEq L] [DecidableEq K] [CharZero K]
  {A B : L} {a b : K} (D : SpecData L K A B a b)

/-- The equation of `E` transported to `Ē`. -/
lemma eq_sp {x y : L} (h : (short A B).Nonsingular x y) (hx : x ∈ D.O) (hy : y ∈ D.O) :
    D.ψ ⟨y, hy⟩ ^ 2 = D.ψ ⟨x, hx⟩ ^ 3 + a * D.ψ ⟨x, hx⟩ + b := by
  have e := (short_equation_iff A B x y).1 h.1
  have e' : (⟨y, hy⟩ : D.O) ^ 2 = ⟨x, hx⟩ ^ 3 + ⟨A, D.hA⟩ * ⟨x, hx⟩ + ⟨B, D.hB⟩ :=
    Subtype.ext (by simpa using e)
  have := congrArg D.ψ e'
  simp only [map_add, map_mul, map_pow] at this
  rwa [D.ψA, D.ψB] at this

open scoped Classical in
/-- The specialization map on points. -/
noncomputable def sp : (short A B).Point → (short a b).Point
  | 0 => 0
  | .some x y h => if hxy : x ∈ D.O ∧ y ∈ D.O then
      .some (D.ψ ⟨x, hxy.1⟩) (D.ψ ⟨y, hxy.2⟩) (ns_of_eq two_ne_zero D.hΔ (D.eq_sp h hxy.1 hxy.2))
    else 0

@[simp] lemma sp_zero : D.sp 0 = 0 := rfl

lemma sp_some {x y : L} (h : (short A B).Nonsingular x y) (hx : x ∈ D.O) (hy : y ∈ D.O) :
    D.sp (.some x y h) = .some (D.ψ ⟨x, hx⟩) (D.ψ ⟨y, hy⟩)
      (ns_of_eq two_ne_zero D.hΔ (D.eq_sp h hx hy)) := by
  simp only [sp, dif_pos (And.intro hx hy)]

/-- Coordinates of torsion points lie in `O`. -/
lemma mem_of_tors {x y : L} {h : (short A B).Nonsingular x y}
    (hP : IsTors (Point.some x y h : (short A B).Point)) : x ∈ D.O ∧ y ∈ D.O := by
  have hx : x ∈ D.O := D.tors _ hP
  refine ⟨hx, D.sq y ?_⟩
  rw [(short_equation_iff A B x y).1 h.1]
  exact add_mem (add_mem (pow_mem hx 3) (mul_mem D.hA hx)) D.hB

lemma sp_ne_zero {P : (short A B).Point} (hP : IsTors P) (h0 : P ≠ 0) : D.sp P ≠ 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl h0
  · obtain ⟨hx, hy⟩ := D.mem_of_tors hP
    rw [D.sp_some h hx hy]; exact Point.some_ne_zero _

lemma negY_short' {F : Type*} [Field F] (c d x y : F) : (short c d).negY x y = -y := by
  simp [Affine.negY]

lemma sp_neg {P : (short A B).Point} (hP : IsTors P) : D.sp (-P) = -D.sp P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨hx, hy⟩ := D.mem_of_tors hP
    have hy' : (short A B).negY x y ∈ D.O := by rw [negY_short']; exact neg_mem hy
    rw [Point.neg_some, D.sp_some _ hx hy', D.sp_some h hx hy, Point.neg_some]
    congr 1
    conv_rhs => rw [negY_short']
    rw [← map_neg]; congr 1; exact Subtype.ext (by simp)

lemma c2 : ((2 : D.O) : L) = 2 := rfl
lemma c4 : ((4 : D.O) : L) = 4 := rfl

lemma ψ_eq {e₁ e₂ : D.O} (h : (e₁ : L) = e₂) : D.ψ e₁ = D.ψ e₂ := by rw [Subtype.ext h]

/-- **Injectivity of specialization on torsion points.** -/
theorem sp_inj {P Q : (short A B).Point} (hP : IsTors P) (hQ : IsTors Q) (h : D.sp P = D.sp Q) :
    P = Q := by
  by_contra hne
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact hne rfl
  · exact D.sp_ne_zero hQ (Point.some_ne_zero _) h.symm
  · exact D.sp_ne_zero hP (Point.some_ne_zero _) h
  obtain ⟨hx1, hy1⟩ := D.mem_of_tors hP
  obtain ⟨hx2, hy2⟩ := D.mem_of_tors hQ
  rw [D.sp_some h₁ hx1 hy1, D.sp_some h₂ hx2 hy2] at h
  simp only [Point.some.injEq] at h
  obtain ⟨hψx, hψy⟩ := h
  have hA' := D.ψA
  have hB' := D.ψB
  set ξ := D.ψ ⟨x₁, hx1⟩ with hξ
  have hf : ξ ^ 3 + a * ξ + b = D.ψ ⟨y₁, hy1⟩ ^ 2 := (D.eq_sp h₁ hx1 hy1).symm
  have h4 : (4 : K) ≠ 0 := by norm_num
  apply D.hΔ
  by_cases hx : x₁ = x₂
  · subst hx
    have e1 := (short_equation_iff A B x₁ y₁).1 h₁.1
    have e2 := (short_equation_iff A B x₁ y₂).1 h₂.1
    have hyy : y₁ = -y₂ := by
      have : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination e1 - e2
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd (by obtain rfl := sub_eq_zero.1 h0; rfl) hne
      · linear_combination h0
    have hψ0 : D.ψ ⟨y₁, hy1⟩ = 0 := by
      have : D.ψ ⟨y₁, hy1⟩ = -D.ψ ⟨y₂, hy2⟩ := by
        rw [← map_neg]; exact D.ψ_eq (by simp [hyy])
      rw [← hψy] at this
      have h2 : (2 : K) * D.ψ ⟨y₁, hy1⟩ = 0 := by linear_combination this
      exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
    have h2P : Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₁ ≠ 0 := by
      intro h0
      apply hne
      have : Point.some x₁ y₁ h₁ = -Point.some x₁ y₁ h₁ := eq_neg_of_add_eq_zero_left h0
      rw [this, Point.neg_some]
      congr 1; rw [negY_short', hyy, neg_neg]
    obtain ⟨-, hd⟩ := HeightEll.doubling (short A B : WeierstrassCurve L) h₁ h2P
    rw [hxc_eq, HeightEll.kPsi, HeightEll.kPhi, short_b₂, short_b₄, short_b₆, short_b₈] at hd
    have hX := D.tors _ (hP.add hP)
    have := D.ψ_eq (e₁ := (4 * ⟨y₁, hy1⟩ ^ 2) * ⟨_, hX⟩)
      (e₂ := ⟨x₁, hx1⟩ ^ 4 - 2 * ⟨A, D.hA⟩ * ⟨x₁, hx1⟩ ^ 2 - 2 * (4 * ⟨B, D.hB⟩) * ⟨x₁, hx1⟩ +
        ⟨A, D.hA⟩ ^ 2) (by
        push_cast [c2, c4]
        linear_combination hd + (4 * xc (Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₁)) * e1)
    simp only [map_mul, map_pow, map_sub, map_add, map_ofNat, hψ0] at this
    rw [hA', hB', ← hξ] at this
    refine disc_eq_zero_of_common_root (ξ := ξ) (by rw [hf, hψ0]; ring) (by linear_combination -this)
  · obtain ⟨-, -, hS, hQ'⟩ := HeightEll.kummer (short A B : WeierstrassCurve L) h₁ h₂ hx
    rw [hxc_eq, hxc_eq, HeightEll.kS, short_b₂, short_b₄, short_b₆] at hS
    rw [hxc_eq, hxc_eq, HeightEll.kQ, short_b₄, short_b₆, short_b₈] at hQ'
    have hU := D.tors _ (hP.add hQ)
    have hV := D.tors _ (hP.sub hQ)
    have t1 := D.ψ_eq (e₁ := (⟨x₁, hx1⟩ - ⟨x₂, hx2⟩) ^ 2 * (⟨_, hU⟩ + ⟨_, hV⟩))
      (e₂ := 2 * ⟨x₁, hx1⟩ * ⟨x₂, hx2⟩ * (⟨x₁, hx1⟩ + ⟨x₂, hx2⟩) +
        2 * ⟨A, D.hA⟩ * (⟨x₁, hx1⟩ + ⟨x₂, hx2⟩) + 4 * ⟨B, D.hB⟩) (by
        push_cast [c2, c4]; rw [hS]; ring)
    have t2 := D.ψ_eq (e₁ := (⟨x₁, hx1⟩ - ⟨x₂, hx2⟩) ^ 2 * (⟨_, hU⟩ * ⟨_, hV⟩))
      (e₂ := ⟨x₁, hx1⟩ ^ 2 * ⟨x₂, hx2⟩ ^ 2 - 2 * ⟨A, D.hA⟩ * ⟨x₁, hx1⟩ * ⟨x₂, hx2⟩ -
        4 * ⟨B, D.hB⟩ * (⟨x₁, hx1⟩ + ⟨x₂, hx2⟩) + ⟨A, D.hA⟩ ^ 2) (by
        push_cast [c2, c4]; rw [hQ']; ring)
    simp only [map_mul, map_pow, map_sub, map_add, map_ofNat] at t1 t2
    rw [hA', hB', ← hξ, ← hψx, sub_self] at t1 t2
    refine disc_eq_zero_of_common_root (ξ := ξ) ?_ (by linear_combination -t2)
    have : (4 : K) * (ξ ^ 3 + a * ξ + b) = 0 := by linear_combination -t1
    exact (mul_eq_zero.1 this).resolve_left h4

/-- **Additivity of specialization on torsion points.** -/
theorem sp_add {P Q : (short A B).Point} (hP : IsTors P) (hQ : IsTors Q) :
    D.sp (P + Q) = D.sp P + D.sp Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [show (Point.zero : (short A B).Point) = 0 from rfl, zero_add, sp_zero, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [show (Point.zero : (short A B).Point) = 0 from rfl, add_zero, sp_zero, add_zero]
  obtain ⟨hx1, hy1⟩ := D.mem_of_tors hP
  obtain ⟨hx2, hy2⟩ := D.mem_of_tors hQ
  have hPQ := hP.add hQ
  have hA' := D.ψA
  have hB' := D.ψB
  by_cases hs : D.ψ ⟨x₁, hx1⟩ = D.ψ ⟨x₂, hx2⟩ ∧
      D.ψ ⟨y₁, hy1⟩ = (short a b).negY (D.ψ ⟨x₂, hx2⟩) (D.ψ ⟨y₂, hy2⟩)
  · rw [D.sp_some h₁ hx1 hy1, D.sp_some h₂ hx2 hy2, Point.add_of_Y_eq hs.1 hs.2]
    have : Point.some x₁ y₁ h₁ = -Point.some x₂ y₂ h₂ := by
      apply D.sp_inj hP hQ.neg
      rw [D.sp_neg hQ, D.sp_some h₁ hx1 hy1, D.sp_some h₂ hx2 hy2, Point.neg_some]
      simp only [Point.some.injEq]; exact hs
    rw [this, neg_add_cancel, sp_zero]
  have hg : ¬(x₁ = x₂ ∧ y₁ = (short A B).negY x₂ y₂) := by
    rintro ⟨hx, hy⟩
    apply hs
    subst hx
    refine ⟨rfl, ?_⟩
    rw [negY_short'] at hy ⊢
    rw [← map_neg]; exact D.ψ_eq (by simp [hy])
  rw [Point.add_some hg] at hPQ ⊢
  obtain ⟨hx3, hy3⟩ := D.mem_of_tors hPQ
  rw [D.sp_some _ hx3 hy3, D.sp_some h₁ hx1 hy1, D.sp_some h₂ hx2 hy2, Point.add_some hs]
  set ℓ := (short A B).slope x₁ x₂ y₁ y₂ with hℓ
  have hℓ2 : ℓ ^ 2 = (short A B).addX x₁ x₂ ℓ + x₁ + x₂ := by simp [Affine.addX]; ring
  have hℓO : ℓ ∈ D.O := D.sq ℓ (by rw [hℓ2]; exact add_mem (add_mem hx3 hx1) hx2)
  have e1 := (short_equation_iff A B x₁ y₁).1 h₁.1
  have e2 := (short_equation_iff A B x₂ y₂).1 h₂.1
  have f1 := D.eq_sp h₁ hx1 hy1
  have f2 := D.eq_sp h₂ hx2 hy2
  have key : D.ψ ⟨ℓ, hℓO⟩ = (short a b).slope (D.ψ ⟨x₁, hx1⟩) (D.ψ ⟨x₂, hx2⟩)
      (D.ψ ⟨y₁, hy1⟩) (D.ψ ⟨y₂, hy2⟩) := by
    by_cases hx : x₁ = x₂
    · subst hx
      have hyeq : y₁ = y₂ := by
        have : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination e1 - e2
        rcases mul_eq_zero.1 this with h0 | h0
        · exact sub_eq_zero.1 h0
        · exact absurd ⟨rfl, by rw [negY_short']; linear_combination h0⟩ hg
      subst hyeq
      have hy0 : y₁ ≠ (short A B).negY x₁ y₁ := fun h => hg ⟨rfl, h⟩
      have hψ0 : D.ψ ⟨y₁, hy1⟩ ≠ (short a b).negY (D.ψ ⟨x₁, hx1⟩) (D.ψ ⟨y₁, hy1⟩) :=
        fun h => hs ⟨rfl, h⟩
      have hsl := (short A B).slope_of_Y_ne rfl hy0
      rw [negY_short'] at hy0 hψ0 hsl
      rw [(short a b).slope_of_Y_ne rfl (by rw [negY_short']; exact hψ0), negY_short']
      have h2y : y₁ - -y₁ ≠ 0 := fun h => hy0 (by linear_combination h)
      have e : ℓ * (2 * y₁) = 3 * x₁ ^ 2 + A := by
        rw [hℓ, hsl, div_mul_eq_mul_div, div_eq_iff h2y]; simp only [short_a₁, short_a₂, short_a₄]; ring
      have t := D.ψ_eq (e₁ := ⟨ℓ, hℓO⟩ * (2 * ⟨y₁, hy1⟩)) (e₂ := 3 * ⟨x₁, hx1⟩ ^ 2 + ⟨A, D.hA⟩)
        (by push_cast [c2]; exact e)
      simp only [map_mul, map_pow, map_add, map_ofNat] at t
      rw [hA'] at t
      have h2y' : D.ψ ⟨y₁, hy1⟩ - -D.ψ ⟨y₁, hy1⟩ ≠ 0 := fun h => hψ0 (by linear_combination h)
      simp only [short_a₁, short_a₂, short_a₄]
      rw [eq_div_iff h2y']
      linear_combination t
    · have hsl := (short A B).slope_of_X_ne (y₁ := y₁) (y₂ := y₂) hx
      have e : ℓ * (x₁ - x₂) = y₁ - y₂ := by
        rw [hℓ, hsl]; field_simp [sub_ne_zero.2 hx]
      have t := D.ψ_eq (e₁ := ⟨ℓ, hℓO⟩ * (⟨x₁, hx1⟩ - ⟨x₂, hx2⟩)) (e₂ := ⟨y₁, hy1⟩ - ⟨y₂, hy2⟩)
        (by push_cast; exact e)
      simp only [map_mul, map_sub] at t
      by_cases hψ : D.ψ ⟨x₁, hx1⟩ = D.ψ ⟨x₂, hx2⟩
      · exfalso
        have hy12 : D.ψ ⟨y₁, hy1⟩ = D.ψ ⟨y₂, hy2⟩ := by
          have : (D.ψ ⟨y₁, hy1⟩ - D.ψ ⟨y₂, hy2⟩) * (D.ψ ⟨y₁, hy1⟩ + D.ψ ⟨y₂, hy2⟩) = 0 := by
            rw [← hψ] at f2; linear_combination f1 - f2
          rcases mul_eq_zero.1 this with h0 | h0
          · exact sub_eq_zero.1 h0
          · exact absurd ⟨hψ, by rw [negY_short']; linear_combination h0⟩ hs
        apply hx
        have := D.sp_inj hP hQ (by
          rw [D.sp_some h₁ hx1 hy1, D.sp_some h₂ hx2 hy2]; simp only [Point.some.injEq]
          exact ⟨hψ, hy12⟩)
        simp only [Point.some.injEq] at this
        exact this.1
      · rw [(short a b).slope_of_X_ne hψ, eq_div_iff (sub_ne_zero.2 hψ)]
        exact t
  have hX : D.ψ ⟨_, hx3⟩ = (short a b).addX (D.ψ ⟨x₁, hx1⟩) (D.ψ ⟨x₂, hx2⟩)
      ((short a b).slope (D.ψ ⟨x₁, hx1⟩) (D.ψ ⟨x₂, hx2⟩) (D.ψ ⟨y₁, hy1⟩) (D.ψ ⟨y₂, hy2⟩)) := by
    rw [← key]
    have := D.ψ_eq (e₁ := ⟨_, hx3⟩) (e₂ := ⟨ℓ, hℓO⟩ ^ 2 - ⟨x₁, hx1⟩ - ⟨x₂, hx2⟩)
      (by push_cast; simp [Affine.addX])
    rw [this]; simp only [map_sub, map_pow, Affine.addX, short_a₁, short_a₂]; ring
  simp only [Point.some.injEq]
  refine ⟨hX, ?_⟩
  have := D.ψ_eq (e₁ := ⟨_, hy3⟩) (e₂ := -(⟨ℓ, hℓO⟩ * (⟨_, hx3⟩ - ⟨x₁, hx1⟩) + ⟨y₁, hy1⟩))
    (by push_cast; simp [Affine.addY, Affine.negAddY, Affine.negY])
  rw [this]
  simp only [map_neg, map_add, map_mul, map_sub, hX, key]
  simp [Affine.addY, Affine.negAddY, Affine.negY]

end SpecData

end TorsionSpec
