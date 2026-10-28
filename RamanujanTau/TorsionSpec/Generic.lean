import RamanujanTau.TorsionSpec.Lifts
import RamanujanTau.TorsionSpec.Degree

/-!
# The universal abscissae `Xₙ` on a short curve over an extension field

Short-curve versions of `HeightEll.xc_nsmul` / `HeightEll.Xs_rel`: for `E = short a b` over `F`,
a field `L ⊇ F` and a point `Q ∈ E(L)` whose abscissa `ξ` is transcendental over `F` and with
`mQ ≠ 0` (`1 ≤ m ≤ N`): `x(nQ) = Xₙ(ξ)` and the Kummer relations hold in `F(t)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TorsionSpec

open Velu WeierstrassCurve WeierstrassCurve.Affine HeightEll Polynomial

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [DecidableEq L] (a b : F)

/-- The base-changed short curve. -/
abbrev VL (a b : F) : WeierstrassCurve.Affine L := short (algebraMap F L a) (algebraMap F L b)

lemma map_short_eq : WeierstrassCurve.map (short a b : WeierstrassCurve F) (algebraMap F L) =
    (VL (L := L) a b : WeierstrassCurve L) := by
  ext <;> simp [short]

/-- Transcendence over `F`. -/
def Transc (F : Type*) [Field F] [Algebra F L] (ξ : L) : Prop := ∀ A : F[X], A ≠ 0 → A.eval₂ (algebraMap F L) ξ ≠ 0

lemma xc_ne_of_nsmul' {Q : (VL (L := L) a b).Point} {m : ℕ} (hm1 : (m + 1) • Q ≠ 0)
    (hm3 : (m + 3) • Q ≠ 0) (hA : (m + 2) • Q ≠ 0) (hQ : Q ≠ 0) :
    xc ((m + 2) • Q) ≠ xc Q := by
  intro h
  rw [← hxc_eq, ← hxc_eq] at h
  rcases HeightEll.eq_or_eq_neg_of_xc_eq (VL (L := L) a b : WeierstrassCurve L) hA hQ h with h | h
  · apply hm1
    have e : (m + 1) • Q + Q = Q := by rw [← succ_nsmul]; exact h
    have := congrArg (· - Q) e
    simpa using this
  · apply hm3
    rw [succ_nsmul, h, neg_add_cancel]

/-- **universality** on the short curve. -/
theorem xc_nsmul_V {ξ : L} (hξ : Transc F ξ) (Q : (VL (L := L) a b).Point) (hQx : xc Q = ξ)
    (N : ℕ) (hN : ∀ m, 1 ≤ m → m ≤ N → m • Q ≠ 0) :
    ∀ n, 1 ≤ n → n ≤ N → xc (n • Q) = evr (algebraMap F L) ξ hξ (Xs (short a b) n) := by
  have hV := map_short_eq (L := L) a b
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hnN
  have hQ : Q ≠ 0 := by simpa using hN 1 le_rfl (by omega)
  obtain ⟨x₀, y₀, h₀, rfl⟩ := HeightEll.eq_some_of_ne_zero (VL (L := L) a b : WeierstrassCurve L) hQ
  simp only [Velu.xc_some] at hQx
  subst hQx
  match n, hn with
  | 1, _ => rw [one_nsmul, Velu.xc_some]; exact (evr_tX _ x₀ hξ).symm
  | 2, _ =>
    have h2 := hN 2 (by omega) hnN
    rw [two_nsmul] at h2 ⊢
    obtain ⟨hp, hd⟩ := doubling _ h₀ h2
    simp only [Xs, map_div₀, map_kPhi, map_kPsi, Wr_map, evr_tX]
    rw [hV, eq_div_iff hp, mul_comm, ← hxc_eq, hd]
  | m + 3, _ =>
    have hA := hN (m + 2) (by omega) (by omega)
    have hx := xc_ne_of_nsmul' a b (hN (m + 1) (by omega) (by omega)) (hN (m + 3) (by omega) hnN) hA hQ
    have ih2 := ih (m + 2) (by omega) (by omega) (by omega)
    have ih1 := ih (m + 1) (by omega) (by omega) (by omega)
    obtain ⟨x₁, y₁, h₁, hA1⟩ := HeightEll.eq_some_of_ne_zero (VL (L := L) a b : WeierstrassCurve L) hA
    rw [hA1, Velu.xc_some] at hx ih2
    rw [Velu.xc_some] at hx
    have hk := (kummer _ h₁ h₀ hx).2.2.1
    rw [← hA1, ← succ_nsmul, show (m + 2) • Point.some x₀ y₀ h₀ - Point.some x₀ y₀ h₀ =
      (m + 1) • Point.some x₀ y₀ h₀ by
        rw [show m + 2 = (m + 1) + 1 from rfl, succ_nsmul, add_sub_cancel_right]] at hk
    rw [hxc_eq, hxc_eq, ih1] at hk
    have hd : (x₁ - x₀) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hx)
    simp only [Xs, map_sub, map_div₀, map_pow, map_kS, Wr_map, evr_tX, ← ih2]
    rw [hV, eq_sub_iff_add_eq, eq_div_iff hd, mul_comm, hk]

/-- The Kummer relations transported to `F(t)`. -/
theorem rel_V {ξ : L} (hξ : Transc F ξ) (Q : (VL (L := L) a b).Point) (hQx : xc Q = ξ)
    (N : ℕ) (hN : ∀ m, 1 ≤ m → m ≤ N → m • Q ≠ 0) (m : ℕ) (hm : m + 3 ≤ N) :
    Xs (short a b) (m + 2) ≠ tX ∧ (Xs (short a b) (m + 2) - tX) ^ 2 *
      (Xs (short a b) (m + 3) * Xs (short a b) (m + 1)) =
      kQ (Wr (short a b)) (Xs (short a b) (m + 2)) tX := by
  have hV := map_short_eq (L := L) a b
  have hU := xc_nsmul_V a b hξ Q hQx N hN
  have hQ : Q ≠ 0 := by simpa using hN 1 le_rfl (by omega)
  have hA := hN (m + 2) (by omega) (by omega)
  have hx := xc_ne_of_nsmul' a b (hN (m + 1) (by omega) (by omega)) (hN (m + 3) (by omega) hm) hA hQ
  obtain ⟨x₀, y₀, h₀, rfl⟩ := HeightEll.eq_some_of_ne_zero (VL (L := L) a b : WeierstrassCurve L) hQ
  obtain ⟨x₁, y₁, h₁, hA1⟩ := HeightEll.eq_some_of_ne_zero (VL (L := L) a b : WeierstrassCurve L) hA
  simp only [Velu.xc_some] at hQx
  have e2 := hU (m + 2) (by omega) (by omega)
  have e3 := hU (m + 3) (by omega) hm
  have e1 := hU (m + 1) (by omega) (by omega)
  rw [hA1, Velu.xc_some] at hx e2
  rw [Velu.xc_some] at hx
  have hk := (kummer _ h₁ h₀ hx).2.2.2
  rw [← hA1, ← succ_nsmul, show (m + 2) • Point.some x₀ y₀ h₀ - Point.some x₀ y₀ h₀ =
    (m + 1) • Point.some x₀ y₀ h₀ by
      rw [show m + 2 = (m + 1) + 1 from rfl, succ_nsmul, add_sub_cancel_right]] at hk
  rw [hxc_eq, hxc_eq, e3, e1, e2, hQx] at hk
  refine ⟨fun h => hx (by rw [e2, hQx, h, evr_tX]), ?_⟩
  apply (evr (algebraMap F L) ξ hξ).injective
  simp only [map_mul, map_pow, map_sub, map_kQ, Wr_map, evr_tX]
  rw [hV]
  exact hk

end TorsionSpec
