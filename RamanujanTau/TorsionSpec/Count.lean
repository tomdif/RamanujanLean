import RamanujanTau.TorsionSpec.Generic
import RamanujanTau.TorsionSpec.R2

/-!
# `E[n]` has exactly `n²` points (algebraically closed, characteristic `0`)

Let `F` be algebraically closed of characteristic `0`, `E : y² = x³ + ax + b` with
`4a³ + 27b² ≠ 0`, and `L ⊇ F` algebraically closed containing an element `t` transcendental over
`F`. Take `Q = (t, √(t³+at+b)) ∈ E(L)` and write `Xₙ = c/d` (`Degree.lean`: coprime, `deg c = n²`,
`deg d = n² − 1`). Then `P ↦ x(Q + P)` is a bijection from `E[n](L)` onto the roots of
`f = c − Xₙ(t)·d`, a separable polynomial of degree `n²`. Hence `#E[n](L) = n²`, and `E[n](F) ≅ E[n](L)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TorsionSpec

open Velu WeierstrassCurve WeierstrassCurve.Affine HeightEll Polynomial

variable {F L : Type*} [Field F] [IsAlgClosed F] [CharZero F] [DecidableEq F]
  [Field L] [IsAlgClosed L] [Algebra F L] [DecidableEq L]

lemma transc_iff {ξ : L} : Transc F ξ ↔ ξ ∉ Set.range (algebraMap F L) := by
  constructor
  · rintro h ⟨z, rfl⟩
    apply h (X - C z) (X_sub_C_ne_zero z)
    simp
  · intro h A hA h0
    apply h
    apply mem_range_of_isIntegral
    exact (show IsAlgebraic F ξ from ⟨A, hA, by rwa [aeval_def]⟩).isIntegral

variable (a b : F)

/-- Torsion points of `E(L)` have coordinates in `F`. -/
lemma tors_mem_range {P : (VL (L := L) a b).Point} {n : ℕ} (hn : 1 ≤ n) (hP : n • P = 0) :
    xc P ∈ Set.range (algebraMap F L) ∧ yc P ∈ Set.range (algebraMap F L) := by
  have hx : _root_.IsIntegral F (xc P) := isIntegral_xc_of_nsmul_eq_zero (R := F) (L := L) a b hn hP
  refine ⟨mem_range_of_isIntegral hx, mem_range_of_isIntegral ?_⟩
  by_cases h0 : P = 0
  · subst h0; exact isIntegral_zero
  · have e := equation_xc_yc h0
    have : _root_.IsIntegral F (yc P ^ 2) := by
      rw [e]
      exact (((hx.pow 3).add ((isIntegral_algebraMap).mul hx)).add isIntegral_algebraMap)
    exact this.of_pow two_pos

/-- A point with abscissa in `F` is a lift. -/
lemma lift_of_xc_mem {R : (VL (L := L) a b).Point} (hx : xc R ∈ Set.range (algebraMap F L)) :
    ∃ R₀, liftPt a b R₀ = R := by
  refine mem_range_lift a b hx ?_
  by_cases h0 : R = 0
  · subst h0; exact ⟨0, by simp⟩
  · have e := equation_xc_yc h0
    have hxI : _root_.IsIntegral F (xc R) := by
      obtain ⟨z, hz⟩ := hx; rw [← hz]; exact isIntegral_algebraMap
    have : _root_.IsIntegral F (yc R ^ 2) := by
      rw [e]
      exact (((hxI.pow 3).add ((isIntegral_algebraMap).mul hxI)).add isIntegral_algebraMap)
    exact mem_range_of_isIntegral (this.of_pow two_pos)

/-- A point with transcendental abscissa is not torsion. -/
lemma nsmul_ne_zero_of_transc {R : (VL (L := L) a b).Point} (hR : Transc F (xc R)) {m : ℕ}
    (hm : 1 ≤ m) : m • R ≠ 0 := fun h =>
  (transc_iff.1 hR) (tors_mem_range a b hm h).1

/-- Lifts of points of `E(F)` are the points with coordinates in `F`; a translate `Q + P` of a point
with transcendental abscissa by a torsion point has transcendental abscissa. -/
lemma transc_add {Q P : (VL (L := L) a b).Point} (hQ : Transc F (xc Q)) {n : ℕ} (hn : 1 ≤ n)
    (hP : n • P = 0) : Transc F (xc (Q + P)) := by
  rw [transc_iff]
  intro h
  obtain ⟨R₀, hR₀⟩ := lift_of_xc_mem a b h
  obtain ⟨P₀, hP₀⟩ := lift_of_xc_mem a b (tors_mem_range a b hn hP).1
  have : Q = liftPt a b (R₀ - P₀) := by
    have := (liftHom (L := L) a b).map_sub R₀ P₀
    simp only [liftHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    rw [this, hR₀, hP₀, add_sub_cancel_right]
  apply transc_iff.1 hQ
  rw [this]
  rcases R₀ - P₀ with _ | ⟨x, y, h⟩
  · exact ⟨0, by simp [liftPt]⟩
  · exact ⟨x, rfl⟩

/-- The Wronskian `c' d − c d'` of the abscissa fraction is nonzero. -/
lemma wronskian_ne_zero {c d : F[X]} {D : ℕ} (hD : 1 ≤ D) (hc : c.natDegree = D + 1)
    (hd : d.natDegree = D) (hc0 : c ≠ 0) (hd0 : d ≠ 0) :
    derivative c * d - c * derivative d ≠ 0 := by
  intro h
  have h1 : (derivative c * d).coeff (D + D) = c.leadingCoeff * ((D : F) + 1) * d.leadingCoeff := by
    rw [coeff_mul_add_eq_of_natDegree_le ((natDegree_derivative_le c).trans (by omega)) hd.le,
      coeff_derivative, ← hc, ← hd]
    rfl
  have h2 : (c * derivative d).coeff ((D + 1) + (D - 1)) =
      c.leadingCoeff * (d.leadingCoeff * ((D - 1 : ℕ) + 1 : F)) := by
    rw [coeff_mul_add_eq_of_natDegree_le hc.le ((natDegree_derivative_le d).trans (by omega)),
      coeff_derivative, ← hc, show D - 1 + 1 = d.natDegree by omega]
    rfl
  have e : (D + 1) + (D - 1) = D + D := by omega
  rw [e] at h2
  have := congrArg (coeff · (D + D)) h
  simp only [coeff_sub, coeff_zero, h1, h2] at this
  have hD' : ((D - 1 : ℕ) : F) + 1 = D := by
    rw [Nat.cast_sub hD]; push_cast; ring
  rw [hD'] at this
  have : c.leadingCoeff * d.leadingCoeff = 0 := by linear_combination this
  exact mul_ne_zero (leadingCoeff_ne_zero.2 hc0) (leadingCoeff_ne_zero.2 hd0) this

section Main

variable {a b} (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) {t : L} (ht : Transc F t)
include hΔ ht

/-- The generic point `Q = (t, √(t³ + at + b))`. -/
lemma exists_Q : ∃ Q : (VL (L := L) a b).Point, xc Q = t := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq
    (t ^ 3 + algebraMap F L a * t + algebraMap F L b) two_pos
  have hΔL : 4 * algebraMap F L a ^ 3 + 27 * algebraMap F L b ^ 2 ≠ 0 := by
    intro h; apply hΔ; apply (algebraMap F L).injective; simpa [map_ofNat] using h
  exact ⟨.some t y (ns_of_eq two_ne_zero hΔL hy), rfl⟩

/-- **`#E[n](L) = n²`** (as a set). -/
theorem tors_ncard {n : ℕ} (hn : 2 ≤ n) :
    {P : (VL (L := L) a b).Point | n • P = 0}.Finite ∧
      {P : (VL (L := L) a b).Point | n • P = 0}.ncard = n ^ 2 := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
  obtain ⟨Q, hQx⟩ := exists_Q hΔ ht
  have hQt : Transc F (xc Q) := hQx ▸ ht
  have hQN : ∀ m, 1 ≤ m → m • Q ≠ 0 := fun m hm => nsmul_ne_zero_of_transc a b hQt hm
  -- the exact-degree representation of `Xₙ`
  obtain ⟨c, d, hcd, hd0, hX, hc, hd, hl⟩ := good_all (W := (short a b : WeierstrassCurve F))
    short_b₂ short_b₄ short_b₆ short_b₈ hΔ
    (fun m => (rel_V a b ht Q hQx (m + 3) (fun k hk _ => hQN k hk) m le_rfl).1)
    (fun m => (rel_V a b ht Q hQx (m + 3) (fun k hk _ => hQN k hk) m le_rfl).2) n (by omega)
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [natDegree_zero] at hc; have := pow_pos (show 0 < n by omega) 2; omega
  set j := algebraMap F L
  -- `x(nR) = c(ξ)/d(ξ)` for non-torsion `R` with transcendental abscissa
  have hval : ∀ R : (VL (L := L) a b).Point, ∀ hR : Transc F (xc R),
      xc (n • R) = c.eval₂ j (xc R) / d.eval₂ j (xc R) := by
    intro R hR
    rw [xc_nsmul_V a b hR R rfl n (fun m hm _ => nsmul_ne_zero_of_transc a b hR hm) n (by omega)
      le_rfl, hX, map_div₀, evr_alg, evr_alg]
  have hdt : ∀ ξ : L, Transc F ξ → d.eval₂ j ξ ≠ 0 := fun ξ hξ => hξ d hd0
  set T := xc (n • Q) with hTdef
  have hT : c.eval₂ j t = T * d.eval₂ j t := by
    rw [hTdef, hval Q hQt, hQx, div_mul_cancel₀ _ (hdt t ht)]
  -- the fibre polynomial
  set f : L[X] := c.map j - C T * d.map j with hf
  have hfeval : ∀ ξ, f.eval ξ = c.eval₂ j ξ - T * d.eval₂ j ξ := by
    intro ξ; simp [hf, eval_map]
  have hdeg : (C T * d.map j).natDegree < (c.map j).natDegree := by
    rw [natDegree_map]
    exact (natDegree_C_mul_le _ _).trans_lt (by rw [natDegree_map, hc]; omega)
  have hfdeg : f.natDegree = n ^ 2 := by
    rw [hf, natDegree_sub_eq_left_of_natDegree_lt hdeg, natDegree_map, hc]
  have hf0 : f ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hfdeg; have := pow_pos (show 0 < n by omega) 2; omega
  -- roots of `f` are not in `F`
  have hnot : ∀ z : F, f.eval (j z) ≠ 0 := by
    intro z hz
    rw [hfeval, eval₂_at_apply, eval₂_at_apply, sub_eq_zero] at hz
    by_cases hdz : d.eval z = 0
    · rw [hdz, map_zero, mul_zero, (map_eq_zero_iff j j.injective)] at hz
      obtain ⟨u, v, huv⟩ := hcd
      have := congrArg (eval z) huv
      simp [hz, hdz] at this
    · set w := c.eval z / d.eval z
      have hTw : T = j w := by
        rw [eq_comm, ← mul_left_inj' ((map_ne_zero j).2 hdz)]
        rw [show w = c.eval z / d.eval z from rfl, map_div₀, div_mul_cancel₀ _ ((map_ne_zero j).2 hdz)]
        exact hz
      apply ht (c - C w * d)
      · intro h0
        have : (C w * d).natDegree < c.natDegree :=
          (natDegree_C_mul_le _ _).trans_lt (by rw [hc]; omega)
        rw [sub_eq_zero] at h0; rw [h0] at this; exact lt_irrefl _ this
      · rw [eval₂_sub, eval₂_mul, eval₂_C, hT, hTw]; ring
  -- separability
  have hsep : f.Separable := by
    rw [separable_def, Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed L L]
    intro ξ
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    simp only [coe_aeval_eq_eval] at h1 h2
    rw [hfeval] at h1
    have hder : derivative f = (derivative c).map j - C T * (derivative d).map j := by
      rw [hf, derivative_sub, derivative_C_mul, derivative_map, derivative_map]
    rw [hder] at h2
    simp only [eval_sub, eval_mul, eval_C, eval_map] at h2
    have hW : (derivative c * d - c * derivative d).eval₂ j ξ = 0 := by
      rw [eval₂_sub, eval₂_mul, eval₂_mul]
      linear_combination (d.eval₂ j ξ) * h2 - (derivative d).eval₂ j ξ * h1
    have hξ : ¬Transc F ξ := fun hξ => hξ _ (wronskian_ne_zero (D := n ^ 2 - 1)
      (by have := Nat.pow_le_pow_left hn 2; omega) (by omega) (by omega) hc0 hd0) hW
    rw [transc_iff, not_not] at hξ
    obtain ⟨z, rfl⟩ := hξ
    exact hnot z (by rw [hfeval]; exact h1)
  -- the bijection `P ↦ x(Q + P)` from `E[n](L)` to the roots
  set S : Set (VL (L := L) a b).Point := {P | n • P = 0}
  set g : (VL (L := L) a b).Point → L := fun P => xc (Q + P)
  have hmaps : ∀ P ∈ S, g P ∈ (f.roots.toFinset : Set L) := by
    intro P hP
    have hP' : n • P = 0 := hP
    have htr := transc_add a b hQt (by omega) hP'
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hf0, IsRoot, hfeval]
    have := hval (Q + P) htr
    rw [nsmul_add, hP', add_zero, ← hTdef] at this
    rw [this, div_mul_cancel₀ _ (hdt _ htr), sub_self]
  have hinj : Set.InjOn g S := by
    intro P hP P' hP' h
    have hP0 : n • P = 0 := hP
    have hP0' : n • P' = 0 := hP'
    have hne : ∀ R : (VL (L := L) a b).Point, n • R = 0 → Q + R ≠ 0 := by
      intro R hR h0
      exact (nsmul_ne_zero_of_transc a b (transc_add a b hQt (by omega) hR) (le_refl 1))
        (by rw [one_nsmul, h0])
    have h' : HeightEll.xc (VL (L := L) a b : WeierstrassCurve L) (Q + P) =
        HeightEll.xc (VL (L := L) a b : WeierstrassCurve L) (Q + P') := by
      rw [hxc_eq, hxc_eq]; exact h
    rcases HeightEll.eq_or_eq_neg_of_xc_eq _ (hne P hP0) (hne P' hP0') h' with e | e
    · exact add_left_cancel e
    · exfalso
      have h2Q : (2 * n) • Q = 0 := by
        have : Q + Q = -(P + P') := by
          rw [neg_add]; rw [← sub_eq_zero] at e ⊢
          rw [← e]; abel
        rw [mul_nsmul, two_nsmul, this, neg_nsmul, nsmul_add, hP0, hP0', add_zero, neg_zero]
      exact hQN (2 * n) (by omega) h2Q
  have hsurj : ∀ ξ ∈ (f.roots.toFinset : Set L), ∃ P ∈ S, g P = ξ := by
    intro ξ hξ
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hf0, IsRoot, hfeval] at hξ
    have htr : Transc F ξ := by
      rw [transc_iff]; rintro ⟨z, rfl⟩; exact hnot z (by rw [hfeval]; exact hξ)
    obtain ⟨R, hRx⟩ := exists_Q hΔ htr
    have hRt : Transc F (xc R) := hRx ▸ htr
    have hnR : xc (n • R) = T := by
      rw [hval R hRt, hRx, div_eq_iff (hdt ξ htr)]; exact sub_eq_zero.1 hξ
    have h' : HeightEll.xc (VL (L := L) a b : WeierstrassCurve L) (n • R) =
        HeightEll.xc (VL (L := L) a b : WeierstrassCurve L) (n • Q) := by
      rw [hxc_eq, hxc_eq, hnR]
    rcases HeightEll.eq_or_eq_neg_of_xc_eq _ (nsmul_ne_zero_of_transc a b hRt (by omega))
      (hQN n (by omega)) h' with e | e
    · refine ⟨R - Q, ?_, ?_⟩
      · show n • (R - Q) = 0
        rw [nsmul_sub, e, sub_self]
      · show xc (Q + (R - Q)) = ξ
        rw [add_sub_cancel, hRx]
    · refine ⟨-R - Q, ?_, ?_⟩
      · show n • (-R - Q) = 0
        rw [nsmul_sub, neg_nsmul, e, neg_neg, sub_self]
      · show xc (Q + (-R - Q)) = ξ
        rw [show Q + (-R - Q) = -R by abel, Velu.xc_neg, hRx]
  have himg : g '' S = (f.roots.toFinset : Set L) := by
    ext ξ; constructor
    · rintro ⟨P, hP, rfl⟩; exact hmaps P hP
    · intro hξ; obtain ⟨P, hP, rfl⟩ := hsurj ξ hξ; exact ⟨P, hP, rfl⟩
  refine ⟨Set.Finite.of_finite_image (himg ▸ Finset.finite_toSet _) hinj, ?_⟩
  rw [← Set.InjOn.ncard_image hinj, himg, Set.ncard_coe_finset,
    Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree, hfdeg]

end Main

end TorsionSpec
