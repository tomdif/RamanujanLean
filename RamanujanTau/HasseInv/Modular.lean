/-
# The modular side: `H = Ā(c₄, −c₆)` via the q-expansion principle (conditional on `H(Tate) = 1`)

Let `T̄ = Tate ⊗ 𝔽_p` over `𝔽_p⟦q⟧` (`TateBar`). Then `c₄(T̄) = Ē₄`, `−c₆(T̄) = Ē₆`, so
* `ev_hassePoly`: the q-expansion `hassePoly(Ē₄, Ē₆)` is `H(T̄)` (`= a` of the formal group of `T̄`).
* `hassePoly_eq_hasseBar_iff`: `hassePoly = Ā` (Swinnerton-Dyer's `hasseBar`) **iff** `H(T̄) = 1`
  (by `ModP.hasseBar_unique`, `iso_hassePoly`).
* `aH_eq_hasseBar`: assuming `H(T̄) = 1`, for every Weierstrass curve over a ring of characteristic
  `p ≥ 5`: `a = Ā(c₄, −c₆)`.
* `coeff_nmul_sub_hasseA_mem`: assuming `H(T̄) = 1`, for every Weierstrass curve over a `ℤ_[p]`-algebra:
  `a ≡ A(c₄, −c₆) (mod p)` with `A ∈ ℤ_[p][X₀,X₁]` the isobaric lift with `A(E₄,E₆) = E_{p−1}`.

The hypothesis `H(T̄) = 1` (equivalently `a(formalGroup T̄) = 1`, the Tate formal group being
multiplicative) is **not** proved here.
-/
import RamanujanTau.HasseInv.Poly
import RamanujanTau.TateCurve.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HasseInv
open EllipticFormal

variable (p : ℕ) [hp : Fact p.Prime]

/-- `𝔽_p⟦q⟧` has characteristic `p`. -/
instance charP_PS : CharP (PowerSeries (ZMod p)) p :=
  charP_of_injective_algebraMap (fun a b h => by
    have := congrArg PowerSeries.constantCoeff h; simpa using this) p

/-- the Tate curve over `𝔽_p⟦q⟧`. -/
noncomputable def TateBar : WeierstrassCurve (PowerSeries (ZMod p)) :=
  TateCurve.Tate.map (PowerSeries.map (Int.castRingHom (ZMod p)))

lemma c₄_TateBar : (TateBar p).c₄ = ModP.E4 (ZMod p) := by
  rw [TateBar, WeierstrassCurve.map_c₄, TateCurve.c₄_Tate_eq_p4]; rfl

lemma neg_c₆_TateBar : -(TateBar p).c₆ = ModP.E6 (ZMod p) := by
  rw [TateBar, WeierstrassCurve.map_c₆, TateCurve.c₆_Tate_eq_neg_p6, map_neg, neg_neg]; rfl

/-- the q-expansion map is evaluation at the Tate curve. -/
lemma ev_eq_evW (P : MvPolynomial (Fin 2) (ZMod p)) : ModP.ev (ZMod p) P = evW (TateBar p) P := by
  rw [ModP.ev, evW, MvPolynomial.aeval_def, MvPolynomial.coe_eval₂Hom]
  congr 1
  · exact Subsingleton.elim _ _
  · funext i; fin_cases i
    · simp [ModP.evVec, c₄_TateBar]
    · simp [ModP.evVec, neg_c₆_TateBar]

/-- **the q-expansion of `hassePoly` is the Hasse invariant of the Tate curve.** -/
theorem ev_hassePoly (hp5 : 5 ≤ p) : ModP.ev (ZMod p) (hassePoly p) = hasseH p (TateBar p) := by
  rw [ev_eq_evW, eval_hassePoly hp5]

lemma hasseH_TateBar_eq_aH (hp5 : 5 ≤ p) :
    hasseH p (TateBar p) = FGL.aH p (formalGroup (TateBar p)) :=
  (aH_formalGroup_eq_hasseH p (by omega) _).symm

/-- **`hassePoly = Ā` iff the Tate curve has Hasse invariant `1`.** -/
theorem hassePoly_eq_hasseBar_iff (hp5 : 5 ≤ p) :
    hassePoly p = ModP.hasseBar p hp5 ↔ hasseH p (TateBar p) = 1 := by
  constructor
  · intro h
    rw [← ev_hassePoly p hp5, h, ModP.ev_hasseBar]
  · intro h
    exact ModP.hasseBar_unique hp5 (iso_hassePoly p (by omega)) (by rw [ev_hassePoly p hp5, h])

/-- **Deligne's identification (conditional on `H(T̄) = 1`)**: in characteristic `p ≥ 5`, the
coefficient `a` of `T^p` in `[p]_W` is `Ā(c₄, −c₆)`. -/
theorem aH_eq_hasseBar (hp5 : 5 ≤ p) (hT : hasseH p (TateBar p) = 1) {R : Type*} [CommRing R]
    [CharP R p] (W : WeierstrassCurve R) :
    FGL.aH p (formalGroup W) = evW W (ModP.hasseBar p hp5) := by
  rw [aH_formalGroup_eq_hassePoly hp5, (hassePoly_eq_hasseBar_iff p hp5).mpr hT]

/-- any ring hom `ℤ_[p] → S` into a ring of characteristic `p` factors through `ℤ_[p] → 𝔽_p`. -/
lemma padic_hom_eq {S : Type*} [CommRing S] [CharP S p] (f : ℤ_[p] →+* S) :
    f = (ZMod.castHom (dvd_refl p) S).comp PadicInt.toZMod := by
  ext x
  have h := PadicInt.toZMod_spec x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  obtain ⟨y, hy⟩ := h
  have := congrArg f hy
  rw [map_sub, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, sub_eq_zero] at this
  rw [this, RingHom.comp_apply, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.cast_eq_val, map_natCast]

/-- **mixed characteristic (conditional on `H(T̄) = 1`)**: for a Weierstrass curve over a
`ℤ_[p]`-algebra, `a ≡ A(c₄, −c₆) (mod p)` where `A(E₄, E₆) = E_{p−1}`. -/
theorem coeff_nmul_sub_hasseA_mem (hp5 : 5 ≤ p) (hT : hasseH p (TateBar p) = 1) {R : Type*}
    [CommRing R] [Algebra ℤ_[p] R] (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (Finsupp.single () p) (FGL.nmul (formalGroup W) p) -
      MvPolynomial.aeval ![W.c₄, -W.c₆] (ModP.hasseA p hp5) ∈ Ideal.span {(p : R)} := by
  set I := Ideal.span {(p : R)}
  set π := Ideal.Quotient.mk I
  by_cases hI : I = ⊤
  · rw [hI]; trivial
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hpS : ((p : R ⧸ I)) = 0 := by
    rw [← map_natCast π, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
  haveI : CharP (R ⧸ I) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr hpS
  have h1 := coeff_nmul_sub_hasseH_mem p (by omega) W
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h1 ⊢
  rw [h1, map_hasseH, ← eval_hassePoly hp5, (hassePoly_eq_hasseBar_iff p hp5).mpr hT, evW,
    MvPolynomial.coe_eval₂Hom, ModP.hasseBar, MvPolynomial.eval₂_map, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_comp_left, ← padic_hom_eq p]
  congr 1
  funext i; fin_cases i
  · simp [WeierstrassCurve.map_c₄] <;> rfl
  · simp [WeierstrassCurve.map_c₆] <;> rfl

end HasseInv
