/-
# The formal group of an elliptic curve has height `≤ 2`

Over a field `k` of characteristic `p ≥ 5`, algebraically closed, for a Weierstrass curve with `Δ ≠ 0`
and Hasse invariant `a = aH p (formalGroup W) = 0`, the coefficient of `T^{p²}` in `[p](T)` is nonzero.

Proof (global, via the universal `x`-coordinate sequence `Xₙ ∈ k(t)`, `ht Xₙ ≤ n²`):
* `[p] ≠ 0` (`nmul_p_ne_zero`): otherwise `X_{p-1} = t` (from the generic formal point `P(T)`), but
  evaluating at `x(T₂ + P(T))` for a `2`-torsion point `T₂` gives `x(T₂ + P) = x(P)`, impossible.
* if `b = 0` then `[p] ∈ k⟦T^{p³}⟧`, so `x([p+1]T) ≡ x(T)` mod `T^{p³-…}`, while `X_{p+1} - t` is a
  nonzero rational function of height `≤ (p+1)² + 1`; comparing `T`-adic orders gives
  `p³ ≤ 2(p+1)² + 6`, false for `p ≥ 5`.
-/
import RamanujanTau.HeightEll.FormalAdd
import RamanujanTau.HeightEll.Seq
import RamanujanTau.HeightEll.Frob
import RamanujanTau.HeightEll.Adic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HeightEll
open MvPowerSeries EllipticFormal WeierstrassCurve.Affine

open scoped Classical

variable {k : Type*} [Field k] (W : WeierstrassCurve k)

local notation "A1" => MvPowerSeries Unit k
local notation "L" => FractionRing (MvPowerSeries Unit k)
local notation "ι" => algebraMap (MvPowerSeries Unit k) (FractionRing (MvPowerSeries Unit k))
local notation "T" => (MvPowerSeries.X () : MvPowerSeries Unit k)
local notation "FG" => formalGroup W

/-- `k → Frac k⟦T⟧`. -/
noncomputable abbrev jk : k →+* L := (ι).comp MvPowerSeries.C

lemma WK_eq : WK W Unit = W.map (jk (k := k)) := by
  rw [WK, WM, WeierstrassCurve.map_map]

lemma xc_P (h2 : (2 : k) ≠ 0) {t : A1} (ht : constantCoeff t = 0) (ht0 : t ≠ 0) :
    xc (W.map (jk (k := k))) (P W h2 t ht ht0 : (W.map (jk (k := k))).toAffine.Point) =
      ι t / ι (wt W t) := rfl

/-- the `x`-coordinate of a formal point with nonzero linear coefficient is not a constant. -/
lemma x_ne_const {t : A1} (ht : constantCoeff t = 0) (hlin : coeff (Finsupp.single () 1) t ≠ 0)
    (r : k) : ι t / ι (wt W t) ≠ jk r := by
  intro h
  have hw : ι (wt W t) ≠ 0 := by
    apply ι_ne; apply wt_ne_zero ht; rintro rfl; simp at hlin
  rw [div_eq_iff hw, RingHom.comp_apply, ← map_mul] at h
  have h' := ι_inj h
  apply hlin
  rw [h', lin_mul, wt_eq ht]
  simp [lin_mul, ht, pow_succ]

/-- transcendence from non-constancy over an algebraically closed field. -/
lemma eval₂_ne_zero_of_ne_const [IsAlgClosed k] {F : Type*} [Field F] (j : k →+* F) (ξ : F)
    (h : ∀ r, ξ ≠ j r) : ∀ A : Polynomial k, A ≠ 0 → A.eval₂ j ξ ≠ 0 := by
  intro A
  induction hA : A.natDegree using Nat.strong_induction_on generalizing A with
  | _ n ih =>
  intro hA0
  by_cases hd : A.degree = 0
  · rw [Polynomial.eq_C_of_degree_eq_zero hd, Polynomial.eval₂_C]
    intro h0
    have : A.coeff 0 = 0 := j.injective (by rw [h0, map_zero])
    apply hA0
    rw [Polynomial.eq_C_of_degree_eq_zero hd, this, map_zero]
  · obtain ⟨a, ha⟩ := IsAlgClosed.exists_root A hd
    have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot.2 ha)
    set B := A /ₘ (Polynomial.X - Polynomial.C a)
    have hB0 : B ≠ 0 := by rintro hB; rw [hB, mul_zero] at hfac; exact hA0 hfac.symm
    have hBd : B.natDegree < n := by
      rw [← hA, ← hfac, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hB0,
        Polynomial.natDegree_X_sub_C]; omega
    rw [← hfac, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
    exact mul_ne_zero (sub_ne_zero.2 (h a)) (ih _ hBd B rfl hB0)

/-- `y = T² v(T)`, with `x(T) = 1/y`. -/
noncomputable def yT : A1 := T ^ 2 * PowerSeries.subst T (v W)

lemma cc_vT : constantCoeff (PowerSeries.subst T (v W) : A1) = 1 := cc_subst_v (by simp)

lemma coeff_X_pow_mul_self (a : ℕ) (u : A1) :
    coeff (Finsupp.single () a) (T ^ a * u) = constantCoeff u := by
  rw [X_pow_eq, coeff_monomial_mul, if_pos le_rfl, tsub_self, one_mul,
    coeff_zero_eq_constantCoeff_apply]

lemma T_ne_zero : (T) ≠ 0 := lin_ne_zero (lin_X' ())

lemma ι_yT_ne : ι (yT W) ≠ 0 := by
  apply ι_ne; intro h
  have := congrArg (coeff (Finsupp.single () 2)) h
  rw [yT, coeff_X_pow_mul_self, cc_vT, map_zero] at this
  exact one_ne_zero this

lemma ξ_eq : ι T / ι (wt W T) = 1 / ι (yT W) := by
  have hT : ι T ≠ 0 := ι_ne T_ne_zero
  rw [wt_eq (by simp), yT, map_mul, map_mul, map_pow, map_pow]
  have hv : ι (PowerSeries.subst T (v W)) ≠ 0 := by
    apply ι_ne; intro h; have := cc_vT W; rw [h, map_zero] at this; exact zero_ne_one this
  field_simp

/-- **`x(T)` is transcendental**. -/
lemma ξ_trans : ∀ A : Polynomial k, A ≠ 0 → A.eval₂ jk (ι T / ι (wt W T)) ≠ 0 := by
  intro A hA h
  have e := eval_u₁ ι A (yT W) (ι_yT_ne W)
  rw [← ξ_eq, h, mul_zero] at e
  have hc := cc_u₁ A (y := yT W) (by simp [yT])
  have : u₁ A (yT W) = 0 := ι_inj (by rw [← e, map_zero])
  rw [this, map_zero] at hc
  exact Polynomial.leadingCoeff_ne_zero.2 hA hc.symm

/-! ## Characteristic `p` bookkeeping -/

section CharP
variable (p : ℕ) [hp : Fact p.Prime] [CharP k p]

lemma cast_ne_zero_of_lt {m : ℕ} (h1 : 1 ≤ m) (hm : m < p) : (m : k) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff k p]
  intro h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega)

lemma two_ne (hp5 : 5 ≤ p) : (2 : k) ≠ 0 := by
  exact_mod_cast cast_ne_zero_of_lt (k := k) p (m := 2) (by omega) (by omega)

lemma three_ne (hp5 : 5 ≤ p) : (3 : k) ≠ 0 := by
  exact_mod_cast cast_ne_zero_of_lt (k := k) p (m := 3) (by omega) (by omega)

end CharP

/-! ## A `2`-torsion point -/

lemma exists_kPsi_root [IsAlgClosed k] (h2 : (2 : k) ≠ 0) : ∃ e : k, kPsi W e = 0 := by
  set KP := kPsi (W.map Polynomial.C) (Polynomial.X : Polynomial k)
  have hKP : KP = Polynomial.C 4 * Polynomial.X ^ 3 + Polynomial.C W.b₂ * Polynomial.X ^ 2 +
      Polynomial.C (2 * W.b₄) * Polynomial.X + Polynomial.C W.b₆ := by
    simp only [KP, kPsi, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
      map_mul, map_ofNat]
  have h4 : (4 : k) ≠ 0 := by
    have : (4 : k) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hd : KP.degree ≠ 0 := by
    rw [hKP, Polynomial.degree_cubic h4]; decide
  obtain ⟨e, he⟩ := IsAlgClosed.exists_root KP hd
  refine ⟨e, ?_⟩
  have := map_kPsi (Polynomial.evalRingHom e) (W.map Polynomial.C) Polynomial.X
  rw [WeierstrassCurve.map_map] at this
  have hid : (Polynomial.evalRingHom e).comp Polynomial.C = RingHom.id k := by
    ext; simp
  rw [hid, WeierstrassCurve.map_id] at this
  simpa [KP, Polynomial.IsRoot] using this.symm.trans he

lemma two_torsion_eqn (h2 : (2 : k) ≠ 0) {e : k} (he : kPsi W e = 0) :
    W.toAffine.Equation e (-(W.a₁ * e + W.a₃) / 2) := by
  rw [equation_iff']
  set y := -(W.a₁ * e + W.a₃) / 2
  have hy : 2 * y + W.a₁ * e + W.a₃ = 0 := by simp only [y]; field_simp; ring
  have h4 : (4 : k) * (y ^ 2 + W.a₁ * e * y + W.a₃ * y - (e ^ 3 + W.a₂ * e ^ 2 + W.a₄ * e + W.a₆)) = 0 := by
    rw [kPsi, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at he
    linear_combination (2 * y + W.a₁ * e + W.a₃) * hy - he
  have : (4 : k) ≠ 0 := by
    have : (4 : k) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  exact (mul_eq_zero.1 h4).resolve_left this

lemma nsmul_two_torsion {G : Type*} [AddCommGroup G] {t : G} (ht : t + t = 0) (n : ℕ) :
    (2 * n) • t = 0 ∧ (2 * n + 1) • t = t := by
  have h0 : (2 * n) • t = 0 := by rw [two_mul, add_nsmul, ← nsmul_add, ht, nsmul_zero]
  exact ⟨h0, by rw [succ_nsmul, h0, zero_add]⟩

/-! ## `[p] ≠ 0` -/

/-- **`[p] ≠ 0`** for an elliptic curve over an algebraically closed field of characteristic `p ≥ 5`. -/
theorem nmul_p_ne_zero [IsAlgClosed k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] (hp5 : 5 ≤ p)
    (hΔ : W.Δ ≠ 0) : FGL.nmul FG p ≠ 0 := by
  intro hπ
  have h2 := two_ne (k := k) p hp5
  have h3 := three_ne (k := k) p hp5
  have hN : ∀ m, 1 ≤ m → m ≤ p - 1 → FGL.nmul FG m ≠ 0 := fun m h1 hm =>
    nmul_ne_zero W (cast_ne_zero_of_lt p h1 (by omega))
  have hmul0 := nsmul_P W h2 h3 (p - 1) hN
  set Q : (W.map (jk (k := k))).toAffine.Point := P W h2 T cc_T' (lin_ne_zero (lin_X' ())) with hQdef
  have hmul : ∀ m (h1 : 1 ≤ m) (hm : m ≤ p - 1), m • Q =
      (P W h2 (FGL.nmul FG m) (FGL.cc_nmul _ m) (hN m h1 hm) : (W.map (jk (k := k))).toAffine.Point) :=
    fun m h1 hm => hmul0 m h1 hm
  set ξ := ι T / ι (wt W T) with hξdef
  have hQx : xc _ Q = ξ := rfl
  have hNQ : ∀ m, 1 ≤ m → m ≤ p - 1 → m • Q ≠ 0 := by
    intro m h1 hm; rw [hmul m h1 hm]; exact Point.some_ne_zero _
  have hξ := ξ_trans W
  have hU := xc_nsmul W jk ξ hξ Q hQx (p - 1) hNQ
  -- `x((p-1) P) = x(P)`
  set s' := FGL.nmul FG (p - 1)
  have hF : subst ![T, s'] (F W) = 0 := by
    rw [← nmul_succ', Nat.sub_add_cancel hp.out.one_lt.le]; exact hπ
  have hTs : (T) ≠ s' := by
    apply ne_of_lin
    rw [lin_X, if_pos rfl, lin_nmul, Nat.cast_sub hp.out.one_lt.le, CharP.cast_eq_zero, zero_sub,
      Nat.cast_one]
    intro h; apply h2; linear_combination h
  have hx := x_eq_of_F_eq_zero W cc_T' (FGL.cc_nmul _ _) hTs hF
  have hs'0 : s' ≠ 0 := hN (p - 1) (by have := hp.out.two_le; omega) le_rfl
  have hxp : xc _ ((p - 1) • Q) = ξ := by
    rw [hmul (p - 1) (by have := hp.out.two_le; omega) le_rfl, xc_P, hξdef,
      div_eq_div_iff (ι_ne (wt_ne_zero (FGL.cc_nmul _ _) hs'0)) (ι_ne (wt_ne_zero cc_T' T_ne_zero)),
      ← map_mul, ← map_mul, ← hx, mul_comm]
  have hXs : Xs W (p - 1) = tX := by
    apply (evr (jk (k := k)) ξ hξ).injective
    rw [← hU (p - 1) (by have := hp.out.two_le; omega) le_rfl, hxp, evr_tX]
  -- the `2`-torsion point
  obtain ⟨e, he⟩ := exists_kPsi_root W h2
  set y₂ := -(W.a₁ * e + W.a₃) / 2
  have hEq := two_torsion_eqn W h2 he
  have hΔL : (W.map (jk (k := k))).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]; exact (map_ne_zero_iff _ jk.injective).2 hΔ
  have hNS : (W.map (jk (k := k))).toAffine.Nonsingular (jk e) (jk y₂) :=
    ((W.map jk).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔL).1
      (WeierstrassCurve.Affine.Equation.map jk hEq)
  set T2 : (W.map (jk (k := k))).toAffine.Point := Point.some _ _ hNS
  have hT2 : T2 + T2 = 0 := by
    apply Point.add_self_of_Y_eq
    rw [negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
    have : 2 * y₂ + W.a₁ * e + W.a₃ = 0 := by simp only [y₂]; field_simp; ring
    have := congrArg jk this
    simp only [map_add, map_mul, map_ofNat, map_zero] at this
    linear_combination this
  have hT2n : -T2 = T2 := neg_eq_of_add_eq_zero_left hT2
  have hT20 : T2 ≠ 0 := Point.some_ne_zero _
  -- `x` of a formal multiple is not the constant `e`
  have hxc : ∀ m, 1 ≤ m → m ≤ p - 1 → ∀ c, xc _ (m • Q) ≠ jk c := by
    intro m h1 hm c
    rw [hmul m h1 hm, xc_P]
    exact x_ne_const W (FGL.cc_nmul _ _) (by rw [lin_nmul]; exact cast_ne_zero_of_lt p h1 (by omega)) c
  have hxm : ∀ m, 1 ≤ m → m ≤ p - 1 → xc _ (m • Q) ≠ jk e := fun m h1 hm => hxc m h1 hm e
  set Q₂ := T2 + Q
  have hNQ2 : ∀ m, 1 ≤ m → m ≤ p - 1 → m • Q₂ ≠ 0 := by
    intro m h1 hm
    rw [nsmul_add]
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
    · rw [(nsmul_two_torsion hT2 n).1, zero_add]; exact hNQ _ h1 hm
    · rw [(nsmul_two_torsion hT2 n).2]
      intro h
      have : (2 * n + 1) • Q = T2 := by rw [← hT2n]; exact eq_neg_of_add_eq_zero_right h
      apply hxm _ h1 hm
      rw [this]; rfl
  have hQ20 : Q₂ ≠ 0 := by simpa using hNQ2 1 le_rfl (by omega)
  have h2Q2 : 2 • Q₂ = 2 • Q := by
    rw [nsmul_add, show (2 : ℕ) = 2 * 1 from rfl, (nsmul_two_torsion hT2 1).1, zero_add]
  -- `x(Q₂)` is transcendental
  have hξ₂ : ∀ A : Polynomial k, A ≠ 0 → A.eval₂ jk (xc _ Q₂) ≠ 0 := by
    apply eval₂_ne_zero_of_ne_const
    intro r hr
    obtain ⟨x₂, y₂', h₂, hQ2e⟩ := eq_some_of_ne_zero _ hQ20
    have h2ne : Point.some _ _ h₂ + Point.some _ _ h₂ ≠ 0 := by
      rw [← hQ2e, ← two_nsmul, h2Q2]; exact hNQ 2 (by omega) (by omega)
    obtain ⟨hp', hd⟩ := doubling _ h₂ h2ne
    rw [hQ2e, xc_some] at hr
    subst hr
    rw [← map_kPsi] at hp'
    rw [← map_kPhi, ← map_kPsi] at hd
    rw [← hQ2e, ← two_nsmul, h2Q2] at hd
    have hp'' : kPsi W r ≠ 0 := by rintro h; rw [h, map_zero] at hp'; exact hp' rfl
    exact hxc 2 (by omega) (by omega) (kPhi W r / kPsi W r)
      (by rw [map_div₀]; exact eq_div_of_mul_eq hp' (by rw [mul_comm]; exact hd))
  have hU2 := xc_nsmul W jk (xc _ Q₂) hξ₂ Q₂ rfl (p - 1) hNQ2 (p - 1)
    (by have := hp.out.two_le; omega) le_rfl
  rw [hXs, evr_tX] at hU2
  -- `(p-1) Q₂ = (p-1) Q` since `p - 1` is even
  obtain ⟨n, hn⟩ : ∃ n, p - 1 = 2 * n := by
    rcases hp.out.eq_two_or_odd' with h | ⟨n, hn⟩
    · omega
    · exact ⟨n, by omega⟩
  have hpQ2 : (p - 1) • Q₂ = (p - 1) • Q := by
    rw [nsmul_add, hn, (nsmul_two_torsion hT2 n).1, zero_add]
  rw [hpQ2, hxp] at hU2
  -- `x(T₂ + P) = x(P)`
  have hQ0 : Q ≠ 0 := by simpa using hNQ 1 le_rfl (by omega)
  rcases eq_or_eq_neg_of_xc_eq _ hQ20 hQ0 (hU2.symm.trans hQx.symm) with h | h
  · apply hT20; simpa [Q₂] using h
  · have : T2 = -(2 • Q) := by
      rw [two_nsmul, neg_add, ← sub_eq_add_neg]; exact eq_sub_of_add_eq h
    apply hxm 2 (by omega) (by omega)
    rw [← xc_neg, ← this]; rfl

lemma field_identity {F : Type*} [Field F] {cξ dξ ξ S WS TT WT : F} (hdξ : dξ ≠ 0) (hWS : WS ≠ 0)
    (hWT : WT ≠ 0) (hU : S / WS = cξ / dξ) (hξ : ξ = TT / WT) :
    (cξ - ξ * dξ) * (WS * WT) = dξ * (S * WT - TT * WS) := by
  have hc : cξ = dξ * (S / WS) := by rw [hU]; field_simp
  rw [hc, hξ]; field_simp

lemma clear_identity {F : Type*} [Field F] {y a dd UA UD Xv Yv : F} {nA nD : ℕ}
    (eA : y ^ nA * a = UA) (eD : y ^ nD * dd = UD) (hL : a * Xv = dd * Yv) :
    UA * y ^ nD * Xv = UD * y ^ nA * Yv := by
  rw [← eA, ← eD]; linear_combination (y ^ nA * y ^ nD) * hL

/-! ## Height `≤ 2` -/

lemma lin_wt_zero {t : A1} (ht : constantCoeff t = 0) : coeff (Finsupp.single () 1) (wt W t) = 0 := by
  rw [wt_eq ht]; simp [lin_mul, ht, pow_succ]

/-- **the formal group of an elliptic curve has height `≤ 2`**: over an algebraically closed field of
characteristic `p ≥ 5`, if `Δ ≠ 0` and the Hasse invariant `a` vanishes, then the coefficient of
`T^{p²}` in `[p](T)` is nonzero. -/
theorem coeff_p2_ne_zero [IsAlgClosed k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] (hp5 : 5 ≤ p)
    (hΔ : W.Δ ≠ 0) (ha : FGL.aH p FG = 0) :
    coeff (Finsupp.single () (p ^ 2)) (FGL.nmul FG p) ≠ 0 := by
  intro hb
  have hπ := nmul_p_ne_zero W p hp5 hΔ
  have h2 := two_ne (k := k) p hp5
  have h3 := three_ne (k := k) p hp5
  have hp1 : (p : k) = 0 := CharP.cast_eq_zero k p
  have hN : ∀ m, 1 ≤ m → m ≤ p + 1 → FGL.nmul FG m ≠ 0 := by
    intro m h1 hm
    rcases Nat.lt_or_ge m p with hlt | hge
    · exact nmul_ne_zero W (cast_ne_zero_of_lt p h1 hlt)
    · rcases Nat.eq_or_lt_of_le hge with h | h
      · rw [← h]; exact hπ
      · obtain rfl : m = p + 1 := by omega
        apply nmul_ne_zero W; push_cast; rw [hp1, zero_add]; exact one_ne_zero
  have hmul0 := nsmul_P W h2 h3 (p + 1) hN
  set Q : (W.map (jk (k := k))).toAffine.Point := P W h2 T cc_T' (lin_ne_zero (lin_X' ())) with hQdef
  have hmul : ∀ m (h1 : 1 ≤ m) (hm : m ≤ p + 1), m • Q =
      (P W h2 (FGL.nmul FG m) (FGL.cc_nmul _ m) (hN m h1 hm) : (W.map (jk (k := k))).toAffine.Point) :=
    fun m h1 hm => hmul0 m h1 hm
  set ξ := ι T / ι (wt W T) with hξdef
  have hQx : xc _ Q = ξ := rfl
  have hNQ : ∀ m, 1 ≤ m → m ≤ p + 1 → m • Q ≠ 0 := by
    intro m h1 hm; rw [hmul m h1 hm]; exact Point.some_ne_zero _
  have hξ := ξ_trans W
  have hU := xc_nsmul W jk ξ hξ Q hQx (p + 1) hNQ (p + 1) (by omega) le_rfl
  have hH := ht_Xs_le W jk ξ hξ Q hQx (p + 1) (by omega) hNQ (p + 1) (by omega) le_rfl
  set s := FGL.nmul FG (p + 1) with hsdef
  set π := FGL.nmul FG p
  have hsc : constantCoeff s = 0 := FGL.cc_nmul _ _
  have hs0 : s ≠ 0 := hN (p + 1) (by omega) le_rfl
  have hsl : coeff (Finsupp.single () 1) s = 1 := by
    rw [lin_nmul]; push_cast; rw [hp1, zero_add]
  rw [hmul (p + 1) (by omega) le_rfl, xc_P] at hU
  -- `X_{p+1} ≠ t`
  set Xp := Xs W (p + 1)
  have hwT : ι (wt W T) ≠ 0 := ι_ne (wt_ne_zero cc_T' T_ne_zero)
  have hws : ι (wt W s) ≠ 0 := ι_ne (wt_ne_zero hsc hs0)
  have hne : Xp ≠ tX := by
    intro h
    rw [h, evr_tX, hξdef, div_eq_div_iff hws hwT, ← map_mul, ← map_mul] at hU
    have hx := ι_inj hU
    by_cases hsT : s = T
    · -- `(p+1) P = P` forces `p P = 0`
      have e1 : (p + 1) • Q = Q := by
        rw [hmul (p + 1) (by omega) le_rfl]; exact P_congr W h2 hsT _ _ _ _
      have : p • Q = 0 := by
        have := congrArg (· - Q) e1; simpa [succ_nsmul] using this
      exact hNQ p (by omega) (by omega) this
    · have hF := F_eq_zero_of_x_eq W cc_T' hsc T_ne_zero hs0 (Ne.symm hsT) (by rw [hx])
      apply nmul_ne_zero W (n := p + 2) (by push_cast; rw [hp1, zero_add]; exact h2)
      rw [nmul_succ']; exact hF
  -- numerator and denominator
  set c := Xp.num
  set d := Xp.denom
  have hd : d ≠ 0 := RatFunc.denom_ne_zero _
  have ex : Xp = ιk c / ιk d := (RatFunc.num_div_denom _).symm
  set Ap := c - Polynomial.X * d
  have hA : Ap ≠ 0 := by
    intro h
    apply hne
    rw [ex, show c = Polynomial.X * d from sub_eq_zero.1 h, map_mul,
      mul_div_cancel_right₀ _ (RatFunc.algebraMap_ne_zero hd)]
  have hdξ : d.eval₂ jk ξ ≠ 0 := hξ d hd
  have hev : evr jk ξ hξ Xp = c.eval₂ jk ξ / d.eval₂ jk ξ := by
    rw [ex, map_div₀, evr_alg, evr_alg]
  rw [hev] at hU
  -- the identity in `L`
  have hL : Ap.eval₂ jk ξ * ι (wt W s * wt W T) = d.eval₂ jk ξ * ι (s * wt W T - T * wt W s) := by
    have := field_identity (TT := ι T) hdξ hws hwT hU hξdef
    simp only [Ap, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, map_mul, map_sub]
    exact this
  -- multiply out by powers of `y`
  set y := yT W
  have hy := ι_yT_ne W
  have eA := eval_u₁ ι Ap y hy
  have eD := eval_u₁ ι d y hy
  rw [← ξ_eq] at eA eD
  set dA := Ap.natDegree
  set dD := d.natDegree
  have hkey : u₁ Ap y * y ^ dD * (wt W s * wt W T) = u₁ d y * y ^ dA * (s * wt W T - T * wt W s) := by
    apply ι_inj
    simp only [map_mul, map_pow]
    have hL' := hL
    rw [map_mul] at hL'
    exact clear_identity eA eD hL'
  -- the right side is divisible by `T^{p³}`
  set M := p ^ 3
  have hπM : T ^ M ∣ π := by
    rw [X_pow_dvd_iff]
    intro e he
    have : e = Finsupp.single () (e ()) := Finsupp.ext fun u => by cases u; simp
    rw [this]
    rcases Nat.eq_zero_or_pos (e ()) with h0 | hpos
    · rw [h0, Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply]; exact FGL.cc_nmul _ _
    · exact coeff_nmul_eq_zero_of_ab p FG ha hb _ fun h => absurd (Nat.le_of_dvd hpos h) (by omega)
  have hsT : T ^ M ∣ s - T := by
    have e1 : subst ![T, π] (F W) = s := (nmul_succ' W p).symm
    have e2 : subst ![T, (0 : A1)] (F W) = T := FGL.ev_T_zero FG
    have key := dvd_subst_sub ![T, π] ![T, (0 : A1)] (FGL.cc_vec2 cc_T' (FGL.cc_nmul _ _))
      (FGL.cc_vec2 cc_T' (by simp)) M (fun i => by fin_cases i <;> simp [hπM]) (F W)
    rwa [e1, e2] at key
  have hwsT : T ^ M ∣ wt W s - wt W T := by
    have := dvd_subst_sub (fun _ : Unit => s) (fun _ : Unit => T) (fun _ => hsc) (fun _ => cc_T') M
      (fun _ => hsT) (w W)
    simpa [wt, PowerSeries.subst_def] using this
  have hNn : T ^ M ∣ s * wt W T - T * wt W s := by
    have : s * wt W T - T * wt W s = (s - T) * wt W T - T * (wt W s - wt W T) := by ring
    rw [this]; exact dvd_sub (dvd_mul_of_dvd_left hsT _) (dvd_mul_of_dvd_right hwsT _)
  have hdiv : T ^ M ∣ u₁ Ap y * y ^ dD * (wt W s * wt W T) := by
    rw [hkey]; exact dvd_mul_of_dvd_right hNn _
  -- the left side is `T^{2 dD + 6}` times a unit
  obtain ⟨s₀, hs₀⟩ : (T) ∣ s := by
    rw [X_dvd_iff]; intro m hm
    have : m = 0 := Finsupp.ext fun u => by cases u; simpa using hm
    rw [this, coeff_zero_eq_constantCoeff_apply]; exact hsc
  have hs₀c : constantCoeff s₀ = 1 := by
    have := hsl; rw [hs₀, ← pow_one (X () : A1), coeff_X_pow_mul_self] at this; exact this
  have hvT : constantCoeff (PowerSeries.subst T (v W) : A1) = 1 := cc_vT W
  have hvs : constantCoeff (PowerSeries.subst s (v W) : A1) = 1 := cc_subst_v hsc
  have hLHS : u₁ Ap y * y ^ dD * (wt W s * wt W T) =
      T ^ (2 * dD + 6) * (u₁ Ap y * (PowerSeries.subst T (v W) : A1) ^ dD *
        (s₀ ^ 3 * PowerSeries.subst s (v W) * PowerSeries.subst T (v W))) := by
    rw [wt_eq hsc, wt_eq cc_T', show y = T ^ 2 * PowerSeries.subst T (v W) from rfl]
    rw [show s ^ 3 = T ^ 3 * s₀ ^ 3 by rw [hs₀]; ring]
    ring
  rw [hLHS] at hdiv
  have hu : constantCoeff (u₁ Ap y * (PowerSeries.subst T (v W) : A1) ^ dD *
      (s₀ ^ 3 * PowerSeries.subst s (v W) * PowerSeries.subst T (v W))) ≠ 0 := by
    rw [map_mul, map_mul, map_mul, map_mul, map_pow, map_pow,
      cc_u₁ Ap (show constantCoeff y = 0 by simp [y, yT]), hvT, hvs, hs₀c]
    simpa using Polynomial.leadingCoeff_ne_zero.2 hA
  have hM := le_of_X_pow_dvd hu hdiv
  -- `deg d ≤ ht X_{p+1} ≤ (p+1)²`
  have hdD : dD ≤ (p + 1) ^ 2 := (le_max_right _ _).trans hH
  have h1 : p ^ 3 ≤ 2 * (p + 1) ^ 2 + 6 := le_trans hM (by omega)
  have h25 : 25 ≤ p * p := Nat.mul_le_mul hp5 hp5
  have h125 : 5 * (p * p) ≤ p * (p * p) := Nat.mul_le_mul_right _ hp5
  nlinarith [h1, h25, h125]

end HeightEll
