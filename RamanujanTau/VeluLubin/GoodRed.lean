/-
# Good reduction from the formal group

`K` complete, algebraically closed, ultrametric, `𝒪 = integers K`, `k = 𝒪/𝔪`, `p ≥ 5` prime with
`‖p‖ < 1` (so `char k = p`, `charP_k`).

**`norm_Δ_eq_one_of_iso`**: if a short curve `W = y² = x³ + ax + b` over `𝒪` has a formal group
isomorphic over `𝒪` (by a homomorphism with unit Lie derivative) to a formal group `G` of height
exactly `2` (`‖[p]_{p²}‖ = 1`, `‖[p]_p‖ < 1`), then `‖Δ(W)‖ = 1`.

Proof: the reduction of `[p]_{F_W}` has order exactly `p²` (orders multiply under composition). If
`Δ ≡ 0`:
* cusp (`a ≡ b ≡ 0`): `F_{Wb}(X,Y) = X + Y`, so `[p]_{F_{Wb}} = pT = 0` — contradiction;
* node (`a ≢ 0`): `(c₄, -c₆) ≡ (u⁴, u⁶)` with `u ≢ 0` (since `c₄³ ≡ c₆²`), so by isobaricity
  `a_{Wb} = Ā(c₄, -c₆) = u^{p-1}·Ā(1,1) = u^{p-1} ≠ 0` (Deligne, `HasseInv.aH_eq_hasseBar'`, and
  `Ā(Ē₄,Ē₆) = 1`): the reduction has order `p` — contradiction.
-/
import RamanujanTau.VeluLubin.Link
import RamanujanTau.QuotientHasse.Reduction
import RamanujanTau.HasseInv.Unconditional

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluLubin
open MvPowerSeries EllipticFormal EllipticI2 CanonicalIsogeny QuotientHasse

/-! ### The cuspidal cubic `y² = x³` has the additive formal group -/

section Cusp
variable {R : Type*} [CommRing R]

lemma dInv_cusp : dInv (shortO (0 : R) 0) = -1 := by
  have h := dd_mul_dInv (shortO (0 : R) 0)
  have hd : dd (shortO (0 : R) 0) = -1 := by simp [dd, WM, shortO]
  rw [hd] at h
  linear_combination -h

lemma F_cusp : F (shortO (0 : R) 0) = X 0 + X 1 := by
  have hB : B (WM (shortO (0 : R) 0) (Fin 2)) (lam (shortO (0 : R) 0)) (nu (shortO (0 : R) 0)) = 0 := by
    simp [B, WM, shortO]
  rw [F, z3, hB, dInv_cusp]; ring

lemma nmul_cusp (n : ℕ) :
    FGL.nmul (formalGroup (shortO (0 : R) 0)) n = (n : MvPowerSeries Unit R) * X () := by
  induction n with
  | zero => simp [FGL.nmul]
  | succ n ih =>
    show FGL.ev _ FGL.T (FGL.nmul _ n) = _
    have hv := FGL.cc_vec2 (FGL.cc_T (R := R)) (FGL.cc_nmul (formalGroup (shortO (0 : R) 0)) n)
    rw [FGL.ev, formalGroup_toPowerSeries, F_cusp, subst_add (FGL.hs hv), FGL.sX _ hv, FGL.sX _ hv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [ih]; push_cast; ring

end Cusp

/-! ### Isobaric evaluation -/

section Isobaric
variable {R S : Type*} [CommRing R] [CommRing S]

theorem eval₂_iso (f : R →+* S) {P : MvPolynomial (Fin 2) R} {k : ℕ} (hP : ModP.Iso P k)
    (t x y : S) :
    MvPolynomial.eval₂ f ![t ^ 4 * x, t ^ 6 * y] P = t ^ k * MvPolynomial.eval₂ f ![x, y] P := by
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw := hP (MvPolynomial.mem_support_iff.1 hd)
  rw [ModP.weight_wt] at hw
  rw [Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [← hw, mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]
  ring

/-- `Ā(1,1) = 1` (the constant term of `Ā(Ē₄,Ē₆) = 1`). -/
lemma eval_hasseBar_one {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    MvPolynomial.eval ![1, 1] (ModP.hasseBar p hp5) = 1 := by
  have h := congrArg PowerSeries.constantCoeff (ModP.ev_hasseBar hp5)
  rw [map_one] at h
  have e : (PowerSeries.constantCoeff).comp (algebraMap (ZMod p) (PowerSeries (ZMod p))) =
      RingHom.id (ZMod p) := by ext x; simp
  have key : MvPolynomial.eval ![1, 1] (ModP.hasseBar p hp5) =
      PowerSeries.constantCoeff (ModP.ev (ZMod p) (ModP.hasseBar p hp5)) := by
    rw [ModP.ev, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, e, MvPolynomial.eval,
      MvPolynomial.coe_eval₂Hom]
    congr 1
    funext i; fin_cases i
    · exact (ModP.constantCoeff_E4 (ZMod p)).symm
    · exact (ModP.constantCoeff_E6 (ZMod p)).symm
  rw [key, h]

lemma node_alg {k : Type*} [CommRing k] [IsDomain k] {c4 c6 s : k} (hc4 : c4 ≠ 0)
    (hrel : c4 ^ 3 = c6 ^ 2) (hs : s ^ 2 * c4 = -c6) : s ^ 4 = c4 ∧ s ^ 6 = -c6 := by
  have h4 : s ^ 4 = c4 := by
    have : c4 ^ 2 * (s ^ 4 - c4) = 0 := by
      linear_combination (s ^ 2 * c4 - c6) * hs - hrel
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 hc4))
  refine ⟨h4, ?_⟩
  have : c4 * (s ^ 6 + c6) = 0 := by
    linear_combination (s ^ 4) * hs - c6 * h4
  have h' := (mul_eq_zero.1 this).resolve_left hc4
  linear_combination h'

end Isobaric

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => integers K

/-! ### The residue field has characteristic `p` -/

lemma norm_intCast_le_one' (a : ℤ) : ‖(a : K)‖ ≤ 1 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a <;>
    simpa using IsUltrametricDist.norm_natCast_le_one K n

/-- `char (𝒪/𝔪) = p`. -/
theorem charP_k (p : ℕ) [hp : Fact p.Prime] (hp1 : ‖(p : K)‖ < 1) : CharP (𝒪 ⧸ mI (K := K)) p := by
  refine ⟨fun n => ?_⟩
  rw [show ((n : 𝒪 ⧸ mI (K := K))) = red (n : 𝒪) by simp, red_eq_zero]
  push_cast
  constructor
  · intro hn
    by_contra hnd
    have hcop : Nat.Coprime n p := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hnd))
    have hb := Nat.gcd_eq_gcd_ab n p
    rw [hcop.gcd_eq_one] at hb
    have hbK : (1 : K) = (n : K) * ((n.gcdA p : ℤ) : K) + (p : K) * ((n.gcdB p : ℤ) : K) := by
      have := congrArg (fun z : ℤ => (z : K)) hb
      simpa using this
    have h1 := IsUltrametricDist.norm_add_le_max ((n : K) * ((n.gcdA p : ℤ) : K))
      ((p : K) * ((n.gcdB p : ℤ) : K))
    rw [← hbK, norm_one, norm_mul, norm_mul] at h1
    have e1 := mul_le_of_le_one_right (norm_nonneg (n : K)) (norm_intCast_le_one' (K := K) (n.gcdA p))
    have e2 := mul_le_of_le_one_right (norm_nonneg (p : K)) (norm_intCast_le_one' (K := K) (n.gcdB p))
    have := h1.trans (max_le_max e1 e2)
    rcases le_max_iff.1 this with h | h <;> linarith
  · rintro ⟨m, rfl⟩
    push_cast
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _)
      (IsUltrametricDist.norm_natCast_le_one K m)) hp1

/-! ### The main argument -/

variable [CompleteSpace K]

lemma red_short (a b : 𝒪) :
    (shortO a b).map (red (K := K)) = shortO (red a) (red b) := by
  ext <;> simp [shortO]

/-- **order of the reduced `[p]` transfers along an isomorphism**. -/
theorem lowOrd_nmul_of_iso (p : ℕ) [hp : Fact p.Prime] (hp1 : ‖(p : K)‖ < 1)
    (G F' : FormalGroup 𝒪) [G.IsComm] (hu : ‖topc G p‖ = 1) (ha : ‖hasse G p‖ < 1)
    (θ : MvPowerSeries Unit 𝒪) (hθ : Hom G F' θ)
    (hθ1 : ‖((coeff (Finsupp.single () 1) θ : 𝒪) : K)‖ = 1) :
    LowOrd (PowerSeries.map (red (K := K)) (FGL.nmul F' p)) (p ^ 2) := by
  have hp0 := hp.out.pos
  have hG := lowOrd_nmul G p hu ha hp1
  have hθo : LowOrd (PowerSeries.map (red (K := K)) θ) 1 := by
    rw [lowOrd_red_iff]
    refine ⟨fun k hk => ?_, hθ1⟩
    have : k = 0 := by omega
    subst this
    rw [Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply, hθ.1]; simp
  have hcomp := hom_nmul G F' θ hθ.1 hθ.2 p
  have hR : LowOrd (PowerSeries.map (red (K := K))
      (subst (fun _ : Unit => FGL.nmul G p) θ)) (1 * p ^ 2) := by
    rw [red_subst (FGL.cc_nmul G p)]
    exact lowOrd_subst hθo hG (Nat.one_le_pow _ _ hp0)
  rw [← hcomp, red_subst hθ.1] at hR
  set g := PowerSeries.map (red (K := K)) (FGL.nmul F' p) with hg
  by_cases hg0 : g = 0
  · exfalso
    rw [hg0] at hR
    have h0 : ∀ s : Unit, MvPowerSeries.constantCoeff
        ((fun _ : Unit => PowerSeries.map (red (K := K)) θ) s) = 0 := fun _ => hθo.cc_zero le_rfl
    rw [FGL.s0 _ h0] at hR
    exact hR.2 (map_zero _)
  have hgo : LowOrd g g.order.toNat :=
    ⟨fun k hk => PowerSeries.coeff_of_lt_order_toNat k hk, PowerSeries.coeff_order hg0⟩
  have h2 := (lowOrd_subst hgo hθo le_rfl).unique hR
  rw [mul_one, one_mul] at h2
  rwa [h2] at hgo

lemma c4_short {R : Type*} [CommRing R] (A B : R) : (shortO A B).c₄ = -48 * A := by
  simp only [shortO, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring

/-- **the Hasse invariant of a nodal short cubic is a unit** (characteristic `p ≥ 5`). -/
theorem aH_node (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) {k : Type*} [CommRing k] [IsDomain k]
    [CharP k p] {A B u : k} (hc4ne : (shortO A B).c₄ ≠ 0) (hΔ : (shortO A B).Δ = 0)
    (hu2 : u ^ 2 * (shortO A B).c₄ = -(shortO A B).c₆) :
    FGL.aH p (formalGroup (shortO A B)) = u ^ (p - 1) ∧ u ≠ 0 := by
  have hrel : (shortO A B).c₄ ^ 3 = (shortO A B).c₆ ^ 2 := by
    have := (shortO A B).c_relation
    rw [hΔ, mul_zero] at this
    exact sub_eq_zero.1 this.symm
  obtain ⟨hu4, hu6⟩ := node_alg hc4ne hrel hu2
  have hune : u ≠ 0 := by
    intro h; apply hc4ne; rw [← hu4, h]; ring
  refine ⟨?_, hune⟩
  rw [HasseInv.aH_eq_hasseBar' p hp5, HasseInv.evW, MvPolynomial.coe_eval₂Hom]
  have e : (![(shortO A B).c₄, -(shortO A B).c₆] : Fin 2 → k) = ![u ^ 4 * 1, u ^ 6 * 1] := by
    rw [hu4, hu6]; simp
  rw [e, eval₂_iso _ (ModP.iso_hasseBar hp5)]
  have h1 := congrArg (ZMod.castHom (dvd_refl p) k) (eval_hasseBar_one hp5)
  rw [map_one, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left] at h1
  have e2 : (ZMod.castHom (dvd_refl p) k) ∘ ![1, 1] = ![1, 1] := by
    funext i; fin_cases i <;> simp
  rw [e2, RingHom.comp_id] at h1
  rw [h1, mul_one]

/-- a square root of `-c₆/c₄` in `𝒪` (for `‖c₄‖ = 1`). -/
lemma exists_sqrt_lift [IsAlgClosed K] (c4 c6 : 𝒪) (hc4n : ‖(c4 : K)‖ = 1) :
    ∃ u : 𝒪, red (K := K) u ^ 2 * red c4 = -red c6 := by
  have hc4K : (c4 : K) ≠ 0 := by intro h; rw [h, norm_zero] at hc4n; exact zero_ne_one hc4n
  obtain ⟨uK, huK⟩ := IsAlgClosed.exists_pow_nat_eq (-(c6 : K) / c4) (n := 2) (by norm_num)
  have hun : ‖uK‖ ≤ 1 := by
    have : ‖uK‖ ^ 2 ≤ 1 := by
      rw [← norm_pow, huK, norm_div, norm_neg, hc4n, div_one]; exact c6.2
    nlinarith [norm_nonneg uK]
  refine ⟨⟨uK, hun⟩, ?_⟩
  rw [← map_pow, ← map_mul, ← map_neg]
  congr 1
  apply Subtype.ext
  simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_neg, huK]
  field_simp

/-- **good reduction from the formal group**: a short curve whose formal group is
`𝒪`-isomorphic to a height-`2` formal group has `‖Δ‖ = 1`. -/
theorem norm_Δ_eq_one_of_iso [IsAlgClosed K] (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hp1 : ‖(p : K)‖ < 1) (a b : 𝒪) (G : FormalGroup 𝒪) [G.IsComm] (hu : ‖topc G p‖ = 1)
    (ha : ‖hasse G p‖ < 1) (θ : MvPowerSeries Unit 𝒪) (hθ : Hom G (formalGroup (shortO a b)) θ)
    (hθ1 : ‖((coeff (Finsupp.single () 1) θ : 𝒪) : K)‖ = 1) :
    ‖(((shortO a b).Δ : 𝒪) : K)‖ = 1 := by
  letI := charP_k (K := K) p hp1
  have hp2 : p < p ^ 2 := by nlinarith [hp.out.two_le]
  have hL := lowOrd_nmul_of_iso p hp1 G _ hu ha θ hθ hθ1
  -- the reduced formal group
  set k := 𝒪 ⧸ mI (K := K)
  have hFk : FGL.nmul (formalGroup (shortO (red a) (red b))) p =
      PowerSeries.map (red (K := K)) (FGL.nmul (formalGroup (shortO a b)) p) := by
    rw [← red_short, ← formalGroup_map, FGL.nmul_map]; rfl
  by_contra hΔ
  have hΔ1 : ‖(((shortO a b).Δ : 𝒪) : K)‖ < 1 := lt_of_le_of_ne ((shortO a b).Δ).2 hΔ
  have hΔk : (shortO (red (K := K) a) (red b)).Δ = 0 := by
    rw [← red_short, WeierstrassCurve.map_Δ]; exact red_eq_zero.2 hΔ1
  have hΔk' : -16 * (4 * red (K := K) a ^ 3 + 27 * red b ^ 2) = 0 := by
    rw [← hΔk]; simp [shortO, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]; ring
  have hnz : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → q ∣ n → q < 5) → (n : k) ≠ 0 := by
    intro n hn hq h
    rw [CharP.cast_eq_zero_iff k p] at h
    have := hq p hp.out h
    omega
  have h2 : (2 : k) ≠ 0 := by
    have := hnz 2 (by norm_num) (fun q hq hd => by
      have := Nat.le_of_dvd (by norm_num) hd; omega)
    exact_mod_cast this
  have h3 : (3 : k) ≠ 0 := by
    have := hnz 3 (by norm_num) (fun q hq hd => by
      have := Nat.le_of_dvd (by norm_num) hd; omega)
    exact_mod_cast this
  by_cases ha0 : red (K := K) a = 0
  · -- cusp
    have hb0 : red (K := K) b = 0 := by
      rw [ha0] at hΔk'
      have : (16 * 27 : k) * red (K := K) b ^ 2 = 0 := by linear_combination -hΔk'
      have h1627 : (16 * 27 : k) ≠ 0 := by
        have : (16 * 27 : k) = 2 ^ 4 * 3 ^ 3 := by ring
        rw [this]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 this).resolve_left h1627)
    rw [ha0, hb0, nmul_cusp, ← map_natCast (C (σ := Unit) (R := k)), CharP.cast_eq_zero, map_zero,
      zero_mul] at hFk
    have := hL.2
    rw [← hFk, map_zero] at this
    exact this rfl
  · -- node
    have hc4ne : (shortO (red (K := K) a) (red b)).c₄ ≠ 0 := by
      rw [c4_short]
      have h48 : (48 : k) ≠ 0 := by
        have : (48 : k) = 2 ^ 4 * 3 := by ring
        rw [this]; exact mul_ne_zero (pow_ne_zero _ h2) h3
      exact mul_ne_zero (neg_ne_zero.2 h48) ha0
    -- lift `c₄` and `c₆`
    have hc4r : red ((shortO a b).c₄) = (shortO (red (K := K) a) (red b)).c₄ := by
      rw [← red_short, WeierstrassCurve.map_c₄]
    have hc6r : red ((shortO a b).c₆) = (shortO (red (K := K) a) (red b)).c₆ := by
      rw [← red_short, WeierstrassCurve.map_c₆]
    obtain ⟨u, hu2⟩ := exists_sqrt_lift (shortO a b).c₄ (shortO a b).c₆
      (red_ne_zero.1 (by rw [hc4r]; exact hc4ne))
    rw [hc4r, hc6r] at hu2
    obtain ⟨hH, hune⟩ := aH_node p hp5 hc4ne hΔk hu2
    have hpc : PowerSeries.coeff p (PowerSeries.map (red (K := K))
        (FGL.nmul (formalGroup (shortO a b)) p)) = red u ^ (p - 1) := by
      rw [← hFk, ← hH]; rfl
    have := hL.1 p hp2
    rw [hpc] at this
    exact pow_ne_zero _ hune this

end VeluLubin
