/-
# Height ≥ 2: `[p] = g(T^p)`, `g` a homomorphism from the Frobenius twist; `a = 0 ⇒ [p] ∈ R⟦T^{p²}⟧`

In characteristic `p` (`[CharP R p]`):
* `[p](T) = g(T^p)` with `g = Σ c_{pk} T^k`;
* `g` is a homomorphism `F^{(p)} → F` (with `F^{(p)} = F.map frobenius`), via
  `F(X,Y)^p = F^{(p)}(X^p, Y^p)` and injectivity of `expand`;
* `g'(0) = a :=` coefficient of `T^p` in `[p]`. If `a = 0` then `g' = 0`, so `[p]` only has monomials
  `T^{p²k}`.
Mixed characteristic (`p_a_dvd`): over any commutative ring, the coefficient of `T^m` in `[p](T)` lies in
the ideal `(p, a)` whenever `p² ∤ m`.
-/
import RamanujanTau.FormalGroupLayer.Endo

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FGL
open MvPowerSeries

variable {R : Type*} [CommRing R]

/-- the unit argument: in characteristic `p`, a series with vanishing derivative has no monomial `T^k`,
`p ∤ k`. -/
lemma coeff_eq_zero_of_pd (p : ℕ) [hp : Fact p.Prime] (hpR : (p : R) = 0) (f : MvPowerSeries Unit R)
    (hf : pd () f = 0) (k : ℕ) (hk : ¬ p ∣ k) : coeff (Finsupp.single () k) f = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (dvd_zero p) hk
    · omega⟩
  have h : coeff (Finsupp.single () (j + 1)) f * ((j : R) + 1) = 0 := by
    have := congrArg (coeff (Finsupp.single () j)) hf
    rw [coeff_pd, ← Finsupp.single_add, Finsupp.single_eq_same] at this
    simpa using this
  have hcop : Nat.Coprime (j + 1) p :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hk))
  obtain ⟨a, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.out.one_lt
  have hunit : ((j + 1 : ℕ) : R) * (a : R) = 1 := by
    have := Nat.div_add_mod ((j + 1) * a) p
    rw [ha.2] at this
    have h' : (((j + 1) * a : ℕ) : R) = 1 := by
      rw [← this]; push_cast; rw [hpR]; ring
    exact_mod_cast h'
  have : coeff (Finsupp.single () (j + 1)) f * (((j + 1 : ℕ) : R) * a) = 0 := by
    rw [← mul_assoc]; push_cast; rw [h, zero_mul]
  rwa [hunit, mul_one] at this

section CharP
variable (p : ℕ) [hp : Fact p.Prime] [CharP R p] (F : FormalGroup R) [F.IsComm]

local notation "Fs" => (F.toPowerSeries : MvPowerSeries (Fin 2) R)

lemma hp0 : p ≠ 0 := hp.out.ne_zero

lemma hpR : (p : R) = 0 := CharP.cast_eq_zero R p

/-- `g = Σ c_{pk} T^k`. -/
noncomputable def gV : MvPowerSeries Unit R := fun e => coeff (p • e) (nmul F p)

lemma nmul_eq_expand : nmul F p = expand p (hp0 p) (gV p F) := by
  refine MvPowerSeries.ext fun m => ?_
  by_cases hm : p ∣ m ()
  · obtain ⟨k, hk⟩ := hm
    have : m = p • Finsupp.single () k := Finsupp.ext fun u => by cases u; simp [hk]
    rw [this, coeff_expand_smul]; rfl
  · rw [coeff_expand_of_not_dvd p (hp0 p) _ hm]
    have : m = Finsupp.single () (m ()) := Finsupp.ext fun u => by cases u; simp
    rw [this]; exact coeff_nmul_eq_zero F p (hpR p) _ hm

lemma cc_gV : constantCoeff (gV p F) = 0 := by
  have h := congrArg constantCoeff (nmul_eq_expand p F)
  rwa [constantCoeff_expand, cc_nmul, eq_comm] at h

/-- the Frobenius twist `F^{(p)}`. -/
noncomputable abbrev Fp : FormalGroup R := F.map (frobenius R p)

lemma expand_eq_subst {β : Type*} (u : MvPowerSeries β R) :
    expand p (hp0 p) u = subst (fun i => (X i : MvPowerSeries β R) ^ p) u := by
  rw [expand, substAlgHom_apply]

lemma expand_inj {β : Type*} {u v : MvPowerSeries β R} (h : expand p (hp0 p) u = expand p (hp0 p) v) :
    u = v := by
  ext m; rw [← coeff_expand_smul p (hp0 p) u, h, coeff_expand_smul]

lemma ev_X0X1 (G : FormalGroup R) :
    ev G (X 0 : MvPowerSeries (Fin 2) R) (X 1) = G.toPowerSeries := by
  rw [ev]
  have : (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 2) R) = X := by funext s; fin_cases s <;> rfl
  rw [this, subst_self]; rfl

lemma ccX {β : Type*} (i : β) : constantCoeff (X i : MvPowerSeries β R) = 0 := by simp

lemma ccXp {β : Type*} (i : β) : constantCoeff ((X i : MvPowerSeries β R) ^ p) = 0 := by
  rw [map_pow, ccX, zero_pow (hp0 p)]

/-- `[p](a) = g(a^p)`. -/
lemma nm_p {β : Type*} [Finite β] {a : MvPowerSeries β R} (ha : constantCoeff a = 0) :
    nm F p a = subst (fun _ : Unit => a ^ p) (gV p F) := by
  rw [nm, nmul_eq_expand, expand_eq_subst, ss _ _ (fun _ => ccXp p ()) (h1 ha)]
  congr 1; funext s
  rw [subst_pow (hs (h1 ha)), sX _ (h1 ha)]

/-- **`g` is a homomorphism `F^{(p)} → F`**. -/
theorem gV_hom :
    subst (fun _ : Unit => ev (Fp p F) (X 0 : MvPowerSeries (Fin 2) R) (X 1)) (gV p F) =
      ev F (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) (gV p F))
        (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) (gV p F)) := by
  haveI : ExpChar R p := ExpChar.prime hp.out
  have X0 := ccX (R := R) (0 : Fin 2)
  have X1 := ccX (R := R) (1 : Fin 2)
  have hE : ∀ i, constantCoeff ((fun i => (X i : MvPowerSeries (Fin 2) R) ^ p) i) = 0 := fun i => ccXp p i
  have hendo := nm_ev F p X0 X1
  rw [nm_p p F (cc_ev F X0 X1), nm_p p F X0, nm_p p F X1, ev_X0X1] at hendo
  -- `F(X,Y)^p = expand (F^{(p)})`
  have hFp : Fs ^ p = expand p (hp0 p) (Fp p F).toPowerSeries := by
    rw [← map_frobenius_expand p (hp0 p), map_expand]; rfl
  rw [hFp] at hendo
  apply expand_inj p
  rw [expand_eq_subst, ss _ _ (h1 (cc_ev _ X0 X1)) hE, expand_eq_subst]
  rw [subst_ev F _ _ _ (cc0 _ (h1 X0) (cc_gV p F)) (cc0 _ (h1 X1) (cc_gV p F)) hE,
    ss _ _ (h1 X0) hE, ss _ _ (h1 X1) hE]
  have e : (fun _ : Unit => subst (fun i => (X i : MvPowerSeries (Fin 2) R) ^ p)
      (ev (Fp p F) (X 0 : MvPowerSeries (Fin 2) R) (X 1))) =
      fun _ => expand p (hp0 p) (Fp p F).toPowerSeries := by
    funext s; rw [ev_X0X1, expand_eq_subst]
  rw [e, sX _ hE, sX _ hE]
  exact hendo

/-- the coefficient `a` of `T^p` in `[p](T)`. -/
noncomputable def aH : R := coeff (Finsupp.single () p) (nmul F p)

lemma coeff_one_gV : coeff (Finsupp.single () 1) (gV p F) = aH p F := by
  show coeff (p • Finsupp.single () 1) (nmul F p) = _
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]; rfl

/-- **height ≥ 2 in characteristic `p`**: if `a = 0` then `[p](T)` has no monomial `T^m` with `p² ∤ m`. -/
theorem coeff_nmul_eq_zero_of_aH (ha : aH p F = 0) (m : ℕ) (hm : ¬ p ^ 2 ∣ m) :
    coeff (Finsupp.single () m) (nmul F p) = 0 := by
  have hG := hom_invariant (Fp p F) F (gV p F) (cc_gV p F) (gV_hom p F)
  rw [coeff_one_gV, ha, map_zero, mul_zero] at hG
  have hg' : pd () (gV p F) = 0 := (isUnit_Ψ_T (Fp p F)).mul_right_eq_zero.mp
    (by rw [mul_comm]; exact hG)
  by_cases hpm : p ∣ m
  · obtain ⟨k, rfl⟩ := hpm
    have hk : ¬ p ∣ k := fun ⟨j, hj⟩ => hm ⟨j, by rw [hj]; ring⟩
    rw [nmul_eq_expand, show Finsupp.single () (p * k) = p • Finsupp.single () k by simp,
      coeff_expand_smul]
    exact coeff_eq_zero_of_pd p (hpR p) _ hg' k hk
  · exact coeff_nmul_eq_zero F p (hpR p) m hpm

end CharP

/-- **mixed characteristic, height ≥ 2 shape**: over any commutative ring, the coefficient of `T^m` in
`[p](T)` lies in the ideal `(p, a)` whenever `p² ∤ m`, where `a` is the coefficient of `T^p`. -/
theorem mem_ideal_coeff_nmul (p : ℕ) [hp : Fact p.Prime] (F : FormalGroup R) [F.IsComm] (m : ℕ)
    (hm : ¬ p ^ 2 ∣ m) :
    coeff (Finsupp.single () m) (nmul F p) ∈
      Ideal.span {(p : R), coeff (Finsupp.single () p) (nmul F p)} := by
  set I := Ideal.span {(p : R), coeff (Finsupp.single () p) (nmul F p)}
  by_cases hI : I = ⊤
  · rw [hI]; trivial
  set π := Ideal.Quotient.mk I
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hpS : ((p : R ⧸ I)) = 0 := by
    rw [← map_natCast π, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span (by simp)
  haveI : CharP (R ⧸ I) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr hpS
  haveI : (F.map π).IsComm := ⟨by
    have := congrArg (MvPowerSeries.map π) (FormalGroup.IsComm.comm (F := F))
    rw [map_subst (hs (cc_vec2 (by simp) (by simp)))] at this
    simp only [FormalGroup.map_toPowerSeries]
    convert this using 2
    funext s; fin_cases s <;> simp⟩
  have ha : aH p (F.map π) = 0 := by
    rw [aH, nmul_map, coeff_map, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have h := coeff_nmul_eq_zero_of_aH p (F.map π) ha m hm
  rwa [nmul_map, coeff_map, Ideal.Quotient.eq_zero_iff_mem] at h

end FGL
