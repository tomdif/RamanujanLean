/-
# The canonical subgroup as a `Lubin.FinSub`, and the Lie derivative of the dual isogeny

Setting: `O` a complete Hausdorff linearly topologized domain, `ι : O →+* K` into a complete ultrametric
field, continuous, injective, `‖ι x‖ ≤ 1`, and `‖ι x‖ < 1 ⇒ x` topologically nilpotent.

Given the hypotheses of `AtkinOBrien.Canonical.canonical_subgroup` with roots `ι ∘ r₀`:
* the roots of `[p]` at points of norm `< 1` are exactly `0` and the `r₀ i`, and the small `r₀ i` are
  pairwise distinct (`root_iff`, `injOn_roots` in `Simple.lean`);
* `H := {0} ∪ {r₀ i : ‖ι (r₀ i)‖ < ρ}` is a finite subgroup (`FinSub`): closed under `+_F` by the
  ultrametric bound and additivity of `[p]`, with inverses `[p−1] x`;
* Lubin's quotient `F → F/H` and its dual `F/H → F` (composite `[p]`) exist, and the dual has
  Lie derivative of norm `‖a‖` (`canonical_isogeny_lie`).
-/
import RamanujanTau.CanonicalIsogeny.Simple
import RamanujanTau.AtkinOBrien.Canonical

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CanonicalIsogeny
open MvPowerSeries MvPowerSeries.WithPiTopology Lubin Finset

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [IsTopologicalRing O]
  [IsLinearTopology O O] [CompleteSpace O] [T2Space O] [IsDomain O] [DecidableEq O]

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- `f` is a homomorphism of formal groups `F → G` (with zero constant term). -/
def IsHom (F G : FormalGroup O) (f : MvPowerSeries Unit O) : Prop :=
  constantCoeff f = 0 ∧
    subst (fun _ : Unit => FGL.ev F (X 0 : MvPowerSeries (Fin 2) O) (X 1)) f =
      FGL.ev G (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) O)) f)
        (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) O)) f)

variable {F : FormalGroup O} [F.IsComm]

/-- **Step 2 of I2**: the canonical subgroup is a finite subgroup, and the dual of the canonical
isogeny `F → F/H` has Lie derivative of norm `‖a‖`. -/
theorem canonical_isogeny_lie (ι : O →+* K) (hιc : Continuous ι) (hinj : Function.Injective ι)
    (hι : ∀ r, ‖ι r‖ ≤ 1) (htn : ∀ x, ‖ι x‖ < 1 → IsTopologicallyNilpotent x)
    (p : ℕ) [hp : Fact p.Prime]
    (hu : ‖ι (coeff (Finsupp.single () (p ^ 2)) (FGL.nmul F p))‖ = 1)
    (hε : 0 < ‖(p : K)‖)
    (hbreak : ‖(p : K)‖ ^ p < ‖ι (coeff (Finsupp.single () p) (FGL.nmul F p))‖ ^ (p + 1))
    {κ : Type*} [Fintype κ] [DecidableEq κ] (r₀ : κ → O)
    (hcard : Fintype.card κ = p ^ 2 - 1)
    (U : PowerSeries K) (hU0 : ‖PowerSeries.constantCoeff U‖ = 1) (hU : ∀ k, ‖PowerSeries.coeff k U‖ ≤ 1)
    (hW : ((∏ i, (Polynomial.X - Polynomial.C (ι (r₀ i))) : Polynomial K) : PowerSeries K) * U =
      PowerSeries.mk fun k => ι (coeff (Finsupp.single () (k + 1)) (FGL.nmul F p))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ #(univ.filter fun i => ‖ι (r₀ i)‖ < ρ) = p - 1 ∧
      ∃ S : FinSub F, S.H = insert 0 ((univ.filter fun i => ‖ι (r₀ i)‖ < ρ).image r₀) ∧
        (∀ h ∈ S.H, pt (fun _ : Unit => h) (FGL.nmul F p) = 0) ∧
        ∃ πd : MvPowerSeries Unit O, IsHom F (quot S) (pis S) ∧ IsHom (quot S) F πd ∧
          subst (fun _ : Unit => pis S) πd = FGL.nmul F p ∧
          ‖ι (coeff (Finsupp.single () 1) πd)‖ = ‖ι (coeff (Finsupp.single () p) (FGL.nmul F p))‖ := by
  classical
  have hp2 := hp.out.two_le
  set a := coeff (Finsupp.single () p) (FGL.nmul F p)
  obtain ⟨ρ, hρ0, hcount, hne, hprod⟩ := AtkinOBrien.Canonical.canonical_subgroup ι hι p F hu hε hbreak
    (fun i => ι (r₀ i)) hcard U hU0 hU hW
  set sm := univ.filter fun i => ‖ι (r₀ i)‖ < ρ with hsm
  -- `ρ < 1`
  have hρ1 : ρ < 1 := by
    by_contra hc; push Not at hc
    have : sm = univ := by
      ext i; simp only [hsm, mem_filter, mem_univ, true_and, iff_true]
      exact lt_of_le_of_ne (le_trans (hι _) hc) (hne i)
    rw [this, card_univ, hcard] at hcount
    have : p < p ^ 2 := by nlinarith
    omega
  set H := insert (0 : O) (sm.image r₀) with hH
  have hroot := fun {z : O} (hz1 : ‖ι z‖ < 1) =>
    root_iff (F := F) ι hιc hinj hι p r₀ U hU0 hU hW (htn z hz1) hz1
  -- membership
  have mem_H : ∀ z : O, z ∈ H ↔ ‖ι z‖ < ρ ∧ pt (fun _ : Unit => z) (FGL.nmul F p) = 0 := by
    intro z
    constructor
    · intro hz
      rcases mem_insert.mp hz with rfl | hz
      · refine ⟨by rw [map_zero, norm_zero]; exact hρ0, ?_⟩
        rw [pt_zero, FGL.cc_nmul]
      · obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
        have hi' : ‖ι (r₀ i)‖ < ρ := (mem_filter.mp hi).2
        exact ⟨hi', (hroot (hi'.trans hρ1)).mpr (Or.inr ⟨i, rfl⟩)⟩
    · rintro ⟨hz1, hz2⟩
      rcases (hroot (hz1.trans hρ1)).mp hz2 with rfl | ⟨i, rfl⟩
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hz1⟩))
  have tn_H : ∀ z ∈ H, IsTopologicallyNilpotent z := fun z hz =>
    htn z (((mem_H z).mp hz).1.trans hρ1)
  have add_H : ∀ x ∈ H, ∀ y ∈ H, padd F x y ∈ H := by
    intro x hx y hy
    obtain ⟨hx1, hx2⟩ := (mem_H x).mp hx
    obtain ⟨hy1, hy2⟩ := (mem_H y).mp hy
    refine (mem_H _).mpr ⟨lt_of_le_of_lt (norm_padd_le F ι hιc hι (tn_H x hx) (tn_H y hy))
      (max_lt hx1 hy1), ?_⟩
    rw [pt_nmul_padd p (tn_H x hx) (tn_H y hy), hx2, hy2, padd_zero tn0]
  have nmul_H : ∀ x ∈ H, ∀ n : ℕ, pt (fun _ : Unit => x) (FGL.nmul F n) ∈ H := by
    intro x hx n
    induction n with
    | zero => rw [show FGL.nmul F 0 = 0 from rfl, pt_zero_series (tn_H x hx)]; exact mem_insert_self _ _
    | succ n ih => rw [pt_nmul_succ (tn_H x hx)]; exact add_H x hx _ ih
  let S : FinSub F :=
    { H := H
      tn := tn_H
      zero_mem := mem_insert_self _ _
      add_mem := add_H
      neg_mem := fun x hx => ⟨_, nmul_H x hx (p - 1), by
        rw [← pt_nmul_succ (tn_H x hx), Nat.sub_add_cancel (by omega)]
        exact ((mem_H x).mp hx).2⟩ }
  have hpS : ∀ h ∈ S.H, pt (fun _ : Unit => h) (FGL.nmul F p) = 0 := fun h hh => ((mem_H h).mp hh).2
  -- the product over `H ∖ 0`
  have h0 : (0 : O) ∉ sm.image r₀ := by
    intro h0
    obtain ⟨i, hi, hi0⟩ := mem_image.mp h0
    have : ∏ j ∈ sm, ‖ι (r₀ j)‖ = 0 := prod_eq_zero hi (by rw [hi0, map_zero, norm_zero])
    rw [this, mul_zero] at hprod
    exact hε.ne' hprod.symm
  have hcan : ‖ι a‖ * ∏ h ∈ S.H.erase 0, ‖ι h‖ = ‖(p : K)‖ := by
    show ‖ι a‖ * ∏ h ∈ H.erase 0, ‖ι h‖ = _
    have hinjr := injOn_roots ι hιc hinj hι htn p (norm_pos_iff.mp hε) r₀ U hU0 hU hW
    rw [hH, erase_insert h0, prod_image fun i hi j hj hij =>
      hinjr (show ‖ι (r₀ i)‖ < 1 from (mem_filter.mp hi).2.trans hρ1)
        (show ‖ι (r₀ j)‖ < 1 from (mem_filter.mp hj).2.trans hρ1) hij]
    exact hprod
  obtain ⟨πd, hπd, hlie⟩ := lie_dual_lubin S ι hι p hpS (ι a) hcan (norm_pos_iff.mp hε)
  have hcc : constantCoeff πd = 0 := by
    have := congrArg constantCoeff hπd
    rwa [FGL.cc_subst _ (fun _ => cc_pis S), FGL.cc_nmul] at this
  exact ⟨ρ, hρ0, hρ1, hcount, S, rfl, hpS, πd, ⟨cc_pis S, pis_hom S⟩, ⟨hcc, dual_hom S p πd hπd⟩,
    hπd, hlie⟩

/-- **Step 2 of I2**, in the requested shape. -/
theorem exists_dual_isogeny_lie (ι : O →+* K) (hιc : Continuous ι) (hinj : Function.Injective ι)
    (hι : ∀ r, ‖ι r‖ ≤ 1) (htn : ∀ x, ‖ι x‖ < 1 → IsTopologicallyNilpotent x)
    (p : ℕ) [Fact p.Prime]
    (hu : ‖ι (coeff (Finsupp.single () (p ^ 2)) (FGL.nmul F p))‖ = 1)
    (hε : 0 < ‖(p : K)‖)
    (hbreak : ‖(p : K)‖ ^ p < ‖ι (coeff (Finsupp.single () p) (FGL.nmul F p))‖ ^ (p + 1))
    {κ : Type*} [Fintype κ] [DecidableEq κ] (r₀ : κ → O)
    (hcard : Fintype.card κ = p ^ 2 - 1)
    (U : PowerSeries K) (hU0 : ‖PowerSeries.constantCoeff U‖ = 1) (hU : ∀ k, ‖PowerSeries.coeff k U‖ ≤ 1)
    (hW : ((∏ i, (Polynomial.X - Polynomial.C (ι (r₀ i))) : Polynomial K) : PowerSeries K) * U =
      PowerSeries.mk fun k => ι (coeff (Finsupp.single () (k + 1)) (FGL.nmul F p))) :
    ∃ (G : FormalGroup O) (π πd : MvPowerSeries Unit O), IsHom F G π ∧ IsHom G F πd ∧
      subst (fun _ : Unit => π) πd = FGL.nmul F p ∧
      ‖ι (coeff (Finsupp.single () 1) πd)‖ = ‖ι (coeff (Finsupp.single () p) (FGL.nmul F p))‖ := by
  obtain ⟨-, -, -, -, S, -, -, πd, h1, h2, h3, h4⟩ :=
    canonical_isogeny_lie ι hιc hinj hι htn p hu hε hbreak r₀ hcard U hU0 hU hW
  exact ⟨quot S, pis S, πd, h1, h2, h3, h4⟩

end CanonicalIsogeny
