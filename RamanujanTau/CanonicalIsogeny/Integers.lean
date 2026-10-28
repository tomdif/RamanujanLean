/-
# The integer ring `{x | ‖x‖ ≤ 1}` of a complete ultrametric field

The ring `𝒪 = integers K` with the subspace topology satisfies all the hypotheses of the Lubin layer
(complete, Hausdorff, linearly topologized domain), the inclusion `𝒪 → K` is continuous, injective,
of norm `≤ 1`, and `‖x‖ < 1 ⇒ x` is topologically nilpotent. Hence `exists_dual_isogeny_lie` applies
verbatim to formal groups over `𝒪`.
-/
import RamanujanTau.CanonicalIsogeny.Subgroup

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CanonicalIsogeny
open MvPowerSeries Finset

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- the closed unit ball as a subring. -/
def integers : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, norm_mul] at *; exact mul_le_one₀ hx (norm_nonneg _) hy
  one_mem' := by simp
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at *
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  zero_mem' := by simp
  neg_mem' {x} hx := by simpa using hx

variable {K}

lemma mem_integers {x : K} : x ∈ integers K ↔ ‖x‖ ≤ 1 := Iff.rfl

/-- the ideal `{x | ‖x‖ < ε}` of `𝒪`. -/
def ballIdeal {ε : ℝ} (hε : 0 < ε) : Ideal (integers K) where
  carrier := {x | ‖(x : K)‖ < ε}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, Subring.coe_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
  zero_mem' := by
    show ‖((0 : integers K) : K)‖ < ε
    simpa using hε
  smul_mem' c {x} hx := by
    simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, norm_mul] at *
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) c.2) hx

lemma norm_coe (x : integers K) : ‖x‖ = ‖(x : K)‖ := rfl

instance : IsLinearTopology (integers K) (integers K) := by
  rw [isLinearTopology_iff_hasBasis_ideal]
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨I, hI, hIt⟩ => Filter.mem_of_superset hI hIt⟩⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht
  have hb : ((ballIdeal (K := K) hε : Ideal (integers K)) : Set (integers K)) = Metric.ball 0 ε := by
    ext x; simp [ballIdeal, dist_eq_norm]
  exact ⟨ballIdeal (K := K) hε, by rw [hb]; exact Metric.ball_mem_nhds _ hε, by rw [hb]; exact hball⟩

lemma isClosed_integers : IsClosed (integers K : Set K) := by
  have : (integers K : Set K) = Metric.closedBall 0 1 := by ext x; simp [mem_integers]
  rw [this]; exact Metric.isClosed_closedBall

instance [CompleteSpace K] : CompleteSpace (integers K) :=
  haveI := isClosed_integers (K := K); IsClosed.completeSpace_coe

/-- the inclusion `𝒪 → K`. -/
abbrev incl : integers K →+* K := (integers K).subtype

lemma continuous_incl : Continuous (incl (K := K)) := continuous_subtype_val
lemma incl_injective : Function.Injective (incl (K := K)) := Subtype.val_injective
lemma norm_incl_le (x : integers K) : ‖incl x‖ ≤ 1 := x.2

lemma isTopologicallyNilpotent_of_norm_lt_one {x : integers K} (hx : ‖incl x‖ < 1) :
    IsTopologicallyNilpotent x := by
  have h := tendsto_pow_atTop_nhds_zero_of_norm_lt_one (R := integers K) (x := x) hx
  exact h

example : IsUniformAddGroup (integers K) := inferInstance
example : IsTopologicalRing (integers K) := inferInstance
example : T2Space (integers K) := inferInstance
example : IsDomain (integers K) := inferInstance

variable [CompleteSpace K]

/-- **Step 2 of I2 over the integer ring** `𝒪 = {x | ‖x‖ ≤ 1}` of a complete ultrametric field `K`.
For a commutative formal group `F` over `𝒪` of height `≤ 2` (`‖[p]_{p²}‖ = 1`) with
`‖p‖^p < ‖a‖^{p+1}` (`a = [p]_p`) and a Weierstrass factorization `[p](T)/T = ∏ (T − rᵢ) · U` with
roots `rᵢ ∈ 𝒪` (`‖U₀‖ = 1`, `‖U_k‖ ≤ 1`), there are a formal group `G` and isogenies
`π : F → G`, `π̌ : G → F` with `π̌ ∘ π = [p]` and `‖Lie π̌‖ = ‖a‖`. -/
theorem exists_dual_isogeny_lie_integers (F : FormalGroup (integers K)) [F.IsComm]
    (p : ℕ) [Fact p.Prime]
    (hu : ‖coeff (Finsupp.single () (p ^ 2)) (FGL.nmul F p)‖ = 1)
    (hε : 0 < ‖(p : K)‖)
    (hbreak : ‖(p : K)‖ ^ p < ‖coeff (Finsupp.single () p) (FGL.nmul F p)‖ ^ (p + 1))
    {κ : Type*} [Fintype κ] [DecidableEq κ] (r : κ → integers K)
    (hcard : Fintype.card κ = p ^ 2 - 1)
    (U : PowerSeries K) (hU0 : ‖PowerSeries.constantCoeff U‖ = 1) (hU : ∀ k, ‖PowerSeries.coeff k U‖ ≤ 1)
    (hW : ((∏ i, (Polynomial.X - Polynomial.C ((r i : K))) : Polynomial K) : PowerSeries K) * U =
      PowerSeries.mk fun k => ((coeff (Finsupp.single () (k + 1)) (FGL.nmul F p) : integers K) : K)) :
    ∃ (G : FormalGroup (integers K)) (π πd : MvPowerSeries Unit (integers K)), IsHom F G π ∧
      IsHom G F πd ∧ subst (fun _ : Unit => π) πd = FGL.nmul F p ∧
      ‖coeff (Finsupp.single () 1) πd‖ = ‖coeff (Finsupp.single () p) (FGL.nmul F p)‖ := by
  classical
  exact exists_dual_isogeny_lie incl continuous_incl incl_injective norm_incl_le
    (fun x hx => isTopologicallyNilpotent_of_norm_lt_one hx) p hu hε hbreak r hcard U hU0 hU hW

end CanonicalIsogeny
