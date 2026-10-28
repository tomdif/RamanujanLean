/-
# Step 2 of I2 for elliptic curves

`W` is a good-reduction Weierstrass curve over `𝒪 = integers K` (`K` complete, algebraically closed,
ultrametric), `p ≥ 5`, `a = coeff_p [p]_{F_W}`, and `0 < v(a) < p/(p+1)`, i.e. `‖a‖ < 1` and
`‖p‖^p < ‖a‖^{p+1}`.

* `elliptic_step2`: the canonical quotient `π : F_W → G`, its dual `π̌` with `π̌ ∘ π = [p]`,
  and `‖Lie π̌‖ = ‖a‖`.
* `norm_eq_of_sub_mem_span_p`: if `x − y ∈ (p)` and `max ‖x‖ ‖y‖ > ‖p‖` then `‖x‖ = ‖y‖`.
* `norm_hasse_eq_norm_Ep_of_break`: in the break region, `‖a‖ = ‖E_{p−1}(W)‖`.
* `elliptic_step2_E`: the same as `elliptic_step2` with `‖a‖` replaced by `‖E_{p−1}(W)‖`
  (unconditional, via `HasseInv.coeff_nmul_sub_hasseA_mem'`).
-/
import RamanujanTau.WeierstrassSupply.Supply
import RamanujanTau.HeightEll.Reduce
import RamanujanTau.HasseInv.Unconditional

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EllipticI2
open MvPowerSeries EllipticFormal CanonicalIsogeny QuotientHasse

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => integers K

/-- the break condition forces `‖p‖ < 1` once `‖a‖ ≤ 1`. -/
lemma norm_p_lt_one {p : ℕ} (hp2 : 2 ≤ p) {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1)
    (hbreak : ‖(p : K)‖ ^ p < α ^ (p + 1)) : ‖(p : K)‖ < 1 := by
  have h2 : ‖(p : K)‖ ^ p < 1 := lt_of_lt_of_le hbreak (pow_le_one₀ hα0 hα)
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h2

/-- the break condition forces `‖p‖ < α`. -/
lemma norm_p_lt_of_break {p : ℕ} (hp2 : 2 ≤ p) {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1)
    (hbreak : ‖(p : K)‖ ^ p < α ^ (p + 1)) : ‖(p : K)‖ < α := by
  have hp1 := norm_p_lt_one hp2 hα0 hα hbreak
  by_contra h
  rw [not_lt] at h
  have : α ^ (p + 1) ≤ ‖(p : K)‖ ^ p :=
    calc α ^ (p + 1) ≤ ‖(p : K)‖ ^ (p + 1) := pow_le_pow_left₀ hα0 h _
      _ ≤ ‖(p : K)‖ ^ p := pow_le_pow_of_le_one (norm_nonneg _) hp1.le (by omega)
  linarith

/-- **Step 2 of I2 for elliptic curves.** -/
theorem elliptic_step2 [CompleteSpace K] [IsAlgClosed K] (W : WeierstrassCurve 𝒪) (p : ℕ)
    [Fact p.Prime] (hp5 : 5 ≤ p) (hε : 0 < ‖(p : K)‖) (hΔ : ‖((W.Δ : 𝒪) : K)‖ = 1)
    (ha : ‖hasse (formalGroup W) p‖ < 1)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse (formalGroup W) p‖ ^ (p + 1)) :
    ∃ (G : FormalGroup 𝒪) (π πd : MvPowerSeries Unit 𝒪), IsHom (formalGroup W) G π ∧
      IsHom G (formalGroup W) πd ∧ subst (fun _ : Unit => π) πd = FGL.nmul (formalGroup W) p ∧
      ‖coeff (Finsupp.single () 1) πd‖ = ‖hasse (formalGroup W) p‖ := by
  have hp1 : ‖(p : K)‖ < 1 :=
    norm_p_lt_one (by omega) (norm_nonneg _) ha.le hbreak
  have hu := HeightEll.topc_norm_eq_one W p hp5 hp1 hΔ ha
  exact WeierstrassSupply.exists_dual_isogeny_lie_integers_algClosed (formalGroup W) p hu ha hε hbreak

/-- ultrametric: elements congruent mod `p`, one of norm `> ‖p‖`, have equal norms. -/
theorem norm_eq_of_sub_mem_span_p (p : ℕ) {x y : 𝒪} (h : x - y ∈ Ideal.span {(p : 𝒪)})
    (hbig : ‖(p : K)‖ < max ‖(x : K)‖ ‖(y : K)‖) : ‖(x : K)‖ = ‖(y : K)‖ := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  have hd : ‖((x : K) - y)‖ ≤ ‖(p : K)‖ := by
    have : ((x : K) - y) = (c : K) * (p : K) := by
      have := congrArg (fun z : 𝒪 => (z : K)) hc
      simpa using this.symm
    rw [this, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) c.2
  have h1 : ‖(x : K)‖ ≤ max ‖(y : K)‖ ‖(x : K) - y‖ := by
    have := IsUltrametricDist.norm_add_le_max (y : K) ((x : K) - y)
    simpa using this
  have h2 : ‖(y : K)‖ ≤ max ‖(x : K)‖ ‖(x : K) - y‖ := by
    have := IsUltrametricDist.norm_add_le_max (x : K) (-((x : K) - y))
    rw [norm_neg] at this
    simpa using this
  rcases le_total ‖(x : K)‖ ‖(y : K)‖ with hxy | hxy
  · rw [max_eq_right hxy] at hbig
    refine le_antisymm hxy ?_
    rcases le_total ‖(x : K)‖ ‖(x : K) - y‖ with h3 | h3
    · rw [max_eq_right h3] at h2; linarith
    · rwa [max_eq_left h3] at h2
  · rw [max_eq_left hxy] at hbig
    refine le_antisymm ?_ hxy
    rcases le_total ‖(y : K)‖ ‖(x : K) - y‖ with h3 | h3
    · rw [max_eq_right h3] at h1; linarith
    · rwa [max_eq_left h3] at h1

variable (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] (integers K)]

/-- `E_{p−1}(W) = A(c₄, −c₆) ∈ 𝒪`, `A ∈ ℤ_[p][X₀, X₁]` the isobaric lift with `A(E₄, E₆) = E_{p−1}`. -/
noncomputable def Ep (hp5 : 5 ≤ p) (W : WeierstrassCurve 𝒪) : 𝒪 :=
  MvPolynomial.aeval ![W.c₄, -W.c₆] (ModP.hasseA p hp5)


/-- `a − E_{p−1}(W) ∈ (p)` (Deligne, unconditional). -/
lemma hasse_sub_Ep_mem (hp5 : 5 ≤ p)
    (W : WeierstrassCurve 𝒪) :
    hasse (formalGroup W) p - Ep p hp5 W ∈ Ideal.span {(p : 𝒪)} :=
  HasseInv.coeff_nmul_sub_hasseA_mem' p hp5 W

/-- **`‖a‖ = ‖E_{p−1}(W)‖` whenever one of them has norm `> ‖p‖`**. -/
theorem norm_hasse_eq_norm_Ep (hp5 : 5 ≤ p)
    (W : WeierstrassCurve 𝒪)
    (hbig : ‖(p : K)‖ < max ‖hasse (formalGroup W) p‖ ‖Ep p hp5 W‖) :
    ‖hasse (formalGroup W) p‖ = ‖Ep p hp5 W‖ :=
  norm_eq_of_sub_mem_span_p p (hasse_sub_Ep_mem p hp5 W) hbig

/-- in the break region `v(a) < p/(p+1)`, `‖a‖ = ‖E_{p−1}(W)‖`. -/
theorem norm_hasse_eq_norm_Ep_of_break (hp5 : 5 ≤ p)
    (W : WeierstrassCurve 𝒪)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse (formalGroup W) p‖ ^ (p + 1)) :
    ‖hasse (formalGroup W) p‖ = ‖Ep p hp5 W‖ := by
  have hp2 := (Fact.out : p.Prime).two_le
  refine norm_hasse_eq_norm_Ep p hp5 W ?_
  exact lt_of_lt_of_le (norm_p_lt_of_break hp2 (norm_nonneg _) (hasse (formalGroup W) p).2 hbreak)
    (le_max_left _ _)

/-- the same, with the break condition stated for `E_{p−1}(W)`. -/
theorem norm_hasse_eq_norm_Ep_of_break' (hp5 : 5 ≤ p)
    (W : WeierstrassCurve 𝒪)
    (hbreak : ‖(p : K)‖ ^ p < ‖Ep p hp5 W‖ ^ (p + 1)) :
    ‖hasse (formalGroup W) p‖ = ‖Ep p hp5 W‖ := by
  have hp2 := (Fact.out : p.Prime).two_le
  refine norm_hasse_eq_norm_Ep p hp5 W ?_
  exact lt_of_lt_of_le (norm_p_lt_of_break hp2 (norm_nonneg _) (Ep p hp5 W).2 hbreak)
    (le_max_right _ _)

/-- **Step 2 of I2 for elliptic curves, in terms of `E_{p−1}`**:
for `0 < v(E_{p−1}(W)) < p/(p+1)`, the canonical quotient exists with `‖Lie π̌‖ = ‖E_{p−1}(W)‖`. -/
theorem elliptic_step2_E [CompleteSpace K] [IsAlgClosed K] (hp5 : 5 ≤ p)
    (W : WeierstrassCurve 𝒪)
    (hε : 0 < ‖(p : K)‖) (hΔ : ‖((W.Δ : 𝒪) : K)‖ = 1)
    (hE : ‖Ep p hp5 W‖ < 1) (hbreak : ‖(p : K)‖ ^ p < ‖Ep p hp5 W‖ ^ (p + 1)) :
    ∃ (G : FormalGroup 𝒪) (π πd : MvPowerSeries Unit 𝒪), IsHom (formalGroup W) G π ∧
      IsHom G (formalGroup W) πd ∧ subst (fun _ : Unit => π) πd = FGL.nmul (formalGroup W) p ∧
      ‖coeff (Finsupp.single () 1) πd‖ = ‖Ep p hp5 W‖ := by
  have he := norm_hasse_eq_norm_Ep_of_break' p hp5 W hbreak
  rw [← he] at hE hbreak ⊢
  exact elliptic_step2 W p hp5 hε hΔ hE hbreak

end EllipticI2
