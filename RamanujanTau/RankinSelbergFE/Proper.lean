/-
# The Rankin–Selberg theorem proper for `Δ`

Let `R(s) = ∑ τ(n)² n^{−11−s}` (`EdgeNonvanishing.RS`, absolutely convergent for `Re s > 1`) and
`γ(s) = 2 π^{−s} Γ(s) Γ(s+11) (4π)^{−s−11}` (`RankinError.gam`). The completed function

    R*(s) = γ(s) ζ(2s) R(s)            (Re s > 1)

is the Mellin transform of `Φ(t) − ‖Δ‖²`, `Φ(t) = ∫_𝓕 |Δ|² y¹² Θ_z(t) dμ`
(`RankinError.rsFE`, Mathlib's `WeakFEPair` with `k = 1`, `ε = 1`, `f₀ = g₀ = ‖Δ‖²`). We package:

* `RStar_one_sub`: `R*(1−s) = R*(s)` for every `s ∈ ℂ`;
* `RStar_eq`: `R*(s) = Λ₀(s) − ‖Δ‖²/s − ‖Δ‖²/(1−s)` with `Λ₀` entire (`differentiable_RStar₀`);
* `differentiableAt_RStar`: `R*` is holomorphic on `ℂ ∖ {0, 1}`;
* `RStar_residue_one`, `RStar_residue_zero`: simple poles with residues `‖Δ‖²` and `−‖Δ‖²`;
* `RStar_eq_of_one_lt`: `R*(s) = γ(s) ζ(2s) R(s)` on all of `Re s > 1` (the repo's `rsUnfold`
  had `Re s > 2`; extended by the identity theorem);
* `Rcont := R* · γ⁻¹ / ζ(2·)`: `meromorphic_Rcont` (meromorphic on `ℂ`), `Rcont_eq`
  (`= R` on `Re s > 1`), `differentiableAt_Rcont` (holomorphic off `{0, 1/2, 1}` and the zeros of
  `ζ(2s)`), and `Rcont_residue_one`: `Res_{s=1} R = (3/π)(4π)¹²‖Δ‖²/11!` (Zagier's constant).
-/
import RamanujanTau.RankinError.RSUnfoldProof
import RamanujanTau.EdgeNonvanishing.RS
import Mathlib.Analysis.Meromorphic.Basic

set_option autoImplicit false

namespace RamanujanTau.RankinSelbergFE

open Complex Filter Topology Set
open RamanujanTau.RankinError
open RamanujanTau.EisensteinReal (petNormSq)
open RamanujanTau.EdgeNonvanishing (RS rsc rs_summable)

/-- The completed Rankin–Selberg function `R*(s)`. -/
noncomputable def RStar (s : ℂ) : ℂ := rsFE.Λ s

/-- The entire part `Λ₀` of `R*`. -/
noncomputable def RStar₀ (s : ℂ) : ℂ := rsFE.Λ₀ s

theorem differentiable_RStar₀ : Differentiable ℂ RStar₀ := rsFE.differentiable_Λ₀

theorem RStar₀_one_sub (s : ℂ) : RStar₀ (1 - s) = RStar₀ s := by
  have := rsFE.functional_equation₀ s
  rw [rsFE_symm_Λ₀] at this
  simpa [rsFE, RStar₀] using this

/-- `R*(s) = Λ₀(s) − ‖Δ‖²/s − ‖Δ‖²/(1−s)`. -/
theorem RStar_eq (s : ℂ) :
    RStar s = RStar₀ s - (petNormSq : ℂ) / s - (petNormSq : ℂ) / (1 - s) := by
  change rsFE.Λ₀ s - (1 / s) • (petNormSq : ℂ) - ((1:ℂ) / (((1:ℝ):ℂ) - s)) • (petNormSq : ℂ) = _
  simp only [smul_eq_mul, Complex.ofReal_one, RStar₀]
  ring

/-- **Functional equation.** `R*(1−s) = R*(s)` for all `s ∈ ℂ`. -/
theorem RStar_one_sub (s : ℂ) : RStar (1 - s) = RStar s := by
  rw [RStar_eq, RStar_eq, RStar₀_one_sub, sub_sub_cancel]
  ring

/-- `R*` is holomorphic on `ℂ ∖ {0, 1}`. -/
theorem differentiableAt_RStar {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : DifferentiableAt ℂ RStar s :=
  rsFE.differentiableAt_Λ (Or.inl h0) (Or.inl (by simpa [rsFE] using h1))

/-- **Simple pole at `s = 1` with residue `‖Δ‖²`.** -/
theorem RStar_residue_one :
    Tendsto (fun s : ℂ => (s - 1) * RStar s) (𝓝[≠] 1) (𝓝 (petNormSq : ℂ)) := by
  have h := rsFE.Λ_residue_k
  have hk : ((rsFE.k : ℝ) : ℂ) = 1 := by simp [rsFE]
  have hε : rsFE.ε • rsFE.g₀ = (petNormSq : ℂ) := by simp [rsFE]
  rw [hk, hε] at h
  simpa only [smul_eq_mul] using h

/-- **Simple pole at `s = 0` with residue `−‖Δ‖²`.** -/
theorem RStar_residue_zero :
    Tendsto (fun s : ℂ => s * RStar s) (𝓝[≠] 0) (𝓝 (-(petNormSq : ℂ))) := by
  have h := rsFE.Λ_residue_zero
  simp only [smul_eq_mul] at h
  exact h

/-- Both poles are genuine: `‖Δ‖² > 0`. -/
theorem petNormSq_ne_zero : (petNormSq : ℂ) ≠ 0 := by
  exact_mod_cast petNormSq_pos.ne'

/-! ### The Dirichlet series side on `Re s > 1` -/

lemma LSeries_aTau_eq_RS : LSeries (fun n => (aTau n : ℂ)) = RS := rfl

lemma abscissa_RS_le_one :
    LSeries.abscissaOfAbsConv (fun n => (aTau n : ℂ)) ≤ ((1 : ℝ) : EReal) :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    rs_summable (by simpa using hy)

lemma differentiableOn_RS : DifferentiableOn ℂ RS {s : ℂ | 1 < s.re} :=
  (LSeries_differentiableOn _).mono fun z (hz : 1 < z.re) =>
    lt_of_le_of_lt abscissa_RS_le_one (EReal.coe_lt_coe_iff.2 hz)

lemma differentiableAt_gam {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ gam z := by
  have hG1 : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z fun m hm => by
    have := congrArg Complex.re hm; simp at this; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hG2 : DifferentiableAt ℂ (fun w => Complex.Gamma (w + 11)) z := by
    refine (Complex.differentiableAt_Gamma (z + 11) fun m hm => ?_).comp z
      (differentiableAt_id.add_const 11)
    have := congrArg Complex.re hm; simp at this; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hp1 : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ (-w)) z :=
    differentiableAt_id.neg.const_cpow (Or.inl pi_ne_zero')
  have hp2 : DifferentiableAt ℂ (fun w : ℂ => ((4 * Real.pi : ℝ) : ℂ) ^ (-w - 11)) z :=
    (differentiableAt_id.neg.sub_const 11).const_cpow (Or.inl fourpi_ne_zero)
  unfold gam
  exact (((((differentiableAt_const _).mul hp1).mul hG1).mul hG2).mul hp2)

/-- **The unfolding identity on the full half-plane `Re s > 1`:**
`R*(s) = 2 π^{−s} Γ(s) Γ(s+11) (4π)^{−s−11} ζ(2s) ∑ τ(n)² n^{−11−s}`. -/
theorem RStar_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    RStar s = gam s * riemannZeta (2 * s) * RS s := by
  set U : Set ℂ := {s : ℂ | 1 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hfd : DifferentiableOn ℂ RStar U := fun z (hz : 1 < z.re) =>
    (differentiableAt_RStar (fun h => by rw [h] at hz; norm_num at hz)
      (fun h => by rw [h] at hz; norm_num at hz)).differentiableWithinAt
  have hgd : DifferentiableOn ℂ (fun s => gam s * riemannZeta (2 * s) * RS s) U := by
    refine DifferentiableOn.mul (fun z (hz : 1 < z.re) => ?_) differentiableOn_RS
    refine DifferentiableAt.differentiableWithinAt ?_
    have hζ : DifferentiableAt ℂ (fun w => riemannZeta (2 * w)) z := by
      refine (differentiableAt_riemannZeta ?_).comp z (differentiableAt_id.const_mul 2)
      intro h; have := congrArg Complex.re h; simp at this; linarith
    exact (differentiableAt_gam (by linarith)).mul hζ
  have h3 : (3 : ℂ) ∈ U := by simp [hU]
  have hev : ∀ᶠ z in 𝓝 (3 : ℂ), RStar z = gam z * riemannZeta (2 * z) * RS z := by
    have hV : {z : ℂ | 2 < z.re} ∈ 𝓝 (3 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp; norm_num)
    filter_upwards [hV] with z (hz : 2 < z.re)
    have hm := (rsFE.hasMellin (s := z) (by simp [rsFE]; linarith)).2
    rw [RStar, ← hm]
    exact rsUnfold z hz
  have hfreq : ∃ᶠ z in 𝓝[≠] (3 : ℂ), RStar z = gam z * riemannZeta (2 * z) * RS z :=
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  exact (hfd.analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
    (hgd.analyticOnNhd hUo) (convex_halfSpace_re_gt 1).isPreconnected h3 hfreq hs

/-- The same identity with the gamma factor written out. -/
theorem RStar_eq_of_one_lt' {s : ℂ} (hs : 1 < s.re) :
    RStar s = 2 * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s * Complex.Gamma (s + 11) *
      ((4 * Real.pi : ℝ) : ℂ) ^ (-s - 11) * riemannZeta (2 * s) *
        ∑' n : ℕ, LSeries.term (fun n => ((((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 : ℝ) : ℂ)) s n :=
  RStar_eq_of_one_lt hs

/-! ### Meromorphic continuation of `R(s)` itself -/

/-- `ζ` is meromorphic on `ℂ`. -/
lemma meromorphicAt_riemannZeta (w : ℂ) : MeromorphicAt riemannZeta w := by
  by_cases hw : w = 1
  · subst hw
    have hA : MeromorphicAt (fun s : ℂ => (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) *
        (Gammaℝ s)⁻¹) 1 := by
      refine MeromorphicAt.mul (((differentiable_completedZeta₀.analyticAt 1).meromorphicAt.sub
        ((MeromorphicAt.const 1 1).div (MeromorphicAt.id 1))).sub
        ((MeromorphicAt.const 1 1).div ((MeromorphicAt.const 1 1).sub (MeromorphicAt.id 1))))
        (differentiable_Gammaℝ_inv.analyticAt 1).meromorphicAt
    refine hA.congr ?_
    have h0 : ∀ᶠ s in 𝓝[≠] (1 : ℂ), s ≠ 0 :=
      (eventually_ne_nhds one_ne_zero).filter_mono nhdsWithin_le_nhds
    filter_upwards [h0] with s hs
    rw [riemannZeta_def_of_ne_zero hs, completedRiemannZeta_eq, ← div_eq_mul_inv]
  · have hd : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun z hz =>
      (differentiableAt_riemannZeta hz).differentiableWithinAt
    exact (hd.analyticAt (isOpen_compl_singleton.mem_nhds hw)).meromorphicAt

lemma meromorphicAt_RStar (w : ℂ) : MeromorphicAt RStar w := by
  have h : RStar = fun s => RStar₀ s - (petNormSq : ℂ) / s - (petNormSq : ℂ) / (1 - s) :=
    funext RStar_eq
  rw [h]
  exact (((differentiable_RStar₀.analyticAt w).meromorphicAt.sub
    ((MeromorphicAt.const _ w).div (MeromorphicAt.id w))).sub
    ((MeromorphicAt.const _ w).div ((MeromorphicAt.const 1 w).sub (MeromorphicAt.id w))))

/-- **The continuation of `R(s) = ∑ τ(n)² n^{−11−s}`:** `R*(s) γ(s)⁻¹ / ζ(2s)`. -/
noncomputable def Rcont (s : ℂ) : ℂ := RStar s * invGam s / riemannZeta (2 * s)

/-- `Rcont` is meromorphic on all of `ℂ`. -/
theorem meromorphic_Rcont : MeromorphicOn Rcont univ := fun w _ => by
  have hζ : MeromorphicAt (fun s : ℂ => riemannZeta (2 * s)) w :=
    (meromorphicAt_riemannZeta (2 * w)).comp_analyticAt
      ((analyticAt_const.mul analyticAt_id))
  exact ((meromorphicAt_RStar w).mul (differentiable_invGam.analyticAt w).meromorphicAt).div hζ

/-- `Rcont = R` on `Re s > 1`. -/
theorem Rcont_eq {s : ℂ} (hs : 1 < s.re) : Rcont s = RS s := by
  have hζ : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hg := gam_mul_invGam (s := s) (by linarith)
  rw [Rcont, RStar_eq_of_one_lt hs]
  calc gam s * riemannZeta (2 * s) * RS s * invGam s / riemannZeta (2 * s)
      = (gam s * invGam s) * RS s * (riemannZeta (2 * s) / riemannZeta (2 * s)) := by ring
    _ = RS s := by rw [hg, div_self hζ]; ring

/-- `Rcont` is holomorphic off `{0, 1/2, 1}` and the zeros of `ζ(2s)`. -/
theorem differentiableAt_Rcont {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (h2 : 2 * s ≠ 1)
    (hζ : riemannZeta (2 * s) ≠ 0) : DifferentiableAt ℂ Rcont s :=
  ((differentiableAt_RStar h0 h1).mul (differentiable_invGam s)).div
    ((differentiableAt_riemannZeta h2).comp s (differentiableAt_id.const_mul 2)) hζ

lemma invGam_one : invGam 1 = (Real.pi : ℂ) * ((4 * Real.pi : ℝ) : ℂ) ^ 12 /
    (2 * (Nat.factorial 11 : ℂ)) := by
  have h12 : Complex.Gamma (1 + 11) = (Nat.factorial 11 : ℂ) := by
    rw [show (1 : ℂ) + 11 = ((11 : ℕ) : ℂ) + 1 by norm_num, Complex.Gamma_nat_eq_factorial]
  have e : ((4 * Real.pi : ℝ) : ℂ) ^ ((1 : ℂ) + 11) = ((4 * Real.pi : ℝ) : ℂ) ^ (12 : ℕ) := by
    rw [show (1 : ℂ) + 11 = ((12 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  unfold invGam
  rw [Complex.cpow_one, e, h12, Complex.Gamma_one]
  have : (Nat.factorial 11 : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos 11).ne'
  field_simp

/-- **Residue of `R` at `s = 1`: Zagier's constant `(3/π)(4π)¹²‖Δ‖²/11!`.** -/
theorem Rcont_residue_one :
    Tendsto (fun s : ℂ => (s - 1) * Rcont s) (𝓝[≠] 1) (𝓝 (rsc : ℂ)) := by
  have hcont : ContinuousAt (fun s : ℂ => invGam s / riemannZeta (2 * s)) 1 := by
    have hζ2 : riemannZeta (2 * 1) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
    refine ((differentiable_invGam 1).continuousAt).div ?_ hζ2
    exact ((differentiableAt_riemannZeta (by norm_num)).comp (1 : ℂ)
      (differentiableAt_id.const_mul 2)).continuousAt
  have h := RStar_residue_one.mul (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  have hval : (petNormSq : ℂ) * (invGam 1 / riemannZeta (2 * 1)) = (rsc : ℂ) := by
    rw [invGam_one, mul_one, riemannZeta_two, RamanujanTau.EdgeNonvanishing.rsc]
    have : (Nat.factorial 11 : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos 11).ne'
    have hpi : (Real.pi : ℂ) ≠ 0 := pi_ne_zero'
    push_cast
    field_simp
    ring
  rw [hval] at h
  refine h.congr fun s => ?_
  simp only [Rcont]
  ring

end RamanujanTau.RankinSelbergFE
