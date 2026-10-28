/-
# Supplying the Weierstrass factorization for `exists_dual_isogeny_lie_integers`

Over an algebraically closed complete ultrametric field `K`, the hypotheses `κ`, `r`, `hcard`, `U`, `hU0`,
`hU`, `hW` of `CanonicalIsogeny.exists_dual_isogeny_lie_integers` are discharged:
* `Prep.lean` factors `[p](T)/T = P·U` over `𝒪 = integers K` (`P` monic of degree `p² − 1`);
* `P` splits in `K` and its roots are integral (ultrametric root bound).
The only extra hypothesis is `ha : ‖coeff_p [p]‖ < 1` (height exactly `2`); without it `[p](T)/T` has
Weierstrass degree `p − 1`, so the factorization `hW` with `p² − 1` roots cannot exist.
-/
import RamanujanTau.WeierstrassSupply.Prep
import RamanujanTau.FormalGroupLayer.HeightTwo

set_option autoImplicit false

namespace WeierstrassSupply
open CanonicalIsogeny Polynomial

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => integers K

/-- ultrametric root bound: a root of a monic polynomial with integral coefficients is integral. -/
lemma norm_root_le_one {Q : K[X]} (hQ : Q.Monic) (hc : ∀ i, ‖Q.coeff i‖ ≤ 1) {x : K}
    (hx : Q.IsRoot x) : ‖x‖ ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  set n := Q.natDegree
  have h0 := hx.eq_zero
  rw [eval_eq_sum_range, Finset.sum_range_succ, hQ.coeff_natDegree, one_mul] at h0
  have hS : ‖∑ i ∈ Finset.range n, Q.coeff i * x ^ i‖ < ‖x ^ n‖ := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn, Finset.sum_range_zero, norm_zero, pow_zero, norm_one]; exact one_pos
    · have hle : ‖∑ i ∈ Finset.range n, Q.coeff i * x ^ i‖ ≤ ‖x‖ ^ (n - 1) := by
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
        rw [norm_mul, norm_pow]
        calc ‖Q.coeff i‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (n - 1) :=
              mul_le_mul (hc i) (pow_le_pow_right₀ hlt.le (by
                have := Finset.mem_range.mp hi; omega)) (by positivity) zero_le_one
          _ = ‖x‖ ^ (n - 1) := one_mul _
      refine hle.trans_lt ?_
      rw [norm_pow]; exact pow_lt_pow_right₀ hlt (by omega)
  have : ∑ i ∈ Finset.range n, Q.coeff i * x ^ i = -x ^ n := eq_neg_of_add_eq_zero_left h0
  rw [this, norm_neg] at hS
  exact lt_irrefl _ hS

/-- a monic `P ∈ 𝒪[X]` of degree `N` splits over algebraically closed `K` into integral roots. -/
theorem exists_split [IsAlgClosed K] (P : Polynomial 𝒪) (hP : P.Monic) :
    ∃ l : List K, (∀ x ∈ l, ‖x‖ ≤ 1) ∧ l.length = P.natDegree ∧
      P.map incl = (l.map fun a => X - C a).prod := by
  set Q := P.map incl
  have hQ : Q.Monic := hP.map incl
  have hdeg : Q.natDegree = P.natDegree := hP.natDegree_map incl
  refine ⟨Q.roots.toList, fun x hx => ?_, ?_, ?_⟩
  · rw [Multiset.mem_toList] at hx
    refine norm_root_le_one hQ (fun i => ?_) (isRoot_of_mem_roots hx)
    rw [coeff_map]; exact (P.coeff i).2
  · rw [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree, hdeg]
  · conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQ
      IsAlgClosed.card_roots_eq_natDegree]
    conv_lhs => rw [← Multiset.coe_toList Q.roots]
    rw [Multiset.map_coe, Multiset.prod_coe]

open MvPowerSeries in
/-- **The canonical isogeny and its dual, with the Weierstrass hypotheses discharged** over an
algebraically closed complete ultrametric field. -/
theorem exists_dual_isogeny_lie_integers_algClosed [CompleteSpace K] [IsAlgClosed K]
    (F : FormalGroup 𝒪) [F.IsComm] (p : ℕ) [Fact p.Prime]
    (hu : ‖coeff (Finsupp.single () (p ^ 2)) (FGL.nmul F p)‖ = 1)
    (ha : ‖coeff (Finsupp.single () p) (FGL.nmul F p)‖ < 1)
    (hε : 0 < ‖(p : K)‖)
    (hbreak : ‖(p : K)‖ ^ p < ‖coeff (Finsupp.single () p) (FGL.nmul F p)‖ ^ (p + 1)) :
    ∃ (G : FormalGroup 𝒪) (π πd : MvPowerSeries Unit 𝒪), IsHom F G π ∧
      IsHom G F πd ∧ subst (fun _ : Unit => π) πd = FGL.nmul F p ∧
      ‖coeff (Finsupp.single () 1) πd‖ = ‖coeff (Finsupp.single () p) (FGL.nmul F p)‖ := by
  classical
  have hp2 := (Fact.out : p.Prime).two_le
  set a := coeff (Finsupp.single () p) (FGL.nmul F p)
  set N := p ^ 2 - 1 with hN
  -- `‖p‖ < 1`
  have hp1 : ‖(p : K)‖ < 1 := by
    have h1 : ‖(a : K)‖ ^ (p + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) a.2
    have h2 : ‖(p : K)‖ ^ p < 1 := lt_of_lt_of_le hbreak h1
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h2
  -- the uniformizing element `π₀` of norm `max ‖p‖ ‖a‖`
  set π₀ : 𝒪 := if ‖(p : K)‖ ≤ ‖(a : K)‖ then a else (p : 𝒪) with hπ₀
  have hπn : ‖(π₀ : K)‖ = max ‖(p : K)‖ ‖(a : K)‖ := by
    rw [hπ₀]; split_ifs with h
    · rw [max_eq_right h]
    · rw [max_eq_left (le_of_lt (not_le.mp h))]; simp
  have hπ0 : π₀ ≠ 0 := by
    intro h; have := hπn; rw [h] at this; simp at this
    have : ‖(p : K)‖ ≤ 0 := by rw [this]; exact le_max_left _ _
    linarith
  have hπ1 : ‖(π₀ : K)‖ < 1 := by rw [hπn]; exact max_lt hp1 ha
  -- `[p](T)/T` over `𝒪`
  set g : PowerSeries 𝒪 := PowerSeries.mk fun k => coeff (Finsupp.single () (k + 1)) (FGL.nmul F p)
    with hg
  have hlow : ∀ k < N, ‖((PowerSeries.coeff k g : 𝒪) : K)‖ ≤ ‖(π₀ : K)‖ := by
    intro k hk
    rw [hg, PowerSeries.coeff_mk, hπn]
    have hnd : ¬ p ^ 2 ∣ k + 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    obtain ⟨s, t, hst⟩ := Ideal.mem_span_pair.mp (FGL.mem_ideal_coeff_nmul p F (k + 1) hnd)
    rw [← hst, Subring.coe_add, Subring.coe_mul, Subring.coe_mul]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) s.2).trans (le_of_eq_of_le ?_ (le_max_left _ _))
      simp
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) t.2).trans (le_max_right _ _)
  have hNc : ‖((PowerSeries.coeff N g : 𝒪) : K)‖ = 1 := by
    rw [hg, PowerSeries.coeff_mk, show N + 1 = p ^ 2 by
      have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega]
    exact hu
  obtain ⟨P, U, hPm, hPd, hU, hgPU⟩ := exists_prep g N π₀ hπ0 hπ1 hlow hNc
  obtain ⟨l, hl, hlen, hsplit⟩ := exists_split P hPm
  let r : Fin l.length → 𝒪 := fun i => ⟨l[i.1], hl _ (List.getElem_mem _)⟩
  have hcard : Fintype.card (Fin l.length) = p ^ 2 - 1 := by rw [Fintype.card_fin, hlen, hPd]
  have hU0 : ‖PowerSeries.constantCoeff (PowerSeries.map incl U)‖ = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact norm_eq_one_of_isUnit (PowerSeries.isUnit_iff_constantCoeff.mp hU)
  have hUb : ∀ k, ‖PowerSeries.coeff k (PowerSeries.map incl U)‖ ≤ 1 := fun k => by
    rw [PowerSeries.coeff_map]; exact (PowerSeries.coeff k U).2
  have hW : ((∏ i, (Polynomial.X - Polynomial.C ((r i : K))) : Polynomial K) : PowerSeries K) *
      PowerSeries.map incl U =
      PowerSeries.mk fun k => ((coeff (Finsupp.single () (k + 1)) (FGL.nmul F p) : 𝒪) : K) := by
    have hprod : (∏ i, (Polynomial.X - Polynomial.C ((r i : K))) : Polynomial K) = P.map incl := by
      rw [hsplit]
      exact Fin.prod_univ_fun_getElem l (fun a => Polynomial.X - Polynomial.C a)
    rw [hprod, Polynomial.polynomial_map_coe, ← map_mul, ← hgPU]
    ext k
    rw [PowerSeries.coeff_map, hg, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    rfl
  exact exists_dual_isogeny_lie_integers F p hu hε hbreak r hcard (PowerSeries.map incl U) hU0 hUb hW

end WeierstrassSupply
