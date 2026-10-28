/-
# Step 2 of I2 with the Vélu kernel of the canonical subgroup, and the link from integral descent

For a short curve `W : y² = x³ + ax + b` over `𝒪` (`K` complete, algebraically closed, ultrametric,
`p ≥ 5`, `0 < ‖p‖`, `‖Δ‖ = 1`, `0 < v(a_W) < p/(p+1)`):

**`exists_step2_with_velu`**: there is a finite subgroup `S ⊆ F_W[p]` of order `p` (the canonical
subgroup) such that, with `G = F_W/S` (Lubin) and `π = pis S`:
1. Step 2: `π̌ : G → F_W` with `π̌ ∘ π = [p]` and `‖Lie π̌‖ = ‖a_W‖`;
2. there is Vélu kernel data `κ` over `K` with `κ.G = Pt(S) ⊆ E(K)` (`Points.lean`);
3. for **every** Vélu kernel `κ` of `W_K`: if `μ φ_κ = θ ∘ π` over `K` for some `θ ∈ 𝒪⟦T⟧`
   (`μ = Lie π`), then `VeluLubinLink G` (`Main.link_of_descent`).
-/
import RamanujanTau.VeluLubin.Main
import RamanujanTau.VeluLubin.Points

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluLubin
open MvPowerSeries EllipticFormal EllipticI2 CanonicalIsogeny QuotientHasse WeierstrassSupply

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => integers K
local notation "ι" => Subring.subtype (integers K)

/-- `0 < ‖p‖ < 1` forces characteristic `0`. -/
theorem charZero_of_norm (p : ℕ) [hp : Fact p.Prime] (hε : 0 < ‖(p : K)‖) (hp1 : ‖(p : K)‖ < 1) :
    CharZero K := by
  refine charZero_of_inj_zero fun n hn0 => ?_
  by_contra hn
  obtain ⟨e, c, hc, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.one_lt.ne'
  have hp0 : (p : K) ≠ 0 := norm_pos_iff.1 hε
  push_cast at hn0
  rcases mul_eq_zero.1 hn0 with h1 | h1
  · exact pow_ne_zero _ hp0 h1
  · have := norm_nat_eq_one (K := K) p hp1 c hc
    rw [h1, norm_zero] at this
    exact zero_ne_one this

variable [CompleteSpace K]

open MvPowerSeries in
/-- **the canonical subgroup** (order `p`, inside `F[p]`) with Step 2 of I2, over an algebraically
closed complete ultrametric field (the explicit-`S` version of
`WeierstrassSupply.exists_dual_isogeny_lie_integers_algClosed`). -/
theorem canonical_data [IsAlgClosed K] (F : FormalGroup 𝒪) [F.IsComm] (p : ℕ) [hp : Fact p.Prime]
    (hu : ‖coeff (Finsupp.single () (p ^ 2)) (FGL.nmul F p)‖ = 1)
    (ha : ‖coeff (Finsupp.single () p) (FGL.nmul F p)‖ < 1)
    (hε : 0 < ‖(p : K)‖)
    (hbreak : ‖(p : K)‖ ^ p < ‖coeff (Finsupp.single () p) (FGL.nmul F p)‖ ^ (p + 1)) :
    ∃ S : Lubin.FinSub F, S.H.card = p ∧
      (∀ h ∈ S.H, Lubin.pt (fun _ : Unit => h) (FGL.nmul F p) = 0) ∧
      ∃ πd : MvPowerSeries Unit 𝒪, IsHom F (Lubin.quot S) (Lubin.pis S) ∧
        IsHom (Lubin.quot S) F πd ∧ subst (fun _ : Unit => Lubin.pis S) πd = FGL.nmul F p ∧
        ‖coeff (Finsupp.single () 1) πd‖ = ‖coeff (Finsupp.single () p) (FGL.nmul F p)‖ := by
  classical
  have hp2 := (Fact.out : p.Prime).two_le
  set a := coeff (Finsupp.single () p) (FGL.nmul F p)
  set N := p ^ 2 - 1 with hN
  have hp1 : ‖(p : K)‖ < 1 := by
    have h1 : ‖(a : K)‖ ^ (p + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) a.2
    have h2 : ‖(p : K)‖ ^ p < 1 := lt_of_lt_of_le hbreak h1
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h2
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
  obtain ⟨ρ, hρ0, hρ1, hcount, S, hSH, hpS, πd, h1, h2, h3, h4⟩ :=
    canonical_isogeny_lie incl continuous_incl incl_injective norm_incl_le
      (fun x hx => isTopologicallyNilpotent_of_norm_lt_one hx) p hu hε hbreak r hcard
      (PowerSeries.map incl U) hU0 hUb hW
  -- `|S| = p`: the roots are nonzero and the small ones are distinct
  have hr0 : ∀ i, r i ≠ 0 := by
    intro i hi
    have h := congrArg (PowerSeries.coeff 0) hW
    rw [PowerSeries.coeff_mk, zero_add, FGL.coeff_one_nmul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, Polynomial.constantCoeff_coe,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod] at h
    have hz : ∏ j, Polynomial.eval 0 (Polynomial.X - Polynomial.C ((r j : K))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [hz, zero_mul] at h
    have hpK : (((p : 𝒪) : K)) = (p : K) := by simp
    exact (norm_pos_iff.1 hε) (hpK ▸ h.symm)
  have hinjr := injOn_roots (F := F) incl continuous_incl incl_injective norm_incl_le
    (fun x hx => isTopologicallyNilpotent_of_norm_lt_one hx) p (norm_pos_iff.1 hε) r
    (PowerSeries.map incl U) hU0 hUb hW
  have hcardS : S.H.card = p := by
    rw [hSH, Finset.card_insert_of_notMem, Finset.card_image_of_injOn, hcount]
    · omega
    · intro i hi j hj hij
      exact hinjr (show ‖incl (r i)‖ < 1 from (Finset.mem_filter.mp hi).2.trans hρ1)
        (show ‖incl (r j)‖ < 1 from (Finset.mem_filter.mp hj).2.trans hρ1) hij
    · intro h0
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h0
      exact hr0 i hi
  exact ⟨S, hcardS, hpS, πd, h1, h2, h3, h4⟩

variable [IsAlgClosed K] [CharZero K] [DecidableEq K]

/-- **Step 2 of I2 for short curves, the Vélu kernel of the canonical subgroup, and the Vélu–Lubin
link from integral descent.** -/
theorem exists_step2_with_velu (a b : 𝒪) (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hε : 0 < ‖(p : K)‖) (hΔ : ‖(((shortO a b).Δ : 𝒪) : K)‖ = 1)
    (ha : ‖hasse (formalGroup (shortO a b)) p‖ < 1)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse (formalGroup (shortO a b)) p‖ ^ (p + 1)) :
    ∃ (S : Lubin.FinSub (formalGroup (shortO a b))) (πd : MvPowerSeries Unit 𝒪),
      IsHom (formalGroup (shortO a b)) (Lubin.quot S) (Lubin.pis S) ∧
      IsHom (Lubin.quot S) (formalGroup (shortO a b)) πd ∧
      subst (fun _ : Unit => Lubin.pis S) πd = FGL.nmul (formalGroup (shortO a b)) p ∧
      ‖coeff (Finsupp.single () 1) πd‖ = ‖hasse (formalGroup (shortO a b)) p‖ ∧
      S.H.card = p ∧
      (∀ h ∈ S.H, nm a b h p = 0) ∧
      ((coeff (Finsupp.single () 1) (Lubin.pis S) : 𝒪) : K) ≠ 0 ∧
      (∃ κ : Velu.Kernel (a : K) (b : K),
        (κ.G : Set (Velu.short (a : K) (b : K)).Point) = Pt a b '' (S.H : Set 𝒪)) ∧
      ∀ κ : Velu.Kernel (a : K) (b : K),
        (∃ θ : MvPowerSeries Unit 𝒪,
          sb (MvPowerSeries.map ι (Lubin.pis S)) (MvPowerSeries.map ι θ) =
            C ((coeff (Finsupp.single () 1) (Lubin.pis S) : 𝒪) : K) * phi κ) →
        Nonempty (VeluLubinLink (Lubin.quot S)) := by
  have hp1 : ‖(p : K)‖ < 1 :=
    EllipticI2.norm_p_lt_one (by have := hp.out.two_le; omega) (norm_nonneg _) ha.le hbreak
  have hu := HeightEll.topc_norm_eq_one (shortO a b) p hp5 hp1 hΔ ha
  obtain ⟨S, hcard, hpS, πd, h1, h2, h3, h4⟩ :=
    canonical_data (formalGroup (shortO a b)) p hu ha hε hbreak
  -- `μ = Lie π ≠ 0`, since `Lie π̌ · Lie π = p`
  have hμ0 : ((coeff (Finsupp.single () 1) (Lubin.pis S) : 𝒪) : K) ≠ 0 := by
    intro h
    have hl := congrArg (coeff (Finsupp.single () 1)) h3
    rw [lin_sb h2.1 h1.1, FGL.coeff_one_nmul] at hl
    have hl' := congrArg (fun x : 𝒪 => (x : K)) hl
    simp only [Subring.coe_mul, h, mul_zero] at hl'
    exact (norm_pos_iff.1 hε) (by exact_mod_cast hl'.symm)
  obtain ⟨huG, haG⟩ := quot_height (formalGroup (shortO a b)) p hu ha hp1 S hcard
  refine ⟨S, πd, h1, h2, h3, h4, hcard, hpS, hμ0,
    exists_kernel_of_finSub a b hp.out hp5 S hpS, ?_⟩
  intro κ ⟨θ, hθ⟩
  exact link_of_descent p hp5 hp1 a b κ (Lubin.quot S) huG haG (Lubin.pis S) ⟨h1.1, h1.2⟩ hμ0 θ hθ

end VeluLubin
