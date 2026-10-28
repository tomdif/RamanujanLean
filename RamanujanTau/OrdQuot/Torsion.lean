/-
# The `p`-torsion of a height-one formal group over `𝒪` (ordinary case)

`K` complete, algebraically closed, ultrametric. For a commutative formal group `F` over `𝒪`
with `‖a_F‖ = 1` (`a_F = coeff_p [p]`, height one) and `0 < ‖p‖ < 1`:

* `tors_unit`: for `‖n‖ = 1` the only `n`-torsion point of the disc is `0`.
* `ord_torsion`: the `p`-torsion `T` of the disc has `p` elements and `∏_{c ∈ T∖0} ‖c‖ = ‖p‖`.
-/
import RamanujanTau.AllQuotients.Final

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OrdQuot
open MvPowerSeries CanonicalIsogeny WeierstrassSupply Lubin QuotientHasse

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [DecidableEq K]

local notation "𝒪" => CanonicalIsogeny.integers K

/-- **no `n`-torsion in the disc for `‖n‖ = 1`**. -/
theorem tors_unit (F : FormalGroup ↥(CanonicalIsogeny.integers K)) [F.IsComm] (n : ℕ)
    (hn : ‖(n : K)‖ = 1) {z : ↥(CanonicalIsogeny.integers K)} (hz : ‖(z : K)‖ < 1)
    (h : pt (fun _ : Unit => z) (FGL.nmul F n) = 0) : z = 0 := by
  classical
  set U : PowerSeries K := PowerSeries.mk fun k => incl (coeff (Finsupp.single () (k + 1)) (FGL.nmul F n))
  have hU0 : ‖PowerSeries.constantCoeff U‖ = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, zero_add,
      FGL.coeff_one_nmul]
    simpa using hn
  have hU : ∀ k, ‖PowerSeries.coeff k U‖ ≤ 1 := fun k => by
    rw [PowerSeries.coeff_mk]; exact (coeff (Finsupp.single () (k + 1)) (FGL.nmul F n)).2
  have hW : ((∏ i : Fin 0, (Polynomial.X - Polynomial.C (incl ((Fin.elim0 i : 𝒪)))) :
      Polynomial K) : PowerSeries K) * U = U := by simp
  rcases (root_iff (F := F) incl continuous_incl incl_injective norm_incl_le n
    (fun i : Fin 0 => (Fin.elim0 i : 𝒪)) U hU0 hU hW
    (isTopologicallyNilpotent_of_norm_lt_one hz) hz).1 h with h0 | ⟨i, -⟩
  · exact h0
  · exact Fin.elim0 i

/-- **the `p`-torsion of the disc, height one**: `p` points, `∏_{c ≠ 0} ‖c‖ = ‖p‖`. -/
theorem ord_torsion [IsAlgClosed K] (F : FormalGroup ↥(CanonicalIsogeny.integers K)) [F.IsComm]
    (p : ℕ) [hp : Fact p.Prime] (ha : ‖hasse F p‖ = 1) (hε : 0 < ‖(p : K)‖)
    (hp1 : ‖(p : K)‖ < 1) :
    ∃ T : Finset ↥(CanonicalIsogeny.integers K),
      (∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ pt (fun _ : Unit => z) (FGL.nmul F p) = 0) ∧
      T.card = p ∧ ∏ c ∈ T.erase 0, ‖(c : K)‖ = ‖(p : K)‖ := by
  classical
  have hp2 := hp.out.two_le
  set N := p - 1 with hN
  set g : PowerSeries 𝒪 := PowerSeries.mk fun k => coeff (Finsupp.single () (k + 1)) (FGL.nmul F p)
    with hg
  have hp0 : (p : 𝒪) ≠ 0 := by
    intro h
    have := congrArg (fun x : 𝒪 => (x : K)) h
    simp only [Subring.coe_natCast, ZeroMemClass.coe_zero] at this
    rw [this, norm_zero] at hε; exact lt_irrefl _ hε
  have hpn : ‖((p : 𝒪) : K)‖ = ‖(p : K)‖ := by simp
  have hlo : ∀ k < N, ‖((PowerSeries.coeff k g : 𝒪) : K)‖ ≤ ‖(p : K)‖ := by
    intro k hk
    rw [hg, PowerSeries.coeff_mk]
    have hnd : ¬ p ∣ k + 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    obtain ⟨s, hs⟩ := FGL.p_dvd_coeff_nmul F p (k + 1) hnd
    rw [hs, Subring.coe_mul, norm_mul]
    refine (mul_le_of_le_one_right (norm_nonneg _) s.2).trans (le_of_eq ?_)
    simp
  have hNc : ‖((PowerSeries.coeff N g : 𝒪) : K)‖ = 1 := by
    rw [hg, PowerSeries.coeff_mk, show N + 1 = p by omega]; exact ha
  obtain ⟨P, U, hPm, hPd, hU, hgPU⟩ := exists_prep g N (p : 𝒪) hp0 (by rw [hpn]; exact hp1)
    (fun k hk => by rw [hpn]; exact hlo k hk) hNc
  obtain ⟨l, hl, hlen, hsplit⟩ := exists_split P hPm
  set n := l.length
  set r : Fin n → 𝒪 := fun i => ⟨l[i.1], hl _ (List.getElem_mem _)⟩
  set UK := PowerSeries.map incl U
  have hU0 : ‖PowerSeries.constantCoeff UK‖ = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact norm_eq_one_of_isUnit (PowerSeries.isUnit_iff_constantCoeff.mp hU)
  have hUk : ∀ k, ‖PowerSeries.coeff k UK‖ ≤ 1 := by
    intro k; rw [PowerSeries.coeff_map]; exact (PowerSeries.coeff k U).2
  set h : PowerSeries K := PowerSeries.mk fun k => incl (coeff (Finsupp.single () (k + 1)) (FGL.nmul F p))
  have hW : ((∏ i, (Polynomial.X - Polynomial.C (incl (r i))) : Polynomial K) : PowerSeries K) * UK
      = h := by
    have hprod : (∏ i : Fin n, (Polynomial.X - Polynomial.C (incl (r i))) : Polynomial K) =
        P.map incl := by
      rw [hsplit]
      exact Fin.prod_univ_fun_getElem l (fun a => Polynomial.X - Polynomial.C a)
    rw [hprod, Polynomial.polynomial_map_coe, ← map_mul, ← hgPU]
    ext k
    rw [PowerSeries.coeff_map, hg, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  have hnN : N = Fintype.card (Fin n) := by rw [Fintype.card_fin, hlen, hPd]
  -- all roots have norm `< 1`: the term `N` dominates at a radius `ρ` with `‖p‖ < ρ^N < 1`
  have hN0 : N ≠ 0 := by omega
  set bb : ℝ := (‖(p : K)‖ + 1) / 2 with hbb
  have hb0 : 0 < bb := by rw [hbb]; linarith
  have hb1 : bb < 1 := by rw [hbb]; linarith
  have hbp : ‖(p : K)‖ < bb := by rw [hbb]; linarith
  set ρ := bb ^ ((N : ℝ)⁻¹) with hρ
  have hρN : ρ ^ N = bb := Real.rpow_inv_natCast_pow hb0.le hN0
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hb0 _
  have hρ1 : ρ < 1 := Real.rpow_lt_one hb0.le hb1 (by positivity)
  have hcN : ‖PowerSeries.coeff N h‖ = 1 := by
    have := hNc; rw [hg, PowerSeries.coeff_mk] at this
    rw [PowerSeries.coeff_mk]; exact this
  have hdom : ∀ k, k ≠ N → ‖PowerSeries.coeff k h‖ * ρ ^ k < ‖PowerSeries.coeff N h‖ * ρ ^ N := by
    intro k hk
    rw [hcN, one_mul, hρN]
    rcases lt_or_gt_of_ne hk with hkN | hkN
    · have h1 : ‖PowerSeries.coeff k h‖ ≤ ‖(p : K)‖ := by
        rw [PowerSeries.coeff_mk]
        have := hlo k hkN
        rw [hg, PowerSeries.coeff_mk] at this
        exact this
      calc ‖PowerSeries.coeff k h‖ * ρ ^ k ≤ ‖(p : K)‖ * 1 :=
            mul_le_mul h1 (pow_le_one₀ hρ0.le hρ1.le) (by positivity) (norm_nonneg _)
        _ < bb := by rw [mul_one]; exact hbp
    · have h1 : ‖PowerSeries.coeff k h‖ ≤ 1 := by
        rw [PowerSeries.coeff_mk]; exact (coeff (Finsupp.single () (k + 1)) (FGL.nmul F p)).2
      calc ‖PowerSeries.coeff k h‖ * ρ ^ k ≤ 1 * ρ ^ k :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ < ρ ^ N := by rw [one_mul]; exact pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 hkN
        _ = bb := hρN
  obtain ⟨hc, -⟩ := root_count (fun i => incl (r i)) UK hU0 hUk hW hρ0 hρ1 N (hnN ▸ le_rfl) hdom
  rw [hnN, ← Finset.card_univ, Finset.card_filter_eq_iff] at hc
  have hlt : ∀ i, ‖((r i : 𝒪) : K)‖ < 1 := fun i => lt_trans (hc i (Finset.mem_univ i)) hρ1
  -- the product of the roots
  have h0 : PowerSeries.coeff 0 h =
      (∏ i, (Polynomial.X - Polynomial.C (incl (r i))) : Polynomial K).coeff 0 *
        PowerSeries.constantCoeff UK := by
    rw [← hW, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
  have hprodn : ∏ i, ‖((r i : 𝒪) : K)‖ = ‖(p : K)‖ := by
    show ∏ i, ‖incl (r i)‖ = ‖(p : K)‖
    have e := congrArg norm h0
    rw [norm_mul, hU0, mul_one, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod,
      norm_prod] at e
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub, norm_neg] at e
    rw [← e, PowerSeries.coeff_mk, zero_add, FGL.coeff_one_nmul]
    simp
  have hne : ∀ i, r i ≠ 0 := by
    intro i hi
    have : ∏ j, ‖((r j : 𝒪) : K)‖ = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; simp)
    rw [hprodn] at this; linarith
  have hpK : (p : K) ≠ 0 := by intro h0; rw [h0, norm_zero] at hε; exact lt_irrefl _ hε
  have hinj : Function.Injective r := fun i j hij =>
    injOn_roots (F := F) incl continuous_incl incl_injective norm_incl_le
      (fun x hx => isTopologicallyNilpotent_of_norm_lt_one hx) p hpK r UK hU0 hUk hW
      (hlt i) (hlt j) hij
  have root := fun {z : 𝒪} (hz : ‖(z : K)‖ < 1) =>
    root_iff (F := F) incl continuous_incl incl_injective norm_incl_le p r UK hU0 hUk hW
      (isTopologicallyNilpotent_of_norm_lt_one hz) hz
  have h0nm : (0 : 𝒪) ∉ Finset.univ.image r := by
    intro h; obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h; exact hne i hi
  refine ⟨insert 0 (Finset.univ.image r), fun z => ?_, ?_, ?_⟩
  · constructor
    · intro hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact ⟨by simp, (root (by simp)).2 (Or.inl rfl)⟩
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact ⟨hlt i, (root (hlt i)).2 (Or.inr ⟨i, rfl⟩)⟩
    · rintro ⟨h1, h2⟩
      rcases (root h1).1 h2 with rfl | ⟨i, rfl⟩
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  · rw [Finset.card_insert_of_notMem h0nm, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin, hlen, hPd]
    omega
  · rw [Finset.erase_insert h0nm, Finset.prod_image (fun i _ j _ hij => hinj hij)]
    exact hprodn

end OrdQuot
