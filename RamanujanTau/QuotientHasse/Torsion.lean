/-
# The `p`-torsion of a height-two formal group over `𝒪 = integers K`: root norms

`K` complete, algebraically closed, ultrametric. For a commutative formal group `G` over `𝒪` with
`‖[p]_{p²}‖ = 1`, `‖a‖ < 1` (`a = [p]_p`, the Hasse coefficient) and `0 < ‖p‖ < 1`, every nonzero
`p`-torsion point `y` of the open unit disc satisfies (`torsion_classify`)
* if `‖p‖^p < ‖a‖^{p+1}` (break): `‖a‖‖y‖^{p−1} = ‖p‖` (canonical) or `‖y‖^{p²−p} = ‖a‖`;
* otherwise: `‖y‖^{p²−1} = ‖p‖`.
In the break case both kinds of points exist (`torsion_exists`).
In valuations: `v(y) = (1−v)/(p−1)` or `v/(p²−p)`, resp. `v(y) = 1/(p²−1)`.
-/
import RamanujanTau.QuotientHasse.Newton
import RamanujanTau.WeierstrassSupply.Supply

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QuotientHasse
open MvPowerSeries CanonicalIsogeny WeierstrassSupply Lubin

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => integers K

/-- the Hasse coefficient `a_G = coeff_p [p]_G`. -/
noncomputable abbrev hasse (G : FormalGroup 𝒪) (p : ℕ) : 𝒪 :=
  coeff (Finsupp.single () p) (FGL.nmul G p)

/-- the coefficient of `T^{p²}` in `[p]_G`. -/
noncomputable abbrev topc (G : FormalGroup 𝒪) (p : ℕ) : 𝒪 :=
  coeff (Finsupp.single () (p ^ 2)) (FGL.nmul G p)

lemma norm_lt_one_of_tn {x : 𝒪} (hx : IsTopologicallyNilpotent x) : ‖(x : K)‖ < 1 := by
  have h : Filter.Tendsto (fun n : ℕ => ‖x ^ n‖) Filter.atTop (nhds 0) := by
    have := (continuous_norm.tendsto (0 : 𝒪)).comp hx
    simpa [Function.comp_def] using this
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (h.eventually (gt_mem_nhds one_pos))
  have h1 : ‖((x ^ (n + 1) : 𝒪) : K)‖ < 1 := hn (n + 1) (by omega)
  rw [SubmonoidClass.coe_pow, norm_pow] at h1
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h1

lemma tn_iff {x : 𝒪} : IsTopologicallyNilpotent x ↔ ‖(x : K)‖ < 1 :=
  ⟨norm_lt_one_of_tn, isTopologicallyNilpotent_of_norm_lt_one⟩

/-- exponent bookkeeping. -/
lemma nat_aux (p : ℕ) (hp : 1 ≤ p) :
    p ^ 2 - 1 - (p - 1) = p ^ 2 - p ∧ p ^ 2 - p = p * (p - 1) ∧ p ^ 2 - 1 = (p + 1) * (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have e : (q + 1) ^ 2 = q * q + 2 * q + 1 := by ring
  have e2 : (q + 1) * q = q * q + q := by ring
  have e3 : (q + 1 + 1) * q = q * q + 2 * q := by ring
  simp only [Nat.add_sub_cancel, e]
  rw [e2, e3]
  omega

/-- the break condition in Newton-polygon form. -/
lemma break_iff (p : ℕ) (hp : 2 ≤ p) {ε α : ℝ} (hε : 0 ≤ ε) (hα : 0 ≤ α) :
    ε ^ p < α ^ (p + 1) ↔ ε ^ (p ^ 2 - 1 - (p - 1)) < α ^ (p ^ 2 - 1) := by
  obtain ⟨e1, e2, e3⟩ := nat_aux p (by omega)
  rw [e1, e2, e3, pow_mul, pow_mul]
  exact ⟨fun h => pow_lt_pow_left₀ h (by positivity) (by omega),
    fun h => lt_of_pow_lt_pow_left₀ (p - 1) (by positivity) h⟩

variable [CompleteSpace K]

/-- `[p](T)/T` has the Newton shape. -/
theorem shape_nmul (G : FormalGroup 𝒪) [G.IsComm] (p : ℕ) [hp : Fact p.Prime]
    (hu : ‖topc G p‖ = 1) :
    Shape (PowerSeries.mk fun k => ((coeff (Finsupp.single () (k + 1)) (FGL.nmul G p) : 𝒪) : K))
      (p - 1) (p ^ 2 - 1) ‖(p : K)‖ ‖((hasse G p : 𝒪) : K)‖ where
  c0 := by rw [PowerSeries.coeff_mk, zero_add, FGL.coeff_one_nmul]; simp
  lo := by
    intro k hk
    rw [PowerSeries.coeff_mk]
    have hp1 := hp.out.one_lt
    have hnd : ¬ p ∣ k + 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    obtain ⟨s, hs⟩ := FGL.p_dvd_coeff_nmul G p (k + 1) hnd
    rw [hs, Subring.coe_mul, norm_mul]
    refine (mul_le_of_le_one_right (norm_nonneg _) s.2).trans (le_of_eq ?_)
    simp
  cm := by rw [PowerSeries.coeff_mk, Nat.sub_add_cancel hp.out.one_lt.le]
  mid := by
    intro k hk1 hk2
    rw [PowerSeries.coeff_mk]
    have hp2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
    have hnd : ¬ p ^ 2 ∣ k + 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    obtain ⟨s, t, hst⟩ := Ideal.mem_span_pair.mp (FGL.mem_ideal_coeff_nmul p G (k + 1) hnd)
    rw [← hst, Subring.coe_add, Subring.coe_mul, Subring.coe_mul]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) s.2).trans
        (le_of_eq_of_le ?_ (le_max_left _ _))
      simp
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) t.2).trans (le_max_right _ _)
  cN := by
    rw [PowerSeries.coeff_mk, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.out.pos)]; exact hu
  le1 := fun k => by
    rw [PowerSeries.coeff_mk]; exact (coeff (Finsupp.single () (k + 1)) (FGL.nmul G p)).2

/-- the Weierstrass factorization `[p](T)/T = ∏ (T − rᵢ) · U` with split polynomial part. -/
theorem exists_factor [IsAlgClosed K] (G : FormalGroup 𝒪) [G.IsComm] (p : ℕ) [hp : Fact p.Prime]
    (hu : ‖topc G p‖ = 1) (ha : ‖hasse G p‖ < 1) (hε : 0 < ‖(p : K)‖) (hp1 : ‖(p : K)‖ < 1) :
    ∃ n : ℕ, n = p ^ 2 - 1 ∧ ∃ r : Fin n → 𝒪, ∃ U : PowerSeries K,
      ‖PowerSeries.constantCoeff U‖ = 1 ∧ (∀ k, ‖PowerSeries.coeff k U‖ ≤ 1) ∧
      ((∏ i, (Polynomial.X - Polynomial.C ((r i : K))) : Polynomial K) : PowerSeries K) * U =
        PowerSeries.mk fun k => ((coeff (Finsupp.single () (k + 1)) (FGL.nmul G p) : 𝒪) : K) := by
  classical
  have hp2 := hp.out.two_le
  set a := hasse G p
  set N := p ^ 2 - 1 with hN
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
  set g : PowerSeries 𝒪 := PowerSeries.mk fun k => coeff (Finsupp.single () (k + 1)) (FGL.nmul G p)
    with hg
  have hS := shape_nmul G p hu
  have hlow : ∀ k < N, ‖((PowerSeries.coeff k g : 𝒪) : K)‖ ≤ ‖(π₀ : K)‖ := by
    intro k hk
    rw [hπn]
    have e : ((PowerSeries.coeff k g : 𝒪) : K) = PowerSeries.coeff k
        (PowerSeries.mk fun k => ((coeff (Finsupp.single () (k + 1)) (FGL.nmul G p) : 𝒪) : K)) := by
      rw [hg, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    rw [e]
    rcases lt_trichotomy k (p - 1) with h1 | h1 | h1
    · exact (hS.lo k h1).trans (le_max_left _ _)
    · rw [h1, hS.cm]; exact le_max_right _ _
    · exact hS.mid k h1 hk
  have hNc : ‖((PowerSeries.coeff N g : 𝒪) : K)‖ = 1 := by
    rw [hg, PowerSeries.coeff_mk, show N + 1 = p ^ 2 by
      have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega]
    exact hu
  obtain ⟨P, U, hPm, hPd, hU, hgPU⟩ := exists_prep g N π₀ hπ0 hπ1 hlow hNc
  obtain ⟨l, hl, hlen, hsplit⟩ := exists_split P hPm
  refine ⟨l.length, by rw [hlen, hPd], fun i => ⟨l[i.1], hl _ (List.getElem_mem _)⟩,
    PowerSeries.map incl U, ?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact norm_eq_one_of_isUnit (PowerSeries.isUnit_iff_constantCoeff.mp hU)
  · intro k; rw [PowerSeries.coeff_map]; exact (PowerSeries.coeff k U).2
  · have hprod : (∏ i : Fin l.length, (Polynomial.X - Polynomial.C
        (((⟨l[i.1], hl _ (List.getElem_mem _)⟩ : 𝒪) : K))) : Polynomial K) = P.map incl := by
      rw [hsplit]
      exact Fin.prod_univ_fun_getElem l (fun a => Polynomial.X - Polynomial.C a)
    rw [hprod, Polynomial.polynomial_map_coe, ← map_mul, ← hgPU]
    ext k
    rw [PowerSeries.coeff_map, hg, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    rfl

/-- **classification of the nonzero `p`-torsion points** of the disc. -/
theorem torsion_classify [IsAlgClosed K] (G : FormalGroup 𝒪) [G.IsComm] (p : ℕ) [hp : Fact p.Prime]
    (hu : ‖topc G p‖ = 1) (ha : ‖hasse G p‖ < 1) (hε : 0 < ‖(p : K)‖) (hp1 : ‖(p : K)‖ < 1)
    {y : 𝒪} (hy0 : y ≠ 0) (hy1 : ‖(y : K)‖ < 1)
    (hy : pt (fun _ : Unit => y) (FGL.nmul G p) = 0) :
    (‖(p : K)‖ ^ p < ‖hasse G p‖ ^ (p + 1) →
      ‖hasse G p‖ * ‖(y : K)‖ ^ (p - 1) = ‖(p : K)‖ ∨ ‖(y : K)‖ ^ (p ^ 2 - p) = ‖hasse G p‖) ∧
    (¬ ‖(p : K)‖ ^ p < ‖hasse G p‖ ^ (p + 1) → ‖(y : K)‖ ^ (p ^ 2 - 1) = ‖(p : K)‖) := by
  classical
  have hp2 := hp.out.two_le
  obtain ⟨n, hn, r, U, hU0, hU, hW⟩ := exists_factor G p hu ha hε hp1
  have hS := shape_nmul G p hu
  rcases (root_iff (F := G) incl continuous_incl incl_injective norm_incl_le p r U hU0 hU hW
    (isTopologicallyNilpotent_of_norm_lt_one hy1) hy1).mp hy with h0 | ⟨i, rfl⟩
  · exact absurd h0 hy0
  have hpos : 0 < ‖((r i : 𝒪) : K)‖ := norm_pos_iff.mpr (by
    intro h; exact hy0 (Subtype.ext h))
  have hcard : p ^ 2 - 1 = Fintype.card (Fin n) := by rw [Fintype.card_fin, hn]
  have hm0 : 0 < p - 1 := by omega
  have hmN : p - 1 < p ^ 2 - 1 := by
    have : p < p ^ 2 := by nlinarith
    omega
  have cl := classify hS hm0 hmN hε hcard (fun i => ((r i : 𝒪) : K)) U hU0 hU hW i hpos hy1
  obtain ⟨e1, -, -⟩ := nat_aux p (by omega)
  have hα0 : 0 ≤ ‖hasse G p‖ := norm_nonneg _
  constructor
  · intro hb
    have := cl.1 ((break_iff p hp2 hε.le hα0).mp hb)
    rwa [e1] at this
  · intro hb
    refine cl.2 ?_
    obtain ⟨-, e2, e3⟩ := nat_aux p (by omega)
    rw [e1, e2, e3, pow_mul, pow_mul]
    exact pow_le_pow_left₀ (by positivity) (le_of_not_gt hb) _

/-- **existence** of canonical and non-canonical `p`-torsion points (break case). -/
theorem torsion_exists [IsAlgClosed K] (G : FormalGroup 𝒪) [G.IsComm] (p : ℕ) [hp : Fact p.Prime]
    (hu : ‖topc G p‖ = 1) (ha : ‖hasse G p‖ < 1) (hε : 0 < ‖(p : K)‖) (hp1 : ‖(p : K)‖ < 1)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse G p‖ ^ (p + 1)) :
    (∃ y : 𝒪, y ≠ 0 ∧ ‖(y : K)‖ < 1 ∧ pt (fun _ : Unit => y) (FGL.nmul G p) = 0 ∧
      ‖hasse G p‖ * ‖(y : K)‖ ^ (p - 1) = ‖(p : K)‖) ∧
    (∃ y : 𝒪, y ≠ 0 ∧ ‖(y : K)‖ < 1 ∧ pt (fun _ : Unit => y) (FGL.nmul G p) = 0 ∧
      ‖(y : K)‖ ^ (p ^ 2 - p) = ‖hasse G p‖) := by
  classical
  have hp2 := hp.out.two_le
  obtain ⟨n, hn, r, U, hU0, hU, hW⟩ := exists_factor G p hu ha hε hp1
  have hS := shape_nmul G p hu
  have hcard : p ^ 2 - 1 = Fintype.card (Fin n) := by rw [Fintype.card_fin, hn]
  have hm0 : 0 < p - 1 := by omega
  have hmN : p - 1 < p ^ 2 - 1 := by
    have : p < p ^ 2 := by nlinarith
    omega
  obtain ⟨e1, -, -⟩ := nat_aux p (by omega)
  have hb := (break_iff p hp2 hε.le (norm_nonneg _)).mp hbreak
  obtain ⟨⟨i, hi0, hi1, hi⟩, ⟨j, hj0, hj1, hj⟩⟩ :=
    exists_small_big hS hm0 hmN hε hp1 ha hcard (fun i => ((r i : 𝒪) : K)) U hU0 hU hW hb
  have root := fun (k : Fin n) (hk : ‖((r k : 𝒪) : K)‖ < 1) =>
    (root_iff (F := G) incl continuous_incl incl_injective norm_incl_le p r U hU0 hU hW
      (isTopologicallyNilpotent_of_norm_lt_one hk) hk).mpr (Or.inr ⟨k, rfl⟩)
  refine ⟨⟨r i, fun h => by rw [h] at hi0; simp at hi0, hi1, root i hi1, hi⟩,
    ⟨r j, fun h => by rw [h] at hj0; simp at hj0, hj1, root j hj1, ?_⟩⟩
  rw [e1] at hj; exact hj

end QuotientHasse
