/-
# The Hasse coefficient of Lubin quotients (Katz 3.10.7 / Buzzard Thm 3.3 (ii), (iv), (v))

`K` complete, algebraically closed, ultrametric; `𝒪 = integers K`; `F` a commutative formal group over
`𝒪` of height two (`‖[p]_{p²}‖ = 1`, `‖a‖ < 1`, `a = [p]_p`) with `‖p‖^p < ‖a‖^{p+1}` (`v < p/(p+1)`,
`v = v(a)`). For a subgroup `C` of order `p` of the `p`-torsion of the disc, `G = F/C = quot C` and
`π = pis C`. With `ε = ‖p‖`, `α = ‖a_F‖`, `α_G = ‖a_G‖`:

* `hasse_quot_noncanonical` (**(v)**, `C ∩ H = 0`): `G` has height two, `α_G^p = α` (`v(a_G) = v/p`),
  `G` satisfies the break condition, and `π` maps `F[p]` into the canonical subgroup of `G`
  (canonical points of `F` to nonzero canonical points of `G`);
* `hasse_quot_canonical` (`C = H`): `G` has height two and
  **(ii)** if `ε < α^{p+1}` (`v < 1/(p+1)`): `α_G = α^p` (`v(a_G) = p v`) and `G` satisfies the break;
  **(iv)** if `α^{p+1} < ε` (`1/(p+1) < v`): `α_G · α = ε` (`v(a_G) = 1 − v`), `G` satisfies the break,
  and `π` maps `F[p]` into the canonical subgroup of `G`.

Method: `[p]_G(π x) = π([p]_F x)`, `‖π(x)‖ = ∏_{c ∈ C} ‖x − c‖` (Weierstrass factorization of `π`),
the root-norm classification `torsion_classify` (applied to `F` and to `G`), and `quot_height`.
-/
import RamanujanTau.QuotientHasse.Reduction

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QuotientHasse
open MvPowerSeries CanonicalIsogeny WeierstrassSupply Lubin

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => integers K

section Ultra

lemma norm_sub_of_lt {x y : K} (h : ‖x‖ < ‖y‖) : ‖x - y‖ = ‖y‖ := by
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (by rw [norm_neg]; exact h.ne), norm_neg, max_eq_right h.le]

lemma norm_sub_of_gt {x y : K} (h : ‖y‖ < ‖x‖) : ‖x - y‖ = ‖x‖ := by
  rw [← norm_neg, neg_sub, norm_sub_of_lt h]

lemma norm_sub_le_max' (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [norm_neg])

end Ultra

section Alg

/-- `E² < E^{p+1}` is impossible for `0 < E < 1`, `p ≥ 1`. -/
lemma no_sq_lt {E : ℝ} (h0 : 0 < E) (h1 : E < 1) (p : ℕ) (hp : 1 ≤ p) : ¬ E ^ 2 < E ^ (p + 1) := by
  intro h
  have := pow_le_pow_of_le_one h0.le h1.le (show 2 ≤ p + 1 by omega)
  linarith

/-- canonical points are smaller than non-canonical ones (the break condition). -/
lemma can_lt_big {p : ℕ} {ε α ℓ u : ℝ} (hα : 0 < α) (hu : 0 ≤ u)
    (hb : ε ^ p < α ^ (p + 1)) (e1 : α * ℓ ^ (p - 1) = ε) (e2 : u ^ (p * (p - 1)) = α) : ℓ < u := by
  by_contra h
  push Not at h
  have h1 : α ≤ ℓ ^ (p * (p - 1)) := e2 ▸ pow_le_pow_left₀ hu h _
  have : α ^ (p + 1) ≤ ε ^ p := by
    calc α ^ (p + 1) = α ^ p * α := pow_succ _ _
      _ ≤ α ^ p * ℓ ^ (p * (p - 1)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (α * ℓ ^ (p - 1)) ^ p := by rw [mul_pow, ← pow_mul, mul_comm (p - 1)]
      _ = ε ^ p := by rw [e1]
  linarith

/-- the valuation computation for **(v)**: a canonical point `x` of `F` (`α ℓ^{p−1} = ε`) maps to a
point of norm `L = ℓ · P0`, `P0^p = α`; the classification of `L` in `G` forces `α_G^p = α`. -/
lemma alg_v {p : ℕ} (hp : 2 ≤ p) {ε α αG ℓ P0 : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hα : 0 < α)
    (hℓ : 0 < ℓ) (hP0 : 0 < P0) (hb : ε ^ p < α ^ (p + 1)) (e1 : α * ℓ ^ (p - 1) = ε)
    (e2 : P0 ^ p = α)
    (cl : (ε ^ p < αG ^ (p + 1) → αG * (ℓ * P0) ^ (p - 1) = ε ∨ (ℓ * P0) ^ (p * (p - 1)) = αG) ∧
      (¬ ε ^ p < αG ^ (p + 1) → (ℓ * P0) ^ ((p + 1) * (p - 1)) = ε)) :
    αG ^ p = α ∧ ε ^ p < αG ^ (p + 1) ∧ αG * (ℓ * P0) ^ (p - 1) = ε := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  set L := ℓ * P0 with hL
  have hL0 : 0 < L := mul_pos hℓ hP0
  have hE0 : 0 < ε ^ (q + 1) := pow_pos hε _
  have hE1 : ε ^ (q + 1) < 1 := pow_lt_one₀ hε.le hε1 (by omega)
  -- `α · L^{pq} = ε^p`
  have key : α * L ^ ((q + 1) * q) = ε ^ (q + 1) := by
    have h1 : L ^ ((q + 1) * q) = (ℓ ^ q) ^ (q + 1) * (P0 ^ (q + 1)) ^ q := by rw [hL]; ring
    have h2 : α ^ (q + 1) * (ℓ ^ q) ^ (q + 1) = ε ^ (q + 1) := by rw [← mul_pow, e1]
    have h3 : α ^ q * (α * L ^ ((q + 1) * q)) = α ^ q * ε ^ (q + 1) := by
      rw [h1, e2, ← h2]; ring
    exact mul_left_cancel₀ (pow_pos hα q).ne' h3
  by_cases hbG : ε ^ (q + 1) < αG ^ (q + 1 + 1)
  · rcases cl.1 hbG with hc | hc
    · refine ⟨?_, hbG, hc⟩
      have h4 : αG ^ (q + 1) * L ^ ((q + 1) * q) = α * L ^ ((q + 1) * q) := by
        rw [key, ← hc]; ring
      exact mul_right_cancel₀ (pow_pos hL0 _).ne' h4
    · exfalso
      rw [hc] at key
      have h5 : ε ^ (q + 1) * ε ^ (q + 1) < ε ^ (q + 1) * α ^ (q + 1 + 1) :=
        mul_lt_mul_of_pos_left hb hE0
      have h6 : ε ^ (q + 1) * α ^ (q + 1 + 1) < αG ^ (q + 1 + 1) * α ^ (q + 1 + 1) :=
        mul_lt_mul_of_pos_right hbG (pow_pos hα _)
      have h7 : αG ^ (q + 1 + 1) * α ^ (q + 1 + 1) = (ε ^ (q + 1)) ^ (q + 1 + 1) := by
        rw [← key, mul_pow, mul_comm]
      exact no_sq_lt hE0 hE1 (q + 1) (by omega) (by rw [sq]; linarith)
  · exfalso
    have hc := cl.2 hbG
    have h7 : α ^ (q + 1 + 1) * (L ^ ((q + 1) * q)) ^ (q + 1 + 1) = (ε ^ (q + 1)) ^ (q + 1 + 1) := by
      rw [← mul_pow, key]
    have h8 : (L ^ ((q + 1) * q)) ^ (q + 1 + 1) = ε ^ (q + 1) := by
      rw [← hc]; ring
    rw [h8] at h7
    have h5 : ε ^ (q + 1) * ε ^ (q + 1) < α ^ (q + 1 + 1) * ε ^ (q + 1) :=
      mul_lt_mul_of_pos_right hb hE0
    exact no_sq_lt hE0 hE1 (q + 1) (by omega) (by rw [sq]; linarith)

/-- **(v)**, other points: a point of norm `≤ u^p` with `u^{p(p−1)} = α` cannot be non-canonical in `G`
when `α_G^p = α`. -/
lemma alg_v_big {p : ℕ} (hp : 2 ≤ p) {α αG u L : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hL : 0 ≤ L) (hLu : L ≤ u ^ p) (e2 : u ^ (p * (p - 1)) = α) (hG : αG ^ p = α)
    (hbig : L ^ (p * (p - 1)) = αG) : False := by
  have h1 : αG ≤ α ^ p := by
    have : L ^ (p * (p - 1)) ≤ (u ^ p) ^ (p * (p - 1)) := pow_le_pow_left₀ hL hLu _
    calc αG = L ^ (p * (p - 1)) := hbig.symm
      _ ≤ (u ^ p) ^ (p * (p - 1)) := this
      _ = (u ^ (p * (p - 1))) ^ p := by ring
      _ = α ^ p := by rw [e2]
  have hαG : 0 ≤ αG := hbig ▸ pow_nonneg hL _
  have h2 : α ≤ α ^ (p * p) := by
    calc α = αG ^ p := hG.symm
      _ ≤ (α ^ p) ^ p := pow_le_pow_left₀ hαG h1 _
      _ = α ^ (p * p) := by rw [← pow_mul]
  have h3 : α ^ (p * p) < α := pow_lt_self_of_lt_one₀ hα hα1 (by nlinarith)
  linarith

end Alg

variable [CompleteSpace K]

/-- **the norm of `π` at a point**: `‖π(x)‖ = ∏_{c ∈ C} ‖x − c‖`. -/
theorem norm_pt_pis {F : FormalGroup 𝒪} [F.IsComm] (S : FinSub F) {x : 𝒪} (hx : ‖(x : K)‖ < 1) :
    ‖((pt (fun _ : Unit => x) (pis S) : 𝒪) : K)‖ = ∏ c ∈ S.H, ‖(x : K) - (c : K)‖ := by
  classical
  obtain ⟨U, hU, hpi⟩ := pis_factor S
  have e := ι_pt incl continuous_incl (isTopologicallyNilpotent_of_norm_lt_one hx) (pis S)
  have hmap : (MvPowerSeries.map incl (pis S) : PowerSeries K) =
      ((∏ c ∈ S.H, (Polynomial.X - Polynomial.C (c : K)) : Polynomial K) : PowerSeries K) *
        MvPowerSeries.map incl U := by
    rw [hpi, map_mul, map_prod]
    congr 1
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_sub, Polynomial.coe_X,
      Polynomial.coe_C, map_sub, map_X, map_C]
    rfl
  have hUb : ∀ k, ‖PowerSeries.coeff k (MvPowerSeries.map incl U : PowerSeries K)‖ ≤ 1 := by
    intro k
    show ‖MvPowerSeries.coeff _ (MvPowerSeries.map incl U)‖ ≤ 1
    rw [MvPowerSeries.coeff_map]; exact (MvPowerSeries.coeff _ U).2
  have hU0 : ‖PowerSeries.constantCoeff (MvPowerSeries.map incl U : PowerSeries K)‖ = 1 := by
    show ‖MvPowerSeries.constantCoeff (MvPowerSeries.map incl U)‖ = 1
    rw [MvPowerSeries.constantCoeff_map]
    exact norm_eq_one_of_isUnit (isUnit_iff_constantCoeff.mp hU)
  show ‖incl (pt (fun _ : Unit => x) (pis S))‖ = _
  rw [e, hmap, evK_mul (sn_poly _ (incl x)) (sn_of_bdd 1 hUb (t := incl x) hx), evK_poly, norm_mul,
    norm_evK_unit hU0 hUb (t := incl x) hx, mul_one, Polynomial.eval_prod, norm_prod]
  simp

/-- `π` maps the disc to the disc. -/
lemma pt_pis_lt_one {F : FormalGroup 𝒪} [F.IsComm] (S : FinSub F) {x : 𝒪} (hx : ‖(x : K)‖ < 1) :
    ‖((pt (fun _ : Unit => x) (pis S) : 𝒪) : K)‖ < 1 := by
  classical
  rw [norm_pt_pis S hx, ← Finset.mul_prod_erase _ _ S.zero_mem]
  have h1 : ∏ c ∈ S.H.erase 0, ‖(x : K) - (c : K)‖ ≤ 1 := by
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun c _ => ?_
    exact (norm_sub_le_max' _ _).trans (max_le x.2 c.2)
  calc ‖(x : K) - ((0 : 𝒪) : K)‖ * ∏ c ∈ S.H.erase 0, ‖(x : K) - (c : K)‖ ≤ ‖(x : K)‖ * 1 := by
        refine mul_le_mul (by simp) h1 (by positivity) (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact hx

/-- **`π` carries `p`-torsion to `p`-torsion**: `[p]_G(π x) = π([p]_F x) = 0`. -/
lemma pt_nmul_quot {F : FormalGroup 𝒪} [F.IsComm] (S : FinSub F) (p : ℕ) {x : 𝒪}
    (hx : ‖(x : K)‖ < 1) (hxp : pt (fun _ : Unit => x) (FGL.nmul F p) = 0) :
    pt (fun _ : Unit => pt (fun _ : Unit => x) (pis S)) (FGL.nmul (quot S) p) = 0 := by
  have hcomp := hom_nmul F (quot S) (pis S) (cc_pis S) (pis_hom S) p
  have hX : AdmPt (fun _ : Unit => x) := fun _ => isTopologicallyNilpotent_of_norm_lt_one hx
  have h := congrArg (pt (fun _ : Unit => x)) hcomp
  rw [pt_subst (fun _ => cc_pis S) hX, pt_subst (fun _ => FGL.cc_nmul F p) hX] at h
  rw [h, hxp, pt_zero, cc_pis]

open scoped Classical in
/-- the product over the nonzero points of `C`, when they all have norm `> ‖x‖`. -/
lemma norm_pt_pis_of_lt {F : FormalGroup 𝒪} [F.IsComm] (S : FinSub F) {x : 𝒪}
    (hx : ‖(x : K)‖ < 1) (hlt : ∀ c ∈ S.H, c ≠ 0 → ‖(x : K)‖ < ‖(c : K)‖) :
    ‖((pt (fun _ : Unit => x) (pis S) : 𝒪) : K)‖ = ‖(x : K)‖ * ∏ c ∈ S.H.erase 0, ‖(c : K)‖ := by
  rw [norm_pt_pis S hx, ← Finset.mul_prod_erase _ _ S.zero_mem]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun c hc => ?_
    exact norm_sub_of_lt (hlt c (Finset.mem_of_mem_erase hc) (Finset.ne_of_mem_erase hc))

/-- the product over the nonzero points of `C`, when they all have norm `< ‖x‖`. -/
lemma norm_pt_pis_of_gt {F : FormalGroup 𝒪} [F.IsComm] (S : FinSub F) {x : 𝒪}
    (hx : ‖(x : K)‖ < 1) (hgt : ∀ c ∈ S.H, c ≠ 0 → ‖(c : K)‖ < ‖(x : K)‖) :
    ‖((pt (fun _ : Unit => x) (pis S) : 𝒪) : K)‖ = ‖(x : K)‖ ^ S.H.card := by
  classical
  rw [norm_pt_pis S hx, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun c hc => ?_
  by_cases h0 : c = 0
  · rw [h0]; simp
  · exact norm_sub_of_gt (hgt c hc h0)

/-- the product bound `‖π(x)‖ ≤ M^{|C|}` when all points of `C` and `x` have norm `≤ M`. -/
lemma norm_pt_pis_le {F : FormalGroup 𝒪} [F.IsComm] (S : FinSub F) {x : 𝒪}
    (hx : ‖(x : K)‖ < 1) {M : ℝ} (hxM : ‖(x : K)‖ ≤ M) (hcM : ∀ c ∈ S.H, ‖(c : K)‖ ≤ M) :
    ‖((pt (fun _ : Unit => x) (pis S) : 𝒪) : K)‖ ≤ M ^ S.H.card := by
  rw [norm_pt_pis S hx, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun c hc =>
    (norm_sub_le_max' _ _).trans (max_le hxM (hcM c hc))

lemma hp_lt_one {p : ℕ} {ε α : ℝ} (hp : 1 ≤ p) (hα0 : 0 ≤ α) (hα : α ≤ 1) (hε : 0 ≤ ε)
    (hb : ε ^ p < α ^ (p + 1)) : ε < 1 :=
  (pow_lt_one_iff_of_nonneg hε (by omega)).mp (lt_of_lt_of_le hb (pow_le_one₀ hα0 hα))


/-- `torsion_classify` with the exponents `p − 1`, `p(p − 1)`, `(p + 1)(p − 1)`. -/
lemma classify' [IsAlgClosed K] (G : FormalGroup 𝒪) [G.IsComm] (p : ℕ) [hp : Fact p.Prime]
    (hu : ‖topc G p‖ = 1) (ha : ‖hasse G p‖ < 1) (hε : 0 < ‖(p : K)‖) (hp1 : ‖(p : K)‖ < 1)
    {y : 𝒪} (hy0 : y ≠ 0) (hy1 : ‖(y : K)‖ < 1)
    (hy : pt (fun _ : Unit => y) (FGL.nmul G p) = 0) :
    (‖(p : K)‖ ^ p < ‖hasse G p‖ ^ (p + 1) →
      ‖hasse G p‖ * ‖(y : K)‖ ^ (p - 1) = ‖(p : K)‖ ∨ ‖(y : K)‖ ^ (p * (p - 1)) = ‖hasse G p‖) ∧
    (¬ ‖(p : K)‖ ^ p < ‖hasse G p‖ ^ (p + 1) → ‖(y : K)‖ ^ ((p + 1) * (p - 1)) = ‖(p : K)‖) := by
  obtain ⟨-, e2, e3⟩ := nat_aux p hp.out.one_lt.le
  have := torsion_classify G p hu ha hε hp1 hy0 hy1 hy
  rwa [e2, e3] at this

lemma alpha_pos {p : ℕ} {ε α : ℝ} (hp : 1 ≤ p) (hε : 0 < ε) (hα : 0 ≤ α)
    (hb : ε ^ p < α ^ (p + 1)) : 0 < α := by
  rcases eq_or_lt_of_le hα with h | h
  · rw [← h, zero_pow (by omega)] at hb; linarith [pow_pos hε p]
  · exact h

lemma pt_pis_ne_zero {F : FormalGroup 𝒪} [F.IsComm] (S : FinSub F) {x : 𝒪}
    (h : 0 < ‖((pt (fun _ : Unit => x) (pis S) : 𝒪) : K)‖) : pt (fun _ : Unit => x) (pis S) ≠ 0 := by
  intro h0; rw [h0] at h; simp at h

lemma pt_pis_zero {F : FormalGroup 𝒪} [F.IsComm] (S : FinSub F) :
    pt (fun _ : Unit => (0 : 𝒪)) (pis S) = 0 := by rw [pt_zero, cc_pis]

lemma ne_zero_of_norm {x : 𝒪} (h : 0 < ‖(x : K)‖) : x ≠ 0 := by
  intro h0; rw [h0] at h; simp at h

lemma norm_pos_of_ne {x : 𝒪} (h : x ≠ 0) : 0 < ‖(x : K)‖ :=
  norm_pos_iff.mpr fun h' => h (Subtype.ext h')

open scoped Classical in
/-- **Buzzard 3.3 (v)**: for a subgroup `C ≠ H` of order `p` (i.e. `C` contains no nonzero canonical
point), `G = F/C` has height two, `‖a_G‖^p = ‖a_F‖` (`v(a_G) = v/p`), `G` satisfies the break condition,
`π` maps every canonical point of `F` to a nonzero canonical point of `G`, and `π(F[p])` lies in the
canonical subgroup `{0} ∪ {y : ‖a_G‖‖y‖^{p−1} = ‖p‖}` of `G`. -/
theorem hasse_quot_noncanonical [IsAlgClosed K] (F : FormalGroup 𝒪) [F.IsComm] (p : ℕ)
    [hp : Fact p.Prime] (hu : ‖topc F p‖ = 1) (ha : ‖hasse F p‖ < 1) (hε : 0 < ‖(p : K)‖)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse F p‖ ^ (p + 1))
    (C : FinSub F) (hCp : ∀ c ∈ C.H, pt (fun _ : Unit => c) (FGL.nmul F p) = 0)
    (hcard : C.H.card = p)
    (hCH : ∀ c ∈ C.H, c ≠ 0 → ‖hasse F p‖ * ‖(c : K)‖ ^ (p - 1) ≠ ‖(p : K)‖) :
    ‖topc (quot C) p‖ = 1 ∧ ‖hasse (quot C) p‖ < 1 ∧
      ‖hasse (quot C) p‖ ^ p = ‖hasse F p‖ ∧
      ‖(p : K)‖ ^ p < ‖hasse (quot C) p‖ ^ (p + 1) ∧
      (∀ x : 𝒪, x ≠ 0 → ‖(x : K)‖ < 1 → pt (fun _ : Unit => x) (FGL.nmul F p) = 0 →
        ‖hasse F p‖ * ‖(x : K)‖ ^ (p - 1) = ‖(p : K)‖ →
        pt (fun _ : Unit => x) (pis C) ≠ 0 ∧
        ‖hasse (quot C) p‖ * ‖((pt (fun _ : Unit => x) (pis C) : 𝒪) : K)‖ ^ (p - 1) =
          ‖(p : K)‖) ∧
      (∀ x : 𝒪, ‖(x : K)‖ < 1 → pt (fun _ : Unit => x) (FGL.nmul F p) = 0 →
        pt (fun _ : Unit => x) (pis C) = 0 ∨
        ‖hasse (quot C) p‖ * ‖((pt (fun _ : Unit => x) (pis C) : 𝒪) : K)‖ ^ (p - 1) =
          ‖(p : K)‖) := by
  have hp2 := hp.out.two_le
  have hα0 : 0 < ‖hasse F p‖ := alpha_pos (by omega) hε (norm_nonneg _) hbreak
  have hp1 : ‖(p : K)‖ < 1 := hp_lt_one (by omega) (norm_nonneg _) ha.le hε.le hbreak
  obtain ⟨huG, haG⟩ := quot_height F p hu ha hp1 C hcard
  -- the nonzero points of `C` are non-canonical
  have hCbig : ∀ c ∈ C.H, c ≠ 0 → ‖(c : K)‖ ^ (p * (p - 1)) = ‖hasse F p‖ := by
    intro c hc hc0
    rcases (classify' F p hu ha hε hp1 hc0 (norm_lt_one_of_tn (C.tn c hc)) (hCp c hc)).1 hbreak
      with h | h
    · exact absurd h (hCH c hc hc0)
    · exact h
  set P0 := ∏ c ∈ C.H.erase 0, ‖(c : K)‖ with hP0
  have hP0pos : 0 < P0 := Finset.prod_pos fun c hc => norm_pos_of_ne (Finset.ne_of_mem_erase hc)
  have hP0p : P0 ^ p = ‖hasse F p‖ := by
    have h1 : (P0 ^ p) ^ (p - 1) = ‖hasse F p‖ ^ (p - 1) := by
      rw [← pow_mul, hP0, ← Finset.prod_pow, Finset.prod_congr rfl (fun c hc =>
        hCbig c (Finset.mem_of_mem_erase hc) (Finset.ne_of_mem_erase hc)), Finset.prod_const,
        Finset.card_erase_of_mem C.zero_mem, hcard]
    exact (pow_left_inj₀ (by positivity) hα0.le (by omega)).mp h1
  -- canonical points
  have can : ∀ x : 𝒪, x ≠ 0 → ‖(x : K)‖ < 1 → pt (fun _ : Unit => x) (FGL.nmul F p) = 0 →
      ‖hasse F p‖ * ‖(x : K)‖ ^ (p - 1) = ‖(p : K)‖ →
      pt (fun _ : Unit => x) (pis C) ≠ 0 ∧ ‖hasse (quot C) p‖ ^ p = ‖hasse F p‖ ∧
      ‖(p : K)‖ ^ p < ‖hasse (quot C) p‖ ^ (p + 1) ∧
      ‖hasse (quot C) p‖ * ‖((pt (fun _ : Unit => x) (pis C) : 𝒪) : K)‖ ^ (p - 1) =
        ‖(p : K)‖ := by
    intro x hx0 hx1 hxp hxc
    have hlt : ∀ c ∈ C.H, c ≠ 0 → ‖(x : K)‖ < ‖(c : K)‖ := fun c hc hc0 =>
      can_lt_big hα0 (norm_nonneg _) hbreak hxc (hCbig c hc hc0)
    have hL := norm_pt_pis_of_lt C hx1 hlt
    rw [← hP0] at hL
    have hLpos : 0 < ‖((pt (fun _ : Unit => x) (pis C) : 𝒪) : K)‖ := by
      rw [hL]; exact mul_pos (norm_pos_of_ne hx0) hP0pos
    have hne := pt_pis_ne_zero C hLpos
    have cl := classify' (quot C) p huG haG hε hp1 hne (pt_pis_lt_one C hx1)
      (pt_nmul_quot C p hx1 hxp)
    rw [hL] at cl
    obtain ⟨h1, h2, h3⟩ := alg_v hp2 hε hp1 hα0 (norm_pos_of_ne hx0) hP0pos hbreak hxc hP0p cl
    exact ⟨hne, h1, h2, by rw [hL]; exact h3⟩
  obtain ⟨⟨h₀, h₀0, h₀1, h₀p, h₀c⟩, -⟩ := torsion_exists F p hu ha hε hp1 hbreak
  obtain ⟨-, hG, hbG, -⟩ := can h₀ h₀0 h₀1 h₀p h₀c
  refine ⟨huG, haG, hG, hbG, fun x hx0 hx1 hxp hxc => ⟨(can x hx0 hx1 hxp hxc).1,
    (can x hx0 hx1 hxp hxc).2.2.2⟩, fun x hx1 hxp => ?_⟩
  by_cases hπ : pt (fun _ : Unit => x) (pis C) = 0
  · exact Or.inl hπ
  right
  have hx0 : x ≠ 0 := by rintro rfl; exact hπ (pt_pis_zero C)
  rcases (classify' F p hu ha hε hp1 hx0 hx1 hxp).1 hbreak with hxc | hxb
  · exact (can x hx0 hx1 hxp hxc).2.2.2
  · -- non-canonical `x`: `‖π x‖ ≤ ‖x‖^p` is too small to be non-canonical in `G`
    have hcle : ∀ c ∈ C.H, ‖(c : K)‖ ≤ ‖(x : K)‖ := by
      intro c hc
      by_cases hc0 : c = 0
      · rw [hc0]; simp
      · exact le_of_eq ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _)
          (Nat.mul_ne_zero (by omega) (by omega) : p * (p - 1) ≠ 0)).mp ((hCbig c hc hc0).trans hxb.symm))
    have hle := norm_pt_pis_le C hx1 le_rfl hcle
    rw [hcard] at hle
    rcases (classify' (quot C) p huG haG hε hp1 hπ (pt_pis_lt_one C hx1)
      (pt_nmul_quot C p hx1 hxp)).1 hbG with h | h
    · exact h
    · exact (alg_v_big hp2 hα0 ha (norm_nonneg _) hle hxb hG h).elim

open scoped Classical in
/-- **Buzzard 3.3 (ii), (iv)**: for the canonical subgroup `C = H` (order `p`, all nonzero points
canonical), `G = F/H` has height two, and
* (ii) if `‖p‖ < ‖a‖^{p+1}` (`v < 1/(p+1)`): `‖a_G‖ = ‖a‖^p` (`v(a_G) = p v`) and `G` satisfies the
  break condition;
* (iv) if `‖a‖^{p+1} < ‖p‖` (`1/(p+1) < v`): `‖a_G‖ · ‖a‖ = ‖p‖` (`v(a_G) = 1 − v`), `G` satisfies
  the break condition, and `π(F[p])` lies in the canonical subgroup of `G`. -/
theorem hasse_quot_canonical [IsAlgClosed K] (F : FormalGroup 𝒪) [F.IsComm] (p : ℕ)
    [hp : Fact p.Prime] (hu : ‖topc F p‖ = 1) (ha : ‖hasse F p‖ < 1) (hε : 0 < ‖(p : K)‖)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse F p‖ ^ (p + 1))
    (C : FinSub F) (hcard : C.H.card = p)
    (hCH : ∀ c ∈ C.H, c ≠ 0 → ‖hasse F p‖ * ‖(c : K)‖ ^ (p - 1) = ‖(p : K)‖) :
    ‖topc (quot C) p‖ = 1 ∧ ‖hasse (quot C) p‖ < 1 ∧
      (‖(p : K)‖ < ‖hasse F p‖ ^ (p + 1) →
        ‖hasse (quot C) p‖ = ‖hasse F p‖ ^ p ∧ ‖(p : K)‖ ^ p < ‖hasse (quot C) p‖ ^ (p + 1)) ∧
      (‖hasse F p‖ ^ (p + 1) < ‖(p : K)‖ →
        ‖hasse (quot C) p‖ * ‖hasse F p‖ = ‖(p : K)‖ ∧
        ‖(p : K)‖ ^ p < ‖hasse (quot C) p‖ ^ (p + 1) ∧
        ∀ x : 𝒪, ‖(x : K)‖ < 1 → pt (fun _ : Unit => x) (FGL.nmul F p) = 0 →
          pt (fun _ : Unit => x) (pis C) = 0 ∨
          ‖hasse (quot C) p‖ * ‖((pt (fun _ : Unit => x) (pis C) : 𝒪) : K)‖ ^ (p - 1) =
            ‖(p : K)‖) := by
  have hp2 := hp.out.two_le
  have hα0 : 0 < ‖hasse F p‖ := alpha_pos (by omega) hε (norm_nonneg _) hbreak
  have hp1 : ‖(p : K)‖ < 1 := hp_lt_one (by omega) (norm_nonneg _) ha.le hε.le hbreak
  obtain ⟨huG, haG⟩ := quot_height F p hu ha hp1 C hcard
  set ε := ‖(p : K)‖ with hεd
  set α := ‖hasse F p‖ with hαd
  set αG := ‖hasse (quot C) p‖ with hαGd
  -- a non-canonical `x` maps to a point of norm `‖x‖^p`
  have big : ∀ x : 𝒪, x ≠ 0 → ‖(x : K)‖ < 1 → pt (fun _ : Unit => x) (FGL.nmul F p) = 0 →
      ‖(x : K)‖ ^ (p * (p - 1)) = α →
      pt (fun _ : Unit => x) (pis C) ≠ 0 ∧
      ‖((pt (fun _ : Unit => x) (pis C) : 𝒪) : K)‖ = ‖(x : K)‖ ^ p := by
    intro x hx0 hx1 hxp hxb
    have hgt : ∀ c ∈ C.H, c ≠ 0 → ‖(c : K)‖ < ‖(x : K)‖ := fun c hc hc0 =>
      can_lt_big hα0 (norm_nonneg _) hbreak (hCH c hc hc0) hxb
    have hL := norm_pt_pis_of_gt C hx1 hgt
    rw [hcard] at hL
    refine ⟨pt_pis_ne_zero C (by rw [hL]; exact pow_pos (norm_pos_of_ne hx0) _), hL⟩
  obtain ⟨-, ⟨yb, hyb0, hyb1, hybp, hybb⟩⟩ := torsion_exists F p hu ha hε hp1 hbreak
  obtain ⟨-, e2n, -⟩ := nat_aux p (by omega)
  rw [e2n] at hybb
  obtain ⟨hne, hL⟩ := big yb hyb0 hyb1 hybp hybb
  have cl := classify' (quot C) p huG haG hε hp1 hne (pt_pis_lt_one C hyb1)
    (pt_nmul_quot C p hyb1 hybp)
  rw [hL] at cl
  set u := ‖(yb : K)‖
  have hq : (u ^ p) ^ (p - 1) = α := by rw [← pow_mul]; exact hybb
  have hpq : (u ^ p) ^ (p * (p - 1)) = α ^ p := by
    rw [show α = u ^ (p * (p - 1)) from hybb.symm]; ring
  have hp1q : (u ^ p) ^ ((p + 1) * (p - 1)) = α ^ (p + 1) := by
    rw [show α = u ^ (p * (p - 1)) from hybb.symm]; ring
  rw [hq, hpq, hp1q] at cl
  rw [← hεd, ← hαGd] at cl
  have hεp : 0 < ε ^ p := pow_pos hε p
  -- canonical image forces `ε < α^{p+1}` to fail
  have nocan : ε ^ p < αG ^ (p + 1) → αG * α = ε → α ^ (p + 1) < ε := by
    intro hbG hc
    have h1 : ε ^ p * α ^ (p + 1) < αG ^ (p + 1) * α ^ (p + 1) :=
      mul_lt_mul_of_pos_right hbG (pow_pos hα0 _)
    rw [← mul_pow, hc, pow_succ] at h1
    exact lt_of_mul_lt_mul_left h1 hεp.le
  refine ⟨huG, haG, fun hii => ?_, fun hiv => ?_⟩
  · by_cases hbG : ε ^ p < αG ^ (p + 1)
    · rcases cl.1 hbG with h | h
      · exact absurd (nocan hbG h) (not_lt.mpr hii.le)
      · exact ⟨h.symm, hbG⟩
    · exact absurd (cl.2 hbG) (ne_of_gt hii)
  · have hbG : ε ^ p < αG ^ (p + 1) := by
      by_contra hbG
      exact absurd (cl.2 hbG) (ne_of_lt hiv)
    have hcan : αG * α = ε := by
      rcases cl.1 hbG with h | h
      · exact h
      · exfalso
        rw [← h, ← pow_mul, mul_comm p, pow_mul] at hbG
        exact absurd (lt_of_pow_lt_pow_left₀ p (by positivity) hbG) (not_lt.mpr hiv.le)
    refine ⟨hcan, hbG, fun x hx1 hxp => ?_⟩
    by_cases hπ : pt (fun _ : Unit => x) (pis C) = 0
    · exact Or.inl hπ
    right
    have hx0 : x ≠ 0 := by rintro rfl; exact hπ (pt_pis_zero C)
    have clx := (classify' (quot C) p huG haG hε hp1 hπ (pt_pis_lt_one C hx1)
      (pt_nmul_quot C p hx1 hxp)).1 hbG
    rw [← hεd, ← hαGd] at clx
    rcases (classify' F p hu ha hε hp1 hx0 hx1 hxp).1 hbreak with hxc | hxb
    · -- canonical `x`: `‖π x‖ ≤ ‖x‖^p` is too small to be non-canonical
      rcases clx with h | h
      · exact h
      · exfalso
        have hcle : ∀ c ∈ C.H, ‖(c : K)‖ ≤ ‖(x : K)‖ := by
          intro c hc
          by_cases hc0 : c = 0
          · rw [hc0]; simp
          · refine le_of_eq ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _)
              (by omega : p - 1 ≠ 0)).mp ?_)
            exact mul_left_cancel₀ hα0.ne' ((hCH c hc hc0).trans hxc.symm)
        have hle := norm_pt_pis_le C hx1 le_rfl hcle
        rw [hcard] at hle
        set ℓ := ‖(x : K)‖
        have hℓq : αG = ℓ ^ (p - 1) := mul_right_cancel₀ hα0.ne' (by rw [hcan, mul_comm]; exact hxc.symm)
        have hℓ0 : 0 < ℓ ^ (p - 1) := pow_pos (norm_pos_of_ne hx0) _
        have hℓ1 : ℓ ^ (p - 1) < 1 := pow_lt_one₀ (norm_nonneg _) hx1 (by omega)
        have h1 : ℓ ^ (p - 1) ≤ (ℓ ^ (p - 1)) ^ (p * p) := by
          calc ℓ ^ (p - 1) = αG := hℓq.symm
            _ = _ := h.symm
            _ ≤ (ℓ ^ p) ^ (p * (p - 1)) := pow_le_pow_left₀ (norm_nonneg _) hle _
            _ = (ℓ ^ (p - 1)) ^ (p * p) := by ring
        have h2 := pow_lt_self_of_lt_one₀ hℓ0 hℓ1 (show 1 < p * p by nlinarith)
        linarith
    · obtain ⟨-, hLx⟩ := big x hx0 hx1 hxp hxb
      rcases clx with h | h
      · exact h
      · exfalso
        rw [hLx, show (‖(x : K)‖ ^ p) ^ (p * (p - 1)) = (‖(x : K)‖ ^ (p * (p - 1))) ^ p by ring,
          hxb] at h
        rw [← h, ← pow_succ] at hcan
        exact absurd hcan (ne_of_lt hiv)

end QuotientHasse
