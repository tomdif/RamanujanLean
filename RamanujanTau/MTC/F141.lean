/-
# The Hecke-type double sum `f_{1,4,1}(x, y, q)` as a series in `x`

The `n = 1, p = 3` analogue of `F373`. Fix `q = t^{qe}` and `y = cy t^{ey}`. Then
`f_{1,4,1}(x,y,q) = Σ_{sg r = sg s} sg(r) (−1)^{r+s} x^r y^s q^{C(r,2) + 4rs + C(s,2)} = Σ_k fS k · x^k`,
where `fS k = (−1)^k q^{C(k,2)} S_k` and `S_k` is the restricted theta sum `Σ_{s ≥ 0}` (for `k ≥ 0`) or
`−Σ_{s < 0}` (for `k < 0`) of `(−1)^s q^{C(s,2)} (q^{4k} y)^s`.

* `fS_ent` — entire;
* `fS_rec` — coefficient form of HM Prop 5.5: `fS k · q^{15k} = −q^{9} y^{−4} fS (k − 1) + InhS k`;
* `fV_FE` — `f(q^{15}x) = −q^9 y^{−4} x f(x) + Inh(x)`.
-/
import RamanujanTau.MTC.F373

set_option autoImplicit false

namespace MTC.H141
open ALz HahnSeries Finset MTC

section F141
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

/-- `S_k`. -/
noncomputable def SK (k : ℤ) : L :=
  if 0 ≤ k then thR hqe (4 * qe * k + ey) cy (0 ≤ ·)
  else -thR hqe (4 * qe * k + ey) cy (· < 0)

/-- the coefficient of `x^k` in `f_{1,4,1}(x, y, q)`. -/
noncomputable def fS (k : ℤ) : L := mono (qe * c2 k) ((-1) ^ k) * SK hqe ey cy k

lemma vge_SK (k : ℤ) : vge (SK hqe ey cy k) (-(ey * ey) - 1) := by
  unfold SK
  have hl := fun s => thE_lb (N := qe) hqe ey s
  split_ifs with hk
  · refine vge_thR _ _ _ _ _ fun s hs => ?_
    have hs' : 0 ≤ s := hs
    have := hl s; unfold thE at *
    have : 0 ≤ 4 * (qe : ℤ) * k * s := mul_nonneg (mul_nonneg (by positivity) hk) hs'
    nlinarith
  · refine vge_neg (vge_thR _ _ _ _ _ fun s hs => ?_)
    have hs' : s < 0 := hs
    have := hl s; unfold thE at *
    have : 0 ≤ 4 * (qe : ℤ) * k * s := by
      have : 0 ≤ (-k) * (-s) := mul_nonneg (by omega) (by omega)
      have hq : (0 : ℤ) ≤ 4 * qe := by positivity
      nlinarith
    nlinarith

lemma fS_ent : Ent (fS hqe ey cy) := by
  intro A
  have h1 : (1 : ℤ) ≤ qe := by exact_mod_cast hqe
  obtain ⟨C, hC⟩ := quad_dom h1 A
  refine ⟨C + ey * ey + 1, fun k => ?_⟩
  refine vge_mono (vge_mul (vge_single _ _) (vge_SK hqe ey cy k)) ?_
  have := hC k
  push_cast at this ⊢
  linarith

/-- the four boundary terms `Σ_{u=−4}^{−1} (−1)^u q^{C(u,2)} (q^{4k} y)^u`. -/
noncomputable def finK (k : ℤ) : L :=
  ∑ u ∈ Finset.Icc (-4 : ℤ) (-1), mono (thE qe (4 * qe * k + ey) u) (thC cy u)

/-- the multiplier `q^{−10} (q^{4k} y)^4`. -/
noncomputable def MK (k : ℤ) : L := mono (4 * (4 * qe * k + ey) - qe * c2 (4 + 1)) ((-1) ^ (4 : ℤ) * cy ^ (4 : ℤ))

include hqe in
lemma SK_rec (hcy : cy ≠ 0) (k : ℤ) :
    SK hqe ey cy (k - 1) = MK (qe := qe) ey cy k * (SK hqe ey cy k + finK (qe := qe) ey cy k) -
      (if k = 0 then MK (qe := qe) ey cy k * θ hqe (4 * qe * k + ey) cy else 0) := by
  have harg : 4 * (qe : ℤ) * (k - 1) + ey = (4 * qe * k + ey) - ((qe : ℕ) : ℤ) * 4 := by ring
  have hsh := fun (P : ℤ → Prop) [DecidablePred P] =>
    thR_shift hqe (4 * qe * k + ey) hcy 4 P
  have hMK : mono ((4 * qe * k + ey) * 4 - ((qe : ℕ) : ℤ) * c2 (4 + 1)) ((-1) ^ (4 : ℤ) * cy ^ (4 : ℤ)) =
      MK (qe := qe) ey cy k := by
    unfold MK; push_cast; congr 1; ring
  have hpos : thR hqe (4 * qe * k + ey) cy (fun u => 0 ≤ u + 4) =
      thR hqe (4 * qe * k + ey) cy (0 ≤ ·) + finK (qe := qe) ey cy k :=
    thR_split hqe _ _ _ _ (-4) (-1) (fun s => by omega) (fun s (hs : 0 ≤ s) => by omega)
  have hneg : thR hqe (4 * qe * k + ey) cy (· < 0) =
      thR hqe (4 * qe * k + ey) cy (fun u => u + 4 < 0) + finK (qe := qe) ey cy k :=
    thR_split hqe _ _ _ _ (-4) (-1) (fun s => by omega) (fun s (hs : s + 4 < 0) => by omega)
  have hcomp := thR_compl hqe (4 * qe * k + ey) cy (0 ≤ ·)
  have hlt : thR hqe (4 * qe * k + ey) cy (fun s => ¬ 0 ≤ s) =
      thR hqe (4 * qe * k + ey) cy (· < 0) := by
    unfold thR; congr 1; ext s : 1; simp only [monoFam_apply, not_le]
  unfold SK
  rw [harg]
  by_cases hk1 : 1 ≤ k
  · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), sub_zero, hsh, hMK, hpos]
  · by_cases hk0 : k = 0
    · rw [if_neg (by omega), if_pos (by omega), if_pos hk0, hsh, hMK]
      linear_combination (MK (qe := qe) ey cy k) * hneg - (MK (qe := qe) ey cy k) * hcomp +
        (MK (qe := qe) ey cy k) * hlt
    · rw [if_neg (by omega), if_neg (by omega), if_neg hk0, sub_zero, hsh, hMK]
      linear_combination (MK (qe := qe) ey cy k) * hneg

/-- the inhomogeneous coefficient. -/
noncomputable def InhS (k : ℤ) : L :=
  mono (15 * qe * k + qe * c2 k) ((-1) ^ k) *
    ((if k = 0 then θ hqe (4 * qe * k + ey) cy else 0) - finK (qe := qe) ey cy k)

/-- `μ_D = −q^{9} y^{−4}`. -/
noncomputable def muD : L := mono (9 * qe - 4 * ey) (-cy ^ (-4 : ℤ))

include hqe in
/-- **coefficient form of HM Prop 5.5 for `f_{1,4,1}`**. -/
theorem fS_rec (hcy : cy ≠ 0) (k : ℤ) :
    fS hqe ey cy k * mono (15 * qe * k) 1 = muD (qe := qe) ey cy * fS hqe ey cy (k - 1) + InhS hqe ey cy k := by
  have hZ : muD (qe := qe) ey cy * mono (qe * c2 (k - 1)) ((-1) ^ (k - 1)) * MK (qe := qe) ey cy k =
      mono (15 * qe * k + qe * c2 k) ((-1) ^ k) := by
    unfold muD MK
    rw [mono_mul, mono_mul]
    have e1 := two_c2 (k - 1); have e2 := two_c2 k
    have e5 : c2 (4 + 1) = 10 := by decide
    congr 1
    · have : c2 (k - 1) = c2 k - k + 1 := by
        have : 2 * c2 (k - 1) = 2 * (c2 k - k + 1) := by linear_combination e1 - e2
        exact mul_left_cancel₀ two_ne_zero this
      rw [this, e5]; ring
    · rw [show k - 1 = k + -1 by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      field_simp
  have hm : mono (qe * c2 k) ((-1) ^ k) * mono (15 * qe * k) 1 =
      mono (15 * qe * k + qe * c2 k) ((-1) ^ k) := by rw [mono_mul]; congr 1 <;> ring
  unfold fS InhS
  rw [SK_rec hqe ey cy hcy k]
  by_cases hc : k = 0
  · simp only [if_pos hc]
    linear_combination SK hqe ey cy k * hm -
      (SK hqe ey cy k + finK (qe := qe) ey cy k - θ hqe (4 * qe * k + ey) cy) * hZ
  · simp only [if_neg hc]
    linear_combination SK hqe ey cy k * hm - (SK hqe ey cy k + finK (qe := qe) ey cy k) * hZ

end F141

section FVal
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

include hqe in
lemma InhS_eq : InhS hqe ey cy = fun k =>
    monoS 0 (θ hqe ey cy) k -
    ∑ u ∈ Finset.Icc (-4 : ℤ) (-1),
      mono (qe * c2 u + ey * u) ((-1) ^ u * cy ^ u) * thSer qe (15 * qe + 4 * qe * u) 1 k := by
  funext k
  unfold InhS finK
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · by_cases hk : k = 0
    · subst hk; simp [monoS, c2]
    · simp [monoS, hk]
  · refine Finset.sum_congr rfl fun u _ => ?_
    simp only [thSer, thE, thC, mono_mul, one_zpow, mul_one]
    congr 1
    · ring
    · ring

/-- the value of the inhomogeneous term. -/
noncomputable def InhV (ex : ℤ) (cx : ℂ) : L :=
  θ hqe ey cy -
    ∑ u ∈ Finset.Icc (-4 : ℤ) (-1),
      mono (qe * c2 u + ey * u) ((-1) ^ u * cy ^ u) * θ hqe (15 * qe + 4 * qe * u + ex) cx

include hqe in
lemma InhS_ent : Ent (InhS hqe ey cy) := by
  rw [InhS_eq hqe ey cy]
  refine (ent_monoS _ _).sub (Ent.sum _ fun u _ => ?_)
  exact (thSer_ent hqe _ one_ne_zero).smul _

include hqe in
lemma InhS_ev (ex : ℤ) (cx : ℂ) : ev (InhS hqe ey cy) ex cx = InhV hqe ey cy ex cx := by
  have h2 : Ent (fun k => ∑ u ∈ Finset.Icc (-4 : ℤ) (-1),
      mono (qe * c2 u + ey * u) ((-1) ^ u * cy ^ u) * thSer qe (15 * qe + 4 * qe * u) 1 k) :=
    Ent.sum _ fun u _ => (thSer_ent hqe _ one_ne_zero).smul _
  rw [InhS_eq hqe ey cy, show (fun k => monoS 0 (θ hqe ey cy) k -
    ∑ u ∈ Finset.Icc (-4 : ℤ) (-1),
      mono (qe * c2 u + ey * u) ((-1) ^ u * cy ^ u) * thSer qe (15 * qe + 4 * qe * u) 1 k) =
    monoS 0 (θ hqe ey cy) -
    (fun k => ∑ u ∈ Finset.Icc (-4 : ℤ) (-1),
      mono (qe * c2 u + ey * u) ((-1) ^ u * cy ^ u) * thSer qe (15 * qe + 4 * qe * u) 1 k) from rfl,
    ev_sub (ent_monoS _ _) h2, ev_sum _ (fun u _ => (thSer_ent hqe _ one_ne_zero).smul _), ev_monoS]
  unfold InhV
  congr 1
  · simp [mono]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [ev_smul (thSer_ent hqe _ one_ne_zero), thSer_ev hqe _ one_ne_zero, one_mul]

include hqe in
/-- **value-level functional equation of `f_{1,4,1}`**: `f(q^{15}x) = μ_D x f(x) + Inh(x)`. -/
theorem fV_FE (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (fS hqe ey cy) (ex + 15 * qe) cx =
      muD (qe := qe) ey cy * mono ex cx * ev (fS hqe ey cy) ex cx + InhV hqe ey cy ex cx := by
  have hE := fS_ent hqe ey cy
  have hser : twist (fS hqe ey cy) (15 * qe) 1 =
      (fun k => muD (qe := qe) ey cy * shiftS (fS hqe ey cy) (-1) k) + InhS hqe ey cy := by
    funext k
    simp only [twist, one_zpow, Pi.add_apply, shiftS]
    rw [fS_rec hqe ey cy hcy k, show k + -1 = k - 1 by ring]
  have := ev_twist hE (15 * qe) 1 ex cx
  rw [mul_one, hser, ev_add ((hE.shift (-1)).smul _) (InhS_ent hqe ey cy), ev_smul (hE.shift (-1)),
    MTC.ev_shift hE (-1) ex hcx, InhS_ev] at this
  rw [← this]
  simp only [mul_neg, neg_neg, zpow_one, mul_one]
  ring

end FVal

end MTC.H141
