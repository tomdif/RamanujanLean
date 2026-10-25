/-
# The Hecke-type double sum `f_{2,3,2}(x, y, q)` as a series in `x` (the `n = 2, p = 1` analogue of `F373`)

* `fS_rec` — HM Prop 5.5: `fS k · q^{5k} = −q⁶ y^{−3} fS (k − 2) + InhS k`;
* `fV_FE` — `f(q⁵x) = −q⁶ y^{−3} x² f(x) + Inh(x)`.
-/
import RamanujanTau.MTC.F373

set_option autoImplicit false

namespace MTC.H232
open ALz HahnSeries Finset MTC

section F232
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

omit hqe in
lemma h2qe (hqe : 1 ≤ qe) : 1 ≤ 2 * qe := by omega

/-- `S_k`. -/
noncomputable def SK (k : ℤ) : L :=
  if 0 ≤ k then thR (h2qe hqe) (3 * qe * k + ey) cy (0 ≤ ·)
  else -thR (h2qe hqe) (3 * qe * k + ey) cy (· < 0)

/-- the coefficient of `x^k` in `f_{3,7,3}(x, y, q)`. -/
noncomputable def fS (k : ℤ) : L := mono (2 * qe * c2 k) ((-1) ^ k) * SK hqe ey cy k

lemma vge_SK (k : ℤ) : vge (SK hqe ey cy k) (-(ey * ey) - 1) := by
  unfold SK
  have hl := fun s => thE_lb (N := 2 * qe) (h2qe hqe) ey s
  split_ifs with hk
  · refine vge_thR _ _ _ _ _ fun s hs => ?_
    have hs' : 0 ≤ s := hs
    have := hl s; unfold thE at *
    have : 0 ≤ 3 * (qe : ℤ) * k * s := mul_nonneg (mul_nonneg (by positivity) hk) hs'
    nlinarith
  · refine vge_neg (vge_thR _ _ _ _ _ fun s hs => ?_)
    have hs' : s < 0 := hs
    have := hl s; unfold thE at *
    have : 0 ≤ 3 * (qe : ℤ) * k * s := by
      have : 0 ≤ (-k) * (-s) := mul_nonneg (by omega) (by omega)
      have hq : (0 : ℤ) ≤ 3 * qe := by positivity
      nlinarith
    nlinarith

lemma fS_ent : Ent (fS hqe ey cy) := by
  intro A
  have h3 : (1 : ℤ) ≤ 2 * qe := by exact_mod_cast h2qe hqe
  obtain ⟨C, hC⟩ := quad_dom h3 A
  refine ⟨C + ey * ey + 1, fun k => ?_⟩
  refine vge_mono (vge_mul (vge_single _ _) (vge_SK hqe ey cy k)) ?_
  have := hC k
  push_cast at this ⊢
  linarith

/-- the three boundary terms `Σ_{u=−3}^{−1} (−1)^u q^{2C(u,2)} (q^{3k} y)^u`. -/
noncomputable def finK (k : ℤ) : L :=
  ∑ u ∈ Finset.Icc (-3 : ℤ) (-1), mono (thE (2 * qe) (3 * qe * k + ey) u) (thC cy u)

/-- the multiplier `−q^{−12} (q^{3k} y)^3`. -/
noncomputable def MK (k : ℤ) : L := mono (3 * (3 * qe * k + ey) - 2 * qe * c2 (3 + 1)) ((-1) ^ (3 : ℤ) * cy ^ (3 : ℤ))

include hqe in
lemma SK_rec (hcy : cy ≠ 0) (k : ℤ) :
    SK hqe ey cy (k - 2) = MK (qe := qe) ey cy k * (SK hqe ey cy k + finK (qe := qe) ey cy k) -
      (if 0 ≤ k ∧ k ≤ 1 then MK (qe := qe) ey cy k * θ (h2qe hqe) (3 * qe * k + ey) cy else 0) := by
  have harg : 3 * (qe : ℤ) * (k - 2) + ey = (3 * qe * k + ey) - ((2 * qe : ℕ) : ℤ) * 3 := by push_cast; ring
  have hsh := fun (P : ℤ → Prop) [DecidablePred P] =>
    thR_shift (h2qe hqe) (3 * qe * k + ey) hcy 3 P
  have hMK : mono ((3 * qe * k + ey) * 3 - ((2 * qe : ℕ) : ℤ) * c2 (3 + 1)) ((-1) ^ (3 : ℤ) * cy ^ (3 : ℤ)) =
      MK (qe := qe) ey cy k := by
    unfold MK; push_cast; congr 1; ring
  have hpos : thR (h2qe hqe) (3 * qe * k + ey) cy (fun u => 0 ≤ u + 3) =
      thR (h2qe hqe) (3 * qe * k + ey) cy (0 ≤ ·) + finK (qe := qe) ey cy k :=
    thR_split (h2qe hqe) _ _ _ _ (-3) (-1) (fun s => by omega) (fun s (hs : 0 ≤ s) => by omega)
  have hneg : thR (h2qe hqe) (3 * qe * k + ey) cy (· < 0) =
      thR (h2qe hqe) (3 * qe * k + ey) cy (fun u => u + 3 < 0) + finK (qe := qe) ey cy k :=
    thR_split (h2qe hqe) _ _ _ _ (-3) (-1) (fun s => by omega) (fun s (hs : s + 3 < 0) => by omega)
  have hcomp := thR_compl (h2qe hqe) (3 * qe * k + ey) cy (0 ≤ ·)
  have hlt : thR (h2qe hqe) (3 * qe * k + ey) cy (fun s => ¬ 0 ≤ s) =
      thR (h2qe hqe) (3 * qe * k + ey) cy (· < 0) := by
    unfold thR; congr 1; ext s : 1; simp only [monoFam_apply, not_le]
  unfold SK
  rw [harg]
  by_cases hk3 : 2 ≤ k
  · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), sub_zero, hsh, hMK, hpos]
  · by_cases hk0 : 0 ≤ k
    · rw [if_neg (by omega), if_pos hk0, if_pos ⟨hk0, by omega⟩, hsh, hMK]
      linear_combination (MK (qe := qe) ey cy k) * hneg - (MK (qe := qe) ey cy k) * hcomp +
        (MK (qe := qe) ey cy k) * hlt
    · rw [if_neg (by omega), if_neg hk0, if_neg (by omega), sub_zero, hsh, hMK]
      linear_combination (MK (qe := qe) ey cy k) * hneg

/-- the inhomogeneous coefficient. -/
noncomputable def InhS (k : ℤ) : L :=
  mono (5 * qe * k + 2 * qe * c2 k) ((-1) ^ k) *
    ((if 0 ≤ k ∧ k ≤ 1 then θ (h2qe hqe) (3 * qe * k + ey) cy else 0) - finK (qe := qe) ey cy k)

/-- `μ_D = −q^{6} y^{−3}`. -/
noncomputable def muD : L := mono (6 * qe - 3 * ey) (-cy ^ (-3 : ℤ))

include hqe in
/-- **coefficient form of HM Prop 5.5 for `f_{2,3,2}`**. -/
theorem fS_rec (hcy : cy ≠ 0) (k : ℤ) :
    fS hqe ey cy k * mono (5 * qe * k) 1 = muD (qe := qe) ey cy * fS hqe ey cy (k - 2) + InhS hqe ey cy k := by
  have hZ : muD (qe := qe) ey cy * mono (2 * qe * c2 (k - 2)) ((-1) ^ (k - 2)) * MK (qe := qe) ey cy k =
      mono (5 * qe * k + 2 * qe * c2 k) ((-1) ^ k) := by
    unfold muD MK
    rw [mono_mul, mono_mul]
    have e1 := two_c2 (k - 2); have e2 := two_c2 k
    have e8 : c2 (3 + 1) = 6 := by decide
    congr 1
    · have : c2 (k - 2) = c2 k - 2 * k + 3 := by
        have : 2 * c2 (k - 2) = 2 * (c2 k - 2 * k + 3) := by linear_combination e1 - e2
        exact mul_left_cancel₀ two_ne_zero this
      rw [this, e8]; ring
    · rw [show k - 2 = k + -2 by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      field_simp
  have hm : mono (2 * qe * c2 k) ((-1) ^ k) * mono (5 * qe * k) 1 =
      mono (5 * qe * k + 2 * qe * c2 k) ((-1) ^ k) := by rw [mono_mul]; congr 1 <;> ring
  unfold fS InhS
  rw [SK_rec hqe ey cy hcy k]
  by_cases hc : 0 ≤ k ∧ k ≤ 1
  · simp only [if_pos hc]
    linear_combination SK hqe ey cy k * hm -
      (SK hqe ey cy k + finK (qe := qe) ey cy k - θ (h2qe hqe) (3 * qe * k + ey) cy) * hZ
  · simp only [if_neg hc]
    linear_combination SK hqe ey cy k * hm - (SK hqe ey cy k + finK (qe := qe) ey cy k) * hZ

end F232

section FVal
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

include hqe in
lemma InhS_eq : InhS hqe ey cy = fun k =>
    (∑ r ∈ Finset.Icc (0 : ℤ) 1,
      monoS r (mono (5 * qe * r + 2 * qe * c2 r) ((-1) ^ r) * θ (h2qe hqe) (3 * qe * r + ey) cy) k) -
    ∑ u ∈ Finset.Icc (-3 : ℤ) (-1),
      mono (2 * qe * c2 u + ey * u) ((-1) ^ u * cy ^ u) * thSer (2 * qe) (5 * qe + 3 * qe * u) 1 k := by
  funext k
  unfold InhS finK
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · by_cases hk : 0 ≤ k ∧ k ≤ 1
    · rw [if_pos hk, Finset.sum_eq_single k]
      · simp [monoS]
      · intro r _ hr; simp [monoS, Ne.symm hr]
      · intro h; exact absurd (Finset.mem_Icc.mpr hk) h
    · rw [if_neg hk, mul_zero]
      refine (Finset.sum_eq_zero fun r hr => ?_).symm
      have : k ≠ r := fun h => hk (h ▸ Finset.mem_Icc.mp hr)
      simp [monoS, this]
  · refine Finset.sum_congr rfl fun u _ => ?_
    simp only [thSer, thE, thC, mono_mul, one_zpow, mul_one]
    congr 1
    · push_cast; ring
    · ring

/-- the value of the inhomogeneous term. -/
noncomputable def InhV (ex : ℤ) (cx : ℂ) : L :=
  (∑ r ∈ Finset.Icc (0 : ℤ) 1,
      mono (5 * qe * r + 2 * qe * c2 r) ((-1) ^ r) * θ (h2qe hqe) (3 * qe * r + ey) cy * mono (ex * r) (cx ^ r)) -
    ∑ u ∈ Finset.Icc (-3 : ℤ) (-1),
      mono (2 * qe * c2 u + ey * u) ((-1) ^ u * cy ^ u) * θ (h2qe hqe) (5 * qe + 3 * qe * u + ex) cx

include hqe in
lemma InhS_ent : Ent (InhS hqe ey cy) := by
  rw [InhS_eq hqe ey cy]
  refine (Ent.sum _ fun r _ => ent_monoS _ _).sub (Ent.sum _ fun u _ => ?_)
  exact (thSer_ent (h2qe hqe) _ one_ne_zero).smul _

include hqe in
lemma InhS_ev (ex : ℤ) (cx : ℂ) : ev (InhS hqe ey cy) ex cx = InhV hqe ey cy ex cx := by
  have h1 : Ent (fun k => ∑ r ∈ Finset.Icc (0 : ℤ) 1,
      monoS r (mono (5 * qe * r + 2 * qe * c2 r) ((-1) ^ r) * θ (h2qe hqe) (3 * qe * r + ey) cy) k) :=
    Ent.sum _ fun r _ => ent_monoS _ _
  have h2 : Ent (fun k => ∑ u ∈ Finset.Icc (-3 : ℤ) (-1),
      mono (2 * qe * c2 u + ey * u) ((-1) ^ u * cy ^ u) * thSer (2 * qe) (5 * qe + 3 * qe * u) 1 k) :=
    Ent.sum _ fun u _ => (thSer_ent (h2qe hqe) _ one_ne_zero).smul _
  rw [InhS_eq hqe ey cy, show (fun k => (∑ r ∈ Finset.Icc (0 : ℤ) 1,
      monoS r (mono (5 * qe * r + 2 * qe * c2 r) ((-1) ^ r) * θ (h2qe hqe) (3 * qe * r + ey) cy) k) -
    ∑ u ∈ Finset.Icc (-3 : ℤ) (-1),
      mono (2 * qe * c2 u + ey * u) ((-1) ^ u * cy ^ u) * thSer (2 * qe) (5 * qe + 3 * qe * u) 1 k) =
    (fun k => ∑ r ∈ Finset.Icc (0 : ℤ) 1,
      monoS r (mono (5 * qe * r + 2 * qe * c2 r) ((-1) ^ r) * θ (h2qe hqe) (3 * qe * r + ey) cy) k) -
    (fun k => ∑ u ∈ Finset.Icc (-3 : ℤ) (-1),
      mono (2 * qe * c2 u + ey * u) ((-1) ^ u * cy ^ u) * thSer (2 * qe) (5 * qe + 3 * qe * u) 1 k) from rfl,
    ev_sub h1 h2, ev_sum _ (fun r _ => ent_monoS _ _), ev_sum _ (fun u _ =>
      (thSer_ent (h2qe hqe) _ one_ne_zero).smul _)]
  unfold InhV
  congr 1
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [ev_monoS]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [ev_smul (thSer_ent (h2qe hqe) _ one_ne_zero), thSer_ev (h2qe hqe) _ one_ne_zero, one_mul]

include hqe in
/-- **value-level functional equation of `f_{2,3,2}`**: `f(q⁵x) = μ_D x² f(x) + Inh(x)`. -/
theorem fV_FE (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (fS hqe ey cy) (ex + 5 * qe) cx =
      muD (qe := qe) ey cy * mono (2 * ex) (cx ^ (2 : ℤ)) * ev (fS hqe ey cy) ex cx + InhV hqe ey cy ex cx := by
  have hE := fS_ent hqe ey cy
  have hser : twist (fS hqe ey cy) (5 * qe) 1 =
      (fun k => muD (qe := qe) ey cy * shiftS (fS hqe ey cy) (-2) k) + InhS hqe ey cy := by
    funext k
    simp only [twist, one_zpow, Pi.add_apply, shiftS]
    rw [fS_rec hqe ey cy hcy k, show k + -2 = k - 2 by ring]
  have := ev_twist hE (5 * qe) 1 ex cx
  rw [mul_one, hser, ev_add ((hE.shift (-2)).smul _) (InhS_ent hqe ey cy), ev_smul (hE.shift (-2)),
    MTC.ev_shift hE (-2) ex hcx, InhS_ev] at this
  rw [← this]
  simp only [mul_neg, neg_neg]
  ring

end FVal

end MTC.H232
