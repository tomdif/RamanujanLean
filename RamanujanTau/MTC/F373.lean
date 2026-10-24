/-
# The Hecke-type double sum `f_{3,7,3}(x, y, q)` as a series in `x`

Fix `q = t^{qe}` and `y = cy t^{ey}`. Then
`f_{3,7,3}(x,y,q) = Σ_{sg r = sg s} sg(r) (−1)^{r+s} x^r y^s q^{3C(r,2) + 7rs + 3C(s,2)} = Σ_k fS k · x^k`,
where `fS k = (−1)^k q^{3C(k,2)} S_k` and `S_k` is the restricted theta sum `Σ_{s ≥ 0}` (for `k ≥ 0`) or
`−Σ_{s < 0}` (for `k < 0`) of `(−1)^s q^{3C(s,2)} (q^{7k} y)^s`.

* `fS_ent` — entire.
* `fS_rec` — coefficient form of HM Prop 5.5:
  `fS k · q^{40k} = q^{66} y^{−7} fS (k − 3) + InhS k`.
-/
import RamanujanTau.MTC.Lambda

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

/-! ## Restricted theta sums -/

section Restricted
variable {N : ℕ} (hN : 1 ≤ N)
include hN

/-- `Σ_{s : P s} (−1)^s q^{C(s,2)} (c tᵉ)^s`. -/
noncomputable def thR (e : ℤ) (c : ℂ) (P : ℤ → Prop) [DecidablePred P] : L :=
  hs (monoFam (thE N e) (fun s => if P s then thC c s else 0) _ (thE_lb hN e) (thE_fin hN e))

lemma thR_compl (e : ℤ) (c : ℂ) (P : ℤ → Prop) [DecidablePred P] :
    thR hN e c P + thR hN e c (fun s => ¬ P s) = θ hN e c := by
  rw [thR, thR, hs, hs, ← SummableFamily.hsum_add, θ, hs]
  congr 1; ext s : 1
  simp only [SummableFamily.add_apply, monoFam_apply, thF]
  split_ifs <;> simp [mono]

/-- splitting off finitely many indices. -/
lemma thR_split (e : ℤ) (c : ℂ) (P Q : ℤ → Prop) [DecidablePred P] [DecidablePred Q] (s0 s1 : ℤ)
    (h : ∀ s, P s ↔ Q s ∨ (s0 ≤ s ∧ s ≤ s1)) (hd : ∀ s, Q s → ¬(s0 ≤ s ∧ s ≤ s1)) :
    thR hN e c P = thR hN e c Q + ∑ s ∈ Finset.Icc s0 s1, mono (thE N e s) (thC c s) := by
  classical
  rw [thR, thR, hs, hs]
  have hfin : (∑ s ∈ Finset.Icc s0 s1, mono (thE N e s) (thC c s) : L) =
      (SummableFamily.ofFinsupp (Finsupp.onFinset (Finset.Icc s0 s1)
        (fun s => if s0 ≤ s ∧ s ≤ s1 then mono (thE N e s) (thC c s) else 0) (fun s hs => by
          by_contra h'; rw [Finset.mem_Icc] at h'; exact hs (if_neg h')))).hsum := by
    rw [SummableFamily.hsum_ofFinsupp, Finsupp.onFinset_sum _ (fun _ => rfl)]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_Icc] at hs; simp [if_pos hs]
  rw [hfin, ← SummableFamily.hsum_add]
  congr 1; ext s : 1
  simp only [SummableFamily.add_apply, monoFam_apply, SummableFamily.coe_ofFinsupp, Finsupp.onFinset_apply]
  by_cases hq : Q s
  · rw [if_pos ((h s).mpr (Or.inl hq)), if_pos hq, if_neg (hd s hq)]; simp
  · rw [if_neg hq]
    by_cases hr : s0 ≤ s ∧ s ≤ s1
    · rw [if_pos ((h s).mpr (Or.inr hr)), if_pos hr]; simp [mono]
    · rw [if_neg (fun hp => (h s |>.mp hp).elim hq hr), if_neg hr]; simp [mono]

/-- shifting the argument by `q^{−a}` reindexes the restriction. -/
lemma thR_shift (e : ℤ) {c : ℂ} (hc : c ≠ 0) (a : ℤ) (P : ℤ → Prop) [DecidablePred P] :
    thR hN (e - N * a) c P =
      mono (e * a - N * c2 (a + 1)) ((-1) ^ a * c ^ a) * thR hN e c (fun u => P (u + a)) := by
  rw [thR, thR]
  refine hsum_reindex _ _ (Equiv.addRight a) _ fun u => ?_
  simp only [monoFam_apply, Equiv.coe_addRight]
  split_ifs with h
  · rw [mono_mul]
    simp only [thE, thC]
    congr 1
    · have e1 := two_c2 (u + a); have e2 := two_c2 u; have e3 := two_c2 (a + 1)
      have key : 2 * c2 (u + a) = 2 * (c2 u + a * u + c2 (a + 1) - a) := by
        linear_combination e1 - e2 - e3
      rw [mul_left_cancel₀ two_ne_zero key]
      linear_combination (N : ℤ) * e3
    · rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_add₀ hc]; ring
  · simp [mono]

lemma vge_thR (e : ℤ) (c : ℂ) (P : ℤ → Prop) [DecidablePred P] (B : ℤ) (hB : ∀ s, P s → B ≤ thE N e s) :
    vge (thR hN e c P) B := by
  refine vge_hs _ fun s => ?_
  simp only [monoFam_apply]
  split_ifs with h
  · exact vge_mono (vge_single _ _) (hB s h)
  · rw [show (mono (thE N e s) (0 : ℂ) : L) = 0 by simp [mono]]; exact vge_zero _

end Restricted

/-! ## The series of `f_{3,7,3}` -/

section F373
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

omit hqe in
lemma h3qe (hqe : 1 ≤ qe) : 1 ≤ 3 * qe := by omega

/-- `S_k`. -/
noncomputable def SK (k : ℤ) : L :=
  if 0 ≤ k then thR (h3qe hqe) (7 * qe * k + ey) cy (0 ≤ ·)
  else -thR (h3qe hqe) (7 * qe * k + ey) cy (· < 0)

/-- the coefficient of `x^k` in `f_{3,7,3}(x, y, q)`. -/
noncomputable def fS (k : ℤ) : L := mono (3 * qe * c2 k) ((-1) ^ k) * SK hqe ey cy k

lemma vge_SK (k : ℤ) : vge (SK hqe ey cy k) (-(ey * ey) - 1) := by
  unfold SK
  have hl := fun s => thE_lb (N := 3 * qe) (h3qe hqe) ey s
  split_ifs with hk
  · refine vge_thR _ _ _ _ _ fun s hs => ?_
    have hs' : 0 ≤ s := hs
    have := hl s; unfold thE at *
    have : 0 ≤ 7 * (qe : ℤ) * k * s := mul_nonneg (mul_nonneg (by positivity) hk) hs'
    nlinarith
  · refine vge_neg (vge_thR _ _ _ _ _ fun s hs => ?_)
    have hs' : s < 0 := hs
    have := hl s; unfold thE at *
    have : 0 ≤ 7 * (qe : ℤ) * k * s := by
      have : 0 ≤ (-k) * (-s) := mul_nonneg (by omega) (by omega)
      have hq : (0 : ℤ) ≤ 7 * qe := by positivity
      nlinarith
    nlinarith

lemma fS_ent : Ent (fS hqe ey cy) := by
  intro A
  have h3 : (1 : ℤ) ≤ 3 * qe := by exact_mod_cast h3qe hqe
  obtain ⟨C, hC⟩ := quad_dom h3 A
  refine ⟨C + ey * ey + 1, fun k => ?_⟩
  refine vge_mono (vge_mul (vge_single _ _) (vge_SK hqe ey cy k)) ?_
  have := hC k
  push_cast at this ⊢
  linarith

/-- the seven boundary terms `Σ_{u=−7}^{−1} (−1)^u q^{3C(u,2)} (q^{7k} y)^u`. -/
noncomputable def finK (k : ℤ) : L :=
  ∑ u ∈ Finset.Icc (-7 : ℤ) (-1), mono (thE (3 * qe) (7 * qe * k + ey) u) (thC cy u)

/-- the multiplier `−q^{−84} (q^{7k} y)^7`. -/
noncomputable def MK (k : ℤ) : L := mono (7 * (7 * qe * k + ey) - 3 * qe * c2 (7 + 1)) ((-1) ^ (7 : ℤ) * cy ^ (7 : ℤ))

include hqe in
lemma SK_rec (hcy : cy ≠ 0) (k : ℤ) :
    SK hqe ey cy (k - 3) = MK (qe := qe) ey cy k * (SK hqe ey cy k + finK (qe := qe) ey cy k) -
      (if 0 ≤ k ∧ k ≤ 2 then MK (qe := qe) ey cy k * θ (h3qe hqe) (7 * qe * k + ey) cy else 0) := by
  have harg : 7 * (qe : ℤ) * (k - 3) + ey = (7 * qe * k + ey) - ((3 * qe : ℕ) : ℤ) * 7 := by push_cast; ring
  have hsh := fun (P : ℤ → Prop) [DecidablePred P] =>
    thR_shift (h3qe hqe) (7 * qe * k + ey) hcy 7 P
  have hMK : mono ((7 * qe * k + ey) * 7 - ((3 * qe : ℕ) : ℤ) * c2 (7 + 1)) ((-1) ^ (7 : ℤ) * cy ^ (7 : ℤ)) =
      MK (qe := qe) ey cy k := by
    unfold MK; push_cast; congr 1; ring
  have hpos : thR (h3qe hqe) (7 * qe * k + ey) cy (fun u => 0 ≤ u + 7) =
      thR (h3qe hqe) (7 * qe * k + ey) cy (0 ≤ ·) + finK (qe := qe) ey cy k :=
    thR_split (h3qe hqe) _ _ _ _ (-7) (-1) (fun s => by omega) (fun s (hs : 0 ≤ s) => by omega)
  have hneg : thR (h3qe hqe) (7 * qe * k + ey) cy (· < 0) =
      thR (h3qe hqe) (7 * qe * k + ey) cy (fun u => u + 7 < 0) + finK (qe := qe) ey cy k :=
    thR_split (h3qe hqe) _ _ _ _ (-7) (-1) (fun s => by omega) (fun s (hs : s + 7 < 0) => by omega)
  have hcomp := thR_compl (h3qe hqe) (7 * qe * k + ey) cy (0 ≤ ·)
  have hlt : thR (h3qe hqe) (7 * qe * k + ey) cy (fun s => ¬ 0 ≤ s) =
      thR (h3qe hqe) (7 * qe * k + ey) cy (· < 0) := by
    unfold thR; congr 1; ext s : 1; simp only [monoFam_apply, not_le]
  unfold SK
  rw [harg]
  by_cases hk3 : 3 ≤ k
  · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), sub_zero, hsh, hMK, hpos]
  · by_cases hk0 : 0 ≤ k
    · rw [if_neg (by omega), if_pos hk0, if_pos ⟨hk0, by omega⟩, hsh, hMK]
      linear_combination (MK (qe := qe) ey cy k) * hneg - (MK (qe := qe) ey cy k) * hcomp +
        (MK (qe := qe) ey cy k) * hlt
    · rw [if_neg (by omega), if_neg hk0, if_neg (by omega), sub_zero, hsh, hMK]
      linear_combination (MK (qe := qe) ey cy k) * hneg

/-- the inhomogeneous coefficient. -/
noncomputable def InhS (k : ℤ) : L :=
  mono (40 * qe * k + 3 * qe * c2 k) ((-1) ^ k) *
    ((if 0 ≤ k ∧ k ≤ 2 then θ (h3qe hqe) (7 * qe * k + ey) cy else 0) - finK (qe := qe) ey cy k)

/-- `μ_D = q^{66} y^{−7}`. -/
noncomputable def muD : L := mono (66 * qe - 7 * ey) (cy ^ (-7 : ℤ))

include hqe in
/-- **coefficient form of HM Prop 5.5 for `f_{3,7,3}`**. -/
theorem fS_rec (hcy : cy ≠ 0) (k : ℤ) :
    fS hqe ey cy k * mono (40 * qe * k) 1 = muD (qe := qe) ey cy * fS hqe ey cy (k - 3) + InhS hqe ey cy k := by
  have hZ : muD (qe := qe) ey cy * mono (3 * qe * c2 (k - 3)) ((-1) ^ (k - 3)) * MK (qe := qe) ey cy k =
      mono (40 * qe * k + 3 * qe * c2 k) ((-1) ^ k) := by
    unfold muD MK
    rw [mono_mul, mono_mul]
    have e1 := two_c2 (k - 3); have e2 := two_c2 k
    have e8 : c2 (7 + 1) = 28 := by decide
    congr 1
    · have : c2 (k - 3) = c2 k - 3 * k + 6 := by
        have : 2 * c2 (k - 3) = 2 * (c2 k - 3 * k + 6) := by linear_combination e1 - e2
        exact mul_left_cancel₀ two_ne_zero this
      rw [this, e8]; ring
    · rw [show k - 3 = k + -3 by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      field_simp
  have hm : mono (3 * qe * c2 k) ((-1) ^ k) * mono (40 * qe * k) 1 =
      mono (40 * qe * k + 3 * qe * c2 k) ((-1) ^ k) := by rw [mono_mul]; congr 1 <;> ring
  unfold fS InhS
  rw [SK_rec hqe ey cy hcy k]
  by_cases hc : 0 ≤ k ∧ k ≤ 2
  · simp only [if_pos hc]
    linear_combination SK hqe ey cy k * hm -
      (SK hqe ey cy k + finK (qe := qe) ey cy k - θ (h3qe hqe) (7 * qe * k + ey) cy) * hZ
  · simp only [if_neg hc]
    linear_combination SK hqe ey cy k * hm - (SK hqe ey cy k + finK (qe := qe) ey cy k) * hZ

end F373

end MTC
