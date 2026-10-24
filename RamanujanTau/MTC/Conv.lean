/-
# Products, shifts and the identity principle for entire bilateral series

* `conv F G` — the Cauchy product `(F ⋆ G) k = Σ_i F i · G (k − i)`; entire, and `ev (F ⋆ G) = ev F · ev G`.
* `shiftS F a` (`k ↦ F (k + a)`, value `x^{−a}·F(x)`) and `twist F eQ cQ` (`k ↦ F k · (cQ t^{eQ})ᵏ`, value `F(cQ t^{eQ} x)`).
* `eq_zero_of_ev` — the identity principle: an entire series vanishing at `c tᵉ` for infinitely many `c` is `0`.
-/
import RamanujanTau.MTC.Ent

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

/-! ## Cauchy product -/

section Conv

lemma conv_lb {F G : ℤ → L} (hF : Ent F) (hG : Ent G) :
    ∃ C : ℤ, ∀ k i n, (F i * G (k - i)).coeff n ≠ 0 → |i| - C ≤ n := by
  obtain ⟨C1, h1⟩ := hF 1
  obtain ⟨C2, h2⟩ := hG.bdd
  refine ⟨C1 + C2, fun k i n hn => ?_⟩
  have := vge_mul (h1 i) (h2 (k - i)) n hn
  linarith

/-- the family `i ↦ F i · G (k − i)`. -/
noncomputable def convFam {F G : ℤ → L} (hF : Ent F) (hG : Ent G) (k : ℤ) : SummableFamily ℤ ℂ ℤ :=
  ofSupp (fun i => F i * G (k - i)) (-(Classical.choose (conv_lb hF hG)))
    (fun i n hn => by
      by_contra h
      have := Classical.choose_spec (conv_lb hF hG) k i n h
      have : 0 ≤ |i| := abs_nonneg i
      omega)
    (fun n => (Set.finite_Icc (-(n + Classical.choose (conv_lb hF hG)))
        (n + Classical.choose (conv_lb hF hG))).subset fun i hi => by
      have := Classical.choose_spec (conv_lb hF hG) k i n hi
      have h2 : |i| ≤ n + Classical.choose (conv_lb hF hG) := by linarith
      exact ⟨(abs_le.mp h2).1, (abs_le.mp h2).2⟩)

@[simp] lemma convFam_apply {F G : ℤ → L} (hF : Ent F) (hG : Ent G) (k i : ℤ) :
    convFam hF hG k i = F i * G (k - i) := rfl

/-- the Cauchy product (zero unless both factors are entire). -/
noncomputable def conv (F G : ℤ → L) : ℤ → L := by
  classical
  exact if h : Ent F ∧ Ent G then fun k => hs (convFam h.1 h.2 k) else fun _ => 0

lemma conv_eq {F G : ℤ → L} (hF : Ent F) (hG : Ent G) (k : ℤ) : conv F G k = hs (convFam hF hG k) := by
  unfold conv; rw [dif_pos ⟨hF, hG⟩]

lemma Ent.conv {F G : ℤ → L} (hF : Ent F) (hG : Ent G) : Ent (MTC.conv F G) := fun A => by
  obtain ⟨C1, h1⟩ := hF (max A 0)
  obtain ⟨C2, h2⟩ := hG (max A 0)
  refine ⟨C1 + C2, fun k => ?_⟩
  rw [conv_eq hF hG]
  refine vge_hs _ fun i => ?_
  refine vge_mono (vge_mul (h1 i) (h2 (k - i))) ?_
  have htri : |k| ≤ |i| + |k - i| := by
    have := abs_add_le i (k - i); rwa [add_sub_cancel] at this
  have hA : A * |k| ≤ max A 0 * |k| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  have hB : max A 0 * |k| ≤ max A 0 * (|i| + |k - i|) := mul_le_mul_of_nonneg_left htri (le_max_right _ _)
  linarith

/-- reindexing `(i, j) ↦ (i + j, i)`. -/
def diagE : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1 + p.2, p.1)
  invFun p := (p.2, p.1 - p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

/-- **evaluation is multiplicative** (at nonzero points). -/
theorem ev_conv {F G : ℤ → L} (hF : Ent F) (hG : Ent G) (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    ev (MTC.conv F G) e c = ev F e c * ev G e c := by
  rw [ev_eq hF, ev_eq hG, ev_eq (hF.conv hG)]; simp only [hs]; rw [← SummableFamily.hsum_mul]
  set M := SummableFamily.Equiv diagE (SummableFamily.mul (evFam hF e c) (evFam hG e c))
  have hM : M.hsum = (SummableFamily.mul (evFam hF e c) (evFam hG e c)).hsum :=
    SummableFamily.hsum_equiv _ _
  rw [← hM]
  refine (hsum_fubini M (evFam (hF.conv hG) e c) (fun k => mono (e * k) (c ^ k) • convFam hF hG k)
    (fun k i => ?_) (fun k => ?_)).symm
  · simp only [M, SummableFamily.Equiv_toFun, SummableFamily.smul_apply,
      HahnSeries.of_symm_smul_of_eq_mul, convFam_apply, SummableFamily.mul_eq_smul]
    change mono (e * k) (c ^ k) * (F i * G (k - i)) =
      (F (diagE.symm (k, i)).1 * mono (e * (diagE.symm (k, i)).1) (c ^ (diagE.symm (k, i)).1)) *
      (G (diagE.symm (k, i)).2 * mono (e * (diagE.symm (k, i)).2) (c ^ (diagE.symm (k, i)).2))
    simp only [diagE, Equiv.coe_fn_symm_mk]
    have hm : mono (e * i) (c ^ i) * mono (e * (k - i)) (c ^ (k - i)) = mono (e * k) (c ^ k) := by
      rw [mono_mul, ← zpow_add₀ hc]; congr 1 <;> ring_nf
    linear_combination (F i * G (k - i)) * hm.symm
  · rw [evFam_apply, conv_eq hF hG, hs, hs, SummableFamily.hsum_smul, mul_comm]

end Conv

/-! ## Shifts, twists, monomials -/

section Shift

/-- `k ↦ F (k + a)`: the series of `x^{−a} F(x)`. -/
def shiftS (F : ℤ → L) (a : ℤ) : ℤ → L := fun k => F (k + a)

lemma Ent.shift {F : ℤ → L} (hF : Ent F) (a : ℤ) : Ent (shiftS F a) := fun A => by
  obtain ⟨C, h⟩ := hF (max A 0)
  refine ⟨C + max A 0 * |a|, fun k => vge_mono (h (k + a)) ?_⟩
  have t1 : |k| ≤ |k + a| + |a| := by
    have := abs_sub_le k (k + a) 0
    simp at this; linarith [abs_neg a, abs_sub_comm (k + a) k]
  have hA : A * |k| ≤ max A 0 * |k| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  have hB : max A 0 * |k| ≤ max A 0 * (|k + a| + |a|) := mul_le_mul_of_nonneg_left t1 (le_max_right _ _)
  have hm := mul_add (max A 0) |k + a| |a|
  linarith

lemma ev_shift {F : ℤ → L} (hF : Ent F) (a e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    ev (shiftS F a) e c = mono (-(e * a)) (c ^ (-a)) * ev F e c := by
  rw [ev_eq hF, ev_eq (hF.shift a)]
  refine hsum_reindex (evFam hF e c) (evFam (hF.shift a) e c) (Equiv.addRight (-a)) _ fun i => ?_
  simp only [evFam_apply, shiftS, Equiv.coe_addRight, neg_add_cancel_right]
  have : mono (e * (i + -a)) (c ^ (i + -a)) = mono (-(e * a)) (c ^ (-a)) * mono (e * i) (c ^ i) := by
    rw [mono_mul, ← zpow_add₀ hc]; congr 1 <;> ring_nf
  rw [this]; ring

/-- `k ↦ F k · (cQ t^{eQ})ᵏ`: the series of `F(cQ t^{eQ} x)`. -/
noncomputable def twist (F : ℤ → L) (eQ : ℤ) (cQ : ℂ) : ℤ → L := fun k => F k * mono (eQ * k) (cQ ^ k)

lemma Ent.twist {F : ℤ → L} (hF : Ent F) (eQ : ℤ) (cQ : ℂ) : Ent (twist F eQ cQ) := fun A => by
  obtain ⟨C, h⟩ := hF (A + |eQ|)
  refine ⟨C, fun k => vge_mono (vge_mul (h k) (vge_single _ _)) ?_⟩
  have : -(|eQ| * |k|) ≤ eQ * k := by rw [← abs_mul]; exact neg_abs_le _
  nlinarith

lemma ev_twist {F : ℤ → L} (hF : Ent F) (eQ : ℤ) (cQ : ℂ) (e : ℤ) (c : ℂ) :
    ev (twist F eQ cQ) e c = ev F (e + eQ) (c * cQ) := by
  rw [ev_eq hF, ev_eq (hF.twist eQ cQ)]
  refine hsum_congr _ _ fun k => ?_
  simp only [evFam_apply, twist]
  rw [mul_assoc, mono_mul, mul_zpow]; congr 2 <;> ring

/-- the monomial series `b·xᵃ`. -/
noncomputable def monoS (a : ℤ) (b : L) : ℤ → L := fun k => if k = a then b else 0

lemma ent_monoS (a : ℤ) (b : L) : Ent (monoS a b) := fun A => by
  obtain ⟨n, hn⟩ := exists_vge b
  refine ⟨A * |a| - n, fun k => ?_⟩
  unfold monoS
  split_ifs with h
  · subst h; exact vge_mono hn (by omega)
  · exact vge_zero _

lemma ev_monoS (a : ℤ) (b : L) (e : ℤ) (c : ℂ) : ev (monoS a b) e c = b * mono (e * a) (c ^ a) := by
  classical
  rw [ev_eq (ent_monoS a b), hs]
  have : evFam (ent_monoS a b) e c = SummableFamily.single a (b * mono (e * a) (c ^ a)) := by
    ext k : 1
    simp only [evFam_apply, monoS, SummableFamily.single]
    split_ifs with h <;> simp [h]
  rw [this, SummableFamily.hsum_single]

end Shift

/-! ## Monomial substitution `x ↦ b·x^d` -/

section Subst

/-- the series of `G(cb t^{eb} x^d)`. -/
noncomputable def subst (G : ℤ → L) (d : ℤ) (eb : ℤ) (cb : ℂ) : ℤ → L := fun k => by
  classical
  exact if d ∣ k then G (k / d) * mono (eb * (k / d)) (cb ^ (k / d)) else 0

lemma Ent.subst {G : ℤ → L} (hG : Ent G) {d : ℤ} (hd : d ≠ 0) (eb : ℤ) (cb : ℂ) : Ent (subst G d eb cb) :=
  fun A => by
  obtain ⟨C, h⟩ := hG (|A| * |d| + |eb|)
  refine ⟨C, fun k => ?_⟩
  unfold MTC.subst
  split_ifs with hk
  · obtain ⟨j, rfl⟩ := hk
    rw [Int.mul_ediv_cancel_left _ hd]
    refine vge_mono (vge_mul (h j) (vge_single _ _)) ?_
    have h1 : -(|eb| * |j|) ≤ eb * j := by rw [← abs_mul]; exact neg_abs_le _
    have h2 : A * |d * j| ≤ |A| * |d| * |j| := by
      rw [abs_mul, ← mul_assoc]; exact (le_abs_self _).trans (by rw [abs_mul, abs_mul, abs_abs, abs_abs])
    nlinarith
  · exact vge_zero _

lemma ev_subst {G : ℤ → L} (hG : Ent G) {d : ℤ} (hd : d ≠ 0) (eb : ℤ) (cb : ℂ) (e : ℤ) (c : ℂ) : ev (subst G d eb cb) e c = ev G (eb + d * e) (cb * c ^ d) := by
  rw [ev_eq hG, ev_eq (hG.subst hd eb cb), hs, hs]
  have hinj : Function.Injective (fun j : ℤ => d * j) := fun a b h => mul_left_cancel₀ hd h
  have : evFam (hG.subst hd eb cb) e c = (evFam hG (eb + d * e) (cb * c ^ d)).embDomain ⟨_, hinj⟩ := by
    ext k : 1
    by_cases hk : d ∣ k
    · obtain ⟨j, rfl⟩ := hk
      rw [show d * j = (⟨_, hinj⟩ : ℤ ↪ ℤ) j from rfl, SummableFamily.embDomain_image]
      simp only [Function.Embedding.coeFn_mk, evFam_apply, MTC.subst, dvd_mul_right, if_true,
        Int.mul_ediv_cancel_left _ hd]
      rw [mul_assoc, mono_mul, mul_zpow, ← zpow_mul]
      congr 2 <;> ring_nf
    · rw [SummableFamily.embDomain_notin_range]
      · simp [MTC.subst, hk]
      · rintro ⟨j, hj⟩; exact hk ⟨j, hj.symm⟩
  rw [this, SummableFamily.hsum_embDomain]

end Subst

/-! ## Identity principle -/

section Identity

open Polynomial in
/-- a Laurent polynomial `Σ_{|k|≤B} a_k cᵏ` vanishing on an infinite set is zero. -/
lemma laurent_vanish (B : ℕ) (a : ℤ → ℂ) (S : Set ℂ) (hS : S.Infinite)
    (h : ∀ c ∈ S, ∑ k ∈ Finset.Icc (-(B : ℤ)) B, a k * c ^ k = 0) (k0 : ℤ) (hk0 : |k0| ≤ B) : a k0 = 0 := by
  classical
  set P : ℂ[X] := ∑ k ∈ Finset.Icc (-(B : ℤ)) B, C (a k) * X ^ (k + B).toNat
  have hroot : ∀ c ∈ S \ {0}, P.IsRoot c := by
    intro c hc
    have hc0 : c ≠ 0 := hc.2
    have := h c hc.1
    simp only [IsRoot, P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    have hpow : ∀ k ∈ Finset.Icc (-(B : ℤ)) B, a k * c ^ (k + B).toNat = c ^ (B : ℕ) * (a k * c ^ k) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_add₀ hc0, zpow_natCast]; ring
    rw [Finset.sum_congr rfl hpow, ← Finset.mul_sum, this, mul_zero]
  have hP : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P
    ((hS.diff (Set.finite_singleton 0)).mono fun c hc => hroot c hc)
  have hcoef := congrArg (fun p => Polynomial.coeff p (k0 + B).toNat) hP
  simp only [P, finsetSum_coeff, coeff_C_mul, coeff_X_pow, Polynomial.coeff_zero] at hcoef
  rw [Finset.sum_eq_single k0] at hcoef
  · simpa using hcoef
  · intro k hk hne
    rw [Finset.mem_Icc] at hk
    have := abs_le.mp hk0
    rw [if_neg (by omega), mul_zero]
  · intro h; exfalso; exact h (Finset.mem_Icc.mpr ⟨by rw [abs_le] at hk0; omega, by rw [abs_le] at hk0; omega⟩)

/-- **identity principle**: an entire series vanishing at `c tᵉ` for infinitely many `c` is zero. -/
theorem eq_zero_of_ev {G : ℤ → L} (hG : Ent G) (e : ℤ) (S : Set ℂ) (hS : S.Infinite)
    (h : ∀ c ∈ S, ev G e c = 0) : G = fun _ => 0 := by
  classical
  funext k0
  ext n0
  simp only [HahnSeries.coeff_zero]
  set m := n0 + e * k0
  obtain ⟨C, hC⟩ := hG (|e| + 1)
  set B : ℕ := (m + C).toNat
  have hsupp : ∀ k, (G k).coeff (m - e * k) ≠ 0 → |k| ≤ B := by
    intro k hk
    have h1 := hC k _ hk
    have : -(|e| * |k|) ≤ e * k := by rw [← abs_mul]; exact neg_abs_le _
    have : |k| ≤ m + C := by nlinarith
    omega
  have hmk : m - e * k0 = n0 := by simp only [m]; ring
  by_cases hz : (G k0).coeff n0 = 0
  · exact hz
  have hk0 : |k0| ≤ B := hsupp k0 (by rwa [hmk])
  have key := laurent_vanish B (fun k => (G k).coeff (m - e * k)) S hS (fun c hc => ?_) k0 hk0
  · simpa [hmk] using key
  have hv := congrArg (fun f : L => f.coeff m) (h c hc)
  simp only [ev_eq hG, hs, SummableFamily.coeff_hsum, evFam_apply, HahnSeries.coeff_zero] at hv
  rw [finsum_eq_sum_of_support_subset (s := Finset.Icc (-(B : ℤ)) B)] at hv
  · rw [← hv]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mono, HahnSeries.coeff_mul_single]
  · intro k hk
    rw [Function.mem_support, mono, HahnSeries.coeff_mul_single] at hk
    have := abs_le.mp (hsupp k (left_ne_zero_of_mul hk))
    exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

end Identity

end MTC
