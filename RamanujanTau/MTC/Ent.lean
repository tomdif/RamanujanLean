/-
# Entire bilateral series over `ℂ((t))`

Infrastructure for the Mock Theta Conjectures campaign (`MTC_GAP_MAP.md`, step L2). A bilateral series in a
variable `x` with coefficients in `L = ℂ((t))` is a function `F : ℤ → L`. It is *entire* (`Ent`) when its
coefficient valuations grow faster than every linear function: `val(F k) ≥ A·|k| − C` for each `A`.

Entire series can be evaluated at every monomial point `x = c·tᵉ` (`ev`). They are closed under sums, products
(`conv`, the Cauchy product), shifts and monomial twists. Evaluation is additive and multiplicative. The
**identity principle** (`eq_zero_of_ev`) says an entire series whose values vanish at `c·tᵉ` for infinitely
many `c` is zero.
-/
import RamanujanTau.ALBase

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

/-! ## Lower bounds on supports -/

/-- every nonzero coefficient of `f` sits at index `≥ n`. -/
def vge (f : L) (n : ℤ) : Prop := ∀ m, f.coeff m ≠ 0 → n ≤ m

lemma vge_zero (n : ℤ) : vge 0 n := fun m h => by simp at h

lemma vge_mono {f : L} {n n' : ℤ} (h : vge f n) (hn : n' ≤ n) : vge f n' := fun m hm => hn.trans (h m hm)

lemma vge_add {f g : L} {n : ℤ} (hf : vge f n) (hg : vge g n) : vge (f + g) n := fun m hm => by
  rw [coeff_add] at hm
  by_cases h : f.coeff m = 0
  · rw [h, zero_add] at hm; exact hg m hm
  · exact hf m h

lemma vge_neg {f : L} {n : ℤ} (hf : vge f n) : vge (-f) n := fun m hm => by
  rw [coeff_neg, neg_ne_zero] at hm; exact hf m hm

lemma vge_sub {f g : L} {n : ℤ} (hf : vge f n) (hg : vge g n) : vge (f - g) n := by
  rw [sub_eq_add_neg]; exact vge_add hf (vge_neg hg)

lemma vge_mul {f g : L} {a b : ℤ} (hf : vge f a) (hg : vge g b) : vge (f * g) (a + b) := by
  intro m hm
  by_contra hlt
  push Not at hlt
  apply hm
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [mem_addAntidiagonal] at hij
  obtain ⟨hi, hj, hsum⟩ := hij
  have h1 := hf ij.1 (by simpa using hi)
  have h2 := hg ij.2 (by simpa using hj)
  omega

lemma vge_single (e : ℤ) (c : ℂ) : vge (mono e c) e := fun m hm => by
  by_contra h
  exact hm (by simp [mono, coeff_single_of_ne (show m ≠ e by omega)])

lemma vge_hs {ι : Type*} (s : SummableFamily ℤ ℂ ι) {n : ℤ} (h : ∀ i, vge (s i) n) : vge (hs s) n := by
  intro m hm
  have := SummableFamily.support_hsum_subset (s := s) (show m ∈ (hs s).support from hm)
  simp only [Set.mem_iUnion, HahnSeries.mem_support] at this
  obtain ⟨i, hi⟩ := this
  exact h i m hi

/-- every Laurent series is bounded below. -/
lemma exists_vge (f : L) : ∃ n, vge f n := by
  by_cases hf : f = 0
  · exact ⟨0, by rw [hf]; exact vge_zero 0⟩
  · refine ⟨f.order, fun m hm => ?_⟩
    by_contra h
    exact hm (HahnSeries.coeff_eq_zero_of_lt_order (lt_of_not_ge h))

/-! ## Entire series -/

/-- `F` is entire: for every slope `A` there is `C` with `val(F k) ≥ A|k| − C`. -/
def Ent (F : ℤ → L) : Prop := ∀ A : ℤ, ∃ C : ℤ, ∀ k, vge (F k) (A * |k| - C)

lemma Ent.bdd {F : ℤ → L} (hF : Ent F) : ∃ C : ℤ, ∀ k, vge (F k) (-C) := by
  obtain ⟨C, hC⟩ := hF 0
  exact ⟨C, fun k => by simpa using hC k⟩

lemma ent_zero : Ent (fun _ : ℤ => (0 : L)) := fun _ => ⟨0, fun _ => vge_zero _⟩

lemma Ent.add {F G : ℤ → L} (hF : Ent F) (hG : Ent G) : Ent (F + G) := fun A => by
  obtain ⟨C1, h1⟩ := hF A; obtain ⟨C2, h2⟩ := hG A
  refine ⟨max C1 C2, fun k => vge_add (vge_mono (h1 k) ?_) (vge_mono (h2 k) ?_)⟩ <;> omega

lemma Ent.neg {F : ℤ → L} (hF : Ent F) : Ent (-F) := fun A => by
  obtain ⟨C, h⟩ := hF A; exact ⟨C, fun k => vge_neg (h k)⟩

lemma Ent.sub {F G : ℤ → L} (hF : Ent F) (hG : Ent G) : Ent (F - G) := by
  rw [sub_eq_add_neg]; exact hF.add hG.neg

/-- multiplying every coefficient by a fixed series. -/
lemma Ent.smul {F : ℤ → L} (hF : Ent F) (a : L) : Ent (fun k => a * F k) := fun A => by
  obtain ⟨n, hn⟩ := exists_vge a
  obtain ⟨C, h⟩ := hF A
  exact ⟨C - n, fun k => vge_mono (vge_mul hn (h k)) (by omega)⟩

lemma Ent.sum {ι : Type*} (s : Finset ι) {F : ι → ℤ → L} (hF : ∀ i ∈ s, Ent (F i)) :
    Ent (fun k => ∑ i ∈ s, F i k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ent_zero
  | insert a s ha ih =>
      have h := (hF a (mem_insert_self a s)).add (ih fun i hi => hF i (mem_insert_of_mem hi))
      simpa [sum_insert ha] using h

/-! ## Evaluation at monomial points -/

section Ev

lemma ev_lb {F : ℤ → L} (hF : Ent F) (e : ℤ) (c : ℂ) :
    ∃ C : ℤ, ∀ k n, (F k * mono (e * k) (c ^ k)).coeff n ≠ 0 → |k| - C ≤ n := by
  obtain ⟨C, hC⟩ := hF (|e| + 1)
  refine ⟨C, fun k n hn => ?_⟩
  have h := vge_mul (hC k) (vge_single (e * k) (c ^ k)) n hn
  have : -(|e| * |k|) ≤ e * k := by
    rw [← abs_mul]; exact neg_abs_le _
  nlinarith

/-- the summable family `k ↦ F k · (c tᵉ)ᵏ`. -/
noncomputable def evFam {F : ℤ → L} (hF : Ent F) (e : ℤ) (c : ℂ) : SummableFamily ℤ ℂ ℤ :=
  ofSupp (fun k => F k * mono (e * k) (c ^ k)) (-(Classical.choose (ev_lb hF e c)))
    (fun k n hn => by
      by_contra h
      have := Classical.choose_spec (ev_lb hF e c) k n h
      have : 0 ≤ |k| := abs_nonneg k
      omega)
    (fun n => (Set.finite_Icc (-(n + Classical.choose (ev_lb hF e c)))
        (n + Classical.choose (ev_lb hF e c))).subset fun k hk => by
      have := Classical.choose_spec (ev_lb hF e c) k n hk
      have h2 : |k| ≤ n + Classical.choose (ev_lb hF e c) := by linarith
      exact ⟨(abs_le.mp h2).1, (abs_le.mp h2).2⟩)

/-- the value of an entire series at `x = c tᵉ` (zero for non-entire input). -/
noncomputable def ev (F : ℤ → L) (e : ℤ) (c : ℂ) : L := by
  classical
  exact if h : Ent F then hs (evFam h e c) else 0

lemma ev_eq {F : ℤ → L} (hF : Ent F) (e : ℤ) (c : ℂ) : ev F e c = hs (evFam hF e c) := by
  unfold ev; rw [dif_pos hF]

@[simp] lemma evFam_apply {F : ℤ → L} (hF : Ent F) (e : ℤ) (c : ℂ) (k : ℤ) :
    evFam hF e c k = F k * mono (e * k) (c ^ k) := rfl

lemma ev_add {F G : ℤ → L} (hF : Ent F) (hG : Ent G) (e : ℤ) (c : ℂ) :
    ev (F + G) e c = ev F e c + ev G e c := by
  rw [ev_eq hF, ev_eq hG, ev_eq (hF.add hG), hs, hs, hs, ← SummableFamily.hsum_add]
  congr 1; ext k : 1
  simp [add_mul]

lemma ev_zero (e : ℤ) (c : ℂ) : ev (fun _ => (0 : L)) e c = 0 := by
  rw [ev_eq ent_zero, hs]
  ext n
  simp [SummableFamily.coeff_hsum]

lemma ev_neg {F : ℤ → L} (hF : Ent F) (e : ℤ) (c : ℂ) : ev (-F) e c = -ev F e c := by
  have h := ev_add hF hF.neg e c
  rw [show F + -F = fun _ => (0 : L) from by ext; simp, ev_zero] at h
  linear_combination -h

lemma ev_sub {F G : ℤ → L} (hF : Ent F) (hG : Ent G) (e : ℤ) (c : ℂ) :
    ev (F - G) e c = ev F e c - ev G e c := by
  rw [sub_eq_add_neg, ev_add hF hG.neg, ev_neg hG, sub_eq_add_neg]

lemma ev_smul {F : ℤ → L} (hF : Ent F) (a : L) (e : ℤ) (c : ℂ) :
    ev (fun k => a * F k) e c = a * ev F e c := by
  rw [ev_eq hF, ev_eq (hF.smul a), hs, hs, ← SummableFamily.hsum_smul]
  congr 1; ext k : 1
  simp [HahnSeries.of_symm_smul_of_eq_mul, mul_assoc]

lemma ev_sum {ι : Type*} (s : Finset ι) {F : ι → ℤ → L} (hF : ∀ i ∈ s, Ent (F i)) (e : ℤ) (c : ℂ) :
    ev (fun k => ∑ i ∈ s, F i k) e c = ∑ i ∈ s, ev (F i) e c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact ev_zero e c
  | insert a s ha ih =>
      have hs' : ∀ i ∈ s, Ent (F i) := fun i hi => hF i (mem_insert_of_mem hi)
      rw [sum_insert ha, ← ih hs', ← ev_add (hF a (mem_insert_self a s)) (Ent.sum s hs')]
      congr 1; ext k; simp [sum_insert ha]

end Ev

end MTC
