import RamanujanTau.KatzForms.Basic
import RamanujanTau.AtkinOBrien.Newton

/-!
# Lifting supersingular test points with prescribed `‖E‖` (step (K), geometric input)

`K` is complete, ultrametric and algebraically closed.

* `exists_root_near`: a polynomial with integral coefficients, one coefficient a unit, and `‖g(b)‖ < 1`
  has a root `s` with `‖s − b‖ < 1`. This is the Newton dominant-term theorem
  (`AtkinOBrien.Newton.dominant`) at a radius just below `1`.
* `exists_lift`: let `E` be integral and isobaric (for weights `4, 6`) with a unit coefficient, `x₀` an
  integral point with `‖x₀₀³ − x₀₁²‖ = 1` and `‖E(x₀)‖ < 1`, and `‖c‖ < 1`. Then some integral `x ≡ x₀`
  has `E(x) = c`. One coordinate of `x₀` is a unit; the other varies along a line, on which `E` restricts
  to a polynomial with a unit coefficient (by isobaricity).
* `exists_norm_between`: the value group is dense in `(0, 1]`.
* `detectsNear_of_ss`: if `P` attains its Gauss norm at a supersingular point (`SSDetect`), then
  `DetectsNear Good E P`, the hypothesis of `katz_iff`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace KatzForms
open Polynomial Filter Topology

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-! ### Univariate integral polynomials -/

/-- Gauss norm of a univariate polynomial. -/
noncomputable def pgn (g : K[X]) : ℝ := ((g.support.sup fun n => ‖g.coeff n‖₊ : NNReal) : ℝ)

lemma pgn_nonneg (g : K[X]) : 0 ≤ pgn g := NNReal.coe_nonneg _

lemma norm_coeff_le_pgn (g : K[X]) (n : ℕ) : ‖g.coeff n‖ ≤ pgn g := by
  by_cases hn : n ∈ g.support
  · have : ‖g.coeff n‖₊ ≤ g.support.sup fun n => ‖g.coeff n‖₊ :=
      Finset.le_sup (f := fun n => ‖g.coeff n‖₊) hn
    exact_mod_cast this
  · rw [notMem_support_iff.mp hn, norm_zero]; exact pgn_nonneg g

lemma exists_coeff_eq_pgn (g : K[X]) : ∃ n, ‖g.coeff n‖ = pgn g := by
  by_cases hs : g.support.Nonempty
  · obtain ⟨n, _, hn⟩ := Finset.exists_mem_eq_sup _ hs fun n => ‖g.coeff n‖₊
    exact ⟨n, by unfold pgn; rw [hn]; rfl⟩
  · rw [Finset.not_nonempty_iff_eq_empty, support_eq_empty] at hs
    exact ⟨0, by simp [hs, pgn]⟩

/-- Integral polynomials. -/
def IntPoly (g : K[X]) : Prop := ∀ n, ‖g.coeff n‖ ≤ 1

lemma IntPoly.mul {g h : K[X]} (hg : IntPoly g) (hh : IntPoly h) : IntPoly (g * h) := by
  intro n
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hg _) (norm_nonneg _) (hh _)

lemma IntPoly.one : IntPoly (1 : K[X]) := by
  intro n; rw [coeff_one]; split_ifs <;> simp

lemma IntPoly.pow {g : K[X]} (hg : IntPoly g) (e : ℕ) : IntPoly (g ^ e) := by
  induction e with
  | zero => rw [pow_zero]; exact IntPoly.one
  | succ e ih => rw [pow_succ]; exact ih.mul hg

lemma intPoly_X_add_C {b : K} (hb : ‖b‖ ≤ 1) : IntPoly (X + C b) := by
  intro n
  rw [coeff_add, coeff_X, coeff_C]
  rcases n with _ | _ | n <;> simp [hb]

lemma intPoly_X_sub_C {b : K} (hb : ‖b‖ ≤ 1) : IntPoly (X - C b) := by
  rw [sub_eq_add_neg, ← C_neg]; exact intPoly_X_add_C (by rwa [norm_neg])

/-- Substituting an integral polynomial does not increase coefficient bounds. -/
lemma coeff_comp_le {g q : K[X]} {C' : ℝ} (hC : 0 ≤ C') (hg : ∀ n, ‖g.coeff n‖ ≤ C')
    (hq : IntPoly q) (n : ℕ) : ‖(g.comp q).coeff n‖ ≤ C' := by
  rw [comp_eq_sum_left, Polynomial.sum, finsetSum_coeff]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun e _ => ?_
  rw [coeff_C_mul, norm_mul]
  calc ‖g.coeff e‖ * ‖(q ^ e).coeff n‖ ≤ C' * 1 :=
        mul_le_mul (hg e) (hq.pow e n) (norm_nonneg _) hC
    _ = C' := mul_one _

/-! ### Roots near the origin (Newton) -/

lemma split_prod [IsAlgClosed K] {g : K[X]} (hg : g ≠ 0) :
    ∃ (N : ℕ) (rt : Fin N → K), N = g.natDegree ∧ (∀ i, g.IsRoot (rt i)) ∧
      g = C g.leadingCoeff * ∏ i, (X - C (rt i)) := by
  set l := g.roots.toList
  refine ⟨l.length, fun i => l[i.1], ?_, fun i => ?_, ?_⟩
  · rw [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree]
  · have : l[i.1] ∈ l := List.getElem_mem _
    exact (mem_roots hg).mp (Multiset.mem_toList.mp this)
  · rw [Fin.prod_univ_fun_getElem l (fun a => X - C a)]
    have hl : (l.map fun a => X - C a).prod = (g.roots.map fun a => X - C a).prod := by
      rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
    rw [hl, C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree]

/-- **Root near `0`.** -/
theorem exists_small_root [IsAlgClosed K] {g : K[X]} (hint : IntPoly g) {n : ℕ}
    (hn : ‖g.coeff n‖ = 1) (h0 : ‖g.coeff 0‖ < 1) : ∃ s, ‖s‖ < 1 ∧ g.IsRoot s := by
  classical
  have hex : ∃ n, ‖g.coeff n‖ = 1 := ⟨n, hn⟩
  set m := Nat.find hex with hm
  have hmu : ‖g.coeff m‖ = 1 := Nat.find_spec hex
  have hlow : ∀ j < m, ‖g.coeff j‖ < 1 := fun j hj =>
    lt_of_le_of_ne (hint j) (Nat.find_min hex hj)
  have hm0 : m ≠ 0 := by
    intro h; rw [h] at hmu; linarith
  have hg : g ≠ 0 := by
    intro h; rw [h, coeff_zero, norm_zero] at hmu; exact zero_ne_one hmu
  -- choose the radius
  have ev : ∀ᶠ ρ in 𝓝 (1 : ℝ), 0 < ρ ∧ ∀ j ∈ Finset.range m, ‖g.coeff j‖ < ρ ^ m := by
    refine (eventually_gt_nhds one_pos).and ?_
    rw [Filter.eventually_all_finset]
    intro j hj
    have := ((continuous_pow m).tendsto (1 : ℝ))
    rw [one_pow] at this
    exact this.eventually_const_lt (hlow j (Finset.mem_range.mp hj))
  obtain ⟨ρ, ⟨hρ0, hρm⟩, hρ1⟩ :=
    ((ev.filter_mono (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))).and self_mem_nhdsWithin).exists
  have hρ1 : ρ < 1 := hρ1
  obtain ⟨N, rt, hN, hroot, hfac⟩ := split_prod hg
  set f := ∏ i, (X - C (rt i)) with hf
  set lc := g.leadingCoeff
  have hlc : lc ≠ 0 := leadingCoeff_ne_zero.mpr hg
  have hlc0 : 0 < ‖lc‖ := norm_pos_iff.mpr hlc
  have hcoef : ∀ j, ‖g.coeff j‖ = ‖lc‖ * ‖f.coeff j‖ := by
    intro j; conv_lhs => rw [hfac]
    rw [coeff_C_mul, norm_mul]
  have hmN : m ≤ Fintype.card (Fin N) := by
    rw [Fintype.card_fin, hN]
    exact le_natDegree_of_ne_zero (by intro h; rw [h, norm_zero] at hmu; exact zero_ne_one hmu)
  have hdom : ∀ j ≤ Fintype.card (Fin N), j ≠ m →
      ‖f.coeff j‖ * ρ ^ j < ‖f.coeff m‖ * ρ ^ m := by
    intro j _ hjm
    suffices ‖g.coeff j‖ * ρ ^ j < ‖g.coeff m‖ * ρ ^ m by
      rw [hcoef, hcoef, mul_assoc, mul_assoc] at this
      exact lt_of_mul_lt_mul_left this hlc0.le
    rw [hmu, one_mul]
    rcases lt_or_gt_of_ne hjm with hlt | hgt
    · calc ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff j‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hρ0.le hρ1.le) (norm_nonneg _)
        _ < ρ ^ m := by rw [mul_one]; exact hρm j (Finset.mem_range.mpr hlt)
    · calc ‖g.coeff j‖ * ρ ^ j ≤ 1 * ρ ^ j :=
            mul_le_mul_of_nonneg_right (hint j) (pow_nonneg hρ0.le _)
        _ < ρ ^ m := by rw [one_mul]; exact pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 hgt
  obtain ⟨hcount, -, -⟩ := AtkinOBrien.Newton.dominant rt ρ hρ0 m hmN hdom
  have hne : (Finset.univ.filter fun i => ‖rt i‖ < ρ).Nonempty := by
    rw [← Finset.card_pos, hcount]; exact Nat.pos_of_ne_zero hm0
  obtain ⟨i, hi⟩ := hne
  exact ⟨rt i, (Finset.mem_filter.mp hi).2.trans hρ1, hroot i⟩

/-- **Root near `b`.** -/
theorem exists_root_near [IsAlgClosed K] {g : K[X]} (hint : IntPoly g) {n : ℕ}
    (hn : ‖g.coeff n‖ = 1) {b : K} (hb : ‖b‖ ≤ 1) (hgb : ‖g.eval b‖ < 1) :
    ∃ s, ‖s - b‖ < 1 ∧ g.IsRoot s := by
  set g₁ := g.comp (X + C b) with hg₁
  have hint₁ : IntPoly g₁ := coeff_comp_le zero_le_one hint (intPoly_X_add_C hb)
  have hback : g₁.comp (X - C b) = g := by
    rw [hg₁, comp_assoc]; simp
  obtain ⟨k, hk⟩ : ∃ k, ‖g₁.coeff k‖ = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk⟩ := exists_coeff_eq_pgn g₁
    have hlt : pgn g₁ < 1 := hk ▸ lt_of_le_of_ne (hint₁ k) (hcon k)
    have := coeff_comp_le (pgn_nonneg g₁) (norm_coeff_le_pgn g₁) (intPoly_X_sub_C hb) n
    rw [hback, hn] at this
    linarith
  have h0 : ‖g₁.coeff 0‖ < 1 := by
    rw [coeff_zero_eq_eval_zero, hg₁, eval_comp]; simpa using hgb
  obtain ⟨t, ht, hroot⟩ := exists_small_root hint₁ hk h0
  refine ⟨t + b, by rwa [add_sub_cancel_right], ?_⟩
  have : g₁.eval t = 0 := hroot
  rw [hg₁, eval_comp] at this
  simpa using this

/-! ### Slices of an isobaric polynomial -/

/-- The restriction of `E` to a line on which one coordinate equals the constant `a`:
`Σ_d E_d a^{o d} X^{e d}`. -/
noncomputable def slice (E : MvPolynomial (Fin 2) K) (e o : (Fin 2 →₀ ℕ) → ℕ) (a : K) : K[X] :=
  ∑ d ∈ E.support, C (E.coeff d * a ^ o d) * X ^ e d

lemma intPoly_slice (E : MvPolynomial (Fin 2) K) (hE : ∀ d, ‖E.coeff d‖ ≤ 1)
    (e o : (Fin 2 →₀ ℕ) → ℕ) {a : K} (ha : ‖a‖ ≤ 1) : IntPoly (slice E e o a) := by
  intro n
  rw [slice, finsetSum_coeff]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun d _ => ?_
  rw [coeff_C_mul_X_pow]
  split_ifs
  · rw [norm_mul, norm_pow]
    exact mul_le_one₀ (hE d) (by positivity) (pow_le_one₀ (norm_nonneg _) ha)
  · simp

lemma coeff_slice_unit (E : MvPolynomial (Fin 2) K) (e o : (Fin 2 →₀ ℕ) → ℕ)
    (huniq : ∀ d d', E.coeff d ≠ 0 → E.coeff d' ≠ 0 → e d = e d' → d = d')
    {a : K} (ha : ‖a‖ = 1) {d₀ : Fin 2 →₀ ℕ} (hd₀ : ‖E.coeff d₀‖ = 1) :
    ‖(slice E e o a).coeff (e d₀)‖ = 1 := by
  have hd₀' : E.coeff d₀ ≠ 0 := by intro h; rw [h, norm_zero] at hd₀; exact zero_ne_one hd₀
  rw [slice, finsetSum_coeff, Finset.sum_eq_single d₀]
  · rw [coeff_C_mul_X_pow, if_pos rfl, norm_mul, norm_pow, hd₀, ha]; simp
  · intro d hd hne
    rw [coeff_C_mul_X_pow, if_neg]
    intro h
    exact hne (huniq d d₀ (MvPolynomial.mem_support_iff.mp hd) hd₀' h.symm)
  · intro h; exact absurd (MvPolynomial.mem_support_iff.mpr hd₀') h

lemma eval_slice_1 (E : MvPolynomial (Fin 2) K) (a s : K) :
    (slice E (fun d => d 1) (fun d => d 0) a).eval s = MvPolynomial.eval ![a, s] E := by
  rw [slice, eval_finsetSum, MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, Fin.prod_univ_two]
  simp [mul_assoc]

lemma eval_slice_0 (E : MvPolynomial (Fin 2) K) (a s : K) :
    (slice E (fun d => d 0) (fun d => d 1) a).eval s = MvPolynomial.eval ![s, a] E := by
  rw [slice, eval_finsetSum, MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

lemma norm_sub_eq_one {u v : K} (hu : ‖u‖ = 1) (hv : ‖v‖ < 1) : ‖u - v‖ = 1 := by
  have hne : ‖u‖ ≠ ‖-v‖ := by rw [norm_neg, hu]; exact hv.ne'
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, hu]
  exact max_eq_left hv.le

lemma norm_sub_lt_one {u v : K} (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) : ‖u - v‖ < 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hu (by rwa [norm_neg]))

/-- Solve `E = c` on a line through `x₀`, varying the coordinate picked by `e`. -/
lemma solve_on_slice [IsAlgClosed K] (E : MvPolynomial (Fin 2) K) (hE : ∀ d, ‖E.coeff d‖ ≤ 1)
    (e o : (Fin 2 →₀ ℕ) → ℕ)
    (huniq : ∀ d d', E.coeff d ≠ 0 → E.coeff d' ≠ 0 → e d = e d' → d = d')
    {d₀ : Fin 2 →₀ ℕ} (hd₀ : ‖E.coeff d₀‖ = 1) {a b c : K} (ha : ‖a‖ = 1) (hb : ‖b‖ ≤ 1)
    (hc : ‖c‖ < 1) (hab : ‖(slice E e o a).eval b‖ < 1) :
    ∃ s, ‖s - b‖ < 1 ∧ (slice E e o a).eval s = c := by
  set H := slice E e o a
  have hint : IntPoly (H - C c) := by
    intro n
    rw [coeff_sub, coeff_C]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (intPoly_slice E hE e o ha.le n) ?_)
    split_ifs <;> simp [hc.le]
  have hunit : ‖(H - C c).coeff (e d₀)‖ = 1 := by
    rw [coeff_sub, coeff_C]
    refine norm_sub_eq_one (coeff_slice_unit E e o huniq ha hd₀) ?_
    split_ifs <;> simp [hc]
  obtain ⟨s, hs, hroot⟩ := exists_root_near hint hunit hb (by
    rw [eval_sub, eval_C]; exact norm_sub_lt_one hab hc)
  refine ⟨s, hs, ?_⟩
  have : (H - C c).eval s = 0 := hroot
  rw [eval_sub, eval_C, sub_eq_zero] at this
  exact this

lemma norm_le_one_of_close {s b : K} (hs : ‖s - b‖ < 1) (hb : ‖b‖ ≤ 1) : ‖s‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (s - b) b
  rw [sub_add_cancel] at this
  exact this.trans (max_le hs.le hb)

/-- **Lifting.** -/
theorem exists_lift [IsAlgClosed K] (E : MvPolynomial (Fin 2) K) (hE : ∀ d, ‖E.coeff d‖ ≤ 1)
    {d₀ : Fin 2 →₀ ℕ} (hd₀ : ‖E.coeff d₀‖ = 1)
    (huniq0 : ∀ d d', E.coeff d ≠ 0 → E.coeff d' ≠ 0 → d 0 = d' 0 → d = d')
    (huniq1 : ∀ d d', E.coeff d ≠ 0 → E.coeff d' ≠ 0 → d 1 = d' 1 → d = d')
    {x₀ : Fin 2 → K} (hx₀ : Integral x₀) (hdisc : ‖x₀ 0 ^ 3 - x₀ 1 ^ 2‖ = 1)
    (hE0 : ‖MvPolynomial.eval x₀ E‖ < 1) {c : K} (hc : ‖c‖ < 1) :
    ∃ x, Integral x ∧ (∀ i, ‖x i - x₀ i‖ < 1) ∧ MvPolynomial.eval x E = c := by
  have hx₀eq : x₀ = ![x₀ 0, x₀ 1] := by ext i; fin_cases i <;> rfl
  by_cases h0 : ‖x₀ 0‖ = 1
  · obtain ⟨s, hs, hsE⟩ := solve_on_slice E hE (fun d => d 1) (fun d => d 0) huniq1 hd₀ h0 (hx₀ 1) hc
      (by rw [eval_slice_1, ← hx₀eq]; exact hE0)
    refine ⟨![x₀ 0, s], fun i => ?_, fun i => ?_, by rw [← eval_slice_1]; exact hsE⟩
    · fin_cases i
      · exact hx₀ 0
      · exact norm_le_one_of_close hs (hx₀ 1)
    · fin_cases i
      · simp
      · exact hs
  · have h0' : ‖x₀ 0‖ < 1 := lt_of_le_of_ne (hx₀ 0) h0
    have h1 : ‖x₀ 1‖ = 1 := by
      by_contra h1
      have h1' : ‖x₀ 1‖ < 1 := lt_of_le_of_ne (hx₀ 1) h1
      have : ‖x₀ 0 ^ 3 - x₀ 1 ^ 2‖ < 1 := norm_sub_lt_one
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) h0' (by norm_num))
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) h1' (by norm_num))
      linarith
    obtain ⟨s, hs, hsE⟩ := solve_on_slice E hE (fun d => d 0) (fun d => d 1) huniq0 hd₀ h1 (hx₀ 0) hc
      (by rw [eval_slice_0, ← hx₀eq]; exact hE0)
    refine ⟨![s, x₀ 1], fun i => ?_, fun i => ?_, by rw [← eval_slice_0]; exact hsE⟩
    · fin_cases i
      · exact norm_le_one_of_close hs (hx₀ 0)
      · exact hx₀ 1
    · fin_cases i
      · exact hs
      · simp

/-! ### Density of the value group -/

theorem exists_norm_between [IsAlgClosed K] {r : K} (hr0 : 0 < ‖r‖) (hr1 : ‖r‖ < 1)
    {s₀ s₁ : ℝ} (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hs₁ : s₁ ≤ 1) : ∃ c : K, s₀ < ‖c‖ ∧ ‖c‖ < s₁ := by
  classical
  have hs₁0 : 0 < s₁ := hs₀.trans hs
  set q := s₀ / s₁
  have hq0 : 0 < q := div_pos hs₀ hs₁0
  have hq1 : q < 1 := (div_lt_one hs₁0).mpr hs
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hr0 hq1
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, pow_zero] at hm; linarith
    · exact h
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_pow_nat_eq r hm0
  set ρ := ‖ω‖
  have hρm : ρ ^ m = ‖r‖ := by rw [← norm_pow, hω]
  have hρq : q < ρ := lt_of_pow_lt_pow_left₀ m (norm_nonneg _) (hρm ▸ hm)
  have hρ0 : 0 < ρ := hq0.trans hρq
  have hρ1 : ρ < 1 := by
    by_contra h; push Not at h
    have := one_le_pow₀ (n := m) h
    linarith
  have hex : ∃ k, ρ ^ k < s₁ := exists_pow_lt_of_lt_one hs₁0 hρ1
  set k := Nat.find hex
  have hk : ρ ^ k < s₁ := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h; rw [h, pow_zero] at hk; linarith
  have hkm : s₁ ≤ ρ ^ (k - 1) := not_lt.mp (Nat.find_min hex (by omega))
  refine ⟨ω ^ k, ?_, by rwa [norm_pow]⟩
  rw [norm_pow]
  have : ρ ^ k = ρ * ρ ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  rw [this]
  calc s₀ = q * s₁ := by simp only [q]; field_simp
    _ < ρ * s₁ := mul_lt_mul_of_pos_right hρq hs₁0
    _ ≤ ρ * ρ ^ (k - 1) := mul_le_mul_of_nonneg_left hkm hρ0.le

/-! ### From supersingular detection to `DetectsNear` -/

/-- Test points of good reduction: integral with unit discriminant `x₀³ − x₁²` (`= 1728 Δ`). -/
def Good (x : Fin 2 → K) : Prop := Integral x ∧ ‖x 0 ^ 3 - x 1 ^ 2‖ = 1

/-- **Supersingular detection** of `P`: `P` attains its Gauss norm at a point of good reduction where
`‖E‖ < 1`, i.e. on the supersingular locus of the special fibre. -/
def SSDetect (E P : MvPolynomial (Fin 2) K) : Prop :=
  ∃ x₀, Good x₀ ∧ ‖MvPolynomial.eval x₀ E‖ < 1 ∧ ‖MvPolynomial.eval x₀ P‖ = gnorm P

lemma good_of_close {x x₀ : Fin 2 → K} (hx : Integral x) (hx₀ : Good x₀)
    (hclose : ∀ i, ‖x i - x₀ i‖ < 1) : Good x := by
  refine ⟨hx, ?_⟩
  have h3 := norm_pow_sub_pow_le (hx 0) (hx₀.1 0) 3
  have h2 := norm_pow_sub_pow_le (hx 1) (hx₀.1 1) 2
  have hd : ‖(x 0 ^ 3 - x 1 ^ 2) - (x₀ 0 ^ 3 - x₀ 1 ^ 2)‖ < 1 := by
    have : (x 0 ^ 3 - x 1 ^ 2) - (x₀ 0 ^ 3 - x₀ 1 ^ 2) =
        (x 0 ^ 3 - x₀ 0 ^ 3) - (x 1 ^ 2 - x₀ 1 ^ 2) := by ring
    rw [this]
    exact norm_sub_lt_one (h3.trans_lt (hclose 0)) (h2.trans_lt (hclose 1))
  have := norm_sub_eq_one hx₀.2 (by rwa [norm_sub_rev] at hd)
  rwa [sub_sub_cancel] at this

theorem detectsNear_of_ss [IsAlgClosed K] (E : MvPolynomial (Fin 2) K) (hE : ∀ d, ‖E.coeff d‖ ≤ 1)
    {d₀ : Fin 2 →₀ ℕ} (hd₀ : ‖E.coeff d₀‖ = 1)
    (huniq0 : ∀ d d', E.coeff d ≠ 0 → E.coeff d' ≠ 0 → d 0 = d' 0 → d = d')
    (huniq1 : ∀ d d', E.coeff d ≠ 0 → E.coeff d' ≠ 0 → d 1 = d' 1 → d = d')
    {r : K} (hr0 : 0 < ‖r‖) (hr1 : ‖r‖ < 1) {P : MvPolynomial (Fin 2) K} (hP : SSDetect E P) :
    DetectsNear Good E P := by
  intro s₀ s₁ hs₀ hs hs₁
  obtain ⟨c, hc0, hc1⟩ := exists_norm_between hr0 hr1 hs₀ hs hs₁
  obtain ⟨x₀, hx₀, hE0, hPx₀⟩ := hP
  obtain ⟨x, hx, hclose, hxE⟩ :=
    exists_lift E hE hd₀ huniq0 huniq1 hx₀.1 hx₀.2 hE0 (hc1.trans_le hs₁)
  refine ⟨x, good_of_close hx hx₀ hclose, by rwa [hxE], by rwa [hxE], ?_⟩
  exact norm_eval_eq_of_close hx hx₀.1 hclose P hPx₀

end KatzForms
