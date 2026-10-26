/-
# Atkin 11^k: Gordon's matrices `C^λ_{i,ν}`

`U(φ^λ J_i) = Σ_ν C^λ_{i,ν} J_ν` for all `λ` (`U_C`), where `C` is defined from the 55 seed rows by the
modular-equation recurrence `C^λ = Σ_j (−1)^{j+1} e_j · C^{λ−j}` (products via the multiplication table);
Gordon's bound `11^{B(λ,i,ν)} ∣ C^λ_{i,ν}` (`C_dvd`) and the support bound `5λ + i ≤ 11ν` (`C_support`).
-/
import RamanujanTau.Atkin11Defs

set_option autoImplicit false

namespace Atkin11
open PowerSeries Finset

variable (hI : Inputs)
include hI

/-! ### the multiplication table -/

lemma gi_mul (b r : ℕ) (hb : b = 1 ∨ b = 2 ∨ b = 3) (hr : r < 5) :
    gi b * gi r = ((tab b r).map fun q => q.2 • (z ^ (q.1 / 5) * gi (q.1 % 5))).sum := by
  have h1 := R1
  have h2 := hI.r2
  rcases hb with rfl | rfl | rfl <;> interval_cases r <;> simp [tab, gi, g4, g6] <;>
    first
    | (linear_combination (0 : PS) * h1)
    | (linear_combination h1)
    | (linear_combination h2)
    | (linear_combination g2 * h1 - h2)
    | (linear_combination g2 ^ 2 * h1 - g2 * h2)
    | (linear_combination g3 * h1 - g2 * h2)
    | (linear_combination (g2 + g3) * h1 + (-g2 - 1) * h2)
    | (linear_combination (g2 * g3 + 11 * z) * h1 - g2 ^ 2 * h2)

omit hI in
lemma J_eq (ν : ℕ) : J ν = z ^ (ν / 5) * gi (ν % 5) := rfl

omit hI in
lemma J_small (b : ℕ) (hb : b < 5) : J b = gi b := by
  rw [J, Nat.div_eq_of_lt hb, Nat.mod_eq_of_lt hb, pow_zero, one_mul]

omit hI in
lemma J_five : J 5 = z := by simp [J, gi]

omit hI in
lemma J_offset (a d : ℕ) : J (5 * a + d) = z ^ a * (z ^ (d / 5) * gi (d % 5)) := by
  rw [J, show (5 * a + d) / 5 = a + d / 5 by omega, show (5 * a + d) % 5 = d % 5 by omega, pow_add]; ring

/-- the row of `J_b · J_ν`. -/
noncomputable def mtF (b ν : ℕ) : ℕ →₀ ℤ := ofList ((tab b (ν % 5)).map fun q => (5 * (ν / 5) + q.1, q.2))

omit hI in
lemma list_sum_mul_left (c : PS) (l : List (ℕ × ℤ)) (f : ℕ × ℤ → PS) :
    c * (l.map f).sum = (l.map fun q => c * f q).sum := by
  induction l with
  | nil => simp
  | cons q l ih => simp [mul_add, ih]

lemma J_mul (b : ℕ) (hb : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 5) (ν : ℕ) : J b * J ν = lc (mtF b ν) := by
  rw [mtF, lc_ofList, List.map_map]
  have hr : ν % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rcases hb with hb | hb | hb | rfl
  · rw [J_small b (by omega), J_eq ν, mul_left_comm, gi_mul hI b _ (by omega) hr, list_sum_mul_left]
    congr 1; refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp, J_offset]; ring
  · rw [J_small b (by omega), J_eq ν, mul_left_comm, gi_mul hI b _ (by omega) hr, list_sum_mul_left]
    congr 1; refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp, J_offset]; ring
  · rw [J_small b (by omega), J_eq ν, mul_left_comm, gi_mul hI b _ (by omega) hr, list_sum_mul_left]
    congr 1; refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp, J_offset]; ring
  · simp only [tab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Function.comp, one_smul]
    rw [J_five, show 5 * (ν / 5) + (ν % 5 + 5) = ν + 5 by omega, J_add_five]

/-- multiplication by `J_b` on rows. -/
noncomputable def mulB (b : ℕ) : (ℕ →₀ ℤ) →ₗ[ℤ] (ℕ →₀ ℤ) := Finsupp.linearCombination ℤ (mtF b)

lemma lc_mulB (b : ℕ) (hb : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 5) (f : ℕ →₀ ℤ) : lc (mulB b f) = J b * lc f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, mul_add]
  | single ν c =>
    rw [mulB, Finsupp.linearCombination_single, map_zsmul, ← J_mul hI b hb, Finsupp.linearCombination_single,
      mul_smul_comm]

/-- multiplication by `e_j` on rows. -/
noncomputable def mulE (j : ℕ) (f : ℕ →₀ ℤ) : ℕ →₀ ℤ := ((eList j).map fun p => p.2 • mulB p.1 f).sum

omit hI in
theorem eList_b : ∀ j < 11, ∀ p ∈ eList (j + 1), p.1 = 1 ∨ p.1 = 2 ∨ p.1 = 3 ∨ p.1 = 5 := by decide

omit hI in
theorem eList_idx : ∀ j < 11, ∀ p ∈ eList (j + 1), 5 * (j + 1) ≤ 11 * p.1 := by decide

omit hI in
theorem tab_idx : ∀ b < 6, ∀ r < 5, ∀ q ∈ tab b r, b + r ≤ q.1 := by decide

omit hI in
lemma eF_eq (j : ℕ) : lc (eF j) = ((eList j).map fun p => p.2 • J p.1).sum := lc_ofList _

lemma lc_mulE (j : ℕ) (hj : j < 11) (f : ℕ →₀ ℤ) : lc (mulE (j + 1) f) = lc (eF (j + 1)) * lc f := by
  rw [mulE, eF_eq, map_list_sum, List.map_map, mul_comm, list_sum_mul_left]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  simp only [Function.comp, map_zsmul, lc_mulB hI p.1 (eList_b j hj p hp), zsmul_eq_mul]
  ring

omit hI in
/-- **Gordon's matrices**: the seeds for `λ ≤ 10`, then the modular-equation recurrence. -/
noncomputable def C : ℕ → ℕ → (ℕ →₀ ℤ)
  | lam, i => if h : lam < 11 then seedF lam i else
      ∑ j ∈ (range 11).attach, ((-1 : ℤ) ^ j.1) • mulE (j.1 + 1) (C (lam - (j.1 + 1)) i)
decreasing_by omega

omit hI in
lemma C_lt {lam : ℕ} (h : lam < 11) (i : ℕ) : C lam i = seedF lam i := by rw [C, dif_pos h]

omit hI in
lemma C_ge {lam : ℕ} (h : ¬ lam < 11) (i : ℕ) :
    C lam i = ∑ j ∈ range 11, ((-1 : ℤ) ^ j) • mulE (j + 1) (C (lam - (j + 1)) i) := by
  rw [C, dif_neg h, ← Finset.sum_attach (range 11) (fun j => ((-1 : ℤ) ^ j) • mulE (j + 1) (C (lam - (j + 1)) i))]

/-- **`U(φ^λ J_i) = Σ_ν C^λ_{i,ν} J_ν`** for every `λ`. -/
theorem U_C (lam : ℕ) : ∀ i < 5, U (φ ^ lam * J i) = lc (C lam i) := by
  induction lam using Nat.strong_induction_on with
  | _ lam ih =>
    intro i hi
    by_cases h : lam < 11
    · rw [C_lt h, hI.seeds lam h i hi]
    · rw [C_ge h, map_sum]
      have e : φ ^ lam * J i = ∑ j ∈ range 11, V ((-1) ^ j * lc (eF (j + 1))) * (φ ^ (lam - (j + 1)) * J i) := by
        rw [show φ ^ lam = φ ^ (lam - 11) * φ ^ 11 by rw [← pow_add]; congr 1; omega, hI.modeq, mul_sum, sum_mul]
        refine sum_congr rfl fun j hj => ?_
        have hj' := mem_range.mp hj
        rw [map_mul, map_pow, map_neg, map_one]
        rw [show lam - (j + 1) = (lam - 11) + (10 - j) by omega, pow_add]; ring
      rw [e, U_sum]
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.mp hj
      rw [U_V_mul, ih _ (by omega) i hi, map_zsmul, lc_mulE hI j hj', zsmul_eq_mul]
      push_cast; ring

/-! ### coefficient lemmas -/

omit hI in
lemma ofList_cons (p : ℕ × ℤ) (l : List (ℕ × ℤ)) : ofList (p :: l) = Finsupp.single p.1 p.2 + ofList l := by
  simp [ofList]

omit hI in
lemma ofList_ne_zero (l : List (ℕ × ℤ)) (ν : ℕ) (h : (ofList l) ν ≠ 0) : ∃ p ∈ l, p.1 = ν := by
  induction l with
  | nil => simp [ofList] at h
  | cons p l ih =>
    rw [ofList_cons, Finsupp.add_apply, Finsupp.single_apply] at h
    by_cases hp : p.1 = ν
    · exact ⟨p, List.mem_cons_self .., hp⟩
    · rw [if_neg hp, zero_add] at h
      obtain ⟨q, hq, e⟩ := ih h
      exact ⟨q, List.mem_cons_of_mem _ hq, e⟩

omit hI in
lemma ofList_dvd (l : List (ℕ × ℤ)) (ν : ℕ) {d : ℤ} (h : ∀ p ∈ l, p.1 = ν → d ∣ p.2) : d ∣ (ofList l) ν := by
  induction l with
  | nil => simp [ofList]
  | cons p l ih =>
    rw [ofList_cons, Finsupp.add_apply, Finsupp.single_apply]
    refine dvd_add ?_ (ih fun q hq e => h q (List.mem_cons_of_mem _ hq) e)
    split_ifs with hp
    · exact h p (List.mem_cons_self ..) hp
    · exact dvd_zero _

omit hI in
lemma mulB_apply (b : ℕ) (f : ℕ →₀ ℤ) (ν : ℕ) : (mulB b f) ν = f.sum fun μ c => c * (mtF b μ) ν := by
  rw [mulB, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  simp [Finsupp.smul_apply]

omit hI in
lemma mulE_apply (j : ℕ) (f : ℕ →₀ ℤ) (ν : ℕ) :
    (mulE j f) ν = ((eList j).map fun p => p.2 * (mulB p.1 f) ν).sum := by
  rw [mulE]
  induction (eList j) with
  | nil => simp
  | cons p l ih => simp [ih]

omit hI in
/-- the nonzero entries of `e_j · g`. -/
lemma mulE_ne_zero (j : ℕ) (g : ℕ →₀ ℤ) (ν : ℕ) (h : (mulE j g) ν ≠ 0) :
    ∃ p ∈ eList j, ∃ μ, g μ ≠ 0 ∧ ∃ q ∈ tab p.1 (μ % 5), ν = 5 * (μ / 5) + q.1 := by
  rw [mulE_apply] at h
  obtain ⟨x, hx, hx0⟩ := List.exists_mem_ne_zero_of_sum_ne_zero h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have h1 : (mulB p.1 g) ν ≠ 0 := fun h0 => hx0 (by rw [h0, mul_zero])
  rw [mulB_apply] at h1
  obtain ⟨μ, hμ, hμ0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  simp only at hμ0
  have h2 : (mtF p.1 μ) ν ≠ 0 := fun h0 => hμ0 (by rw [h0, mul_zero])
  rw [mtF] at h2
  obtain ⟨q', hq', e⟩ := ofList_ne_zero _ _ h2
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
  exact ⟨p, hp, μ, Finsupp.mem_support_iff.mp hμ, q, hq, e.symm⟩

omit hI in
lemma ofList_map_dvd {d c : ℤ} {ν a : ℕ} {g : ℤ} (_ : True) (l : List (ℕ × ℤ))
    (h : ∀ q ∈ l, ν = a + q.1 → d ∣ c * q.2 * g) :
    d ∣ c * (ofList (l.map fun q => (a + q.1, q.2))) ν * g := by
  induction l with
  | nil => simp [ofList]
  | cons q l ih =>
    rw [List.map_cons, ofList_cons, Finsupp.add_apply, Finsupp.single_apply, mul_add, add_mul]
    refine dvd_add ?_ (ih fun q' hq' e => h q' (List.mem_cons_of_mem _ hq') e)
    split_ifs with hq
    · exact h q (List.mem_cons_self ..) hq.symm
    · simp

omit hI in
/-- divisibility of the entries of `e_j · g`. -/
lemma mulE_dvd (j : ℕ) (g : ℕ →₀ ℤ) (ν : ℕ) {d : ℤ}
    (h : ∀ p ∈ eList j, ∀ μ, ∀ q ∈ tab p.1 (μ % 5), ν = 5 * (μ / 5) + q.1 → d ∣ p.2 * q.2 * g μ) :
    d ∣ (mulE j g) ν := by
  rw [mulE_apply]
  refine List.dvd_sum fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  rw [mulB_apply, Finsupp.sum, Finset.mul_sum]
  refine Finset.dvd_sum fun μ _ => ?_
  rw [mtF, mul_comm (g μ), ← mul_assoc]
  exact ofList_map_dvd trivial _ (fun q hq e => h p hp μ q hq e)

/-! ### the support and Gordon's bound -/

omit hI in
lemma seed_entry {lam i : ℕ} (hlam : lam < 11) (hi : i < 5) {p : ℕ × ℤ} (hp : p ∈ seedRows.getD (5 * lam + i) []) :
    seedOK lam i p.1 p.2 = true := by
  have h := rowsOK_true
  rw [rowsOK, List.all_eq_true] at h
  have := List.all_eq_true.mp (h (5 * lam + i) (List.mem_range.mpr (by omega))) p hp
  rwa [show (5 * lam + i) / 5 = lam by omega, show (5 * lam + i) % 5 = i by omega] at this

omit hI in
/-- **support**: `C^λ_{i,ν} ≠ 0 ⇒ 5λ + i ≤ 11ν`. -/
theorem C_support (lam : ℕ) : ∀ i < 5, ∀ ν, (C lam i) ν ≠ 0 → 5 * lam + i ≤ 11 * ν := by
  induction lam using Nat.strong_induction_on with
  | _ lam ih =>
    intro i hi ν hν
    by_cases h : lam < 11
    · rw [C_lt h, seedF] at hν
      obtain ⟨p, hp, rfl⟩ := ofList_ne_zero _ _ hν
      have := seed_entry h hi hp
      simp only [seedOK, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2
    · rw [C_ge h, Finsupp.finsetSum_apply] at hν
      obtain ⟨j, hj, hj0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hν
      have hj' := mem_range.mp hj
      rw [Finsupp.smul_apply] at hj0
      have h1 : (mulE (j + 1) (C (lam - (j + 1)) i)) ν ≠ 0 := fun h0 => hj0 (by rw [h0, smul_zero])
      obtain ⟨p, hp, μ, hμ, q, hq, rfl⟩ := mulE_ne_zero _ _ _ h1
      have hb := eList_idx j hj' p hp
      have hb6 : p.1 < 6 := by rcases eList_b j hj' p hp with h | h | h | h <;> omega
      have hq' := tab_idx p.1 hb6 (μ % 5) (Nat.mod_lt _ (by norm_num)) q hq
      have := ih (lam - (j + 1)) (by omega) i hi μ hμ
      omega

omit hI in
lemma toNat_le_add (X Y : ℤ) : X.toNat ≤ Y.toNat + (X - Y).toNat := by omega

omit hI in
/-- the inductive step of Gordon's bound for one term (from the periodic box check). -/
lemma step_dvd (i : ℕ) (hi : i < 5) (lam : ℕ) (j : ℕ) (hj : j < 11) (hlam : j + 1 ≤ lam) (p : ℕ × ℤ)
    (hp : p ∈ eList (j + 1)) (μ : ℕ) (q : ℕ × ℤ) (hq : q ∈ tab p.1 (μ % 5)) :
    (11 : ℤ) ^ (B lam i (5 * (μ / 5) + q.1) - B ((lam - (j + 1) : ℕ) : ℤ) i μ).toNat ∣ p.2 * q.2 := by
  have h := boxOK_true
  simp only [boxOK, List.all_eq_true, List.mem_range] at h
  have hc := h i hi (lam % 2) (Nat.mod_lt _ (by norm_num)) j hj (μ % 10) (Nat.mod_lt _ (by norm_num))
  simp only [stepOK, List.all_eq_true] at hc
  have hq10 : q ∈ tab p.1 (μ % 10 % 5) := by rwa [Nat.mod_mod_of_dvd _ (by norm_num : 5 ∣ 10)]
  have hc2 := hc p hp q hq10
  simp only [beq_iff_eq] at hc2
  have hdiv := Int.dvd_of_emod_eq_zero hc2
  -- periodicity
  have e1 : B lam i (5 * (μ / 5) + q.1) = B ((lam % 2 : ℕ) : ℤ) i (5 * (μ % 10 / 5) + q.1) - (lam / 2 : ℕ)
      + 11 * (μ / 10 : ℕ) := by
    rw [← B_shift]; congr 1
    · push_cast; omega
    · omega
  have e2 : B ((lam - (j + 1) : ℕ) : ℤ) i μ = B (((lam % 2 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)) i (μ % 10)
      - (lam / 2 : ℕ) + 11 * (μ / 10 : ℕ) := by
    rw [← B_shift]; congr 1
    · push_cast; omega
    · omega
  rw [e1, e2]
  convert hdiv using 3
  push_cast; ring

omit hI in
/-- **Gordon's bound**: `11^{B(λ,i,ν)} ∣ C^λ_{i,ν}`. -/
theorem C_dvd (lam : ℕ) : ∀ i < 5, ∀ ν, (11 : ℤ) ^ (B lam i ν).toNat ∣ (C lam i) ν := by
  induction lam using Nat.strong_induction_on with
  | _ lam ih =>
    intro i hi ν
    by_cases h : lam < 11
    · rw [C_lt h, seedF]
      refine ofList_dvd _ _ fun p hp e => ?_
      have := seed_entry h hi hp
      simp only [seedOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
      rw [← e]; exact Int.dvd_of_emod_eq_zero this.1
    · rw [C_ge h, Finsupp.finsetSum_apply]
      refine Finset.dvd_sum fun j hj => ?_
      have hj' := mem_range.mp hj
      rw [Finsupp.smul_apply, smul_eq_mul]
      refine dvd_mul_of_dvd_right ?_ _
      refine mulE_dvd _ _ _ fun p hp μ q hq e => ?_
      subst e
      have h1 := step_dvd i hi lam j hj' (by omega) p hp μ q hq
      have h2 := ih (lam - (j + 1)) (by omega) i hi μ
      have h3 : (11 : ℤ) ^ (B lam i (5 * (μ / 5) + q.1)).toNat ∣
          (11 : ℤ) ^ (B ((lam - (j + 1) : ℕ) : ℤ) i μ).toNat *
            11 ^ (B lam i (5 * (μ / 5) + q.1) - B ((lam - (j + 1) : ℕ) : ℤ) i μ).toNat := by
        rw [← pow_add]; exact pow_dvd_pow _ (toNat_le_add _ _)
      refine h3.trans ?_
      rw [show p.2 * q.2 * (C (lam - (j + 1)) i) μ = (C (lam - (j + 1)) i) μ * (p.2 * q.2) by ring]
      exact mul_dvd_mul h2 h1

end Atkin11
