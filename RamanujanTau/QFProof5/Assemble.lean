/-
# Euler assembly: the three `QEuler` bounds under `[DeligneBound]`

* `prod_Tl_le`: `Π_{q∈T} T_q ≤ e^{65540} Π_{q∈T, q|d} tt_q(v_q d)` (L1 + `Σ 1/p² ≤ 1` for `q ∤ d`);
* `Mass_le_tt`: `M_d(y) ≤ e^{65540} Π_{p|d} tt_p(v_p d)`;
* `MassV_le_tt`: `M'_d(y) ≤ e^{65540} Π_{p|d} tt_p · (2 log d + Σ_{p≤y} V₀(p))`;
* `abs_Wd_le`: `|W(d)| ≤ 1/d`; `abs_W1d_le`: `|W₁(d)| ≤ (|γ_R| + 16 log d)/d`;
* **`qEuler1`, `qEuler2`, `qEuler3`**.
-/
import RamanujanTau.QFProof5.Euler

set_option autoImplicit false

namespace RamanujanTau.QFProof5

open Finset ArithmeticFunction RamanujanTau.QFProof RamanujanTau.QFProof2 RamanujanTau.QFProof3
open RamanujanTau.QFProof4
open RamanujanTau.SelbergCoeffs3 (PrimesTo sum_inv_sq_PrimesTo_le)
open RamanujanTau.HafnerBridge (lam gamR)

/-- `E₀ = e^{65540}`. -/
noncomputable def E0 : ℝ := Real.exp 65540

lemma E0_pos : 0 < E0 := Real.exp_pos _

lemma Tl_nonneg (q e N : ℕ) : 0 ≤ Tl q e N := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
lemma TlV_nonneg (q e N : ℕ) : 0 ≤ TlV q e N := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

lemma mem_pf_fac_ne {d p : ℕ} (h : p ∈ d.primeFactors) : d.factorization p ≠ 0 := by
  rw [← Nat.support_factorization] at h; exact Finsupp.mem_support_iff.1 h

lemma PrimesTo_of_fac {y q : ℕ} (h : q ∈ (y.factorial).primeFactors) : q ∈ PrimesTo y := by
  have hq := Nat.prime_of_mem_primeFactors h
  have hd := Nat.dvd_of_mem_primeFactors h
  simp only [PrimesTo, mem_filter, mem_Ioc]
  exact ⟨⟨hq.pos, (Nat.Prime.dvd_factorial hq).1 hd⟩, hq⟩

/-- `V₀(p) = λ(p)² X log p / 2 + 65540 X` (bound for `T'_p(0)`). -/
noncomputable def V0 (p : ℕ) : ℝ := lam p ^ 2 * Xp p * Real.log p / 2 + 65540 * Xp p

lemma V0_nonneg (p : ℕ) : 0 ≤ V0 p := by
  unfold V0 Xp
  have : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  positivity

section Deligne

variable [DeligneBound]

lemma Tl_le_tt {p : ℕ} (hp : p.Prime) {e : ℕ} (he : e ≠ 0) (N : ℕ) : Tl p e N ≤ tt p e := by
  unfold tt
  rw [if_neg he]
  split_ifs with h1
  · subst h1; exact Tl_one_le hp N
  · exact Tl_le hp e N

lemma TlV_le_tt {p : ℕ} (hp : p.Prime) {e : ℕ} (he : e ≠ 0) (N : ℕ) :
    TlV p e N ≤ ((e : ℝ) + 1) * Real.log p * tt p e := by
  have hl := log_p_nonneg hp
  unfold tt
  rw [if_neg he]
  split_ifs with h1
  · subst h1
    have := TlV_one_le hp N
    have h0 : 0 ≤ |lam p| := abs_nonneg _
    have hX := Xp_pos hp
    push_cast
    nlinarith [mul_nonneg hl (by positivity : (0 : ℝ) ≤ |lam p| + 65536 * Xp p)]
  · have := TlV_le hp e N
    have he1 : (1 : ℝ) ≤ (e : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) e; linarith
    have : 0 ≤ 16384 * Real.log p * ((e : ℝ) + 1) ^ 6 := by positivity
    nlinarith

lemma prod_Tl_le {y d : ℕ} {T : Finset ℕ} (hT : T ⊆ (y.factorial).primeFactors ∪ d.primeFactors) :
    ∏ q ∈ T, Tl q (d.factorization q) ((y.factorial).factorization q) ≤
      E0 * ∏ q ∈ T.filter (· ∈ d.primeFactors), tt q (d.factorization q) := by
  rw [← prod_filter_mul_prod_filter_not T (· ∈ d.primeFactors)]
  have hA : ∏ q ∈ T.filter (· ∈ d.primeFactors), Tl q (d.factorization q) ((y.factorial).factorization q) ≤
      ∏ q ∈ T.filter (· ∈ d.primeFactors), tt q (d.factorization q) := by
    refine prod_le_prod (fun _ _ => Tl_nonneg _ _ _) fun q hq => ?_
    have hqd := (mem_filter.1 hq).2
    exact Tl_le_tt (Nat.prime_of_mem_primeFactors hqd) (mem_pf_fac_ne hqd) _
  have hB : ∏ q ∈ T.filter (fun q => ¬ q ∈ d.primeFactors),
      Tl q (d.factorization q) ((y.factorial).factorization q) ≤ E0 := by
    have hsub : T.filter (fun q => ¬ q ∈ d.primeFactors) ⊆ PrimesTo y := by
      intro q hq
      obtain ⟨hqT, hqd⟩ := mem_filter.1 hq
      rcases mem_union.1 (hT hqT) with h | h
      · exact PrimesTo_of_fac h
      · exact absurd h hqd
    have hpt : ∀ q ∈ T.filter (fun q => ¬ q ∈ d.primeFactors),
        Tl q (d.factorization q) ((y.factorial).factorization q) ≤ Real.exp (65540 * (1 / (q : ℝ) ^ 2)) := by
      intro q hq
      have hqP := hsub hq
      have hqp : q.Prime := (mem_filter.1 hqP).2
      rw [vanish_off (mem_filter.1 hq).2]
      refine (Tl_zero_le hqp _).trans ?_
      have : Xp q ^ 2 = 1 / (q : ℝ) ^ 2 := by unfold Xp; rw [inv_pow, one_div]
      rw [this]
      have := Real.add_one_le_exp (65540 * (1 / (q : ℝ) ^ 2))
      linarith
    calc _ ≤ ∏ q ∈ T.filter (fun q => ¬ q ∈ d.primeFactors), Real.exp (65540 * (1 / (q : ℝ) ^ 2)) :=
          prod_le_prod (fun _ _ => Tl_nonneg _ _ _) hpt
      _ = Real.exp (65540 * ∑ q ∈ T.filter (fun q => ¬ q ∈ d.primeFactors), 1 / (q : ℝ) ^ 2) := by
          rw [← Real.exp_sum, mul_sum]
      _ ≤ E0 := by
          unfold E0
          refine Real.exp_le_exp.2 ?_
          have h1 := sum_le_sum_of_subset_of_nonneg hsub (f := fun q : ℕ => 1 / (q : ℝ) ^ 2)
            (fun _ _ _ => by positivity)
          have h2 := sum_inv_sq_PrimesTo_le y
          nlinarith
  calc _ ≤ (∏ q ∈ T.filter (· ∈ d.primeFactors), tt q (d.factorization q)) * E0 :=
        mul_le_mul hA hB (prod_nonneg fun _ _ => Tl_nonneg _ _ _) (prod_nonneg fun _ _ => tt_nonneg _ _)
    _ = _ := mul_comm _ _

lemma filter_S_eq {y d : ℕ} : ((y.factorial).primeFactors ∪ d.primeFactors).filter (· ∈ d.primeFactors) =
    d.primeFactors := by
  ext q; simp only [mem_filter, mem_union]; tauto

/-- `M_d(y) ≤ E₀ Π_{p|d} tt_p`. -/
theorem Mass_le_tt {y d : ℕ} (hy : 1 ≤ y) (hd : d ≠ 0) :
    Mass (Γc Ud) y d ≤ E0 * ∏ p ∈ d.primeFactors, tt p (d.factorization p) := by
  refine (Mass_le_prod hy hd).trans ?_
  have := prod_Tl_le (y := y) (d := d) (T := (y.factorial).primeFactors ∪ d.primeFactors) subset_rfl
  rwa [filter_S_eq] at this

lemma Mass_nonneg (Γ : ℕ → ℕ → ℕ → ℝ) (y d : ℕ) : 0 ≤ Mass Γ y d :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

lemma sum_succ_log_le {d : ℕ} (hd : d ≠ 0) :
    ∑ p ∈ d.primeFactors, ((d.factorization p : ℝ) + 1) * Real.log p ≤ 2 * Real.log d := by
  rw [Real.log_nat_eq_sum_factorization d, Finsupp.sum, Nat.support_factorization, mul_sum]
  refine sum_le_sum fun p hp => ?_
  have he : (1 : ℝ) ≤ d.factorization p := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (mem_pf_fac_ne hp)
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  nlinarith

/-- `M'_d(y) ≤ E₀ Π_{p|d} tt_p · (2 log d + Σ_{p≤y} V₀(p))`. -/
theorem MassV_le_tt {y d : ℕ} (hd : d ≠ 0) :
    Mass (Γc Vd) y d ≤ E0 * (∏ p ∈ d.primeFactors, tt p (d.factorization p)) *
      (2 * Real.log d + ∑ p ∈ PrimesTo y, V0 p) := by
  set S := (y.factorial).primeFactors ∪ d.primeFactors with hS
  set P := ∏ p ∈ d.primeFactors, tt p (d.factorization p) with hP
  have hP0 : 0 ≤ P := prod_nonneg fun _ _ => tt_nonneg _ _
  refine (MassV_le hd).trans ?_
  rw [← sum_filter_add_sum_filter_not S (· ∈ d.primeFactors)]
  have hT : ∀ p, (S.erase p) ⊆ S := fun p => erase_subset p S
  -- primes dividing `d`
  have h1 : ∑ p ∈ S.filter (· ∈ d.primeFactors), TlV p (d.factorization p) ((y.factorial).factorization p) *
      ∏ q ∈ S.erase p, Tl q (d.factorization q) ((y.factorial).factorization q) ≤
      E0 * P * (2 * Real.log d) := by
    have hpt : ∀ p ∈ S.filter (· ∈ d.primeFactors),
        TlV p (d.factorization p) ((y.factorial).factorization p) *
          ∏ q ∈ S.erase p, Tl q (d.factorization q) ((y.factorial).factorization q) ≤
        E0 * P * (((d.factorization p : ℝ) + 1) * Real.log p) := by
      intro p hpS
      have hpd := (mem_filter.1 hpS).2
      have hp := Nat.prime_of_mem_primeFactors hpd
      have hV := TlV_le_tt hp (mem_pf_fac_ne hpd) ((y.factorial).factorization p)
      have hR := prod_Tl_le (y := y) (d := d) (hT p)
      have hf : (S.erase p).filter (· ∈ d.primeFactors) = d.primeFactors.erase p := by
        rw [filter_erase, filter_S_eq]
      rw [hf] at hR
      have hPe : tt p (d.factorization p) * ∏ q ∈ d.primeFactors.erase p, tt q (d.factorization q) = P :=
        mul_prod_erase _ (fun q => tt q (d.factorization q)) hpd
      have hl := log_p_nonneg hp
      calc _ ≤ (((d.factorization p : ℝ) + 1) * Real.log p * tt p (d.factorization p)) *
            (E0 * ∏ q ∈ d.primeFactors.erase p, tt q (d.factorization q)) :=
            mul_le_mul hV hR (prod_nonneg fun _ _ => Tl_nonneg _ _ _)
              (mul_nonneg (mul_nonneg (by positivity) hl) (tt_nonneg _ _))
        _ = E0 * (tt p (d.factorization p) * ∏ q ∈ d.primeFactors.erase p, tt q (d.factorization q)) *
            (((d.factorization p : ℝ) + 1) * Real.log p) := by ring
        _ = _ := by rw [hPe]
    refine (sum_le_sum hpt).trans ?_
    rw [← mul_sum, filter_S_eq]
    exact mul_le_mul_of_nonneg_left (sum_succ_log_le hd) (mul_nonneg E0_pos.le hP0)
  -- primes not dividing `d`
  have h2 : ∑ p ∈ S.filter (fun p => ¬ p ∈ d.primeFactors),
      TlV p (d.factorization p) ((y.factorial).factorization p) *
      ∏ q ∈ S.erase p, Tl q (d.factorization q) ((y.factorial).factorization q) ≤
      E0 * P * ∑ p ∈ PrimesTo y, V0 p := by
    have hsub : S.filter (fun p => ¬ p ∈ d.primeFactors) ⊆ PrimesTo y := by
      intro q hq
      obtain ⟨hqT, hqd⟩ := mem_filter.1 hq
      rcases mem_union.1 hqT with h | h
      · exact PrimesTo_of_fac h
      · exact absurd h hqd
    have hpt : ∀ p ∈ S.filter (fun p => ¬ p ∈ d.primeFactors),
        TlV p (d.factorization p) ((y.factorial).factorization p) *
          ∏ q ∈ S.erase p, Tl q (d.factorization q) ((y.factorial).factorization q) ≤ E0 * P * V0 p := by
      intro p hpS
      have hpd := (mem_filter.1 hpS).2
      have hp : p.Prime := (mem_filter.1 (hsub hpS)).2
      have hV : TlV p (d.factorization p) ((y.factorial).factorization p) ≤ V0 p := by
        rw [vanish_off hpd]; exact TlV_zero_le hp _
      have hR := prod_Tl_le (y := y) (d := d) (hT p)
      have hf : (S.erase p).filter (· ∈ d.primeFactors) = d.primeFactors := by
        rw [filter_erase, filter_S_eq, erase_eq_of_notMem hpd]
      rw [hf] at hR
      calc _ ≤ V0 p * (E0 * P) :=
            mul_le_mul hV hR (prod_nonneg fun _ _ => Tl_nonneg _ _ _) (V0_nonneg p)
        _ = _ := by ring
    refine (sum_le_sum hpt).trans ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => V0_nonneg _)
      (mul_nonneg E0_pos.le hP0)
  linarith

/-- `Σ_{p≤y} V₀(p) ≤ c₁ + c₂ log y`. -/
lemma sum_V0_le : ∃ c : ℝ, 0 ≤ c ∧ ∀ y : ℕ, 1 ≤ y → ∑ p ∈ PrimesTo y, V0 p ≤ c * (1 + Real.log y) := by
  obtain ⟨E, hE⟩ := RamanujanTau.SelbergCoeffs2.mertens1_prime
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hE 1 le_rfl)
  refine ⟨E + 65541, by positivity, fun y hy => ?_⟩
  have hly : 0 ≤ Real.log y := Real.log_natCast_nonneg y
  have hm := (abs_le.1 (hE y hy)).2
  have hharm : ∑ p ∈ PrimesTo y, (1 : ℝ) / p ≤ 1 + Real.log y := by
    have h := harmonic_le_one_add_log y
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    refine le_trans ?_ h
    refine (sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun _ _ _ => by positivity).trans
      (le_of_eq (sum_congr rfl fun _ _ => one_div _))
    simp only [PrimesTo, mem_filter, mem_Ioc] at hq
    exact mem_Icc.2 ⟨hq.1.1, hq.1.2⟩
  have hsplit : ∑ p ∈ PrimesTo y, V0 p = (1 / 2) * ∑ p ∈ (Ioc 0 y).filter Nat.Prime,
      RamanujanTau.EdgeNonvanishing.lam p ^ 2 * Real.log p / p + 65540 * ∑ p ∈ PrimesTo y, (1 : ℝ) / p := by
    rw [mul_sum, mul_sum, show (Ioc 0 y).filter Nat.Prime = PrimesTo y from rfl, ← sum_add_distrib]
    refine sum_congr rfl fun p hp => ?_
    have hpp : p.Prime := (mem_filter.1 hp).2
    unfold V0 Xp
    rw [lam_prime_eq hpp]; ring
  rw [hsplit]
  nlinarith

lemma abs_Wd_le {d : ℕ} (hd : d ≠ 0) : |Wd d| ≤ ((d : ℝ))⁻¹ := by
  rw [inv_cast_eq_prod hd subset_rfl, Wd, abs_prod]
  exact prod_le_prod (fun _ _ => abs_nonneg _) fun p hp =>
    abs_Wc_le (Nat.prime_of_mem_primeFactors hp) _

lemma abs_W1d_le {d : ℕ} (hd : d ≠ 0) :
    |W1d d| ≤ (|gamR| + 16 * Real.log d) * ((d : ℝ))⁻¹ := by
  have hinv := inv_cast_eq_prod hd (subset_rfl : d.primeFactors ⊆ d.primeFactors)
  have hd0 : 0 ≤ ((d : ℝ))⁻¹ := by positivity
  unfold W1d
  have hterm : ∀ p ∈ d.primeFactors, |Real.log p * wd (lam p) (Xp p) (d.factorization p) *
      ∏ q ∈ d.primeFactors.erase p, Wc (lam q) (Xp q) (d.factorization q)| ≤
      8 * (((d.factorization p : ℝ) + 1) * Real.log p) * ((d : ℝ))⁻¹ := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hl := log_p_nonneg hpp
    have hw := abs_wd_le hpp (d.factorization p)
    have hW : |∏ q ∈ d.primeFactors.erase p, Wc (lam q) (Xp q) (d.factorization q)| ≤
        ∏ q ∈ d.primeFactors.erase p, Xp q ^ (d.factorization q) := by
      rw [abs_prod]
      exact prod_le_prod (fun _ _ => abs_nonneg _) fun q hq =>
        abs_Wc_le (Nat.prime_of_mem_primeFactors (mem_erase.1 hq).2) _
    have hprod : Xp p ^ (d.factorization p) * ∏ q ∈ d.primeFactors.erase p, Xp q ^ (d.factorization q) =
        ((d : ℝ))⁻¹ := by
      rw [hinv]; exact mul_prod_erase _ (fun q => Xp q ^ (d.factorization q)) hp
    rw [abs_mul, abs_mul, abs_of_nonneg hl]
    calc Real.log p * |wd (lam p) (Xp p) (d.factorization p)| *
          |∏ q ∈ d.primeFactors.erase p, Wc (lam q) (Xp q) (d.factorization q)|
        ≤ Real.log p * (8 * ((d.factorization p : ℝ) + 1) * Xp p ^ (d.factorization p)) *
          ∏ q ∈ d.primeFactors.erase p, Xp q ^ (d.factorization q) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw hl) hW (abs_nonneg _) (by
            have := Xp_pos hpp; positivity)
      _ = 8 * (((d.factorization p : ℝ) + 1) * Real.log p) *
          (Xp p ^ (d.factorization p) * ∏ q ∈ d.primeFactors.erase p, Xp q ^ (d.factorization q)) := by
          ring
      _ = _ := by rw [hprod]
  calc |gamR * Wd d + ∑ p ∈ d.primeFactors, Real.log p * wd (lam p) (Xp p) (d.factorization p) *
        ∏ q ∈ d.primeFactors.erase p, Wc (lam q) (Xp q) (d.factorization q)|
      ≤ |gamR| * |Wd d| + ∑ p ∈ d.primeFactors, 8 * (((d.factorization p : ℝ) + 1) * Real.log p) *
          ((d : ℝ))⁻¹ := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
        exact add_le_add le_rfl ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm))
    _ ≤ |gamR| * ((d : ℝ))⁻¹ + 8 * (2 * Real.log d) * ((d : ℝ))⁻¹ := by
        refine add_le_add (mul_le_mul_of_nonneg_left (abs_Wd_le hd) (abs_nonneg _)) ?_
        rw [← sum_mul, ← mul_sum]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sum_succ_log_le hd) (by norm_num)) hd0
    _ = _ := by ring

lemma one_le_log {y : ℕ} (hy : 3 ≤ y) : 1 ≤ Real.log y := by
  have h3 : (3 : ℝ) ≤ y := by exact_mod_cast hy
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

lemma log_le_two_log {y d : ℕ} (hd : d ∈ Icc 1 (y ^ 2)) : Real.log d ≤ 2 * Real.log y := by
  have h := mem_Icc.1 hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h.1
  have : (d : ℝ) ≤ (y : ℝ) ^ 2 := by exact_mod_cast h.2
  have := Real.log_le_log (by linarith) this
  rw [Real.log_pow] at this; push_cast at this; linarith

lemma fT_div_eq {d : ℕ} (hd : d ≠ 0) (c : ℝ) :
    ((d : ℝ))⁻¹ * (c * ∏ p ∈ d.primeFactors, tt p (d.factorization p)) ^ 2 = c ^ 2 * (fT d / d) := by
  rw [fT_eq hd, prod_pow]; ring

/-- **`QEuler Wd (Γc Ud) 1`.** -/
theorem qEuler1 : QEuler Wd (Γc Ud) 1 := by
  obtain ⟨A, hA0, hA⟩ := euler_fT
  refine ⟨E0 ^ 2 * A, fun y hy => ?_⟩
  have hpt : ∀ d ∈ Icc 1 (y ^ 2), |Wd d| * Mass (Γc Ud) y d ^ 2 ≤ E0 ^ 2 * (fT d / d) := by
    intro d hd
    have hd0 : d ≠ 0 := by have := (mem_Icc.1 hd).1; omega
    have hM := Mass_le_tt (by omega : 1 ≤ y) hd0
    rw [← fT_div_eq hd0]
    exact mul_le_mul (abs_Wd_le hd0) (pow_le_pow_left₀ (Mass_nonneg _ _ _) hM 2) (sq_nonneg _)
      (by positivity)
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum, pow_one, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hA y (by omega)) (sq_nonneg _)

/-- **`QEuler W1d (Γc Ud) 2`.** -/
theorem qEuler2 : QEuler W1d (Γc Ud) 2 := by
  obtain ⟨A, hA0, hA⟩ := euler_fT
  refine ⟨(|gamR| + 32) * E0 ^ 2 * A, fun y hy => ?_⟩
  have hly := one_le_log hy
  have hpt : ∀ d ∈ Icc 1 (y ^ 2), |W1d d| * Mass (Γc Ud) y d ^ 2 ≤
      (|gamR| + 32 * Real.log y) * (E0 ^ 2 * (fT d / d)) := by
    intro d hd
    have hd0 : d ≠ 0 := by have := (mem_Icc.1 hd).1; omega
    have hM := Mass_le_tt (by omega : 1 ≤ y) hd0
    have hW : |W1d d| ≤ (|gamR| + 32 * Real.log y) * ((d : ℝ))⁻¹ := by
      refine (abs_W1d_le hd0).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have := log_le_two_log hd; linarith
    rw [← fT_div_eq hd0]
    calc |W1d d| * Mass (Γc Ud) y d ^ 2
        ≤ ((|gamR| + 32 * Real.log y) * ((d : ℝ))⁻¹) *
          (E0 * ∏ p ∈ d.primeFactors, tt p (d.factorization p)) ^ 2 :=
          mul_le_mul hW (pow_le_pow_left₀ (Mass_nonneg _ _ _) hM 2) (sq_nonneg _)
            (by have := abs_nonneg gamR; positivity)
      _ = _ := by ring
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum, ← mul_sum]
  have hS := hA y (by omega)
  have hS0 : 0 ≤ ∑ d ∈ Icc 1 (y ^ 2), fT d / d := sum_nonneg fun d _ => div_nonneg (fT_nonneg d) (by positivity)
  have hg : 0 ≤ |gamR| := abs_nonneg _
  have hE : 0 ≤ E0 ^ 2 := sq_nonneg _
  calc (|gamR| + 32 * Real.log y) * (E0 ^ 2 * ∑ d ∈ Icc 1 (y ^ 2), fT d / d)
      ≤ ((|gamR| + 32) * Real.log y) * (E0 ^ 2 * (A * Real.log y)) :=
        mul_le_mul (by nlinarith) (mul_le_mul_of_nonneg_left hS hE) (by positivity) (by positivity)
    _ = _ := by ring

/-- **`QEuler Wd (Γc Vd) 3`.** -/
theorem qEuler3 : QEuler Wd (Γc Vd) 3 := by
  obtain ⟨A, hA0, hA⟩ := euler_fT
  obtain ⟨c, hc0, hc⟩ := sum_V0_le
  set K3 : ℝ := 4 + 2 * c
  refine ⟨E0 ^ 2 * K3 ^ 2 * A, fun y hy => ?_⟩
  have hly := one_le_log hy
  have hpt : ∀ d ∈ Icc 1 (y ^ 2), |Wd d| * Mass (Γc Vd) y d ^ 2 ≤
      (E0 * K3 * Real.log y) ^ 2 * (fT d / d) := by
    intro d hd
    have hd0 : d ≠ 0 := by have := (mem_Icc.1 hd).1; omega
    have hM := MassV_le_tt (y := y) hd0
    have hP0 : 0 ≤ ∏ p ∈ d.primeFactors, tt p (d.factorization p) := prod_nonneg fun _ _ => tt_nonneg _ _
    have hB : 2 * Real.log d + ∑ p ∈ PrimesTo y, V0 p ≤ K3 * Real.log y := by
      have h1 := log_le_two_log hd
      have h2 := hc y (by omega)
      simp only [K3]; nlinarith
    have hM' : Mass (Γc Vd) y d ≤ (E0 * K3 * Real.log y) * ∏ p ∈ d.primeFactors, tt p (d.factorization p) := by
      refine hM.trans ?_
      calc E0 * (∏ p ∈ d.primeFactors, tt p (d.factorization p)) * (2 * Real.log d + ∑ p ∈ PrimesTo y, V0 p)
          ≤ E0 * (∏ p ∈ d.primeFactors, tt p (d.factorization p)) * (K3 * Real.log y) :=
            mul_le_mul_of_nonneg_left hB (mul_nonneg E0_pos.le hP0)
        _ = _ := by ring
    rw [← fT_div_eq hd0]
    exact mul_le_mul (abs_Wd_le hd0) (pow_le_pow_left₀ (Mass_nonneg _ _ _) hM' 2) (sq_nonneg _)
      (by positivity)
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum]
  have hS := hA y (by omega)
  calc (E0 * K3 * Real.log y) ^ 2 * ∑ d ∈ Icc 1 (y ^ 2), fT d / d
      ≤ (E0 * K3 * Real.log y) ^ 2 * (A * Real.log y) := mul_le_mul_of_nonneg_left hS (sq_nonneg _)
    _ = _ := by ring

end Deligne

end RamanujanTau.QFProof5
