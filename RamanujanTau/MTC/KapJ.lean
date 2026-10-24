/-
# `κ = Λ₀(1) = (q;q)_∞³`

`κ = Σ_n Θlo(n)` with `Θlo(n) = Σ_{i ≤ n} (−1)^i q^{C(i,2)}`. Write `Θlo(n) = −Σ_{i > n}` for `n ≥ 0` and swap the
order of summation: each `i` occurs `−i` times, so `κ = −Σ_i i (−1)^i q^{C(i,2)}`, which is `(q;q)_∞³` by Jacobi's
identity (`ALz.kappa_jacobi`).
-/
import RamanujanTau.MTC.Lambda
import RamanujanTau.ALJacobi

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

lemma hs_eq_mulK {ι : Type*} {s u : SummableFamily ℤ ℂ ι} (a : L) (h : ∀ k, u k = a * s k) :
    hs u = a * hs s := by
  rw [hs, hs, ← SummableFamily.hsum_smul]
  congr 1; ext k : 1
  simp [HahnSeries.of_symm_smul_of_eq_mul, h k]

lemma hs_eq_fsK {ι : Type*} {s : SummableFamily ℤ ℂ ι} (S : Finset ι) (h : ∀ i ∉ S, s i = 0) :
    hs s = ∑ i ∈ S, s i := by
  ext g
  rw [hs, SummableFamily.coeff_hsum_eq_sum_of_subset (t := S) (fun i hi => by
    by_contra hS; apply hi; rw [h i hS, HahnSeries.coeff_zero]), HahnSeries.coeff_sum]

lemma mono_ext_k {E E' : ℤ} {C C' : ℂ} (hE : E = E') (hC : C = C') : mono E C = mono E' C' := by
  subst hE hC; rfl

lemma neg_mono_k (E : ℤ) (C : ℂ) : -(mono E C : L) = mono E (-C) := by simp [mono]

lemma nsmul_mono (k : ℕ) (E : ℤ) (c : ℂ) : k • (mono E c : L) = mono E (k * c) := by
  induction k with
  | zero => simp [mono]
  | succ k ih =>
    rw [succ_nsmul, ih, mono, mono, mono, ← HahnSeries.single_add]
    push_cast; ring_nf

section Kap
variable {N : ℕ} (hN : 1 ≤ N)

/-- `(−1)^i q^{C(i,2)}`. -/
noncomputable def kt (i : ℤ) : L := mono (N * c2 i) ((-1) ^ i)

/-- the family `g(n, i)`: `[i ≤ n]` for `n < 0`, `−[n < i]` for `n ≥ 0`. -/
noncomputable def gk (p : ℤ × ℤ) : L :=
  if p.1 < 0 then (if p.2 ≤ p.1 then kt (N := N) p.2 else 0) else (if p.1 < p.2 then -kt (N := N) p.2 else 0)

include hN in
lemma gk_lb (p : ℤ × ℤ) (n : ℤ) (hn : (gk (N := N) p).coeff n ≠ 0) :
    n = N * c2 p.2 ∧ |p.1| ≤ |p.2| := by
  unfold gk kt at hn
  split_ifs at hn with h1 h2 h3
  · exact ⟨coeff_mono_ne hn, by rw [abs_of_neg h1, abs_of_neg (by omega)]; omega⟩
  · simp at hn
  · rw [HahnSeries.coeff_neg, neg_ne_zero] at hn
    exact ⟨coeff_mono_ne hn, by rw [abs_of_nonneg (by omega), abs_of_pos (by omega)]; omega⟩
  · simp at hn

noncomputable def GK : SummableFamily ℤ ℂ (ℤ × ℤ) :=
  ofSupp (gk (N := N)) 0
    (fun p n hn => by
      by_contra h
      obtain ⟨rfl, -⟩ := gk_lb hN p n h
      have := c2_nonneg p.2
      have : (0 : ℤ) ≤ N := by positivity
      nlinarith)
    (fun n => ((Finset.Icc (-(2 * |n| + 1)) (2 * |n| + 1) ×ˢ Finset.Icc (-(2 * |n| + 1)) (2 * |n| + 1) :
        Finset (ℤ × ℤ)) : Set (ℤ × ℤ)).toFinite.subset fun p hp => by
      obtain ⟨h1, h2⟩ := gk_lb hN p n hp
      have hb := thE_bound (N := N) hN 0 p.2 n (by unfold thE; rw [h1]; ring)
      have a1 := le_abs_self p.1; have a2 := neg_abs_le p.1; have a3 := le_abs_self p.2
      have a4 := neg_abs_le p.2
      simp only [abs_zero, mul_zero, add_zero] at hb
      simp only [Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc]
      omega)

/-- the rows are the partial theta sums. -/
lemma row_GK (n : ℤ) : hs (row (GK hN) n) = Θlo hN n := by
  by_cases hn : n < 0
  · unfold Θlo
    refine hsum_congr _ _ fun i => ?_
    simp only [row_apply, thInd, monoFam_apply]
    show gk (N := N) (n, i) = _
    unfold gk kt
    simp only [if_pos hn]
    split_ifs with h
    · exact mono_ext_k (by unfold thE; ring) rfl
    · simp [mono]
  · have h2 := thInd_add hN (· ≤ n)
    have h3 : hs (row (GK hN) n) = -1 * hs (thInd hN (fun i => ¬ (i ≤ n))) := by
      refine hs_eq_mulK _ fun i => ?_
      simp only [row_apply, thInd, monoFam_apply]
      show gk (N := N) (n, i) = _
      unfold gk kt
      simp only [if_neg hn]
      by_cases h : n < i
      · rw [if_pos h, if_pos (show ¬ i ≤ n by omega)]
        rw [show (-1 : L) * mono (thE N 0 i) ((-1) ^ i) = -mono (thE N 0 i) ((-1) ^ i) by ring]
        exact congrArg Neg.neg (mono_ext_k (by unfold thE; ring) rfl)
      · rw [if_neg h, if_neg (show ¬¬ i ≤ n by omega)]
        simp [mono]
    rw [h3, Θlo]
    linear_combination -h2

/-- the columns: each `i` occurs `−i` times. -/
lemma col_GK (i : ℤ) :
    hs (row (SummableFamily.Equiv (Equiv.prodComm ℤ ℤ) (GK hN)) i) = mono (N * c2 i) (-(i : ℂ) * (-1) ^ i) := by
  have hrow : ∀ n, row (SummableFamily.Equiv (Equiv.prodComm ℤ ℤ) (GK hN)) i n = gk (N := N) (n, i) := fun n => rfl
  by_cases hi : i ≤ 0
  · rw [hs_eq_fsK (Finset.Ico i 0) (fun n hn => by
      rw [hrow]; unfold gk
      rw [Finset.mem_Ico] at hn
      split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega))]
    rw [Finset.sum_congr rfl (fun n hn => by
      rw [hrow]; unfold gk
      rw [Finset.mem_Ico] at hn
      rw [if_pos hn.2, if_pos hn.1] : ∀ n ∈ Finset.Ico i 0, _ = kt (N := N) i)]
    rw [Finset.sum_const, Int.card_Ico, kt, nsmul_mono]
    exact mono_ext_k rfl (by
      rw [show (((0 - i).toNat : ℕ) : ℂ) = ((0 - i : ℤ) : ℂ) from by exact_mod_cast Int.toNat_of_nonneg (by omega)]
      push_cast; ring)
  · rw [hs_eq_fsK (Finset.Ico 0 i) (fun n hn => by
      rw [hrow]; unfold gk
      rw [Finset.mem_Ico] at hn
      split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega))]
    rw [Finset.sum_congr rfl (fun n hn => by
      rw [hrow]; unfold gk
      rw [Finset.mem_Ico] at hn
      rw [if_neg (by omega), if_pos hn.2] : ∀ n ∈ Finset.Ico 0 i, _ = -kt (N := N) i)]
    rw [Finset.sum_const, Int.card_Ico, kt, smul_neg, nsmul_mono, neg_mono_k]
    exact mono_ext_k rfl (by
      rw [show (((i - 0).toNat : ℕ) : ℂ) = ((i - 0 : ℤ) : ℂ) from by exact_mod_cast Int.toNat_of_nonneg (by omega)]
      push_cast; ring)

/-- **`κ = (q;q)_∞³`**. -/
theorem kap_eq : kap hN = (ιN hN MockTheta5.JTP.qfacInf) ^ 3 := by
  have hE := lam0S_ent hN
  have h1 : kap hN = hs (GK hN) := by
    rw [kap, ev_eq hE]
    exact (hsum_fubini (GK hN) (evFam hE 0 1) (row (GK hN)) (fun _ _ => rfl) fun n => by
      rw [evFam_apply, row_GK, zero_mul, one_zpow, show (mono 0 1 : L) = 1 from rfl, mul_one]; rfl).symm
  have h2 : hs (GK hN) = hs (cFam hN fun u => -(u : ℂ) * (-1) ^ u) := by
    rw [show hs (GK hN) = hs (SummableFamily.Equiv (Equiv.prodComm ℤ ℤ) (GK hN)) by
      rw [hs, hs, SummableFamily.hsum_equiv]]
    exact hsum_fubini (SummableFamily.Equiv (Equiv.prodComm ℤ ℤ) (GK hN)) (cFam hN fun u => -(u : ℂ) * (-1) ^ u)
      (row (SummableFamily.Equiv (Equiv.prodComm ℤ ℤ) (GK hN))) (fun _ _ => rfl) fun i => by
      rw [col_GK]
      show mono (thE N 0 i) _ = _
      exact mono_ext_k (by unfold thE; ring) rfl
  have h3 : hs (cFam hN fun u => -(u : ℂ) * (-1) ^ u) = -1 * hs (cFam hN fun u => (u : ℂ) * (-1) ^ u) :=
    hs_eq_mulK _ fun u => by
      show mono (thE N 0 u) (-(u : ℂ) * (-1) ^ u) = -1 * mono (thE N 0 u) ((u : ℂ) * (-1) ^ u)
      rw [show ∀ x : L, (-1 : L) * x = -x from fun x => by ring, neg_mono_k]
      exact mono_ext_k rfl (by ring)
  rw [h1, h2, h3, ← hs_kF0, kappa_jacobi]
  ring

end Kap

end MTC
