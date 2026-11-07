/-
# The prime-power part of `Λ_Δ`, without Deligne

`vH n = Λ_Δ(n)` for `n = p^k`, `k ≥ 2`, and `0` otherwise.  Unconditionally

  `Σ_{n ≤ N} |vH(n)| ≤ C N^{9/10}`    (`sum_abs_vH_le`).

* `k = 2`: `|Λ_Δ(p²)| = |λ(p)² − 2| log p ≤ (τ(p)²/p¹¹ + 2) log N`, and Rankin's
  `Σ_{m ≤ √N} τ(m)²/m¹¹ ≪ √N` gives `≪ √N log N`.
* `k ≥ 3`: `|Λ_Δ(p^k)| ≤ 2‖α_p‖^k log p ≤ 2√N log N` (`‖α_p‖² ≤ p`, no Deligne), and there are
  `≤ (N^{1/3}+1)·log₂ N` such pairs `(p, k)`; total `≪ N^{5/6} log² N`.
-/
import RamanujanTau.TauPNTError.PrimeForm

set_option autoImplicit false

namespace RamanujanTau.TauPNTError

open Filter Topology
open RamanujanTau.TauPNT RamanujanTau.EdgeNonvanishing

/-- Prime part of `Λ_Δ`. -/
noncomputable def vP (n : ℕ) : ℝ := if n.Prime then vM n else 0

/-- Higher prime-power part of `Λ_Δ`. -/
noncomputable def vH (n : ℕ) : ℝ := if n.Prime then 0 else vM n

lemma vP_add_vH (n : ℕ) : vP n + vH n = vM n := by
  unfold vP vH; split_ifs <;> simp

lemma vP_zero : vP 0 = 0 := by simp [vP, Nat.not_prime_zero]

lemma vH_zero : vH 0 = 0 := by simp [vH, Nat.not_prime_zero, vM_of_not, IsPrimePow]

lemma lam_sq_eq {p : ℕ} (hp : 0 < p) : lam p ^ 2 = rsb p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  simp only [lam, uu, rr, pow_one, rsb]
  rw [mul_pow, ← Real.rpow_natCast ((p : ℝ) ^ (-(11 / 2 : ℝ))), ← Real.rpow_mul hp0.le]
  rw [show (-(11 / 2 : ℝ) * ((2 : ℕ) : ℝ)) = -((11 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg hp0.le, Real.rpow_natCast]
  rw [div_eq_mul_inv]

lemma log_le_pow (x : ℝ) (hx : 1 ≤ x) : Real.log x ≤ 30 * x ^ (1 / 30 : ℝ) := by
  have := Real.log_le_rpow_div (x := x) (by linarith) (ε := 1 / 30) (by norm_num)
  linarith [show x ^ (1 / 30 : ℝ) / (1 / 30) = 30 * x ^ (1 / 30 : ℝ) by ring]

lemma abs_vH_pow_le {p : ℕ} (hp : p.Prime) (j : ℕ) {N : ℕ} (hN : p ^ (j + 2) ≤ N) :
    |vH (p ^ (j + 2))| ≤
      (if j = 0 then rsb p + 2 else 2 * Real.sqrt N) * Real.log N := by
  have hnp : ¬ (p ^ (j + 2)).Prime := Nat.Prime.not_prime_pow (by omega)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  have hpN : (p : ℝ) ≤ N := by
    have : p ≤ p ^ (j + 2) := Nat.le_self_pow (by omega) p
    exact_mod_cast this.trans hN
  have hlog : Real.log p ≤ Real.log N := Real.log_le_log (by linarith) hpN
  rw [vH, if_neg hnp, show j + 2 = (j + 1) + 1 by ring, vM_pow hp, abs_mul,
    abs_of_nonneg hlogp]
  split_ifs with hj
  · subst hj
    rw [show 0 + 1 + 1 = 2 by rfl, AA_two, lam_sq_eq hp.pos]
    have h1 : |rsb p - 2| ≤ rsb p + 2 := by
      rw [abs_le]; constructor <;> linarith [rsb_nonneg p]
    exact mul_le_mul h1 hlog hlogp (by linarith [rsb_nonneg p])
  · refine mul_le_mul ?_ hlog hlogp (by positivity)
    refine (abs_AA_le p _).trans ?_
    have hsa : ‖sa p‖ ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (norm_sa_sq_le hp)
    have h2 : ‖sa p‖ ^ (j + 1 + 1) ≤ Real.sqrt p ^ (j + 1 + 1) :=
      pow_le_pow_left₀ (norm_nonneg _) hsa _
    have h3 : Real.sqrt p ^ (j + 1 + 1) ≤ Real.sqrt N := by
      apply Real.le_sqrt_of_sq_le
      rw [← pow_mul, show (j + 1 + 1) * 2 = 2 * (j + 2) by ring, pow_mul,
        Real.sq_sqrt (by positivity)]
      exact_mod_cast hN
    linarith

/-- The pairs `(p, j)` with `p^{j+2} ≤ N`. -/
noncomputable def ppairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.range (N + 1)).filter Nat.Prime) ×ˢ Finset.range N).filter
    (fun q => q.1 ^ (q.2 + 2) ≤ N)

lemma sum_vH_le_pairs (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, |vH n| ≤ ∑ q ∈ ppairs N, |vH (q.1 ^ (q.2 + 2))| := by
  classical
  set f : ℕ × ℕ → ℕ := fun q => q.1 ^ (q.2 + 2) with hf
  have hinj : Set.InjOn f ↑(ppairs N) := by
    intro q hq r hr hqr
    simp only [ppairs, Finset.coe_filter, Finset.mem_product, Finset.mem_filter,
      Finset.mem_range, Set.mem_setOf_eq] at hq hr
    have := Nat.Prime.pow_inj (m := q.2 + 1) (n := r.2 + 1) hq.1.1.2 hr.1.1.2 hqr
    exact Prod.ext this.1 (by omega)
  rw [← Finset.sum_image (f := fun n => |vH n|) hinj]
  have hsub : (Finset.Icc 1 N).filter (fun n => vH n ≠ 0) ⊆ (ppairs N).image f := by
    intro n hn
    obtain ⟨hn1, hn0⟩ := Finset.mem_filter.1 hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn1
    have hnp : ¬ n.Prime := by intro h; apply hn0; simp [vH, h]
    have hpp : IsPrimePow n := by
      by_contra h; apply hn0; simp [vH, hnp, vM_of_not h]
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      subst this; exact hnp (by simpa using hp)
    rw [Finset.mem_image]
    refine ⟨(p, k - 2), ?_, by simp [hf, show k - 2 + 2 = k by omega]⟩
    simp only [ppairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨⟨?_, hp⟩, ?_⟩, by rw [show k - 2 + 2 = k by omega]; exact h2⟩
    · have : p ≤ p ^ k := Nat.le_self_pow (by omega) p
      omega
    · have h3 : k < 2 ^ k := Nat.lt_two_pow_self
      have h4 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
      omega
  calc ∑ n ∈ Finset.Icc 1 N, |vH n|
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => vH n ≠ 0), |vH n| := by
        refine (Finset.sum_filter_of_ne fun n _ h => ?_).symm
        intro h0; apply h; simp [h0]
    _ ≤ ∑ n ∈ (ppairs N).image f, |vH n| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _

lemma rpow_mono_exp {x : ℝ} (hx : 1 ≤ x) {a b : ℝ} (hab : a ≤ b) : x ^ a ≤ x ^ b :=
  Real.rpow_le_rpow_of_exponent_le hx hab

/-- **The higher prime powers contribute `≪ N^{9/10}`** (unconditional). -/
theorem sum_abs_vH_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Finset.Icc 1 N, |vH n| ≤ C * (N : ℝ) ^ (9 / 10 : ℝ) := by
  classical
  obtain ⟨K, hK0, hK⟩ := rs_partial_le
  refine ⟨30 * (K + 2) + 8 * 900, by positivity, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hsN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  refine (sum_vH_le_pairs N).trans ?_
  set P := ppairs N with hP
  rw [← Finset.sum_filter_add_sum_filter_not P (fun q => q.2 = 0)]
  -- `j = 0`
  have hA : ∑ q ∈ P.filter (fun q => q.2 = 0), |vH (q.1 ^ (q.2 + 2))| ≤
      (K + 2) * Real.sqrt N * Real.log N := by
    have h1 : ∑ q ∈ P.filter (fun q => q.2 = 0), |vH (q.1 ^ (q.2 + 2))| ≤
        ∑ q ∈ P.filter (fun q => q.2 = 0), (rsb q.1 + 2) * Real.log N := by
      refine Finset.sum_le_sum fun q hq => ?_
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
      simp only [hP, ppairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq1
      have := abs_vH_pow_le hq1.1.1.2 q.2 hq1.2
      rwa [if_pos hq2] at this
    have hinj : Set.InjOn Prod.fst (↑(P.filter (fun q => q.2 = 0)) : Set (ℕ × ℕ)) := by
      intro q hq r hr h
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq hr
      exact Prod.ext h (hq.2.trans hr.2.symm)
    have h2 : ∑ q ∈ P.filter (fun q => q.2 = 0), (rsb q.1 + 2) ≤
        ∑ p ∈ Finset.Icc 1 (Nat.sqrt N), (rsb p + 2) := by
      rw [← Finset.sum_image (f := fun p => rsb p + 2) hinj]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => by linarith [rsb_nonneg p]
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
      simp only [hP, ppairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq1
      rw [hq2] at hq1
      refine Finset.mem_Icc.2 ⟨hq1.1.1.2.one_lt.le, Nat.le_sqrt'.2 hq1.2⟩
    have h3 : ∑ p ∈ Finset.Icc 1 (Nat.sqrt N), (rsb p + 2) ≤ (K + 2) * Real.sqrt N := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      have := hK (Nat.sqrt N)
      have hs : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
      simp only [add_tsub_cancel_right]
      nlinarith
    rw [← Finset.sum_mul] at h1
    calc _ ≤ (∑ q ∈ P.filter (fun q => q.2 = 0), (rsb q.1 + 2)) * Real.log N := h1
      _ ≤ ((K + 2) * Real.sqrt N) * Real.log N := by
          gcongr; exact h2.trans h3
  -- `j ≥ 1`
  set M : ℕ := ⌊(N : ℝ) ^ (1 / 3 : ℝ)⌋₊ with hM
  set L : ℕ := Nat.log 2 N with hL
  have hB : ∑ q ∈ P.filter (fun q => ¬ q.2 = 0), |vH (q.1 ^ (q.2 + 2))| ≤
      ((M + 1 : ℕ) * L : ℝ) * (2 * Real.sqrt N * Real.log N) := by
    have h1 : ∀ q ∈ P.filter (fun q => ¬ q.2 = 0), |vH (q.1 ^ (q.2 + 2))| ≤
        2 * Real.sqrt N * Real.log N := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
      simp only [hP, ppairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq1
      have := abs_vH_pow_le hq1.1.1.2 q.2 hq1.2
      rwa [if_neg hq2] at this
    have hsub : P.filter (fun q => ¬ q.2 = 0) ⊆ Finset.range (M + 1) ×ˢ Finset.range L := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
      simp only [hP, ppairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq1
      obtain ⟨⟨⟨_, hp⟩, _⟩, hpow⟩ := hq1
      simp only [Finset.mem_product, Finset.mem_range]
      constructor
      · -- `p³ ≤ N`
        have h3 : q.1 ^ 3 ≤ N := by
          have : q.1 ^ 3 ≤ q.1 ^ (q.2 + 2) := Nat.pow_le_pow_right hp.pos (by omega)
          omega
        have h4 : (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
          have h5 : ((q.1 : ℝ) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) = q.1 := by
            rw [← Real.rpow_mul (by positivity)]; norm_num
          rw [← h5]
          apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          exact_mod_cast h3
        have := Nat.le_floor h4
        omega
      · have h3 : 2 ^ (q.2 + 2) ≤ N :=
          (Nat.pow_le_pow_left hp.two_le _).trans hpow
        have := Nat.le_log_of_pow_le (by norm_num) h3
        omega
    calc _ ≤ ∑ _q ∈ P.filter (fun q => ¬ q.2 = 0), 2 * Real.sqrt N * Real.log N :=
          Finset.sum_le_sum h1
      _ = (P.filter (fun q => ¬ q.2 = 0)).card * (2 * Real.sqrt N * Real.log N) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Finset.range (M + 1) ×ˢ Finset.range L).card : ℝ) * (2 * Real.sqrt N * Real.log N) := by
          have : ((P.filter (fun q => ¬ q.2 = 0)).card : ℝ) ≤
              ((Finset.range (M + 1) ×ˢ Finset.range L).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
          have : 0 ≤ 2 * Real.sqrt N * Real.log N := by positivity
          nlinarith
      _ = _ := by rw [Finset.card_product, Finset.card_range, Finset.card_range]; push_cast; ring
  -- numerics
  have hcube : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hM1 : ((M + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 3 : ℝ) := by
    push_cast
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    linarith
  have hL1 : (L : ℝ) ≤ 2 * Real.log N := by
    have h1 : (2 : ℝ) ^ L ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have h2 : (L : ℝ) * Real.log 2 ≤ Real.log N := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h1
    have h3 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    nlinarith
  have hlog := log_le_pow (N : ℝ) hN1
  have hsq : Real.sqrt N = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have e1 : Real.sqrt N * Real.log N ≤ 30 * (N : ℝ) ^ (9 / 10 : ℝ) := by
    have hm := rpow_mono_exp hN1 (show (8 / 15 : ℝ) ≤ 9 / 10 by norm_num)
    calc Real.sqrt N * Real.log N ≤ Real.sqrt N * (30 * (N : ℝ) ^ (1 / 30 : ℝ)) := by gcongr
      _ = 30 * (N : ℝ) ^ (8 / 15 : ℝ) := by
          rw [hsq, show (8 / 15 : ℝ) = 1 / 2 + 1 / 30 by norm_num, Real.rpow_add hN0]; ring
      _ ≤ 30 * (N : ℝ) ^ (9 / 10 : ℝ) := by linarith
  have e2 : (N : ℝ) ^ (1 / 3 : ℝ) * Real.sqrt N * Real.log N ^ 2 ≤ 900 * (N : ℝ) ^ (9 / 10 : ℝ) := by
    have h0 : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) * Real.sqrt N := by positivity
    have : Real.log N ^ 2 ≤ (30 * (N : ℝ) ^ (1 / 30 : ℝ)) ^ 2 := pow_le_pow_left₀ hlogN hlog 2
    calc (N : ℝ) ^ (1 / 3 : ℝ) * Real.sqrt N * Real.log N ^ 2
        ≤ (N : ℝ) ^ (1 / 3 : ℝ) * Real.sqrt N * (30 * (N : ℝ) ^ (1 / 30 : ℝ)) ^ 2 := by gcongr
      _ = 900 * (N : ℝ) ^ (9 / 10 : ℝ) := by
          have h30 : (30 * (N : ℝ) ^ (1 / 30 : ℝ)) ^ 2 = 900 * (N : ℝ) ^ (1 / 15 : ℝ) := by
            rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (1 / 30 : ℝ)), ← Real.rpow_mul hN0.le]
            norm_num
          rw [h30, hsq]
          have : (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) * (900 * (N : ℝ) ^ (1 / 15 : ℝ)) =
              900 * ((N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 15 : ℝ)) := by
            ring
          rw [this, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
          norm_num
  have hB' : ((M + 1 : ℕ) * L : ℝ) * (2 * Real.sqrt N * Real.log N) ≤ 8 * 900 * (N : ℝ) ^ (9 / 10 : ℝ) := by
    calc ((M + 1 : ℕ) * L : ℝ) * (2 * Real.sqrt N * Real.log N)
        ≤ (2 * (N : ℝ) ^ (1 / 3 : ℝ) * (2 * Real.log N)) * (2 * Real.sqrt N * Real.log N) := by
          gcongr
      _ = 8 * ((N : ℝ) ^ (1 / 3 : ℝ) * Real.sqrt N * Real.log N ^ 2) := by ring
      _ ≤ 8 * (900 * (N : ℝ) ^ (9 / 10 : ℝ)) := by gcongr
      _ = _ := by ring
  have hA' : (K + 2) * Real.sqrt N * Real.log N ≤ 30 * (K + 2) * (N : ℝ) ^ (9 / 10 : ℝ) := by
    calc (K + 2) * Real.sqrt N * Real.log N = (K + 2) * (Real.sqrt N * Real.log N) := by ring
      _ ≤ (K + 2) * (30 * (N : ℝ) ^ (9 / 10 : ℝ)) := by gcongr
      _ = _ := by ring
  have : (30 * (K + 2) + 8 * 900) * (N : ℝ) ^ (9 / 10 : ℝ) =
      30 * (K + 2) * (N : ℝ) ^ (9 / 10 : ℝ) + 8 * 900 * (N : ℝ) ^ (9 / 10 : ℝ) := by ring
  linarith

end RamanujanTau.TauPNTError
