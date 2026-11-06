/-
# The Euler sum `Σ_{d≤N} f(d)/d ≪ log N` for the local-mass majorant (κ = 1)

* `logmean_geo`: variant of `SelbergCoeffs3.logmean_upper` with `f(p^k) ≤ B (3/2)^k` for `k ≥ 2`
  (geometric instead of bounded prime-power values);
* `tt p e`: the majorant of the local mass (`1`, `|λ(p)| + 65536/p`, `16384 (e+1)^6`);
* `fT = ofLocal (tt²)`, `fT p ≤ λ(p)² + K/p`, `fT p^k ≤ B (3/2)^k`;
* **`euler_fT`** (`[DeligneBound]`): `∃ A, ∀ y ≥ 2, Σ_{d≤y²} fT(d)/d ≤ A log y`.
-/
import RamanujanTau.QFProof5.Local
import RamanujanTau.SelbergCoeffs3.LogMean
import RamanujanTau.SelbergCoeffs2.Mertens2

set_option autoImplicit false

namespace RamanujanTau.QFProof5

open Finset ArithmeticFunction RamanujanTau.QFProof3 RamanujanTau.QFProof4
open RamanujanTau.SelbergCoeffs3 (PrimesTo primesBelow_succ_eq sum_inv_sq_PrimesTo_le exp_loglog)
open RamanujanTau.SelbergCoeffs (ofLocal ofLocal_apply ofLocal_ppow isMultiplicative_ofLocal)
open RamanujanTau.HafnerBridge (lam)

/-- `logmean_upper` with geometric prime-power growth `f(p^k) ≤ B (3/2)^k` (`k ≥ 2`). -/
theorem logmean_geo (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative) (h0 : ∀ n, 0 ≤ f n)
    {B κ C : ℝ} (hB0 : 0 ≤ B) (hB : ∀ p k : ℕ, p.Prime → 2 ≤ k → f (p ^ k) ≤ B * (3 / 2 : ℝ) ^ k)
    (hS : ∀ M : ℕ, 2 ≤ M → ∑ p ∈ PrimesTo M, f p / p ≤ κ * Real.log (Real.log M) + C) :
    ∀ N : ℕ, 2 ≤ N → ∑ n ∈ Ioc 0 N, f n / n ≤ Real.exp (C + 9 * B) * Real.log N ^ κ := by
  intro N hN
  set g : ℕ → ℝ := fun n => f n / n
  have hg0 : ∀ n, 0 ≤ g n := fun n => div_nonneg (h0 n) (Nat.cast_nonneg _)
  have hg1 : g 1 = 1 := by simp [g, hf.map_one]
  have hgm : ∀ {m n : ℕ}, m.Coprime n → g (m * n) = g m * g n := fun {m n} h => by
    simp only [g, hf.map_mul_of_coprime h, Nat.cast_mul]; ring
  -- `r = 3/(2p) ≤ 3/4`
  have hr : ∀ {p : ℕ}, p.Prime → 0 ≤ (3 / 2 : ℝ) / p ∧ (3 / 2 : ℝ) / p ≤ 3 / 4 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by linarith)]; linarith
  have hloc : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, g (p ^ (k + 2)) ≤ B * ((3 / 2 : ℝ) / p) ^ (k + 2) := by
    intro p hp k
    simp only [g, Nat.cast_pow]
    rw [div_pow, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hB p (k + 2) hp (by omega)) (by positivity)
  have hgeo : ∀ {p : ℕ}, p.Prime → Summable fun k : ℕ => ((3 / 2 : ℝ) / p) ^ k := fun hp =>
    summable_geometric_of_lt_one (hr hp).1 (by linarith [(hr hp).2])
  have hsumloc : ∀ {p : ℕ}, p.Prime → Summable fun k : ℕ => ‖g (p ^ k)‖ := by
    intro p hp
    rw [← summable_nat_add_iff 2]
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      (((summable_nat_add_iff 2).mpr (hgeo hp)).mul_left B)
    rw [Real.norm_of_nonneg (hg0 _)]; exact hloc hp k
  obtain ⟨hsm, hhas⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hg1 hgm hsumloc (N + 1)
  rw [primesBelow_succ_eq] at hhas
  have hsm' : Summable fun m : (N + 1).smoothNumbers => g m := hsm.of_norm
  have hmem : ∀ n ∈ Ioc 0 N, n ∈ (N + 1).smoothNumbers := fun n hn => by
    rw [mem_Ioc] at hn
    exact Nat.mem_smoothNumbers_of_lt (by omega) (by omega)
  have h1 : ∑ n ∈ Ioc 0 N, g n ≤ ∏ p ∈ PrimesTo N, ∑' k : ℕ, g (p ^ k) := by
    rw [← hhas.tsum_eq, ← Finset.sum_subtype_of_mem g hmem]
    exact hsm'.sum_le_tsum _ (fun _ _ => hg0 _)
  have h2 : ∀ p ∈ PrimesTo N, ∑' k : ℕ, g (p ^ k) ≤ Real.exp (f p / p + 9 * B * (1 / (p : ℝ) ^ 2)) := by
    intro p hpP
    have hp : p.Prime := (mem_filter.mp hpP).2
    have hs : Summable fun k : ℕ => g (p ^ k) := (hsumloc hp).of_norm
    obtain ⟨hr0, hr1⟩ := hr hp
    set r := (3 / 2 : ℝ) / p with hrdef
    rw [← hs.sum_add_tsum_nat_add 2]
    have e : ∑ k ∈ range 2, g (p ^ k) = 1 + f p / p := by
      simp [sum_range_succ, g, hf.map_one]
    have htail : ∑' k : ℕ, g (p ^ (k + 2)) ≤ ∑' k : ℕ, B * r ^ (k + 2) :=
      ((summable_nat_add_iff 2).mpr hs).tsum_le_tsum (fun k => hloc hp k)
        (((summable_nat_add_iff 2).mpr (hgeo hp)).mul_left B)
    have hgv : ∑' k : ℕ, B * r ^ (k + 2) = B * (r ^ 2 * (1 - r)⁻¹) := by
      rw [tsum_mul_left]
      simp_rw [pow_add, mul_comm _ (r ^ 2)]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 (by linarith)]
    have h14 : (1 - r)⁻¹ ≤ 4 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hr2 : r ^ 2 = 9 / 4 * (1 / (p : ℝ) ^ 2) := by rw [hrdef, div_pow]; ring
    have hb : B * (r ^ 2 * (1 - r)⁻¹) ≤ 9 * B * (1 / (p : ℝ) ^ 2) := by
      have := mul_le_mul_of_nonneg_left h14 (sq_nonneg r)
      rw [hr2] at this ⊢
      have hq : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
      nlinarith
    rw [e]
    have := Real.add_one_le_exp (f p / p + 9 * B * (1 / (p : ℝ) ^ 2))
    linarith
  have h3 : ∏ p ∈ PrimesTo N, ∑' k : ℕ, g (p ^ k) ≤
      Real.exp (∑ p ∈ PrimesTo N, (f p / p + 9 * B * (1 / (p : ℝ) ^ 2))) := by
    rw [Real.exp_sum]
    exact prod_le_prod (fun p _ => tsum_nonneg fun _ => hg0 _) h2
  have h4 : ∑ p ∈ PrimesTo N, (f p / p + 9 * B * (1 / (p : ℝ) ^ 2)) ≤
      κ * Real.log (Real.log N) + C + 9 * B := by
    rw [sum_add_distrib, ← mul_sum]
    have := sum_inv_sq_PrimesTo_le N
    have := hS N hN
    nlinarith
  calc ∑ n ∈ Ioc 0 N, f n / n = ∑ n ∈ Ioc 0 N, g n := rfl
    _ ≤ _ := h1.trans h3
    _ ≤ Real.exp (κ * Real.log (Real.log N) + C + 9 * B) := Real.exp_le_exp.mpr h4
    _ = Real.exp (C + 9 * B) * Real.log N ^ κ := by
        rw [← exp_loglog hN κ, ← Real.exp_add]; ring_nf

/-- The majorant of the local masses. -/
noncomputable def tt (p e : ℕ) : ℝ :=
  if e = 0 then 1 else if e = 1 then |lam p| + 65536 * Xp p else 16384 * ((e : ℝ) + 1) ^ 6

lemma tt_nonneg (p e : ℕ) : 0 ≤ tt p e := by
  unfold tt Xp; split_ifs <;> positivity

/-- `fT = ofLocal (tt²)`. -/
noncomputable def fT : ArithmeticFunction ℝ := ofLocal fun p e => tt p e ^ 2

lemma fT_nonneg (n : ℕ) : 0 ≤ fT n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [fT, ofLocal_apply _ hn, Finsupp.prod]
  exact prod_nonneg fun _ _ => sq_nonneg _

lemma fT_eq {n : ℕ} (hn : n ≠ 0) : fT n = ∏ p ∈ n.primeFactors, tt p (n.factorization p) ^ 2 := by
  rw [fT, ofLocal_apply _ hn, Finsupp.prod, Nat.support_factorization]

lemma fT_ppow {p : ℕ} (hp : p.Prime) (k : ℕ) : fT (p ^ k) = tt p k ^ 2 :=
  ofLocal_ppow (h := fun p e => tt p e ^ 2) (fun p => by simp [tt]) hp k

/-- `K` with `fT(p) ≤ λ(p)² + K/p`. -/
noncomputable def Kp : ℝ := 4 * 65536 + 65536 ^ 2

section Deligne

variable [DeligneBound]

lemma fT_prime_le {p : ℕ} (hp : p.Prime) : fT p ≤ lam p ^ 2 + Kp * Xp p := by
  have h := fT_ppow hp 1
  rw [pow_one] at h
  rw [h]
  simp only [tt, one_ne_zero, if_false, if_true]
  have hl := abs_lam_le_two hp
  have hX := Xp_pos hp
  have hX2 := Xp_le_half hp
  have : (|lam p| + 65536 * Xp p) ^ 2 = lam p ^ 2 + 2 * 65536 * |lam p| * Xp p + 65536 ^ 2 * Xp p ^ 2 := by
    rw [add_sq, sq_abs]; ring
  rw [this, Kp]
  have h1 : 2 * 65536 * |lam p| * Xp p ≤ 4 * 65536 * Xp p := by nlinarith
  have h2 : (65536 : ℝ) ^ 2 * Xp p ^ 2 ≤ 65536 ^ 2 * Xp p := by nlinarith
  nlinarith

lemma fT_ppow_le {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    fT (p ^ k) ≤ (16384 ^ 2 * (100 / 3 : ℝ) ^ 12) * (3 / 2 : ℝ) ^ k := by
  rw [fT_ppow hp]
  simp only [tt, show k ≠ 0 by omega, show k ≠ 1 by omega, if_false]
  have := poly_le_geom k
  rw [mul_pow, ← pow_mul]
  norm_num
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3 / 2) k]

/-- **The Euler sum with κ = 1.** -/
theorem euler_fT : ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℕ, 2 ≤ y →
    ∑ d ∈ Icc 1 (y ^ 2), fT d / d ≤ A * Real.log y := by
  obtain ⟨Cm, hCm⟩ := RamanujanTau.SelbergCoeffs2.mertens2_bound
  set B : ℝ := 16384 ^ 2 * (100 / 3 : ℝ) ^ 12
  have hB0 : 0 ≤ B := by positivity
  have hS : ∀ M : ℕ, 2 ≤ M → ∑ p ∈ PrimesTo M, fT p / p ≤ 1 * Real.log (Real.log M) + (Cm + Kp) := by
    intro M hM
    have hm := (abs_le.1 (hCm M)).2
    have hpt : ∀ p ∈ PrimesTo M, fT p / p ≤ RamanujanTau.EdgeNonvanishing.lam p ^ 2 / p +
        Kp * (1 / (p : ℝ) ^ 2) := by
      intro p hpP
      have hp : p.Prime := (mem_filter.mp hpP).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have h := fT_prime_le hp
      rw [lam_prime_eq hp] at h
      have : fT p / p ≤ (RamanujanTau.EdgeNonvanishing.lam p ^ 2 + Kp * Xp p) / p :=
        div_le_div_of_nonneg_right h hp0.le
      refine this.trans (le_of_eq ?_)
      unfold Xp; field_simp
    have hsq := sum_inv_sq_PrimesTo_le M
    have hK : (0 : ℝ) ≤ Kp := by unfold Kp; norm_num
    calc ∑ p ∈ PrimesTo M, fT p / p
        ≤ ∑ p ∈ PrimesTo M, (RamanujanTau.EdgeNonvanishing.lam p ^ 2 / p + Kp * (1 / (p : ℝ) ^ 2)) :=
          sum_le_sum hpt
      _ = ∑ p ∈ PrimesTo M, RamanujanTau.EdgeNonvanishing.lam p ^ 2 / p +
            Kp * ∑ p ∈ PrimesTo M, 1 / (p : ℝ) ^ 2 := by rw [sum_add_distrib, mul_sum]
      _ ≤ (Real.log (Real.log M) + Cm) + Kp * 1 := by
          refine add_le_add ?_ (mul_le_mul_of_nonneg_left hsq hK)
          have : PrimesTo M = (Ioc 0 M).filter Nat.Prime := rfl
          rw [this]; linarith
      _ = _ := by ring
  have hL := logmean_geo fT isMultiplicative_ofLocal fT_nonneg hB0
    (fun p k hp hk => fT_ppow_le hp hk) hS
  refine ⟨2 * Real.exp (Cm + Kp + 9 * B), by positivity, fun y hy => ?_⟩
  have hy2 : 2 ≤ y ^ 2 := by nlinarith
  have h := hL (y ^ 2) hy2
  rw [Real.rpow_one] at h
  have hI : Icc 1 (y ^ 2) = Ioc 0 (y ^ 2) := by ext; simp only [mem_Icc, mem_Ioc]; omega
  rw [hI]
  refine h.trans (le_of_eq ?_)
  push_cast
  rw [Real.log_pow]; push_cast; ring

end Deligne

end RamanujanTau.QFProof5
