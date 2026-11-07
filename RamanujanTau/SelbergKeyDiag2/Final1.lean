/-
# M3 step 6a: polynomial bounds for the local factors

* `abs_rhoP_le`, `norm_rhoCfac_le`: `|ρ_p(a)|, |N_p(a,s)/D_p(s)| ≤ Gp(p,a)` (`Re s = 1`);
* `abs_rho_le`, `norm_rhoC_le`: `|ρ(m)|, |ρ(m, s)| ≤ M^{ω(m)} m²`;
* `two_pow_card_pf_le`: `2^{ω(m)} ≤ m`, hence `M^{ω(m)} ≤ m^K` for `M ≤ 2^K`.
Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.Phase

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex Finset PowerSeries RamanujanTau.HafnerBridge RamanujanTau.HafnerBridge2
open RamanujanTau.SelbergKey (NpC DpC rhoC)
open scoped Real

lemma inv_le_pow23 {p : ℕ} (hp : p.Prime) (j : ℕ) : ((p : ℝ)⁻¹) ^ j ≤ ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j := by
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  gcongr
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)

lemma abs_rhoP_le {M : ℝ} (hM : ∀ (p a : ℕ), p.Prime → 1 ≤ a →
      Summable (fun j : ℕ => |gseq p a j| * ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j) ∧ Gp p a ≤ M * ((p : ℝ) ^ a) ^ 2)
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) : |rhoP p a| ≤ M * ((p : ℝ) ^ a) ^ 2 := by
  obtain ⟨C, hC1, hC⟩ := lam_bound
  obtain ⟨hs2, hG⟩ := hM p a hp ha
  refine le_trans ?_ hG
  rw [← Gg_gseq hC1 hC hp a]
  unfold Gg Gp
  have hs := SN_gps hp a
  calc |∑' j : ℕ, gseq p a j * ((p : ℝ)⁻¹) ^ j| ≤ ∑' j : ℕ, ‖gseq p a j * ((p : ℝ)⁻¹) ^ j‖ := by
        rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ, |gseq p a j| * ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j := by
        refine hs.tsum_le_tsum (fun j => ?_) hs2
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((p : ℝ)⁻¹) ^ j)]
        exact mul_le_mul_of_nonneg_left (inv_le_pow23 hp j) (abs_nonneg _)

lemma norm_rhoCfac_le {M : ℝ} (hM : ∀ (p a : ℕ), p.Prime → 1 ≤ a →
      Summable (fun j : ℕ => |gseq p a j| * ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j) ∧ Gp p a ≤ M * ((p : ℝ) ^ a) ^ 2)
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) {s : ℂ} (hs : s.re = 1) :
    ‖NpC p a s / DpC p s‖ ≤ M * ((p : ℝ) ^ a) ^ 2 := by
  obtain ⟨hs2, hG⟩ := hM p a hp ha
  refine le_trans ?_ hG
  rw [← (evC_gps hp a hs).2]
  unfold evC Gp
  have hx := norm_p_cpow hp hs
  have hsn := SNC hx (SN_gps hp a)
  refine (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum (fun j => ?_) hs2)
  rw [norm_term_evC hx, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((p : ℝ)⁻¹) ^ j)]
  exact mul_le_mul_of_nonneg_left (inv_le_pow23 hp j) (abs_nonneg _)

lemma prod_pf_pow_eq {m : ℕ} (hm : m ≠ 0) :
    ∏ p ∈ m.primeFactors, ((p : ℝ) ^ (m.factorization p)) = m := by
  have h := Nat.prod_factorization_pow_eq_self hm
  rw [Finsupp.prod, Nat.support_factorization] at h
  exact_mod_cast h

lemma prod_bound {m : ℕ} (hm : 1 ≤ m) {M : ℝ} (f : ℕ → ℝ)
    (hf : ∀ p ∈ m.primeFactors, |f p| ≤ M * ((p : ℝ) ^ (m.factorization p)) ^ 2) :
    |∏ p ∈ m.primeFactors, f p| ≤ M ^ m.primeFactors.card * (m : ℝ) ^ 2 := by
  rw [Finset.abs_prod]
  calc ∏ p ∈ m.primeFactors, |f p| ≤ ∏ p ∈ m.primeFactors, M * ((p : ℝ) ^ (m.factorization p)) ^ 2 :=
        Finset.prod_le_prod (fun p _ => abs_nonneg _) hf
    _ = M ^ m.primeFactors.card * (∏ p ∈ m.primeFactors, ((p : ℝ) ^ (m.factorization p))) ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow]
    _ = _ := by rw [prod_pf_pow_eq (by omega)]

theorem abs_rho_le {M : ℝ} (hM : ∀ (p a : ℕ), p.Prime → 1 ≤ a →
      Summable (fun j : ℕ => |gseq p a j| * ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j) ∧ Gp p a ≤ M * ((p : ℝ) ^ a) ^ 2)
    {m : ℕ} (hm : 1 ≤ m) : |rho m| ≤ M ^ m.primeFactors.card * (m : ℝ) ^ 2 := by
  unfold rho
  refine prod_bound hm _ fun p hp => ?_
  exact abs_rhoP_le hM (Nat.prime_of_mem_primeFactors hp)
    ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp))

theorem norm_rhoC_le {M : ℝ} (hM : ∀ (p a : ℕ), p.Prime → 1 ≤ a →
      Summable (fun j : ℕ => |gseq p a j| * ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j) ∧ Gp p a ≤ M * ((p : ℝ) ^ a) ^ 2)
    {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : s.re = 1) :
    ‖rhoC m s‖ ≤ M ^ m.primeFactors.card * (m : ℝ) ^ 2 := by
  unfold rhoC
  rw [norm_prod]
  calc ∏ p ∈ m.primeFactors, ‖NpC p (m.factorization p) s / DpC p s‖
      ≤ ∏ p ∈ m.primeFactors, M * ((p : ℝ) ^ (m.factorization p)) ^ 2 :=
        Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p hp =>
          norm_rhoCfac_le hM (Nat.prime_of_mem_primeFactors hp)
            ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd (by omega)
              (Nat.dvd_of_mem_primeFactors hp)) hs
    _ = M ^ m.primeFactors.card * (∏ p ∈ m.primeFactors, ((p : ℝ) ^ (m.factorization p))) ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow]
    _ = _ := by rw [prod_pf_pow_eq (by omega)]

lemma two_pow_card_pf_le {m : ℕ} (hm : 1 ≤ m) : 2 ^ m.primeFactors.card ≤ m := by
  calc 2 ^ m.primeFactors.card = ∏ _p ∈ m.primeFactors, 2 := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ m.primeFactors, p := Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ m := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)

lemma pow_card_pf_le {M : ℝ} {K : ℕ} (hM0 : 0 ≤ M) (hMK : M ≤ 2 ^ K) {m : ℕ} (hm : 1 ≤ m) :
    M ^ m.primeFactors.card ≤ (m : ℝ) ^ K := by
  calc M ^ m.primeFactors.card ≤ ((2:ℝ) ^ K) ^ m.primeFactors.card := by gcongr
    _ = ((2:ℝ) ^ m.primeFactors.card) ^ K := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (m : ℝ) ^ K := by gcongr; exact_mod_cast two_pow_card_pf_le hm

end RamanujanTau.SelbergKeyDiag2
