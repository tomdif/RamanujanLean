/-
# Twisting the AFE: reindexing `(M, N) ↦ (kM, hN)` and polarisation

* `wq c t q = (xy)^{−1/2} (y/x)^{it} V(log xy − c − 2 log(t/2π))` (`x = q.1+1`, `y = q.2+1`).
* `bG2 a b c t q = a(x) b(y) wq c t q`.
* `twist_reindex`: `(Σ_p bD_t(p)) (h/k)^{it} = √(hk) Σ_q bG2 ι_k ι_h (log hk) t q`.
* `polarise`: `bG2 α β + bG2 β α = (bG2 g₊ g₊ − bG2 g₋ g₋)/(2r²)` for `g_± = r(α ± β)`.
-/
import RamanujanTau.TwistedMoment.TwSeq

set_option autoImplicit false

namespace RamanujanTau.TwistedMoment

open Complex Finset
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm

noncomputable def wq (c t : ℝ) (q : ℕ × ℕ) : ℂ :=
  ((Real.exp (-((lg q.1 + lg q.2) / 2)) : ℝ) : ℂ) * cexp (t * I * ((lg q.2 - lg q.1 : ℝ) : ℂ)) *
    ((V (lg q.1 + lg q.2 - c - 2 * ellT t) : ℝ) : ℂ)

noncomputable def bG2 (a b : ℕ → ℝ) (c t : ℝ) (q : ℕ × ℕ) : ℂ := ((a (q.1 + 1) * b (q.2 + 1) : ℝ) : ℂ) * wq c t q

lemma lg_mul {a : ℕ} (ha : 1 ≤ a) (m : ℕ) : lg (a * (m + 1) - 1) = Real.log a + lg m := by
  unfold lg
  have h1 : 1 ≤ a * (m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [show ((a * (m + 1) - 1 : ℕ) : ℝ) + 1 = (a : ℝ) * ((m : ℝ) + 1) by
    rw [Nat.cast_sub h1]; push_cast; ring]
  rw [Real.log_mul (by positivity) (by positivity)]

lemma iota_mul {a : ℕ} (ha : 1 ≤ a) (m : ℕ) : iota a (a * (m + 1) - 1 + 1) = lamS (m + 1) := by
  have h1 : 1 ≤ a * (m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [Nat.sub_add_cancel h1]
  unfold iota
  rw [if_pos (dvd_mul_right a _), Nat.mul_div_cancel_left _ (by omega)]

/-- Pointwise identity for the reindexed terms. -/
lemma bG2_reindex {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) (t : ℝ) (p : ℕ × ℕ) :
    bG2 (iota k) (iota h) (Real.log ((h * k : ℕ) : ℝ)) t (k * (p.1 + 1) - 1, h * (p.2 + 1) - 1) =
      ((Real.sqrt ((h * k : ℕ) : ℝ))⁻¹ : ℂ) *
        (bD t (2 * ellT t) p * cexp (t * I * ((Real.log h - Real.log k : ℝ) : ℂ))) := by
  unfold bG2 wq bD coefD
  simp only
  rw [iota_mul hk, iota_mul hh, lg_mul hk, lg_mul hh]
  simp only [lamS]
  rw [GoodSecondTerm2.lam_succ_eq, GoodSecondTerm2.lam_succ_eq]
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog : Real.log ((h * k : ℕ) : ℝ) = Real.log h + Real.log k := by
    push_cast; exact Real.log_mul hhr.ne' hkr.ne'
  have hsq : (Real.sqrt ((h * k : ℕ) : ℝ))⁻¹ = Real.exp (-((Real.log k + Real.log h) / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity), Real.rpow_def_of_pos (by push_cast; positivity),
      hlog]
    congr 1; ring
  rw [← Complex.ofReal_inv, hsq, hlog]
  have eV : Real.log k + lg p.1 + (Real.log h + lg p.2) - (Real.log h + Real.log k) - 2 * ellT t =
      lg p.1 + lg p.2 - 2 * ellT t := by ring
  rw [eV]
  have eE : Real.exp (-((Real.log k + lg p.1 + (Real.log h + lg p.2)) / 2)) =
      Real.exp (-((Real.log k + Real.log h) / 2)) * Real.exp (-((lg p.1 + lg p.2) / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have eC : Real.exp (-(11 / 2 * lg p.1)) * Real.exp (-(11 / 2 * lg p.2)) * Real.exp (-((lg p.1 + lg p.2) / 2)) =
      Real.exp (-(6 * (lg p.1 + lg p.2))) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have eP : cexp (t * I * (((Real.log h + lg p.2) - (Real.log k + lg p.1) : ℝ) : ℂ)) =
      cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) * cexp (t * I * ((Real.log h - Real.log k : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [eE, eP]
  have : (((((tau (p.1 + 1) : ℤ) : ℝ) * Real.exp (-(11 / 2 * lg p.1)) *
      (((tau (p.2 + 1) : ℤ) : ℝ) * Real.exp (-(11 / 2 * lg p.2)))) : ℝ) : ℂ) *
      (((Real.exp (-((Real.log k + Real.log h) / 2)) * Real.exp (-((lg p.1 + lg p.2) / 2))) : ℝ) : ℂ) =
      ((Real.exp (-((Real.log k + Real.log h) / 2)) : ℝ) : ℂ) *
        (((((tau (p.1 + 1) : ℤ) : ℝ) * ((tau (p.2 + 1) : ℤ) : ℝ) * Real.exp (-(6 * (lg p.1 + lg p.2)))) : ℝ) : ℂ) := by
    rw [← eC]; push_cast; ring
  linear_combination (cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) *
      cexp (t * I * ((Real.log h - Real.log k : ℝ) : ℂ)) * ((V (lg p.1 + lg p.2 - 2 * ellT t) : ℝ) : ℂ)) * this

/-- **Reindexing.** -/
theorem twist_reindex {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) (t : ℝ) :
    (∑' p, bD t (2 * ellT t) p) * cexp (t * I * ((Real.log h - Real.log k : ℝ) : ℂ)) =
      (Real.sqrt ((h * k : ℕ) : ℝ) : ℂ) * ∑' q, bG2 (iota k) (iota h) (Real.log ((h * k : ℕ) : ℝ)) t q := by
  set G : ℕ × ℕ → ℕ × ℕ := fun p => (k * (p.1 + 1) - 1, h * (p.2 + 1) - 1) with hG
  have hGinj : Function.Injective G := by
    intro p q hpq
    simp only [hG, Prod.mk.injEq] at hpq
    have a1 : 1 ≤ k * (p.1 + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have a2 : 1 ≤ k * (q.1 + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have a3 : 1 ≤ h * (p.2 + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have a4 : 1 ≤ h * (q.2 + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have e1 : k * (p.1 + 1) = k * (q.1 + 1) := by omega
    have e2 : h * (p.2 + 1) = h * (q.2 + 1) := by omega
    have := Nat.eq_of_mul_eq_mul_left (by omega) e1
    have := Nat.eq_of_mul_eq_mul_left (by omega) e2
    ext <;> omega
  set F := bG2 (iota k) (iota h) (Real.log ((h * k : ℕ) : ℝ)) t with hF
  have hsupp : Function.support F ⊆ Set.range G := by
    intro q hq
    rw [Function.mem_support] at hq
    simp only [hF, bG2] at hq
    have h1 : iota k (q.1 + 1) ≠ 0 := by intro h0; apply hq; simp [h0]
    have h2 : iota h (q.2 + 1) ≠ 0 := by intro h0; apply hq; simp [h0]
    unfold iota at h1 h2
    have d1 : k ∣ q.1 + 1 := by by_contra hc; exact h1 (if_neg hc)
    have d2 : h ∣ q.2 + 1 := by by_contra hc; exact h2 (if_neg hc)
    obtain ⟨M, hM⟩ := d1
    obtain ⟨N, hN⟩ := d2
    have hM1 : 1 ≤ M := by rcases Nat.eq_zero_or_pos M with h0 | h0 <;> [simp [h0] at hM; exact h0]
    have hN1 : 1 ≤ N := by rcases Nat.eq_zero_or_pos N with h0 | h0 <;> [simp [h0] at hN; exact h0]
    refine ⟨(M - 1, N - 1), ?_⟩
    simp only [hG]
    rw [Nat.sub_add_cancel hM1, Nat.sub_add_cancel hN1, ← hM, ← hN]
    ext <;> simp
  rw [← hGinj.tsum_eq hsupp]
  simp only [hF, hG]
  simp_rw [bG2_reindex hh hk t]
  rw [tsum_mul_left, tsum_mul_right, ← mul_assoc]
  have hs : (0 : ℝ) < Real.sqrt ((h * k : ℕ) : ℝ) := Real.sqrt_pos.mpr (by
    have : 1 ≤ h * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this)
  have hs' : (Real.sqrt ((h * k : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hs'), one_mul]

/-- **Polarisation.** -/
lemma polarise (α β : ℕ → ℝ) {r : ℝ} (hr : r ≠ 0) (c t : ℝ) (q : ℕ × ℕ) :
    bG2 α β c t q + bG2 β α c t q =
      ((1 / (2 * r ^ 2) : ℝ) : ℂ) * (bG2 (fun n => r * (α n + 1 * β n)) (fun n => r * (α n + 1 * β n)) c t q -
        bG2 (fun n => r * (α n + (-1) * β n)) (fun n => r * (α n + (-1) * β n)) c t q) := by
  unfold bG2
  have hr2 : (r : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 hr
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  push_cast
  field_simp
  ring

end RamanujanTau.TwistedMoment
