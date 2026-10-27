/-
# The 55 seeds, and Ramanujan's conjecture for powers of 11 unconditionally

For `i < 5` and `λ ≤ 10`, `F = Y^λ S_i(Y) mod P` satisfies `F(φ) = φ^λ S_i(φ)`. By H2 and Lagrange
(`trace_of_H2`), `11·U(φ^λ g_i) = [Y¹⁰]F`, and the kernel check `seedOK` says `[Y¹⁰]F = 11·C^λ_{i,·}`.
So all three `Inputs` are theorems, and `Atkin11.ramanujan_pow11` holds unconditionally.
-/
import RamanujanTau.Atkin11Seed.H2
import RamanujanTau.Atkin11Seed.SeedCheck
import RamanujanTau.Atkin11Final

set_option autoImplicit false

namespace Atkin11Seed
open Atkin11 PowerSeries

lemma evY_iterF (y : PS) (hy : IsRoot y) : ∀ (n : ℕ) (F : PY) (lam : ℕ), lam ≤ n →
    evY y ((iterF n F).getD lam []) = y ^ lam * evY y F
  | 0, F, lam, h => by
    obtain rfl : lam = 0 := by omega
    simp [iterF]
  | n + 1, F, 0, _ => by simp [iterF]
  | n + 1, F, lam + 1, h => by
    rw [iterF, List.getD_cons_succ, evY_iterF y hy n _ lam (by omega), evY_redP y hy, evY_zero_cons]; ring

lemma ofPairs_eval (l : List (ℕ × ℤ)) : (ofPairs l).eval = lc (ofList l) := by
  rw [lc_ofList]
  induction l with
  | nil => simp [ofPairs, JE.eval_zero]
  | cons p l ih =>
    simp only [ofPairs, List.foldr_cons] at ih ⊢
    rw [JE.eval_add, ih, JE.eval_single, evZ_shiftZ, List.map_cons, List.sum_cons]
    simp only [evZ_cons, evZ_nil, mul_zero, add_zero, J, zsmul_eq_mul]
    ring

lemma seedOK_all (i : ℕ) (hi : i < 5) : seedOK i = true := by
  interval_cases i
  exacts [seedOK_0, seedOK_1, seedOK_2, seedOK_3, seedOK_4]

/-- **the 55 seeds** `U(φ^λ J_i) = Σ_ν C^λ_{i,ν} J_ν`. -/
theorem seeds_proved : ∀ lam < 11, ∀ i < 5, U (φ ^ lam * J i) = lc (seedF lam i) := by
  intro lam hlam i hi
  have h := seedOK_all i hi
  simp only [seedOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlen, hz⟩ := h lam hlam
  have ht := trace_of_H2 (gi i) (Snum i) (H2_all i hi) lam _
    (by rw [evY_iterF φ φ_isRoot 10 _ lam (by omega), evY_redP φ φ_isRoot]) hlen
  have he := JE.eval_isZero _ hz
  rw [JE.eval_add, JE.eval_smul, ofPairs_eval] at he
  rw [J_small i hi]
  have h11 : (11 : PS) ≠ 0 := fun h0 => by
    have := congrArg (constantCoeff (R := ℤ)) h0
    rw [map_ofNat, map_zero] at this
    norm_num at this
  apply mul_left_cancel₀ h11
  rw [ht, seedF]
  push_cast at he
  linear_combination he

end Atkin11Seed

namespace Atkin11

/-- **All the Atkin–Gordon inputs are theorems**: R2, the modular equation, and the 55 seeds. -/
theorem inputs_proved : Inputs := ⟨r2_proved, modeq_proved, Atkin11Seed.seeds_proved⟩

/-- **Ramanujan's conjecture for powers of 11** (Atkin 1967), unconditionally:
if `24m ≡ 1 (mod 11ʳ)`, `r ≥ 1`, then `11ʳ ∣ p(m)`. -/
theorem ramanujan_pow11_unconditional {r : ℕ} (hr : 1 ≤ r) (m : ℕ) (hm : 24 * m ≡ 1 [MOD 11 ^ r]) :
    11 ^ r ∣ Fintype.card (Nat.Partition m) :=
  ramanujan_pow11 inputs_proved hr m hm

end Atkin11
