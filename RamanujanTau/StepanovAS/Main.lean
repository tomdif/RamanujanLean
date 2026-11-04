/-
# Weil's bound for Kloosterman sums, unconditionally

* `sum_units_eq_sum_fiber`: `K_r = ∑_{c ∈ F_p} ψ(c) · #S_c`, `S_c = {x ∈ L^× : Tr(x + b/x) = c}`.
* `norm_sum_le_of_fiber_le`: one-sided bounds `#S_c ≤ B` for all `c` give
  `|K_r| ≤ p B − (q − 1)` (since `∑ ψ(c) = 0` and `∑ #S_c = q − 1`).
* `norm_klGF_le`: for `r ≥ 6`, `|K_r(1,b;p)| ≤ (3p² + 1) p^{⌈r/2⌉}`.
* `stepanovKloostermanEventually`: the named hypothesis of `KloostermanL/Main.lean`, proved.
* `weilPrimeBound`: `|S(1,b;p)| ≤ 2√p` for every prime `p` and `b ≢ 0`.
* `tau_isBigO_23_4_unconditional`: `τ(n) = O(n^{23/4+ε})`.
-/
import RamanujanTau.StepanovAS.Kloosterman
import RamanujanTau.KloostermanL.Main

set_option autoImplicit false

namespace RamanujanTau.StepanovAS

open Polynomial Finset
open scoped Classical

variable (p : ℕ) [hp : Fact p.Prime]
variable (L : Type*) [Field L] [Fintype L] [Algebra (ZMod p) L]

/-- `K = ∑_{c} #S_c · ψ(c)`. -/
theorem sum_units_eq_sum_fiber (ψ : AddChar (ZMod p) ℂ) (b : ZMod p) :
    ∑ x : Lˣ, ψ (Algebra.trace (ZMod p) L (algebraMap (ZMod p) L 1 * x +
      algebraMap (ZMod p) L b * ((x⁻¹ : Lˣ) : L))) =
      ∑ c : ZMod p, ((traceFiber p L b c).card : ℂ) * ψ c := by
  set F : L → ZMod p := fun y => Algebra.trace (ZMod p) L (y + algebraMap (ZMod p) L b * y⁻¹)
  set T : Finset L := Finset.univ.filter (fun y : L => y ≠ 0)
  have h1 : ∑ x : Lˣ, ψ (Algebra.trace (ZMod p) L (algebraMap (ZMod p) L 1 * x +
      algebraMap (ZMod p) L b * ((x⁻¹ : Lˣ) : L))) = ∑ y ∈ T, ψ (F y) := by
    rw [Finset.sum_subtype T (p := fun y : L => y ≠ 0) (by simp [T])]
    refine Fintype.sum_equiv unitsEquivNeZero _ _ fun x => ?_
    simp [F, unitsEquivNeZero]
  rw [h1, ← Finset.sum_fiberwise T F]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hT : T.filter (fun y => F y = c) = traceFiber p L b c := by
    ext y; simp [T, F, traceFiber]
  rw [hT, Finset.sum_congr rfl (g := fun _ => ψ c) (fun y hy =>
    congrArg ψ (Finset.mem_filter.mp hy).2.2)]
  simp

theorem sum_card_fiber (b : ZMod p) : ∑ c : ZMod p, (traceFiber p L b c).card = Fintype.card L - 1 := by
  set F : L → ZMod p := fun y => Algebra.trace (ZMod p) L (y + algebraMap (ZMod p) L b * y⁻¹)
  set T : Finset L := Finset.univ.filter (fun y : L => y ≠ 0)
  have hT : ∀ c, T.filter (fun y => F y = c) = traceFiber p L b c := by
    intro c; ext y; simp [T, F, traceFiber]
  have := Finset.card_eq_sum_card_fiberwise (s := T) (t := Finset.univ) (f := F)
    (fun _ _ => Finset.mem_univ _)
  simp_rw [hT] at this
  rw [← this]
  simp only [T, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/-- **From one-sided fibre bounds to the character sum.** -/
theorem norm_sum_le_of_fiber_le (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1) (b : ZMod p) (B : ℕ)
    (hB : ∀ c, (traceFiber p L b c).card ≤ B) :
    ‖∑ c : ZMod p, ((traceFiber p L b c).card : ℂ) * ψ c‖ ≤
      (p * B : ℝ) - (Fintype.card L - 1 : ℕ) := by
  have hsum0 : ∑ c : ZMod p, ψ c = 0 := AddChar.sum_eq_zero_of_ne_one hψ
  have e : ∑ c : ZMod p, ((traceFiber p L b c).card : ℂ) * ψ c =
      ∑ c : ZMod p, (((traceFiber p L b c).card : ℂ) - B) * ψ c := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum0, mul_zero, sub_zero]
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ c, ‖(((traceFiber p L b c).card : ℂ) - B) * ψ c‖ =
      (B : ℝ) - (traceFiber p L b c).card := by
    intro c
    rw [norm_mul, AddChar.norm_apply, mul_one]
    have : (((traceFiber p L b c).card : ℂ) - B) = (((traceFiber p L b c).card : ℝ) - B : ℝ) := by
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg (by have := hB c; rw [sub_nonneg]; exact_mod_cast this)]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have := sum_card_fiber p L b
  rw [← this]
  push_cast
  exact le_rfl

/-- **The Stepanov bound for Kloosterman sums over `F_{p^r}`**, `r ≥ 6`:
`|K_r(1,b;p)| ≤ 3p²·p^{r - ⌊r/2⌋} + 1`. -/
theorem norm_klL_le (b : ZMod p) {r : ℕ} (hr6 : 6 ≤ r) (hr : Module.finrank (ZMod p) L = r) :
    ‖KloostermanL.klL L ZMod.stdAddChar 1 b‖ ≤ 3 * (p : ℝ) ^ 2 * (p : ℝ) ^ (r - r / 2) + 1 := by
  have hψ : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := fun h =>
    ZMod.isPrimitive_stdAddChar p (one_ne_zero (α := ZMod p)) (by rw [h]; ext x; simp)
  set s := r / 2
  set t := r - r / 2
  have hst : r = s + t := by omega
  have hB := card_traceFiber_le p L (s := s) (t := t) (by omega) (by omega) (by omega)
    (by rw [hr]; exact hst) b
  unfold KloostermanL.klL
  rw [sum_units_eq_sum_fiber]
  refine (norm_sum_le_of_fiber_le p L _ hψ b _ hB).trans (le_of_eq ?_)
  have hq : Fintype.card L = p ^ (s - 1) * p * p ^ t := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card, hr, hst, pow_add, ← pow_succ]
    congr 2; omega
  have hq1 : 1 ≤ Fintype.card L := Fintype.card_pos
  rw [Nat.cast_sub hq1, hq]
  push_cast
  ring

/-- the bound in the form `C · √p^r`. -/
theorem norm_klGF_le (b : ZMod p) {r : ℕ} (hr6 : 6 ≤ r) :
    ‖KloostermanL.klGF p r 1 b‖ ≤ (3 * (p : ℝ) ^ 2 + 1) * Real.sqrt p * Real.sqrt p ^ r := by
  letI : Fintype (GaloisField p r) := Fintype.ofFinite _
  rw [KloostermanL.klGF_def]
  have hfr : Module.finrank (ZMod p) (GaloisField p r) = r := GaloisField.finrank p (by omega)
  refine (norm_klL_le p (GaloisField p r) b hr6 hfr).trans ?_
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hs1 : 1 ≤ Real.sqrt p := Real.one_le_sqrt.mpr hp1
  have hpt : (p : ℝ) ^ (r - r / 2) ≤ Real.sqrt p * Real.sqrt p ^ r := by
    have hsq : (p : ℝ) = Real.sqrt p ^ 2 := (Real.sq_sqrt (by positivity)).symm
    calc (p : ℝ) ^ (r - r / 2) = (Real.sqrt p ^ 2) ^ (r - r / 2) := by
          conv_lhs => rw [hsq]
      _ = Real.sqrt p ^ (2 * (r - r / 2)) := by rw [← pow_mul]
      _ ≤ Real.sqrt p ^ (r + 1) := pow_le_pow_right₀ hs1 (by omega)
      _ = Real.sqrt p * Real.sqrt p ^ r := by rw [pow_succ']
  have hpt1 : (1 : ℝ) ≤ (p : ℝ) ^ (r - r / 2) := one_le_pow₀ hp1
  calc 3 * (p : ℝ) ^ 2 * (p : ℝ) ^ (r - r / 2) + 1
      ≤ (3 * (p : ℝ) ^ 2 + 1) * (p : ℝ) ^ (r - r / 2) := by nlinarith
    _ ≤ (3 * (p : ℝ) ^ 2 + 1) * (Real.sqrt p * Real.sqrt p ^ r) :=
        mul_le_mul_of_nonneg_left hpt (by positivity)
    _ = _ := by ring

end RamanujanTau.StepanovAS

namespace RamanujanTau.StepanovAS

/-- **`StepanovKloostermanEventually`, proved** (Stepanov's method for `y^p − y = x + b/x`). -/
theorem stepanovKloostermanEventually : KloostermanL.StepanovKloostermanEventually := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  intro b _
  exact ⟨(3 * (p : ℝ) ^ 2 + 1) * Real.sqrt p, 6, fun r hr => norm_klGF_le p b hr⟩

/-- **Weil's bound** `|S(1,b;p)| ≤ 2√p` for all primes `p` and `b ≢ 0 (mod p)`. -/
theorem weilPrimeBound : WeilKloosterman.WeilPrimeBound :=
  KloostermanL.weilPrimeBound_of_stepanovEventually stepanovKloostermanEventually

/-- **Weil's exponent for `τ`, unconditionally**: `τ(n) = O(n^{23/4+ε})`. -/
theorem tau_isBigO_23_4_unconditional (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (RamanujanTau.tau n : ℝ)) =O[Filter.atTop]
      fun n => (n : ℝ) ^ ((23 / 4 : ℝ) + ε) :=
  WeilKloosterman.tau_isBigO_23_4_of_weil weilPrimeBound ε hε

end RamanujanTau.StepanovAS

#print axioms RamanujanTau.StepanovAS.stepanov_hasse_card_le
#print axioms RamanujanTau.StepanovAS.card_traceFiber_le
#print axioms RamanujanTau.StepanovAS.norm_klL_le
#print axioms RamanujanTau.StepanovAS.norm_klGF_le
#print axioms RamanujanTau.StepanovAS.stepanovKloostermanEventually
#print axioms RamanujanTau.StepanovAS.weilPrimeBound
#print axioms RamanujanTau.StepanovAS.tau_isBigO_23_4_unconditional
