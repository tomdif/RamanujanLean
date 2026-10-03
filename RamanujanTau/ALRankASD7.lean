/-
# Atkin–Swinnerton-Dyer rank equalities mod 7

`decomp` rewritten in a canonical form `R(ζ) = Σ_t C(P_t(ζ)) G_t` (31 class-pure `ζ`-free pieces); with
`rank_eq_of_decomp` this gives every equality `N(a,7,7n+c) = N(b,7,7n+c)`.
-/
import RamanujanTau.ALRankASD7Count

set_option autoImplicit false

namespace ALz
open HahnSeries

/-- the `ζ`-free pieces of `R(ζ)` (canonical form). -/
noncomputable def Gs : Fin 31 → L := ![
  1,
  mono (0) (1 : ℂ) * (Ab hP (a := 77) (β := 7) (by norm_num) (by norm_num) 1 1 / θ hP 7 1),
  mono (-1) (1 : ℂ) * (Ab hP (a := 56) (β := 7) (by norm_num) (by norm_num) 1 1 / θ hP 7 1),
  mono (-5) (1 : ℂ) * (Ab hP (a := 35) (β := 7) (by norm_num) (by norm_num) 1 1 / θ hP 7 1),
  mono (-12) (1 : ℂ) * (Ab hP (a := 14) (β := 7) (by norm_num) (by norm_num) 1 1 / θ hP 7 1),
  mono (-22) (1 : ℂ) * (Ab hP (a := -7) (β := 140) (by norm_num) (by norm_num) 1 1 / θ hP 140 1),
  mono (-35) (1 : ℂ) * (Ab hP (a := -28) (β := 140) (by norm_num) (by norm_num) 1 1 / θ hP 140 1),
  mono (-51) (1 : ℂ) * (Ab hP (a := -49) (β := 140) (by norm_num) (by norm_num) 1 1 / θ hP 140 1),
  mono (0) (1 : ℂ) * (Ab hP (a := 70) (β := 7) (by norm_num) (by norm_num) 1 1 / θ hP 7 1),
  mono (-2) (1 : ℂ) * (Ab hP (a := 49) (β := 7) (by norm_num) (by norm_num) 1 1 / θ hP 7 1),
  mono (-7) (1 : ℂ) * (Ab hP (a := 28) (β := 7) (by norm_num) (by norm_num) 1 1 / θ hP 7 1),
  mono (-15) (1 : ℂ) * (Ab hP (a := 7) (β := 7) (by norm_num) (by norm_num) 1 1 / θ hP 7 1),
  mono (-26) (1 : ℂ) * (Ab hP (a := -14) (β := 140) (by norm_num) (by norm_num) 1 1 / θ hP 140 1),
  mono (-40) (1 : ℂ) * (Ab hP (a := -35) (β := 140) (by norm_num) (by norm_num) 1 1 / θ hP 140 1),
  mono (-57) (1 : ℂ) * (Ab hP (a := -56) (β := 140) (by norm_num) (by norm_num) 1 1 / θ hP 140 1),
  mono 0 (1 : ℂ) * ((θ hP 14 1) * ((-hs (kF hP 0))) / (((θ hP 7 1) ^ 2) * (θ hP 63 1))),
  mono 0 (1 : ℂ) * (((-hs (kF hP 0))) * (mono 7 (1:ℂ)) / ((θ hP 21 1) * (θ hP 49 1))),
  mono 0 (1 : ℂ) * ((θ hP 14 1) * (θ hP 56 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 21 1) * (θ hP 35 1) * (θ hP 49 1))),
  mono 0 (1 : ℂ) * ((θ hP 28 1) * (θ hP 56 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 49 1))),
  mono 0 (1 : ℂ) * ((θ hP 70 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 49 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 14 1) * (θ hP 35 1) * (θ hP 42 1) * (θ hP 56 1) * (θ hP 63 1))),
  mono 1 (1 : ℂ) * ((θ hP 49 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 42 1) * (θ hP 56 1))),
  mono 2 (1 : ℂ) * (((-hs (kF hP 0))) * ((mono 7 (1:ℂ)) ^ 2) / ((θ hP 49 1) * (θ hP 63 1))),
  mono 2 (1 : ℂ) * ((θ hP 56 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 49 1) * (θ hP 63 1))),
  mono 2 (1 : ℂ) * ((θ hP 70 1) * (θ hP 42 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 21 1) * (θ hP 49 1) * (θ hP 63 1) * (mono 7 (1:ℂ)))),
  mono 2 (1 : ℂ) * ((θ hP 14 1) * (θ hP 35 1) * (θ hP 49 1) * (θ hP 63 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 56 1))),
  mono 3 (1 : ℂ) * ((θ hP 49 1) * ((-hs (kF hP 0))) / ((θ hP 14 1) * (θ hP 35 1) * (θ hP 63 1))),
  mono 4 (1 : ℂ) * ((θ hP 49 1) * ((-hs (kF hP 0))) / ((θ hP 70 1) * (θ hP 21 1) * (θ hP 28 1))),
  mono 6 (1 : ℂ) * (((-hs (kF hP 0))) * (mono 7 (1:ℂ)) / ((θ hP 42 1) * (θ hP 49 1))),
  mono 6 (1 : ℂ) * ((θ hP 35 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 49 1) * (θ hP 63 1))),
  mono 6 (1 : ℂ) * ((θ hP 35 1) * (θ hP 56 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 14 1) * (θ hP 42 1) * (θ hP 49 1) * ((mono 7 (1:ℂ)) ^ 2))),
  mono 6 (1 : ℂ) * ((θ hP 7 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 56 1) * ((-hs (kF hP 0))) / ((θ hP 70 1) * (θ hP 14 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 35 1) * (θ hP 63 1)))]

/-- their classes mod 7. -/
def cs : Fin 31 → ℕ := ![0, 0, 6, 2, 2, 6, 0, 5, 0, 5, 0, 6, 2, 2, 6, 0, 0, 0, 0, 0, 1, 2, 2, 2, 2, 3, 4, 6, 6, 6, 6]

/-- their `ζ`-coefficient vectors (exponents mod 7). -/
def vs : Fin 31 → Fin 7 → ℤ := ![
  ![1, -1, 0, 0, 0, 0, 0],
  ![-1, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, -1, 0],
  ![0, -1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, -1],
  ![0, 0, -1, 1, 0, 0, 0],
  ![-1, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, -1, 1, 0, 0],
  ![1, 0, 0, 0, 0, 0, -1],
  ![0, 0, 0, 1, -1, 0, 0],
  ![-1, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, -1, 0],
  ![0, -1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, -1],
  ![0, 0, -1, 1, 0, 0, 0],
  ![-1, 1, 0, 0, 0, 0, 0],
  ![3, 0, 1, 1, 1, 1, 0],
  ![-3, 0, -1, -1, -1, -1, 0],
  ![3, 0, 1, 1, 1, 1, 0],
  ![-2, 0, -1, -1, -1, -1, 0],
  ![1, 0, 0, 0, 0, 0, 0],
  ![-1, 0, -2, -1, -1, -2, 0],
  ![1, 0, 2, 1, 1, 2, 0],
  ![1, 0, 2, 1, 1, 2, 0],
  ![-1, 0, -1, -1, -1, -1, 0],
  ![1, 0, 1, 0, 0, 1, 0],
  ![0, 0, -1, 0, 0, -1, 0],
  ![0, 0, 1, -1, -1, 1, 0],
  ![0, 0, -1, 1, 1, -1, 0],
  ![0, 0, -1, 1, 1, -1, 0],
  ![-1, 0, 0, -1, -1, 0, 0]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem decomp2 {ζ : ℂ} (h7 : ζ ^ 7 = 1) (hζ : ζ ≠ 1) :
    ι1 (CrankProof.Dser ζ ζ⁻¹) = ∑ t, HahnSeries.C (Pv (fun k => (vs t k : ℂ)) ζ) * Gs t := by
  rw [decomp h7 hζ]
  unfold msum ThetaG Gs vs Pv
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons,
    Fin.val_zero, Fin.val_succ, spCX, spA, c2]
  have p7 : ∀ k : ℕ, (ζ ^ k) ^ 7 = 1 := fun k => by rw [← pow_mul, mul_comm, pow_mul, h7, one_pow]
  simp only [p7, mul_one]
  simp only [mono]
  set q : L := single 1 (1 : ℂ) with hq
  have hsq : ∀ (e : ℤ) (c : ℂ), (single e c : L) = q ^ e * HahnSeries.C c := fun e c => by
    rw [hq, ← mono, mono_zpow, HahnSeries.C_apply, mono, single_mul_single]; simp
  simp only [hsq, map_mul, map_pow, map_inv₀, map_neg, map_one, map_zpow₀, map_sub, map_ofNat, map_add, map_intCast,
    map_zero]
  set Z : L := HahnSeries.C ζ with hZ
  have hZ7 : Z ^ 7 = 1 := by rw [hZ, ← map_pow, h7, map_one]
  have r7 : Z ^ 7 = Z ^ 0 := by rw [show 7 = 0 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r8 : Z ^ 8 = Z ^ 1 := by rw [show 8 = 1 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r9 : Z ^ 9 = Z ^ 2 := by rw [show 9 = 2 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r10 : Z ^ 10 = Z ^ 3 := by rw [show 10 = 3 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r11 : Z ^ 11 = Z ^ 4 := by rw [show 11 = 4 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r12 : Z ^ 12 = Z ^ 5 := by rw [show 12 = 5 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r13 : Z ^ 13 = Z ^ 6 := by rw [show 13 = 6 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r14 : Z ^ 14 = Z ^ 0 := by rw [show 14 = 0 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r15 : Z ^ 15 = Z ^ 1 := by rw [show 15 = 1 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r16 : Z ^ 16 = Z ^ 2 := by rw [show 16 = 2 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r17 : Z ^ 17 = Z ^ 3 := by rw [show 17 = 3 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r18 : Z ^ 18 = Z ^ 4 := by rw [show 18 = 4 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r19 : Z ^ 19 = Z ^ 5 := by rw [show 19 = 5 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r20 : Z ^ 20 = Z ^ 6 := by rw [show 20 = 6 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r21 : Z ^ 21 = Z ^ 0 := by rw [show 21 = 0 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r22 : Z ^ 22 = Z ^ 1 := by rw [show 22 = 1 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r23 : Z ^ 23 = Z ^ 2 := by rw [show 23 = 2 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r24 : Z ^ 24 = Z ^ 3 := by rw [show 24 = 3 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r25 : Z ^ 25 = Z ^ 4 := by rw [show 25 = 4 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r26 : Z ^ 26 = Z ^ 5 := by rw [show 26 = 5 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r27 : Z ^ 27 = Z ^ 6 := by rw [show 27 = 6 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r28 : Z ^ 28 = Z ^ 0 := by rw [show 28 = 0 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r29 : Z ^ 29 = Z ^ 1 := by rw [show 29 = 1 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r30 : Z ^ 30 = Z ^ 2 := by rw [show 30 = 2 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r31 : Z ^ 31 = Z ^ 3 := by rw [show 31 = 3 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r32 : Z ^ 32 = Z ^ 4 := by rw [show 32 = 4 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r33 : Z ^ 33 = Z ^ 5 := by rw [show 33 = 5 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r34 : Z ^ 34 = Z ^ 6 := by rw [show 34 = 6 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r35 : Z ^ 35 = Z ^ 0 := by rw [show 35 = 0 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r36 : Z ^ 36 = Z ^ 1 := by rw [show 36 = 1 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r37 : Z ^ 37 = Z ^ 2 := by rw [show 37 = 2 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r38 : Z ^ 38 = Z ^ 3 := by rw [show 38 = 3 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r39 : Z ^ 39 = Z ^ 4 := by rw [show 39 = 4 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r40 : Z ^ 40 = Z ^ 5 := by rw [show 40 = 5 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r41 : Z ^ 41 = Z ^ 6 := by rw [show 41 = 6 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r42 : Z ^ 42 = Z ^ 0 := by rw [show 42 = 0 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r43 : Z ^ 43 = Z ^ 1 := by rw [show 43 = 1 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r44 : Z ^ 44 = Z ^ 2 := by rw [show 44 = 2 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  norm_num
  simp only [zpow_ofNat, zpow_natCast, zpow_neg, Int.reduceNeg]
  ring_nf
  try simp only [r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44]
  ring_nf


lemma InCls.mono_mul' {f : L} (hf : InCls 0 f) {e c : ℤ} (he : e % 7 = c) (a : ℂ) : InCls c (mono e a * f) :=
  he ▸ InCls.mono_mul hf e a

macro "cls0'" : tactic => `(tactic| repeat' (first
  | exact c0_k | with_reducible apply c0_add | with_reducible apply c0_sub | with_reducible apply c0_neg
  | with_reducible apply c0_div | with_reducible apply c0_mul | with_reducible apply c0_inv
  | with_reducible apply c0_pow | (with_reducible apply c0_θ; norm_num) | (with_reducible apply c0_mono; norm_num)
  | (refine InCls.Ab hP (by norm_num) (by norm_num) (by norm_num) _ _ one_ne_zero one_ne_zero)))

set_option maxHeartbeats 4000000 in
/-- each canonical piece is class-pure. -/
theorem Gs_cls : ∀ t, InCls (cs t : ℤ) (Gs t) := by
  simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, Gs, cs, Matrix.cons_val_zero, Matrix.cons_val_succ, and_true]
  refine ⟨by simpa using InCls.one, ?_⟩
  repeat' constructor
  all_goals (refine InCls.mono_mul' ?_ (by norm_num) _; cls0')

lemma hdec7 : ∀ j : ℕ, 0 < j → j < 7 →
    ι1 (CrankProof.Dser (CrankProof.ω7 ^ j) (CrankProof.ω7 ^ j)⁻¹) =
      ∑ t, HahnSeries.C (Pv (fun k => (vs t k : ℂ)) (CrankProof.ω7 ^ j)) * Gs t := fun j h0 hj =>
  decomp2 (by rw [← pow_mul, mul_comm, pow_mul, CrankProof.ω7_pow7, one_pow])
    (CrankProof.ω7_prim.pow_ne_one_of_pos_of_lt (by omega) hj)

/-- the rank equalities mod 7 that the decomposition certifies. -/
theorem asd7 {c : ℕ} (hc : c < 7) (a b : Fin 7) (hcond : ∀ t, cs t = c → vs t a = vs t b) (n : ℕ) :
    CrankProof.rankCount7 (7 * n + c) a = CrankProof.rankCount7 (7 * n + c) b :=
  rank_eq_of_decomp Gs cs vs Gs_cls hdec7 hc a b hcond n

end ALz

namespace CrankProof
open ALz

/-- **Atkin–Swinnerton-Dyer (1954), rank mod 7.** Writing `N(k, m) = #{λ ⊢ m : rank λ ≡ k (mod 7)}`:
`N(2,7n) = N(3,7n)`; `N(1,7n+1) = N(2,7n+1) = N(3,7n+1)`; `N(0,7n+2) = N(3,7n+2)`;
`N(0,7n+3) = N(2,7n+3)`, `N(1,7n+3) = N(3,7n+3)`; `N(0,7n+4) = N(1,7n+4) = N(3,7n+4)`
(and `N(k,·) = N(7−k,·)` by conjugation; class `7n+5` is `rank_equidistribution_mod7`). -/
theorem rank_mod7_ASD (n : ℕ) :
    rankCount7 (7 * n) 2 = rankCount7 (7 * n) 3 ∧
    rankCount7 (7 * n + 1) 1 = rankCount7 (7 * n + 1) 2 ∧ rankCount7 (7 * n + 1) 1 = rankCount7 (7 * n + 1) 3 ∧
    rankCount7 (7 * n + 2) 0 = rankCount7 (7 * n + 2) 3 ∧
    rankCount7 (7 * n + 3) 0 = rankCount7 (7 * n + 3) 2 ∧ rankCount7 (7 * n + 3) 1 = rankCount7 (7 * n + 3) 3 ∧
    rankCount7 (7 * n + 4) 0 = rankCount7 (7 * n + 4) 1 ∧ rankCount7 (7 * n + 4) 0 = rankCount7 (7 * n + 4) 3 := by
  refine ⟨?_, asd7 (c := 1) (by norm_num) 1 2 (by decide) n, asd7 (c := 1) (by norm_num) 1 3 (by decide) n,
    asd7 (c := 2) (by norm_num) 0 3 (by decide) n, asd7 (c := 3) (by norm_num) 0 2 (by decide) n,
    asd7 (c := 3) (by norm_num) 1 3 (by decide) n, asd7 (c := 4) (by norm_num) 0 1 (by decide) n,
    asd7 (c := 4) (by norm_num) 0 3 (by decide) n⟩
  simpa using asd7 (c := 0) (by norm_num) 2 3 (by decide) n

end CrankProof
