/-
# Entry 3.18 (Bressoud; Cao's ECS proof, arXiv:2503.11445, Identity 18)

`2q{G(q³¹)H(q) − q⁶G(q)H(q³¹)} = χ(q)χ(q³¹) − χ(−q)χ(−q³¹) + 2q⁴/(χ(−q²)χ(−q⁶²))`
(Ramanujan's (3.21) multiplied by `2q`).

After multiplying by `f(−q)f(−q³¹)` this is Cao's (71). In `ℂ((t))` (`t² = q`) it reads `t²·C = A − B` for the
three forms of determinant 31
* `A = Σ (−1)^{x₁} t^{4x₁²+2x₁x₂+8x₂²}` (`L18A`: `φ(−q²)φ(−q⁶²) + 2q⁴ψ(−q)ψ(−q³¹)`),
* `B = Σ (−1)^{x₁} t^{2x₁²+2x₁x₂+16x₂²}` (`L18B`: `φ(−q)φ(−q³¹)`),
* `C = Σ (−1)^{x₁+x₂} t^{5x₁²+4x₁x₂+7x₂²+3x₁−5x₂}` (`L18C`: the two products of the left side),
glued by parity splits of `x₁` (`S18p`, `S18q`), the swap `x₁ ↔ x₂` (`S18s`, `S18t`) and the index-2 cover
`(1 −1; −1 −1)` of `C` (`S18c`), all through `QS` (QS.lean).
-/
import RamanujanTau.Forty.QS
import RamanujanTau.Forty.E17

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm4 : 1 ≤ 4 := by norm_num
private lemma hm8 : 1 ≤ 8 := by norm_num
private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm124 : 1 ≤ 124 := by norm_num
private lemma hm248 : 1 ≤ 248 := by norm_num
private lemma hm310 : 1 ≤ 310 := by norm_num

/-- `S18p`: `B = (2 0; 0 1)`, shifts `i (1, 0)`, `i ∈ {0, 1}`. -/
def B18p : ECS where
  b11 := 2
  b12 := 0
  b21 := 0
  b22 := 1
  r1 := 1
  r2 := 0
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), ((2 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem S18p : QS (qmono 4 1 8 0 0 1 0) = QS (qmono 16 2 8 0 0 0 0) - mono 4 1 * QS (qmono 16 2 8 16 2 0 0) := by
  have h := QS_sub 4 1 8 0 0 1 0 B18p (fun i hi => by
    simp only [B18p, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, B18p])
      (by norm_num [sA, sB, sC, B18p]))
  simp only [B18p] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  simp only [qmono_par 16 2 8 0 0 2 0 0 0 (by decide) (by decide), qmono_par 16 2 8 16 2 2 0 0 0 (by decide) (by decide)] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `S18q`: `B = (2 0; 0 1)`, shifts `i (1, 0)`, `i ∈ {0, 1}`. -/
def B18q : ECS where
  b11 := 2
  b12 := 0
  b21 := 0
  b22 := 1
  r1 := 1
  r2 := 0
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), ((2 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem S18q : QS (qmono 2 1 16 0 0 1 0) = QS (qmono 8 2 16 0 0 0 0) - mono 2 1 * QS (qmono 8 2 16 8 2 0 0) := by
  have h := QS_sub 2 1 16 0 0 1 0 B18q (fun i hi => by
    simp only [B18q, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, B18q])
      (by norm_num [sA, sB, sC, B18q]))
  simp only [B18q] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  simp only [qmono_par 8 2 16 0 0 2 0 0 0 (by decide) (by decide), qmono_par 8 2 16 8 2 2 0 0 0 (by decide) (by decide)] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `S18s`: `B = (0 1; 1 0)`, shifts `i (1, 0)`, `i ∈ {0}`. -/
def B18s : ECS where
  b11 := 0
  b12 := 1
  b21 := 1
  b22 := 0
  r1 := 1
  r2 := 0
  I := {0}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 0 * n - 0) % 1 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((0 * (m - 1 * ((0 * m + 0 * n - 0) % 1 + 0)) - 1 * (n - 0 * ((0 * m + 0 * n - 0) % 1 + 0))) / (-1)), ((0 * (n - 0 * ((0 * m + 0 * n - 0) % 1 + 0)) - 1 * (m - 1 * ((0 * m + 0 * n - 0) % 1 + 0))) / (-1)), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem S18s : QS (qmono 16 2 8 0 0 0 0) = QS (qmono 8 2 16 0 0 0 0) := by
  have h := QS_sub 16 2 8 0 0 0 0 B18s (fun i hi => by
    simp only [B18s, mem_insert, mem_singleton] at hi
    rcases hi with rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, B18s])
      (by norm_num [sA, sB, sC, B18s]))
  simp only [B18s] at h
  rw [sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `S18t`: `B = (0 1; 1 0)`, shifts `i (1, 0)`, `i ∈ {0}`. -/
def B18t : ECS where
  b11 := 0
  b12 := 1
  b21 := 1
  b22 := 0
  r1 := 1
  r2 := 0
  I := {0}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 0 * n - 0) % 1 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((0 * (m - 1 * ((0 * m + 0 * n - 0) % 1 + 0)) - 1 * (n - 0 * ((0 * m + 0 * n - 0) % 1 + 0))) / (-1)), ((0 * (n - 0 * ((0 * m + 0 * n - 0) % 1 + 0)) - 1 * (m - 1 * ((0 * m + 0 * n - 0) % 1 + 0))) / (-1)), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem S18t : QS (qmono 16 2 8 16 2 0 0) = QS (qmono 8 2 16 2 16 0 0) := by
  have h := QS_sub 16 2 8 16 2 0 0 B18t (fun i hi => by
    simp only [B18t, mem_insert, mem_singleton] at hi
    rcases hi with rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, B18t])
      (by norm_num [sA, sB, sC, B18t]))
  simp only [B18t] at h
  rw [sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `S18c`: `B = (1 -1; -1 -1)`, shifts `i (1, 0)`, `i ∈ {(-1), 0}`. -/
def B18c : ECS where
  b11 := 1
  b12 := (-1)
  b21 := (-1)
  b22 := (-1)
  r1 := 1
  r2 := 0
  I := {(-1), 0}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 1 * n - (-1)) % 2 + (-1)), by simp only [mem_insert, mem_singleton]; omega,
    (((-1) * (m - 1 * ((1 * m + 1 * n - (-1)) % 2 + (-1))) - (-1) * (n - 0 * ((1 * m + 1 * n - (-1)) % 2 + (-1)))) / (-2)), ((1 * (n - 0 * ((1 * m + 1 * n - (-1)) % 2 + (-1))) - (-1) * (m - 1 * ((1 * m + 1 * n - (-1)) % 2 + (-1)))) / (-2)), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem S18c : QS (qmono 5 2 7 3 (-5) 1 1) = -(mono 2 1 * QS (qmono 8 2 16 2 16 0 0)) + QS (qmono 8 2 16 8 2 0 0) := by
  have h := QS_sub 5 2 7 3 (-5) 1 1 B18c (fun i hi => by
    simp only [B18c, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, B18c])
      (by norm_num [sA, sB, sC, B18c]))
  simp only [B18c] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  simp only [qmono_par 8 2 16 2 16 0 (-2) 0 0 (by decide) (by decide), qmono_par 8 2 16 8 2 0 (-2) 0 0 (by decide) (by decide)] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `L18A`: `B = (1 -1; 0 4)`, shifts `i (0, 1)`, `i ∈ {(-4), (-3), (-2), (-1)}`. -/
def B18A : ECS where
  b11 := 1
  b12 := (-1)
  b21 := 0
  b22 := 4
  r1 := 0
  r2 := 1
  I := {(-4), (-3), (-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-4)) % 4 + (-4)), by simp only [mem_insert, mem_singleton]; omega,
    ((4 * (m - 0 * ((0 * m + 1 * n - (-4)) % 4 + (-4))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-4)) % 4 + (-4)))) / 4), ((1 * (n - 1 * ((0 * m + 1 * n - (-4)) % 4 + (-4))) - 0 * (m - 0 * ((0 * m + 1 * n - (-4)) % 4 + (-4)))) / 4), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L18A : QS (qmono 4 1 8 0 0 1 0) = (θ hm8 4 1 * θ hm248 124 1) + 2 * (mono 8 1 * (θ hm8 2 1 * θ hm248 62 1)) := by
  have h := (QS_orth 4 1 8 0 0 1 0 B18A hm8 hm248 (by norm_num [B18A])
    (by norm_num [B18A]) (by norm_num [B18A])).2
  simp only [B18A] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm248 62 (-1) (-62) (-1) (e := (-62)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm8 2 (-1) (-2) (-1) (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm248 124 (-1) one_ne_zero (-124) (-1) (e := (-124)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm8 4 (-1) one_ne_zero (-4) (-1) (e := (-4)) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm248 0 (e := 0) (by norm_num), θz' hm8 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `L18B`: `B = (1 -1; 0 2)`, shifts `i (0, 1)`, `i ∈ {(-2), (-1)}`. -/
def B18B : ECS where
  b11 := 1
  b12 := (-1)
  b21 := 0
  b22 := 2
  r1 := 0
  r2 := 1
  I := {(-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-2)) % 2 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((2 * (m - 0 * ((0 * m + 1 * n - (-2)) % 2 + (-2))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-2)) % 2 + (-2)))) / 2), ((1 * (n - 1 * ((0 * m + 1 * n - (-2)) % 2 + (-2))) - 0 * (m - 0 * ((0 * m + 1 * n - (-2)) % 2 + (-2)))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L18B : QS (qmono 2 1 16 0 0 1 0) = (θ hm4 2 1 * θ hm124 62 1) := by
  have h := (QS_orth 2 1 16 0 0 1 0 B18B hm4 hm124 (by norm_num [B18B])
    (by norm_num [B18B]) (by norm_num [B18B])).2
  simp only [B18B] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_sh hm124 62 (-1) one_ne_zero (-62) (-1) (e := (-62)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm4 2 (-1) one_ne_zero (-2) (-1) (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm124 0 (e := 0) (by norm_num), θz' hm4 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `L18C`: `B = (1 -2; 0 5)`, shifts `i (0, 1)`, `i ∈ {(-5), (-4), (-3), (-2), (-1)}`. -/
def B18C : ECS where
  b11 := 1
  b12 := (-2)
  b21 := 0
  b22 := 5
  r1 := 0
  r2 := 1
  I := {(-5), (-4), (-3), (-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-5)) % 5 + (-5)), by simp only [mem_insert, mem_singleton]; omega,
    ((5 * (m - 0 * ((0 * m + 1 * n - (-5)) % 5 + (-5))) - (-2) * (n - 1 * ((0 * m + 1 * n - (-5)) % 5 + (-5)))) / 5), ((1 * (n - 1 * ((0 * m + 1 * n - (-5)) % 5 + (-5))) - 0 * (m - 0 * ((0 * m + 1 * n - (-5)) % 5 + (-5)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L18C : QS (qmono 5 2 7 3 (-5) 1 1) = 2 * (θ hm10 2 1 * θ hm310 124 1) - 2 * (mono 12 1 * (θ hm10 4 1 * θ hm310 62 1)) := by
  have h := (QS_orth 5 2 7 3 (-5) 1 1 B18C hm10 hm310 (by norm_num [B18C])
    (by norm_num [B18C]) (by norm_num [B18C])).2
  simp only [B18C] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm10 2 (-2) (-14) 1 (e := (-12)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm10 4 (-1) (-4) (-1) (e := (-4)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm310 124 (-1) (-124) (-1) (e := (-124)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm310 62 (-1) (-62) (-1) (e := (-62)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm10 2 (-1) one_ne_zero (-8) (-1) (e := (-8)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm310 124 (-1) one_ne_zero (-186) (-1) (e := (-186)) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm10 0 (e := 0) (by norm_num), θz' hm310 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


private lemma monoT18 (k : ℕ) : (mono (k : ℤ) 1 : L) = mono 1 1 ^ k := by
  rw [mono, single_pow]; simp

/-- Cao (71) at `q = t²`, in `ℂ((t))`. -/
theorem L3_18 : mono 2 1 * (2 * (θ hm10 2 1 * θ hm310 124 1) - 2 * (mono 12 1 * (θ hm10 4 1 * θ hm310 62 1))) =
    (θ hm8 4 1 * θ hm248 124 1) + 2 * (mono 8 1 * (θ hm8 2 1 * θ hm248 62 1)) - θ hm4 2 1 * θ hm124 62 1 := by
  rw [← L18A, ← L18B, ← L18C, S18p, S18q, S18s, S18t, S18c]
  simp only [show (mono 2 1 : L) = mono 1 1 ^ 2 from monoT18 2, show (mono 4 1 : L) = mono 1 1 ^ 4 from monoT18 4]
  ring

/-- Cao (71), product form: `2qf(−q,−q⁴)f(−q⁶²,−q⁹³) − 2q⁷f(−q²,−q³)f(−q³¹,−q¹²⁴)
= φ(−q²)φ(−q⁶²) + 2q⁴ψ(−q)ψ(−q³¹) − φ(−q)φ(−q³¹)`. -/
theorem P3_18 : 2 * PowerSeries.X * (J 1 5 * J 62 155) - 2 * PowerSeries.X ^ 7 * (J 2 5 * J 31 155) =
    J 2 4 * J 62 124 + 2 * PowerSeries.X ^ 4 * (J 1 4 * J 31 124) - J 1 2 * J 31 62 := by
  apply S_inj 2
  have h := L3_18
  rw [θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm310 124 (e' := 124) (by norm_num) (by norm_num) (by norm_num),
    θu' hm310 62 (e' := 62) (by norm_num) (by norm_num) (by norm_num),
    θu' hm8 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm8 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm248 124 (e' := 124) (by norm_num) (by norm_num) (by norm_num),
    θu' hm248 62 (e' := 62) (by norm_num) (by norm_num) (by norm_num),
    θu' hm4 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm124 62 (e' := 62) (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [show (mono 2 1 : L) = mono 1 1 ^ 2 from monoT18 2, show (mono 8 1 : L) = mono 1 1 ^ 8 from monoT18 8,
    show (mono 12 1 : L) = mono 1 1 ^ 12 from monoT18 12] at h
  apply ι_inj
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, S_J 2 1 5 (by norm_num) (by norm_num),
    S_J 2 62 155 (by norm_num) (by norm_num), S_J 2 2 5 (by norm_num) (by norm_num),
    S_J 2 31 155 (by norm_num) (by norm_num), S_J 2 2 4 (by norm_num) (by norm_num),
    S_J 2 62 124 (by norm_num) (by norm_num), S_J 2 1 4 (by norm_num) (by norm_num),
    S_J 2 31 124 (by norm_num) (by norm_num), S_J 2 1 2 (by norm_num) (by norm_num),
    S_J 2 31 62 (by norm_num) (by norm_num), show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _]
  simp only [Nat.reduceMul, ι_X, map_pow]
  linear_combination h

lemma S31_chip1 : S 31 (chip 1) = chip 31 := by rw [chip, S_one]; rfl

/-- **Entry 3.18** (Bressoud; Cao), multiplied by `2q`:
`2q{G(q³¹)H(q) − q⁶G(q)H(q³¹)} = χ(q)χ(q³¹) − χ(−q)χ(−q³¹) + 2q⁴/(χ(−q²)χ(−q⁶²))`. -/
theorem entry_3_18 : 2 * PowerSeries.X * (S 31 G * H - PowerSeries.X ^ 6 * G * S 31 H) =
    chip 1 * chip 31 - chim 1 * chim 31 + 2 * PowerSeries.X ^ 4 * Ring.inverse (chim 2 * chim 62) := by
  have e1 := SG_E 31
  have e2 := SH_E 31
  have e3 := G_E
  have e4 := H_E
  norm_num at e1 e2
  have hc1 := chip_mul 1
  norm_num at hc1
  have hsp := E1_split
  have a2 := atom 2 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [prod_range_succ, prod_range_zero, one_mul] at a2
  norm_num at a2
  -- `χ(q) f(−q) = φ(−q²)`, `χ(−q) f(−q) = φ(−q)`, `χ(−q²) ψ(−q) = f(−q)`
  have l1 : chip 1 * Pinf 1 1 = J 2 4 := by
    simp only [J, Nat.reduceSub]; rw [hsp, a2]; linear_combination (Pinf 2 4 * Pinf 4 4) * hc1
  have m1 : chim 1 * Pinf 1 1 = J 1 2 := by
    simp only [J, chim, Nat.reduceSub, Nat.reduceMul]; rw [hsp]; ring
  have n1 : Pinf 2 4 * J 1 4 = Pinf 1 1 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 4]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have l31 := congrArg (S 31) l1
  have m31 := congrArg (S 31) m1
  have n31 := congrArg (S 31) n1
  simp only [map_mul, S31_chip1, chim, S_P' 31 1 1 le_rfl le_rfl (rfl : 31 = 31 * 1) (rfl : 31 = 31 * 1),
    S_P' 31 1 2 le_rfl (by norm_num) (rfl : 31 = 31 * 1) (rfl : 62 = 31 * 2),
    S_P' 31 2 4 (by norm_num) (by norm_num) (rfl : 62 = 31 * 2) (rfl : 124 = 31 * 4),
    S_J' 31 2 4 (by norm_num) (by norm_num) (rfl : 62 = 31 * 2) (rfl : 124 = 31 * 4),
    S_J' 31 1 2 le_rfl (by norm_num) (rfl : 31 = 31 * 1) (rfl : 62 = 31 * 2),
    S_J' 31 1 4 le_rfl (by norm_num) (rfl : 31 = 31 * 1) (rfl : 124 = 31 * 4), Nat.reduceMul] at l31 m31 n31
  have hu : IsUnit (chim 2 * chim 62) :=
    (isUnit_Pinf 2 4 (by norm_num) (by norm_num)).mul (isUnit_Pinf 62 124 (by norm_num) (by norm_num))
  have hinv := Ring.inverse_mul_cancel _ hu
  simp only [chim, Nat.reduceMul] at hinv m1 ⊢
  have P := P3_18
  have hW : (Pinf 1 1 * Pinf 31 31 : PowerSeries ℤ) ≠ 0 :=
    mul_ne_zero (Pinf_ne 1 1 le_rfl le_rfl) (Pinf_ne 31 31 (by norm_num) (by norm_num))
  apply mul_left_cancel₀ hW
  linear_combination 2 * PowerSeries.X * (H * Pinf 1 1) * e1 + 2 * PowerSeries.X * J 62 155 * e4
    - 2 * PowerSeries.X ^ 7 * (S 31 H * Pinf 31 31) * e3 - 2 * PowerSeries.X ^ 7 * J 2 5 * e2 + P
    - (chip 31 * Pinf 31 31) * l1 - J 2 4 * l31
    + (Pinf 31 62 * Pinf 31 31) * m1 + J 1 2 * m31
    + 2 * PowerSeries.X ^ 4 * Ring.inverse (Pinf 2 4 * Pinf 62 124) * Pinf 31 31 * n1
    + 2 * PowerSeries.X ^ 4 * Ring.inverse (Pinf 2 4 * Pinf 62 124) * Pinf 2 4 * J 1 4 * n31
    - 2 * PowerSeries.X ^ 4 * (J 1 4 * J 31 124) * hinv

end Forty
