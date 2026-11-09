/-
# Entry 3.19(ii) (Bressoud; Cao's ECS proof, arXiv:2503.11445, Identity 19-2)

`2q{G(q)G(q³⁹) + q⁸H(q)H(q³⁹)} f(−q)f(−q³⁹) = φ(−q³)φ(−q¹³) − φ(−q)φ(−q³⁹)`
(Ramanujan's (3.22), second equality, multiplied by `2q`; the first equality is `entry_3_19_i`).

In `ℂ((t))` (`t² = q`) this is `t²·C = A − B` for three forms of determinant 39:
* `A = Σ (−1)^{x₁} t^{6x₁²+6x₁x₂+8x₂²}` (`L19A`: `φ(−q³)φ(−q¹³)`),
* `B = Σ (−1)^{x₁} t^{2x₁²+2x₁x₂+20x₂²}` (`L19B`: `φ(−q)φ(−q³⁹)`),
* `C = Σ (−1)^{x₁} t^{5x₁²+2x₁x₂+8x₂²+x₁+8x₂}` (the form of Entry 3.19(i); `L19C`),
glued through `QS` by the covers `(0 −2; 1 1)` of `A` (`S19a`), the parity of `x₁` in `B` (`S19b`) and `(0 2; 1 0)`
of `C` (`S19c`).
-/
import RamanujanTau.Forty.QS
import RamanujanTau.Forty.E19
import RamanujanTau.Forty.E17

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm4 : 1 ≤ 4 := by norm_num
private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm12 : 1 ≤ 12 := by norm_num
private lemma hm52 : 1 ≤ 52 := by norm_num
private lemma hm156 : 1 ≤ 156 := by norm_num
private lemma hm390 : 1 ≤ 390 := by norm_num

/-- `S19a`: `B = (0 -2; 1 1)`, shifts `i (1, 0)`, `i ∈ {0, 1}`. -/
def B19a : ECS where
  b11 := 0
  b12 := (-2)
  b21 := 1
  b22 := 1
  r1 := 1
  r2 := 0
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0)) - (-2) * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), ((0 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0)) - 1 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem S19a : QS (qmono 6 3 8 0 0 1 0) = QS (qmono 8 2 20 0 0 0 0) - mono 6 1 * QS (qmono 8 2 20 6 (-18) 0 0) := by
  have h := QS_sub 6 3 8 0 0 1 0 B19a (fun i hi => by
    simp only [B19a, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, B19a])
      (by norm_num [sA, sB, sC, B19a]))
  simp only [B19a] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  simp only [qmono_par 8 2 20 0 0 0 (-2) 0 0 (by decide) (by decide), qmono_par 8 2 20 6 (-18) 0 (-2) 0 0 (by decide) (by decide)] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `S19b`: `B = (2 0; 0 1)`, shifts `i (1, 0)`, `i ∈ {0, 1}`. -/
def B19b : ECS where
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

theorem S19b : QS (qmono 2 1 20 0 0 1 0) = QS (qmono 8 2 20 0 0 0 0) - mono 2 1 * QS (qmono 8 2 20 8 2 0 0) := by
  have h := QS_sub 2 1 20 0 0 1 0 B19b (fun i hi => by
    simp only [B19b, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, B19b])
      (by norm_num [sA, sB, sC, B19b]))
  simp only [B19b] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  simp only [qmono_par 8 2 20 0 0 2 0 0 0 (by decide) (by decide), qmono_par 8 2 20 8 2 2 0 0 0 (by decide) (by decide)] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `S19c`: `B = (0 2; 1 0)`, shifts `i (1, 0)`, `i ∈ {(-1), 0}`. -/
def B19c : ECS where
  b11 := 0
  b12 := 2
  b21 := 1
  b22 := 0
  r1 := 1
  r2 := 0
  I := {(-1), 0}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - (-1)) % 2 + (-1)), by simp only [mem_insert, mem_singleton]; omega,
    ((0 * (m - 1 * ((1 * m + 0 * n - (-1)) % 2 + (-1))) - 2 * (n - 0 * ((1 * m + 0 * n - (-1)) % 2 + (-1)))) / (-2)), ((0 * (n - 0 * ((1 * m + 0 * n - (-1)) % 2 + (-1))) - 1 * (m - 1 * ((1 * m + 0 * n - (-1)) % 2 + (-1)))) / (-2)), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem S19c : QS (qmono 5 1 8 1 8 1 0) = -(mono 4 1 * QS (qmono 8 2 20 6 (-18) 0 0)) + QS (qmono 8 2 20 8 2 0 0) := by
  have h := QS_sub 5 1 8 1 8 1 0 B19c (fun i hi => by
    simp only [B19c, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, B19c])
      (by norm_num [sA, sB, sC, B19c]))
  simp only [B19c] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  simp only [qmono_par 8 2 20 6 (-18) 0 2 0 0 (by decide) (by decide), qmono_par 8 2 20 8 2 0 2 0 0 (by decide) (by decide)] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `L19A`: `B = (1 -1; 0 2)`, shifts `i (0, 1)`, `i ∈ {(-2), (-1)}`. -/
def B19A : ECS where
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

theorem L19A : QS (qmono 6 3 8 0 0 1 0) = (θ hm12 6 1 * θ hm52 26 1) := by
  have h := (QS_orth 6 3 8 0 0 1 0 B19A hm12 hm52 (by norm_num [B19A])
    (by norm_num [B19A]) (by norm_num [B19A])).2
  simp only [B19A] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_sh hm12 6 (-1) one_ne_zero (-6) (-1) (e := (-6)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm52 26 (-1) one_ne_zero (-26) (-1) (e := (-26)) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm12 0 (e := 0) (by norm_num), θz' hm52 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `L19B`: `B = (1 -1; 0 2)`, shifts `i (0, 1)`, `i ∈ {(-2), (-1)}`. -/
def B19B : ECS where
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

theorem L19B : QS (qmono 2 1 20 0 0 1 0) = (θ hm4 2 1 * θ hm156 78 1) := by
  have h := (QS_orth 2 1 20 0 0 1 0 B19B hm4 hm156 (by norm_num [B19B])
    (by norm_num [B19B]) (by norm_num [B19B])).2
  simp only [B19B] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_sh hm156 78 (-1) one_ne_zero (-78) (-1) (e := (-78)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm4 2 (-1) one_ne_zero (-2) (-1) (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm156 0 (e := 0) (by norm_num), θz' hm4 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `L19C`: `B = (-1 1; 0 -5)`, shifts `i (0, 1)`, `i ∈ {(-3), (-2), (-1), 0, 1}`. -/
def B19C : ECS where
  b11 := (-1)
  b12 := 1
  b21 := 0
  b22 := (-5)
  r1 := 0
  r2 := 1
  I := {(-3), (-2), (-1), 0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-3)) % 5 + (-3)), by simp only [mem_insert, mem_singleton]; omega,
    (((-5) * (m - 0 * ((0 * m + 1 * n - (-3)) % 5 + (-3))) - 1 * (n - 1 * ((0 * m + 1 * n - (-3)) % 5 + (-3)))) / 5), (((-1) * (n - 1 * ((0 * m + 1 * n - (-3)) % 5 + (-3))) - 0 * (m - 0 * ((0 * m + 1 * n - (-3)) % 5 + (-3)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L19C : QS (qmono 5 1 8 1 8 1 0) = 2 * (θ hm10 4 1 * θ hm390 156 1) + 2 * (mono 16 1 * (θ hm10 2 1 * θ hm390 78 1)) := by
  have h := (QS_orth 5 1 8 1 8 1 0 B19C hm10 hm390 (by norm_num [B19C])
    (by norm_num [B19C]) (by norm_num [B19C])).2
  simp only [B19C] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm10 2 0 0 1 (e := 8) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm10 4 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm390 156 0 0 1 (e := 234) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm390 78 0 0 1 (e := 312) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm10 1 (e := 10) (by norm_num), θz' hm390 1 (e := 390) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


private lemma monoT19 (k : ℕ) : (mono (k : ℤ) 1 : L) = mono 1 1 ^ k := by
  rw [mono, single_pow]; simp

/-- Cao (84) at `q = t²`, in `ℂ((t))`. -/
theorem L3_19ii : mono 2 1 * (2 * (θ hm10 4 1 * θ hm390 156 1) + 2 * (mono 16 1 * (θ hm10 2 1 * θ hm390 78 1))) =
    θ hm12 6 1 * θ hm52 26 1 - θ hm4 2 1 * θ hm156 78 1 := by
  rw [← L19A, ← L19B, ← L19C, S19a, S19b, S19c]
  simp only [show (mono 2 1 : L) = mono 1 1 ^ 2 from monoT19 2, show (mono 4 1 : L) = mono 1 1 ^ 4 from monoT19 4,
    show (mono 6 1 : L) = mono 1 1 ^ 6 from monoT19 6]
  ring

/-- Cao (84), product form: `2qf(−q²,−q³)f(−q⁷⁸,−q¹¹⁷) + 2q⁹f(−q,−q⁴)f(−q³⁹,−q¹⁵⁶) = φ(−q³)φ(−q¹³) − φ(−q)φ(−q³⁹)`. -/
theorem P3_19ii : 2 * PowerSeries.X * (J 2 5 * J 78 195) + 2 * PowerSeries.X ^ 9 * (J 1 5 * J 39 195) =
    J 3 6 * J 13 26 - J 1 2 * J 39 78 := by
  apply S_inj 2
  have h := L3_19ii
  rw [θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm390 156 (e' := 156) (by norm_num) (by norm_num) (by norm_num),
    θu' hm390 78 (e' := 78) (by norm_num) (by norm_num) (by norm_num),
    θu' hm12 6 (e' := 6) (by norm_num) (by norm_num) (by norm_num),
    θu' hm52 26 (e' := 26) (by norm_num) (by norm_num) (by norm_num),
    θu' hm4 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm156 78 (e' := 78) (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [show (mono 2 1 : L) = mono 1 1 ^ 2 from monoT19 2,
    show (mono 16 1 : L) = mono 1 1 ^ 16 from monoT19 16] at h
  apply ι_inj
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, S_J 2 2 5 (by norm_num) (by norm_num),
    S_J 2 78 195 (by norm_num) (by norm_num), S_J 2 1 5 (by norm_num) (by norm_num),
    S_J 2 39 195 (by norm_num) (by norm_num), S_J 2 3 6 (by norm_num) (by norm_num),
    S_J 2 13 26 (by norm_num) (by norm_num), S_J 2 1 2 (by norm_num) (by norm_num),
    S_J 2 39 78 (by norm_num) (by norm_num), show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _]
  simp only [Nat.reduceMul, ι_X, map_pow]
  linear_combination h

local notation "φ" => RamanujanTau.Septic.phi

/-- **Entry 3.19(ii)** (Bressoud; Cao), multiplied by `2q`:
`2q{G(q)G(q³⁹) + q⁸H(q)H(q³⁹)} f(−q)f(−q³⁹) = φ(−q³)φ(−q¹³) − φ(−q)φ(−q³⁹)`. -/
theorem entry_3_19_ii : 2 * PowerSeries.X * (G * S 39 G + PowerSeries.X ^ 8 * H * S 39 H) * (fm 1 * fm 39) =
    S 3 (Ng φ) * S 13 (Ng φ) - Ng φ * S 39 (Ng φ) := by
  have e1 := SG_E 39
  have e2 := SH_E 39
  have e3 := G_E
  have e4 := H_E
  norm_num at e1 e2
  have hφ : Ng φ = J 1 2 := by rw [Ng_phi]; simp only [J, Nat.reduceSub]; ring
  have hS : ∀ (a : ℕ) [NeZero a], S a (Ng φ) = J a (2 * a) := fun a _ => by
    have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (NeZero.ne a)
    rw [hφ, S_J a 1 2 le_rfl (by norm_num), mul_one, mul_comm]
  rw [hS 3, hS 13, hS 39, hφ]
  simp only [fm, Nat.reduceMul]
  linear_combination 2 * PowerSeries.X * (S 39 G * Pinf 39 39) * e3 + 2 * PowerSeries.X * J 2 5 * e1
    + 2 * PowerSeries.X ^ 9 * (S 39 H * Pinf 39 39) * e4 + 2 * PowerSeries.X ^ 9 * J 1 5 * e2 + P3_19ii

end Forty
