/-
# Entry 3.35

Yesilyurt (JMAA 388 (2012), §5) in the language of `E35e`/`E35f`, with `u = χ(q)χ(Q)`, `v = χ(−q)χ(−Q)`,
`w = χ(−q²)χ(−Q²) = uv`, `Q = q⁴⁷`, `P = f(−q²)f(−Q²)`:
* `E518` (his (5.18)): `T1(q²) = T1(q⁴) + 2q¹²ψ(q²)ψ(Q²) + q²(f(q)f(Q) + f(−q)f(−Q)) + 2q⁸f(−q⁴)f(−Q⁴)`,
  from `E47` at `q`, `−q`, `q⁴` and the even-part identities `R2`, `R3`;
* `phi_sq` (`φ(q)² = φ(q²)² + 4qψ(q⁴)²`, two orthogonal covers of `x² + y²`), giving
  `2T1(q²)² = φ²(q)φ²(Q) + φ²(−q)φ²(−Q) + 16q²⁴ψ²(q²)ψ²(Q²)`;
* in `u, v`: `2w²T1(q²) = P·K` and `2w⁴T1(q²)² = P²·M`, so `K² = 2M`, and
  `K² − 2M = (2q⁶ + uv(u+v))(2q⁶ − 2q²uv + uv(u+v))·E` (certificates: `scripts/forty/round10/alg47.py`);
  the first two factors have constant term `2`, so `E = 0`:
* **`M47`** (his (5.24), the degree-47 modular equation): with `L = u + v`, `T = uv`,
  `4T³ − T²L² + 2q²T²L + 8q⁴T² + 4q⁶TL + 4q⁸T − 4q¹² = 0`;
* **`entry_3_35`**: with `x = χ(−q)χ(−q⁴⁷)` and `AB = {G(q)G(q⁹⁴)+q¹⁹H(q)H(q⁹⁴)}{G(q⁴⁷)H(q²)−q⁹G(q²)H(q⁴⁷)}`,
  `(AB − x − 2q² − 2q⁴/x)² = q²(4x + 9q² + 8q⁴/x)` (from `entry_3_35_AB` and `M47`);
  `entry_3_35_root`: `AB = x + 2q² + 2q⁴/x + q·r` with `r² = 4x + 9q² + 8q⁴/x` and `r(0) = 2`, and `r` is the only
  such series (`entry_3_35_unique`).
-/
import RamanujanTau.Forty.E35f
import RamanujanTau.Forty.E28g

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Forty
open ALz HahnSeries Finset MTC PowerSeries
open RankProof (Pinf isUnit_Pinf)

private lemma hm2 : 1 ≤ 2 := by norm_num
private lemma hm4 : 1 ≤ 4 := by norm_num

/-- `LphA`: `B = (1 0; 0 1)`, shifts `i (1, 0)`, `i ∈ {(-1)}`. -/
def BphA : ECS where
  b11 := 1
  b12 := 0
  b21 := 0
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 0 * n - (-1)) % 1 + (-1)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((0 * m + 0 * n - (-1)) % 1 + (-1))) - 0 * (n - 0 * ((0 * m + 0 * n - (-1)) % 1 + (-1)))) / 1), ((1 * (n - 0 * ((0 * m + 0 * n - (-1)) % 1 + (-1))) - 0 * (m - 1 * ((0 * m + 0 * n - (-1)) % 1 + (-1)))) / 1), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem LphA : QS (qmono 1 0 1 0 0 0 0) = (θ hm2 1 (-1) * θ hm2 1 (-1)) := by
  have h := (QS_orth 1 0 1 0 0 0 0 BphA hm2 hm2 (by norm_num [BphA])
    (by norm_num [BphA]) (by norm_num [BphA])).2
  simp only [BphA] at h
  rw [sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_sh hm2 1 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-1) 1 (e := (-1)) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `LphB`: `B = (1 1; -1 1)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1)}`. -/
def BphB : ECS where
  b11 := 1
  b12 := 1
  b21 := (-1)
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 1 * n - (-2)) % 2 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 1 * n - (-2)) % 2 + (-2))) - 1 * (n - 0 * ((1 * m + 1 * n - (-2)) % 2 + (-2)))) / 2), ((1 * (n - 0 * ((1 * m + 1 * n - (-2)) % 2 + (-2))) - (-1) * (m - 1 * ((1 * m + 1 * n - (-2)) % 2 + (-2)))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem LphB : QS (qmono 1 0 1 0 0 0 0) = (θ hm4 2 (-1) * θ hm4 2 (-1)) + (mono 1 1 * (θ hm4 0 (-1) * θ hm4 0 (-1))) := by
  have h := (QS_orth 1 0 1 0 0 0 0 BphB hm4 hm4 (by norm_num [BphB])
    (by norm_num [BphB]) (by norm_num [BphB])).2
  simp only [BphB] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_sh hm4 2 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-2) 1 (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- `φ(q)² = φ(q²)² + 4qψ(q⁴)²`. -/
theorem phi_sq : fb 1 2 ^ 2 = fb 2 4 ^ 2 + X * fb0 4 ^ 2 := by
  have h := LphA.symm.trans LphB
  rw [θfb hm2 1 (e' := 1) (by norm_num) (by norm_num) (by norm_num),
    θfb hm4 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num), θfb0 (N := 4) hm4] at h
  apply ι_inj
  simp only [map_add, map_mul, map_pow, ι_X]
  linear_combination h

lemma a22 : Pinf 2 2 = Pinf 2 4 * Pinf 4 4 := by
  have h := atom 2 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [prod_range_succ, prod_range_zero, one_mul] at h
  norm_num at h
  exact h

/-- `φ(q) = χ(q)² f(−q²)`. -/
lemma fb12_eq : fb 1 2 = chip 1 ^ 2 * Pinf 2 2 := by
  apply mul_right_cancel₀ (isUnit_J 1 2 le_rfl (by norm_num)).ne_zero
  rw [fb_mul 1 2 le_rfl (by norm_num)]
  simp only [J, Nat.reduceMul, Nat.reduceSub]
  rw [a22, r24]
  ring

/-- `ψ(q)(q;q²) = (q²;q²)`. -/
lemma fb14_mul : fb 1 4 * Pinf 1 2 = Pinf 2 2 := by
  apply mul_right_cancel₀ (isUnit_J 1 4 le_rfl (by norm_num)).ne_zero
  have h1 := fb_mul 1 4 le_rfl (by norm_num)
  simp only [Nat.reduceMul] at h1
  linear_combination Pinf 1 2 * h1 + psi_prod1

/-- `ψ(q²) χ(−q²)² = f(−q²)`. -/
lemma fb28_eq : fb 2 8 * (chip 1 * Pinf 1 2) ^ 2 = Pinf 2 2 := by
  have h := congrArg (S 2) fb14_mul
  simp only [map_mul, S_fb 2 1 4 le_rfl (by norm_num) (rfl : 2 = 2 * 1) (rfl : 8 = 2 * 4),
    S_P' 2 1 2 le_rfl (by norm_num) (rfl : 2 = 2 * 1) (rfl : 4 = 2 * 2),
    S_P' 2 2 2 (by norm_num) (by norm_num) (rfl : 4 = 2 * 2) (rfl : 4 = 2 * 2)] at h
  rw [r24] at h
  rw [a22, r24]
  linear_combination (chip 1 * Pinf 1 2) * h

/-- `φ(q)ψ(q²) = ψ(q)²`, i.e. `f(q,q) f(1,q²) = 2 f(q,q³)²`. -/
lemma fb12_fb02 : fb 1 2 * fb0 2 = 2 * fb 1 4 ^ 2 := by
  have h0 := fb0_mul 2 (by norm_num)
  have h1 := fb14_mul
  simp only [Nat.reduceMul] at h0
  rw [r24] at h0
  rw [a22, r24] at h1
  have hne : Pinf 2 4 * Pinf 1 2 ^ 2 ≠ 0 :=
    mul_ne_zero (Pinf_ne 2 4 (by norm_num) (by norm_num)) (pow_ne_zero _ (Pinf_ne 1 2 le_rfl (by norm_num)))
  apply mul_right_cancel₀ hne
  rw [fb12_eq, a22, r24]
  linear_combination (Pinf 1 2 ^ 3 * Pinf 4 4 * chip 1 ^ 3) * h0
    + (-2 * fb 1 4 * Pinf 1 2 ^ 2 * chip 1 - 2 * Pinf 1 2 ^ 2 * Pinf 4 4 * chip 1 ^ 2) * h1

lemma J13_eq : J 1 3 = Pinf 1 1 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom _ _ 3]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
    add_zero, mul_one]

/-- **(5.18)** in theta form: `T1(q²) = T1(q⁴) + 2q¹²ψ(q²)ψ(Q²) + q²(f(−q)f(−Q) + f(q)f(Q)) + 2q⁸f(−q⁴)f(−Q⁴)`. -/
theorem E518 : S 2 T1 = S 4 T1 + 2 * X ^ 12 * (fb 2 8 * fb 94 376)
    + X ^ 2 * (J 1 3 * J 47 141 + Ng (J 1 3) * Ng (J 47 141)) + 2 * X ^ 8 * (S 4 (J 1 3) * S 4 (J 47 141)) := by
  have e := E47
  have ne := congrArg Ng E47
  simp only [map_sub, map_mul, map_pow, map_ofNat, Ng_X, neg_sq] at ne
  have s4 := congrArg (S 4) E47
  simp only [map_sub, map_mul, map_pow, map_ofNat, SkX] at s4
  have tw : S 2 T2 = S 4 T1 + 2 * X ^ 12 * (fb 2 8 * fb 94 376) := by
    simp (disch := norm_num) only [T1, T2, map_add, map_mul, map_pow, map_ofNat, SkX, S_fb_s, S_fb0_s,
      Nat.reduceMul, ← pow_mul]
    ring
  have r2 := R2
  have r3 := R3
  apply mul_left_cancel₀ two_ne
  linear_combination -r2 + r3 + e + ne + 2 * s4 + 2 * tw

/-- `u = χ(q)χ(q⁴⁷)`. -/
noncomputable def u47 : PowerSeries ℤ := chip 1 * chip 47
/-- `v = χ(−q)χ(−q⁴⁷)`. -/
noncomputable def v47 : PowerSeries ℤ := chim 1 * chim 47

/-- **The degree-47 modular equation** (Ramanujan; Yesilyurt (5.24)): with `u = χ(q)χ(q⁴⁷)`, `v = χ(−q)χ(−q⁴⁷)`,
`L = u + v`, `T = uv`: `4T³ − T²L² + 2q²T²L + 8q⁴T² + 4q⁶TL + 4q⁸T − 4q¹² = 0`. -/
theorem M47 : 4 * (u47 * v47) ^ 3 - (u47 * v47) ^ 2 * (u47 + v47) ^ 2 + 2 * X ^ 2 * (u47 * v47) ^ 2 * (u47 + v47)
    + 8 * X ^ 4 * (u47 * v47) ^ 2 + 4 * X ^ 6 * (u47 * v47) * (u47 + v47) + 4 * X ^ 8 * (u47 * v47) - 4 * X ^ 12 = 0 := by
  -- product forms
  have f12 := fb12_eq
  have f47 : fb 47 94 = chip 47 ^ 2 * Pinf 94 94 := by
    have h := congrArg (S 47) fb12_eq
    simp only [map_mul, map_pow, S_fb 47 1 2 le_rfl (by norm_num) (rfl : 47 = 47 * 1) (rfl : 94 = 47 * 2),
      S_chip 47 1 47 rfl, S_P' 47 2 2 (by norm_num) (by norm_num) (rfl : 94 = 47 * 2) (rfl : 94 = 47 * 2)] at h
    exact h
  have J12 : J 1 2 = Pinf 1 2 ^ 2 * Pinf 2 2 := by simp only [J, Nat.reduceSub]; ring
  have J4794 : J 47 94 = Pinf 47 94 ^ 2 * Pinf 94 94 := by simp only [J, Nat.reduceSub]; ring
  have hps := fb28_eq
  have hPs : fb 94 376 * (chip 47 * Pinf 47 94) ^ 2 = Pinf 94 94 := by
    have h := congrArg (S 47) fb28_eq
    simp only [map_mul, map_pow, S_fb 47 2 8 (by norm_num) (by norm_num) (rfl : 94 = 47 * 2) (rfl : 376 = 47 * 8),
      S_chip 47 1 47 rfl, S_P' 47 1 2 le_rfl (by norm_num) (rfl : 47 = 47 * 1) (rfl : 94 = 47 * 2),
      S_P' 47 2 2 (by norm_num) (by norm_num) (rfl : 94 = 47 * 2) (rfl : 94 = 47 * 2)] at h
    exact h
  have k13 := J13_eq
  have k47 : J 47 141 = Pinf 47 47 := by
    have h := congrArg (S 47) J13_eq
    simp only [S_J 47 1 3 le_rfl (by norm_num), S_P' 47 1 1 le_rfl le_rfl (rfl : 47 = 47 * 1) (rfl : 47 = 47 * 1),
      Nat.reduceMul] at h
    exact h
  have sp1 := E1_split
  have sp47 : Pinf 47 47 = Pinf 47 94 * Pinf 94 94 := by
    have h := congrArg (S 47) E1_split
    simp only [map_mul, S_P' 47 1 1 le_rfl le_rfl (rfl : 47 = 47 * 1) (rfl : 47 = 47 * 1),
      S_P' 47 1 2 le_rfl (by norm_num) (rfl : 47 = 47 * 1) (rfl : 94 = 47 * 2),
      S_P' 47 2 2 (by norm_num) (by norm_num) (rfl : 94 = 47 * 2) (rfl : 94 = 47 * 2)] at h
    exact h
  have hV : J 1 3 * J 47 141 = Pinf 1 2 * Pinf 2 2 * (Pinf 47 94 * Pinf 94 94) := by
    rw [k13, k47, sp1, sp47]
  have hNV : Ng (J 1 3) * Ng (J 47 141) = chip 1 * Pinf 2 2 * (chip 47 * Pinf 94 94) := by
    rw [k13, k47, Ng_E1, Ng_P4747]; ring
  have a4 : Pinf 4 4 * (chip 1 * Pinf 1 2) = Pinf 2 2 := by rw [a22, r24]; ring
  have a188 : Pinf 188 188 * (chip 47 * Pinf 47 94) = Pinf 94 94 := by
    have h := congrArg (S 47) a4
    simp only [map_mul, S_chip 47 1 47 rfl, S_P' 47 4 4 (by norm_num) (by norm_num) (rfl : 188 = 47 * 4) (rfl : 188 = 47 * 4),
      S_P' 47 1 2 le_rfl (by norm_num) (rfl : 47 = 47 * 1) (rfl : 94 = 47 * 2),
      S_P' 47 2 2 (by norm_num) (by norm_num) (rfl : 94 = 47 * 2) (rfl : 94 = 47 * 2)] at h
    exact h
  have hS4V : S 4 (J 1 3) * S 4 (J 47 141) * (chip 1 * Pinf 1 2 * (chip 47 * Pinf 47 94)) = Pinf 2 2 * Pinf 94 94 := by
    rw [k13, k47, S_P' 4 1 1 le_rfl le_rfl (rfl : 4 = 4 * 1) (rfl : 4 = 4 * 1),
      S_P' 4 47 47 (by norm_num) (by norm_num) (rfl : 188 = 4 * 47) (rfl : 188 = 4 * 47)]
    linear_combination (Pinf 188 188 * (chip 47 * Pinf 47 94)) * a4 + Pinf 2 2 * a188
  -- 2 T1(q⁴) = φ(q)φ(Q) + φ(−q)φ(−Q)
  have hS4 : 2 * S 4 T1 = chip 1 ^ 2 * Pinf 2 2 * (chip 47 ^ 2 * Pinf 94 94)
      + Pinf 1 2 ^ 2 * Pinf 2 2 * (Pinf 47 94 ^ 2 * Pinf 94 94) := by
    obtain ⟨d1, d2⟩ := phi_dis
    rw [phi_chip, ← fb12_eq] at d1 d2
    have m8 := fb0_mul 8 (by norm_num)
    have m48 := fb_mul 4 8 (by norm_num) (by norm_num)
    simp only [Nat.reduceMul] at m8 m48
    have e1 : fb 1 2 - J 1 2 = 2 * X * fb0 8 := by
      apply mul_right_cancel₀ (Pinf_ne 8 16 (by norm_num) (by norm_num))
      linear_combination d1 - 2 * X * m8
    have e2 : fb 1 2 + J 1 2 = 2 * fb 4 8 := by
      apply mul_right_cancel₀ (isUnit_J 4 8 (by norm_num) (by norm_num)).ne_zero
      linear_combination d2 - 2 * m48
    have e1Q := congrArg (S 47) e1
    have e2Q := congrArg (S 47) e2
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, SkX,
      S_fb 47 1 2 le_rfl (by norm_num) (rfl : 47 = 47 * 1) (rfl : 94 = 47 * 2),
      S_fb 47 4 8 (by norm_num) (by norm_num) (rfl : 188 = 47 * 4) (rfl : 376 = 47 * 8),
      S_fb0 47 8 (by norm_num) (rfl : 376 = 47 * 8), S_J 47 1 2 le_rfl (by norm_num), Nat.reduceMul] at e1Q e2Q
    have hT : S 4 T1 = fb 4 8 * fb 188 376 + X ^ 48 * (fb0 8 * fb0 376) := by
      simp (disch := norm_num) only [T1, map_add, map_mul, map_pow, SkX, S_fb_s, S_fb0_s, Nat.reduceMul, ← pow_mul]
    apply mul_left_cancel₀ two_ne
    rw [hT, ← f12, ← f47, ← J12, ← J4794]
    linear_combination -(fb 47 94 + J 47 94) * e2 - 2 * fb 4 8 * e2Q - (fb 47 94 - J 47 94) * e1
      - 2 * X * fb0 8 * e1Q
  have h518 := E518
  have hX1 : S 2 T1 = fb 2 4 * fb 94 188 + X ^ 24 * (fb0 4 * fb0 188) := by
    simp (disch := norm_num) only [T1, map_add, map_mul, map_pow, SkX, S_fb_s, S_fb0_s, Nat.reduceMul, ← pow_mul]
  -- the squares
  have sq := phi_sq
  rw [f12] at sq
  have sqN : (Pinf 1 2 ^ 2 * Pinf 2 2) ^ 2 = fb 2 4 ^ 2 - X * fb0 4 ^ 2 := by
    have h := congrArg Ng phi_sq
    simp only [map_add, map_mul, map_pow, Ng_X, Ng_fb_odd 1 2 ⟨0, rfl⟩ ⟨1, rfl⟩ (by norm_num),
      Ng_fb_ev 2 4 ⟨1, rfl⟩ ⟨2, rfl⟩ (by norm_num) (by norm_num), Ng_fb0_ev 4 ⟨2, rfl⟩ (by norm_num)] at h
    rw [← J12]
    linear_combination h
  have sqQ : (chip 47 ^ 2 * Pinf 94 94) ^ 2 = fb 94 188 ^ 2 + X ^ 47 * fb0 188 ^ 2 := by
    have h := congrArg (S 47) phi_sq
    simp only [map_add, map_mul, map_pow, SkX, S_fb 47 1 2 le_rfl (by norm_num) (rfl : 47 = 47 * 1) (rfl : 94 = 47 * 2),
      S_fb 47 2 4 (by norm_num) (by norm_num) (rfl : 94 = 47 * 2) (rfl : 188 = 47 * 4),
      S_fb0 47 4 (by norm_num) (rfl : 188 = 47 * 4)] at h
    rw [← f47]
    exact h
  have sqQN : (Pinf 47 94 ^ 2 * Pinf 94 94) ^ 2 = fb 94 188 ^ 2 - X ^ 47 * fb0 188 ^ 2 := by
    have h := congrArg Ng sqQ
    rw [← f47] at h
    simp only [map_add, map_mul, map_pow, Ng_X, Ng_fb_odd 47 94 ⟨23, rfl⟩ ⟨47, rfl⟩ (by norm_num),
      Ng_fb_ev 94 188 ⟨47, rfl⟩ ⟨94, rfl⟩ (by norm_num) (by norm_num), Ng_fb0_ev 188 ⟨94, rfl⟩ (by norm_num)] at h
    rw [← J4794]
    linear_combination h
  have p6 : fb 2 4 * fb0 4 = 2 * fb 2 8 ^ 2 := by
    have h := congrArg (S 2) fb12_fb02
    simp only [map_mul, map_pow, map_ofNat, S_fb 2 1 2 le_rfl (by norm_num) (rfl : 2 = 2 * 1) (rfl : 4 = 2 * 2),
      S_fb0 2 2 (by norm_num) (rfl : 4 = 2 * 2), S_fb 2 1 4 le_rfl (by norm_num) (rfl : 2 = 2 * 1) (rfl : 8 = 2 * 4)] at h
    exact h
  have p6Q : fb 94 188 * fb0 188 = 2 * fb 94 376 ^ 2 := by
    have h := congrArg (S 94) fb12_fb02
    simp only [map_mul, map_pow, map_ofNat, S_fb 94 1 2 le_rfl (by norm_num) (rfl : 94 = 94 * 1) (rfl : 188 = 94 * 2),
      S_fb0 94 2 (by norm_num) (rfl : 188 = 94 * 2), S_fb 94 1 4 le_rfl (by norm_num) (rfl : 94 = 94 * 1) (rfl : 376 = 94 * 4)] at h
    exact h
  -- the two quadratic relations for X₁ = T1(q²)
  have K1 : 2 * ((chip 1)*(Pinf 1 2)*(chip 47)*(Pinf 47 94)) ^ 2 * S 2 T1 = ((Pinf 2 2)*(Pinf 94 94)) * (2*(chip 1)^2*(Pinf 1 2)^2*(chip 47)^2*(Pinf 47 94)^2*(X)^2*((chip 1)*(chip 47) + (Pinf 1 2)*(Pinf 47 94)) + (chip 1)^2*(Pinf 1 2)^2*(chip 47)^2*(Pinf 47 94)^2*((chip 1)^2*(chip 47)^2 + (Pinf 1 2)^2*(Pinf 47 94)^2) + 4*(chip 1)*(Pinf 1 2)*(chip 47)*(Pinf 47 94)*(X)^8 + 4*(X)^12) := by
    linear_combination (2 * ((chip 1)*(Pinf 1 2)*(chip 47)*(Pinf 47 94))^2) * h518 + ((chip 1)*(Pinf 1 2)*(chip 47)*(Pinf 47 94))^2 * hS4 + 4 * X^12 * ((((chip 47)*(Pinf 47 94))^2 * ((fb 94 376))) * hps + ((Pinf 2 2)) * hPs) + 2 * X^2 * ((chip 1)*(Pinf 1 2)*(chip 47)*(Pinf 47 94))^2 * (hV + hNV) + 4 * X^8 * ((chip 1)*(Pinf 1 2)*(chip 47)*(Pinf 47 94)) * hS4V
  have K2 : 2 * ((chip 1)*(Pinf 1 2)*(chip 47)*(Pinf 47 94)) ^ 4 * S 2 T1 ^ 2 = ((Pinf 2 2)*(Pinf 94 94)) ^ 2 * (((chip 1)^4*(Pinf 1 2)^4*(chip 47)^4*(Pinf 47 94)^4*((chip 1)^4*(chip 47)^4 + (Pinf 1 2)^4*(Pinf 47 94)^4) + 16*(X)^24)) := by
    linear_combination ((chip 1)*(Pinf 1 2)*(chip 47)*(Pinf 47 94))^4 * ((2 * ((S 2 T1) + (fb 94 188)*(fb 2 4) + (fb0 188)*(fb0 4)*(X)^24)) * hX1 - (((chip 1)^2*(Pinf 2 2))^2 * sqQ + ((fb 94 188)^2 + (fb0 188)^2*(X)^47) * sq) - (((Pinf 1 2)^2*(Pinf 2 2))^2 * sqQN + ((fb 94 188)^2 - (fb0 188)^2*(X)^47) * sqN) + 4 * X^24 * (((fb 94 188)*(fb0 188)) * p6 + 2 * ((fb 2 8))^2 * p6Q)) + 16 * X^24 * ((fb 94 376)*(chip 1)^2*(Pinf 1 2)^2*(chip 47)^2*(Pinf 47 94)^2*(fb 2 8) + (Pinf 2 2)*(Pinf 94 94)) * (((fb 94 376)*(chip 47)^2*(Pinf 47 94)^2) * hps + ((Pinf 2 2)) * hPs)
  have key : ((Pinf 2 2)*(Pinf 94 94)) ^ 2 * (((chip 1)^2*(Pinf 1 2)*(chip 47)^2*(Pinf 47 94) + (chip 1)*(Pinf 1 2)^2*(chip 47)*(Pinf 47 94)^2 + 2*(X)^6) * ((chip 1)^2*(Pinf 1 2)*(chip 47)^2*(Pinf 47 94) + (chip 1)*(Pinf 1 2)^2*(chip 47)*(Pinf 47 94)^2 - 2*(chip 1)*(Pinf 1 2)*(chip 47)*(Pinf 47 94)*(X)^2 + 2*(X)^6) * (4 * (u47 * v47) ^ 3 - (u47 * v47) ^ 2 * (u47 + v47) ^ 2
      + 2 * X ^ 2 * (u47 * v47) ^ 2 * (u47 + v47) + 8 * X ^ 4 * (u47 * v47) ^ 2 + 4 * X ^ 6 * (u47 * v47) * (u47 + v47)
      + 4 * X ^ 8 * (u47 * v47) - 4 * X ^ 12)) = 0 := by
    simp only [u47, v47, chim, Nat.reduceMul]
    linear_combination (-(((Pinf 2 2)*(Pinf 94 94)) * (2*(chip 1)^2*(Pinf 1 2)^2*(chip 47)^2*(Pinf 47 94)^2*(X)^2*((chip 1)*(chip 47) + (Pinf 1 2)*(Pinf 47 94)) + (chip 1)^2*(Pinf 1 2)^2*(chip 47)^2*(Pinf 47 94)^2*((chip 1)^2*(chip 47)^2 + (Pinf 1 2)^2*(Pinf 47 94)^2) + 4*(chip 1)*(Pinf 1 2)*(chip 47)*(Pinf 47 94)*(X)^8 + 4*(X)^12) + 2 * ((chip 1)*(Pinf 1 2)*(chip 47)*(Pinf 47 94)) ^ 2 * S 2 T1)) * K1 + 2 * K2
  have hP : ((Pinf 2 2)*(Pinf 94 94)) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero (Pinf_ne 2 2 (by norm_num) (by norm_num))
    (Pinf_ne 94 94 (by norm_num) (by norm_num)))
  have ccs : constantCoeff (chip 1) = 1 ∧ constantCoeff (chip 47) = 1 ∧ constantCoeff (Pinf 1 2) = 1 ∧
      constantCoeff (Pinf 47 94) = 1 :=
    ⟨cc_chip 1, cc_chip 47, cc_Pinf 1 2 le_rfl (by norm_num), cc_Pinf 47 94 (by norm_num) (by norm_num)⟩
  have hf1 : ((chip 1)^2*(Pinf 1 2)*(chip 47)^2*(Pinf 47 94) + (chip 1)*(Pinf 1 2)^2*(chip 47)*(Pinf 47 94)^2 + 2*(X)^6) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, constantCoeff_X, ccs.1, ccs.2.1, ccs.2.2.1, ccs.2.2.2,
      map_zero] at this
    norm_num at this
  have hf2 : ((chip 1)^2*(Pinf 1 2)*(chip 47)^2*(Pinf 47 94) + (chip 1)*(Pinf 1 2)^2*(chip 47)*(Pinf 47 94)^2 - 2*(chip 1)*(Pinf 1 2)*(chip 47)*(Pinf 47 94)*(X)^2 + 2*(X)^6) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, constantCoeff_X, ccs.1, ccs.2.1, ccs.2.2.1, ccs.2.2.2,
      map_zero] at this
    norm_num at this
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hP
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (mul_ne_zero hf1 hf2)
  · exact h

lemma chim_w47 : chim 2 * chim 94 = u47 * v47 := by
  have r94 : Pinf 94 188 = chip 47 * Pinf 47 94 := by
    have h := congrArg (S 47) r24
    simp only [map_mul, S_chip 47 1 47 rfl, S_P' 47 2 4 (by norm_num) (by norm_num) (rfl : 94 = 47 * 2) (rfl : 188 = 47 * 4),
      S_P' 47 1 2 le_rfl (by norm_num) (rfl : 47 = 47 * 1) (rfl : 94 = 47 * 2)] at h
    exact h
  simp only [chim, u47, v47, Nat.reduceMul]
  rw [r24, r94]
  ring

lemma isUnit_v47 : IsUnit v47 :=
  (isUnit_Pinf 1 (2 * 1) le_rfl (by norm_num)).mul (isUnit_Pinf 47 (2 * 47) (by norm_num) (by norm_num))

lemma isUnit_w47 : IsUnit (u47 * v47) := by
  rw [← chim_w47]
  exact (isUnit_Pinf 2 (2 * 2) (by norm_num) (by norm_num)).mul (isUnit_Pinf 94 (2 * 94) (by norm_num) (by norm_num))

/-- **Entry 3.35** (squared form): with `x = χ(−q)χ(−q⁴⁷)`,
`({G(q)G(q⁹⁴)+q¹⁹H(q)H(q⁹⁴)}{G(q⁴⁷)H(q²)−q⁹G(q²)H(q⁴⁷)} − x − 2q² − 2q⁴/x)² = q²(4x + 9q² + 8q⁴/x)`. -/
theorem entry_3_35 :
    ((G * S 94 G + X ^ 19 * H * S 94 H) * (S 47 G * S 2 H - X ^ 9 * S 2 G * S 47 H)
      - chim 1 * chim 47 - 2 * X ^ 2 - 2 * X ^ 4 * Ring.inverse (chim 1 * chim 47)) ^ 2 =
    X ^ 2 * (4 * (chim 1 * chim 47) + 9 * X ^ 2 + 8 * X ^ 4 * Ring.inverse (chim 1 * chim 47)) := by
  rw [entry_3_35_AB, chim_w47]
  have hE := M47
  have hw := Ring.inverse_mul_cancel _ isUnit_w47
  have hv : Ring.inverse v47 = Ring.inverse (u47 * v47) * u47 := by
    have h1 := Ring.inverse_mul_cancel _ isUnit_v47
    calc Ring.inverse v47 = Ring.inverse v47 * (Ring.inverse (u47 * v47) * (u47 * v47)) := by rw [hw, mul_one]
      _ = (Ring.inverse v47 * v47) * (Ring.inverse (u47 * v47) * u47) := by ring
      _ = _ := by rw [h1, one_mul]
  have hu : chip 1 * chip 47 = u47 := rfl
  rw [show chim 1 * chim 47 = v47 from rfl, hu, hv]
  linear_combination (-(Ring.inverse (u47 * v47)) ^ 2) * hE + (4*Ring.inverse (u47 * v47)*X^8 + 4*Ring.inverse (u47 * v47)*X^6*u47 + 4*Ring.inverse (u47 * v47)*X^6*v47 + 8*Ring.inverse (u47 * v47)*X^4*u47*v47 + 2*Ring.inverse (u47 * v47)*X^2*u47^2*v47 + 2*Ring.inverse (u47 * v47)*X^2*u47*v47^2 - Ring.inverse (u47 * v47)*u47^3*v47 + 2*Ring.inverse (u47 * v47)*u47^2*v47^2 - Ring.inverse (u47 * v47)*u47*v47^3 + 8*X^4 + 2*X^2*u47 + 2*X^2*v47 - u47^2 + 2*u47*v47 - v47^2) * hw

end Forty
