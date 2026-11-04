import RamanujanTau.AtkinSporadic.HalfHecke
import RamanujanTau.BLBound.AhlgrenBoylan
import RamanujanTau.MockTheta5PartitionCount

/-!
# The twisted partition series modulo 13 is `G/η` with `G` a level-one cusp form

Let `P̄ = Σ p(N) qᴺ` and keep only the `N` with `((24N − 1)/13) = −1`:
`twPGF = Σ_{((24N−1)/13) = −1} p(N) qᴺ`.

**`twisted_eq`** (unconditional): there is a level-one modular form `g` of weight `168` with integer
q-expansion and no constant term such that `twPGF ≡ g · P̄ (mod 13)`. Equivalently
`Σ_{((m/13)) = −1} p((m+1)/24) q^{m/24} ≡ g/η (mod 13)`: the twisted class is the reduction of a
cusp form of weight `167/2` on `SL₂(ℤ)` with multiplier `ν_η^{−1}`.

Proof. Euler's criterion turns the twist into `τ(N) = 7((24N−1)^12 − (24N−1)^6)`. Since
`P̄ · E^169 = E^168` with `E = (q;q)_∞` and `E^169 ≡ E(q^169)` is supported on multiples of 13, the
twist passes through `E^169`; on `q⁷E^168 = Δ⁷` it is `7(24^12 θ^12 − 24^6 θ^6)`, which preserves
reductions of level-one forms (`FormBar.theta_iter`). The result vanishes to order 8, so it is
`Δ⁸` times a reduced form of weight 156 (`div_Delta_pow`), which lifts to `ℤ` (`lift_iso`).
-/

set_option autoImplicit false

namespace RamanujanTau.AtkinSporadic.Twist13
open PowerSeries BoylanWebb RamanujanTau.BLBound ModP
open MockTheta5.JTP (qfacInf partitionGF)

instance fact13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The twist weight `τ(N) = ½((24N−1)^12 − (24N−1)^6)` in `𝔽₁₃`. -/
def tau (N : ℕ) : ZMod 13 := 7 * ((24 * (N : ZMod 13) - 1) ^ 12 - (24 * (N : ZMod 13) - 1) ^ 6)

/-- Multiply the `N`-th coefficient by `τ(N)`. -/
noncomputable def tw (f : PowerSeries (ZMod 13)) : PowerSeries (ZMod 13) :=
  PowerSeries.mk fun N => tau N * coeff N f

lemma coeff_tw (f : PowerSeries (ZMod 13)) (N : ℕ) : coeff N (tw f) = tau N * coeff N f := by
  rw [tw, coeff_mk]

/-- The twisted partition generating function. -/
noncomputable def twPGF : PowerSeries ℤ :=
  PowerSeries.mk fun N =>
    if legendreSym 13 (24 * (N : ℤ) - 1) = -1 then (Fintype.card (Nat.Partition N) : ℤ) else 0

/-- Euler's criterion: `τ(N)` is the indicator of `((24N−1)/13) = −1`. -/
lemma tau_eq (N : ℕ) : tau N = if legendreSym 13 (24 * (N : ℤ) - 1) = -1 then 1 else 0 := by
  have he := legendreSym.eq_pow 13 (24 * (N : ℤ) - 1)
  have hx : (24 * (N : ZMod 13) - 1) = (((24 * (N : ℤ) - 1 : ℤ)) : ZMod 13) := by push_cast; ring
  have h13 : (13 : ℕ) / 2 = 6 := by norm_num
  rw [h13] at he
  have hsq : (24 * (N : ZMod 13) - 1) ^ 12 = ((24 * (N : ZMod 13) - 1) ^ 6) ^ 2 := by ring
  rw [tau, hsq, hx, ← he]
  by_cases h0 : ((24 * (N : ℤ) - 1 : ℤ) : ZMod 13) = 0
  · rw [(legendreSym.eq_zero_iff 13 _).mpr h0]; decide
  · rcases legendreSym.eq_one_or_neg_one 13 h0 with h | h <;> rw [h] <;> decide

lemma Ψ_twPGF : Ψ 13 twPGF = tw (Ψ 13 partitionGF) := by
  ext N
  rw [coeff_tw, coeff_map, coeff_map, twPGF, coeff_mk, tau_eq,
    MockTheta5.JTP.coeff_partitionGF_eq_card]
  split_ifs <;> simp

/-- `τ` depends only on `N mod 13`, so the twist passes through series in `q^13`. -/
lemma tw_mul_of_support (f g : PowerSeries (ZMod 13)) (hg : ∀ n, ¬ 13 ∣ n → coeff n g = 0) :
    tw (f * g) = tw f * g := by
  ext N
  rw [coeff_tw, coeff_mul, coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [coeff_tw]
  by_cases hd : 13 ∣ p.2
  · have hc : (N : ZMod 13) = (p.1 : ZMod 13) := by
      rw [← hp, Nat.cast_add, (ZMod.natCast_eq_zero_iff _ _).mpr hd, add_zero]
    rw [tau, tau, hc]; ring
  · rw [hg _ hd]; ring

lemma coeff_theta_iter' (m n : ℕ) (f : PowerSeries (ZMod 13)) :
    coeff n (Igusa.theta^[m] f) = (n : ZMod 13) ^ m * coeff n f := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', Igusa.coeff_theta, ih, pow_succ]
    ring

/-- On `q⁷ f` the twist is `7(24^12 θ^12 − 24^6 θ^6)`, since `24·7 ≡ −1 (mod 13)`. -/
lemma X7_tw (f : PowerSeries (ZMod 13)) :
    X ^ 7 * tw f = (7 : ZMod 13) • ((24 : ZMod 13) ^ 12 • Igusa.theta^[12] (X ^ 7 * f) -
      (24 : ZMod 13) ^ 6 • Igusa.theta^[6] (X ^ 7 * f)) := by
  ext n
  rw [coeff_X_pow_mul', coeff_smul, map_sub, coeff_smul, coeff_smul, coeff_theta_iter',
    coeff_theta_iter', coeff_X_pow_mul', smul_eq_mul, smul_eq_mul, smul_eq_mul]
  split_ifs with h
  · rw [coeff_tw, tau]
    obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show 7 + N - 7 = N by omega]
    have h24 : (24 : ZMod 13) * ((7 + N : ℕ) : ZMod 13) = 24 * (N : ZMod 13) - 1 := by
      push_cast
      have : (24 : ZMod 13) * 7 = -1 := by decide
      linear_combination this
    have e12 : (24 : ZMod 13) ^ 12 * ((7 + N : ℕ) : ZMod 13) ^ 12 = (24 * (N : ZMod 13) - 1) ^ 12 := by
      rw [← mul_pow, h24]
    have e6 : (24 : ZMod 13) ^ 6 * ((7 + N : ℕ) : ZMod 13) ^ 6 = (24 * (N : ZMod 13) - 1) ^ 6 := by
      rw [← mul_pow, h24]
    linear_combination (7 * coeff N f) * (-e12 + e6)
  · simp

lemma h5 : 5 ≤ 13 := by norm_num

/-- **The twisted partition series is the reduction of `g/η`, `g ∈ S₁₆₈(SL₂(ℤ))` integral.** -/
theorem twisted_eq : ∃ g : PowerSeries ℤ, IntForm ((168 : ℕ) : ℤ) g ∧ constantCoeff g = 0 ∧
    Ψ 13 twPGF = Ψ 13 (g * partitionGF) := by
  set E : PowerSeries (ZMod 13) := Ψ 13 qfacInf with hEdef
  set P : PowerSeries (ZMod 13) := Ψ 13 partitionGF with hPdef
  have hEP : E * P = 1 := by rw [hEdef, hPdef, ← map_mul, qfac_mul_pgf, map_one]
  -- the twist through `E^169`
  have hsupp : ∀ n, ¬ 13 ∣ n → coeff n (E ^ 169) = 0 := by
    intro n hn
    rw [show E ^ 169 = (E ^ 13) ^ 13 by rw [← pow_mul], coeff_pow_char, if_neg hn]
  have h1 : tw P * E ^ 169 = tw (E ^ 168) := by
    rw [← tw_mul_of_support _ _ hsupp]
    congr 1
    linear_combination E ^ 168 * hEP
  -- `q⁷ E^168 = Δ⁷`
  have hD7 : X ^ 7 * E ^ 168 = Dl 13 ^ 7 := by
    rw [Dl_pow, hEdef, map_pow]
  set H : PowerSeries (ZMod 13) := X ^ 7 * tw (E ^ 168) with hHdef
  have hH : FormBar 13 252 H := by
    rw [hHdef, X7_tw, hD7]
    have hA : FormBar 13 252 (Igusa.theta^[12] (Dl 13 ^ 7)) := by
      have := (formBar_Dl_pow (ℓ := 13) h5 7).theta_iter h5 12
      simpa using this
    have hB : FormBar 13 252 (Igusa.theta^[6] (Dl 13 ^ 7)) := by
      have := ((formBar_Dl_pow (ℓ := 13) h5 7).theta_iter h5 6).up h5 7
      simpa using this
    exact ((hA.smul' _).sub (hB.smul' _)).smul' _
  have hlow : ∀ n < 8, coeff n H = 0 := by
    intro n hn
    rw [hHdef, coeff_X_pow_mul']
    split_ifs with h
    · rw [show n - 7 = 0 by omega, coeff_tw, show tau 0 = 0 by decide, zero_mul]
    · rfl
  have hmain : X ^ 7 * (tw P * E ^ 169) = H := by rw [h1]
  obtain ⟨Pp, hPp, hPe⟩ := hH
  by_cases hne : H = 0
  · -- degenerate case: the twisted series vanishes mod 13
    refine ⟨0, IntForm.zero, by simp, ?_⟩
    rw [zero_mul, map_zero, Ψ_twPGF]
    have hX : (X : PowerSeries (ZMod 13)) ^ 7 ≠ 0 := pow_ne_zero _ X_ne_zero
    have h2 : tw P * E ^ 169 = 0 := by
      rcases mul_eq_zero.mp (hmain.trans hne) with h | h
      · exact absurd h hX
      · exact h
    have h3 : tw P = tw P * E ^ 169 * P ^ 169 := by
      rw [mul_assoc, ← mul_pow, hEP, one_pow, mul_one]
    rw [h3, h2, zero_mul]
  · obtain ⟨-, K, hK, hKe⟩ := div_Delta_pow (ℓ := 13) h5 8 hPp (by rw [hPe]; exact hlow)
      (by rw [hPe]; exact hne)
    obtain ⟨g0, hg0, hg0e⟩ := lift_iso 13 (252 - 12 * 8) K hK
    refine ⟨Dz * g0, (IntForm.disc.mul hg0).cast (by norm_num), ?_, ?_⟩
    · rw [map_mul, map_mul, PowerSeries.constantCoeff_X, zero_mul, zero_mul]
    · -- `X⁷ (tw P · E^169) = Δ⁸ · K`
      have h8 : X ^ 7 * (tw P * E ^ 169) = X ^ 7 * (X * E ^ 192 * ev (ZMod 13) K) := by
        rw [hmain, ← hPe, hKe, Dl_pow, hEdef, map_pow]
        ring
      have hX : (X : PowerSeries (ZMod 13)) ^ 7 ≠ 0 := pow_ne_zero _ X_ne_zero
      have h9 := mul_left_cancel₀ hX h8
      rw [Ψ_twPGF, map_mul, map_mul, map_mul, map_pow, map_X, hg0e]
      change tw P = X * E ^ 24 * ev (ZMod 13) K * P
      have h3 : tw P = tw P * E ^ 169 * P ^ 169 := by
        rw [mul_assoc, ← mul_pow, hEP, one_pow, mul_one]
      rw [h3, h9]
      have hp : (E * P) ^ 169 = 1 := by rw [hEP, one_pow]
      rw [show X * E ^ 192 * ev (ZMod 13) K * P ^ 169 = X * ev (ZMod 13) K * E ^ 23 * (E * P) ^ 169 by ring,
        show X * E ^ 24 * ev (ZMod 13) K * P = X * ev (ZMod 13) K * E ^ 23 * (E * P) by ring, hp, hEP]

end RamanujanTau.AtkinSporadic.Twist13
