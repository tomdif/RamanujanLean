/-
# The `(q;q)_∞⁴` vanishing: every coefficient at an exponent `≡ 4 (mod 5)` is `≡ 0 (mod 5)`

`(q;q)_∞⁴ = (q;q)_∞ · (q;q)_∞³ = pentSeries · jacobiCubeSum`. A coefficient of `q^a` is a sum of terms
`±(2m+1)` over pairs `(k,m)` with `pent(k)+tri(m)=a`. When `a ≡ 4 (mod 5)`, the arithmetic heart
`jacobi_weight_dvd_of_exponent` forces `2m+1 ≡ 0 (mod 5)` on every such pair, so

  **`coeff_qfac4_mod5`:**  `a % 5 = 4  →  coeff a (Ψ₅ (q;q)_∞⁴) = 0`.

Uses only the coefficient *support* of `pentSeries` (an exponent is a generalized pentagonal number) and the
coefficient *value* of `jacobiCubeSum`. No `sorry`.
-/
import RamanujanTau.MockTheta5Frobenius
import RamanujanTau.MockTheta5JacobiCubeProof
import RamanujanTau.PartitionCongruenceMod5

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- `coeff a (q^e · w) = w` if `e = a`, else `0`. -/
private lemma coeff_XpowC (e a : ℕ) (w : ℤ) :
    coeff a (X ^ e * PowerSeries.C w) = if e = a then w else 0 := by
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C]
  split_ifs <;> first | rfl | (exfalso; omega)

private lemma two_dvd_succ (m : ℕ) : 2 ∣ m * (m + 1) := by
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨j * (m + 1), by subst hj; ring⟩
  · exact ⟨(j + 1) * m, by subst hj; ring⟩

/-! ### support of `pentSeries`: a nonzero coefficient sits at a generalized pentagonal number -/

private lemma two_dvd_pent2 (m : ℕ) : 2 ∣ (m + 1) * (3 * m + 2) := by
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨(2 * j + 1) * (3 * j + 1), by subst hj; ring⟩
  · exact ⟨(j + 1) * (6 * j + 5), by subst hj; ring⟩

private lemma two_dvd_pent4 (m : ℕ) : 2 ∣ (m + 1) * (3 * m + 4) := by
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨(2 * j + 1) * (3 * j + 2), by subst hj; ring⟩
  · exact ⟨(j + 1) * (6 * j + 7), by subst hj; ring⟩

/-- `pent(m+1)` doubled: `(m+1)(3(m+1)−1) = 2·⌊(m+1)(3m+2)/2⌋`. -/
private lemma pent_double_pos (m : ℕ) :
    ((m : ℤ) + 1) * (3 * ((m : ℤ) + 1) - 1) = 2 * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) := by
  have hev : 2 * ((m + 1) * (3 * m + 2) / 2) = (m + 1) * (3 * m + 2) := by
    have := two_dvd_pent2 m; omega
  have h2 : 2 * (((m + 1) * (3 * m + 2) / 2 : ℕ) : ℤ) = (((m + 1) * (3 * m + 2) : ℕ) : ℤ) := by
    rw [← Nat.cast_two, ← Nat.cast_mul, hev]
  rw [h2]; push_cast; ring

/-- `pent(−(m+1))` doubled: `(−(m+1))(3(−(m+1))−1) = 2·⌊(m+1)(3m+4)/2⌋`. -/
private lemma pent_double_neg (m : ℕ) :
    (-((m : ℤ) + 1)) * (3 * (-((m : ℤ) + 1)) - 1) = 2 * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) := by
  have hev : 2 * ((m + 1) * (3 * m + 4) / 2) = (m + 1) * (3 * m + 4) := by
    have := two_dvd_pent4 m; omega
  have h2 : 2 * (((m + 1) * (3 * m + 4) / 2 : ℕ) : ℤ) = (((m + 1) * (3 * m + 4) : ℕ) : ℤ) := by
    rw [← Nat.cast_two, ← Nat.cast_mul, hev]
  rw [h2]; push_cast; ring

lemma map_evm1_pentTermP (m : ℕ) :
    PowerSeries.map evm1 (pentTermP m)
      = X ^ ((m + 1) * (3 * m + 2) / 2) * PowerSeries.C (sgn ((m : ℤ) + 1))
        + X ^ ((m + 1) * (3 * m + 4) / 2) * PowerSeries.C (sgn (-((m : ℤ) + 1))) := by
  rw [pentTermP, map_add, map_mul, map_mul, map_pow, map_pow, PowerSeries.map_X,
      PowerSeries.map_C, PowerSeries.map_C, evm1_T_eq_sgn, evm1_T_eq_sgn]

/-- **support of `pentSeries`.** A nonzero coefficient of `q^a` forces `a` to be a generalized pentagonal
number: `∃ k : ℤ, k(3k−1) = 2a`. -/
lemma coeff_pentSeries_support {a : ℕ} (h : coeff a pentSeries ≠ 0) :
    ∃ k : ℤ, k * (3 * k - 1) = 2 * (a : ℤ) := by
  by_contra hcon
  push_neg at hcon
  apply h
  rw [pentSeries, PowerSeries.coeff_map, coeff_pentTheta (le_refl (a + 1)), ← PowerSeries.coeff_map,
      pentFiniteP, map_add, map_one, map_sum, map_add, map_sum]
  have ha0 : a ≠ 0 := by rintro rfl; exact hcon 0 (by norm_num)
  rw [PowerSeries.coeff_one, if_neg ha0, zero_add]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  rw [map_evm1_pentTermP, map_add, coeff_XpowC, coeff_XpowC,
      if_neg (fun he => hcon ((m : ℤ) + 1) (by rw [pent_double_pos, he])),
      if_neg (fun he => hcon (-((m : ℤ) + 1)) (by rw [pent_double_neg, he])), add_zero]

/-! ### value of `jacobiCubeSum`: a nonzero coefficient equals `±(2m+1)` at a triangular exponent -/

private lemma tri_injective : Function.Injective (fun m : ℕ => m * (m + 1) / 2) := by
  intro a b hab
  simp only at hab
  have ha := two_dvd_succ a
  have hb := two_dvd_succ b
  have he : a * (a + 1) = b * (b + 1) := by omega
  rcases lt_trichotomy a b with h | h | h
  · exfalso; nlinarith
  · exact h
  · exfalso; nlinarith

/-- **value of `jacobiCubeSum`.** A nonzero coefficient of `q^y` sits at a triangular number and equals
`(−1)ᵐ(2m+1)`: `∃ m, m(m+1) = 2y ∧ coeff y jacobiCubeSum = (−1)ᵐ(2m+1)`. -/
lemma coeff_jacobiCubeSum_value {y : ℕ} (h : coeff y jacobiCubeSum ≠ 0) :
    ∃ m : ℕ, (m : ℤ) * ((m : ℤ) + 1) = 2 * (y : ℤ)
      ∧ coeff y jacobiCubeSum = (-1 : ℤ) ^ m * (2 * (m : ℤ) + 1) := by
  have hsum : coeff y jacobiCubeSum
      = ∑ m ∈ Finset.range (y + 1), (if m * (m + 1) / 2 = y then (-1 : ℤ) ^ m * (2 * m + 1) else 0) := by
    rw [coeff_jacobiCubeSum (le_refl (y + 1))]
    exact Finset.sum_congr rfl (fun m _ => coeff_XpowC _ _ _)
  rw [hsum] at h
  obtain ⟨m₀, hmem, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have htri : m₀ * (m₀ + 1) / 2 = y := by by_contra hc; rw [if_neg hc] at hne; exact hne rfl
  have hnat : m₀ * (m₀ + 1) = 2 * y := by have := two_dvd_succ m₀; omega
  refine ⟨m₀, ?_, ?_⟩
  · rw [show (m₀ : ℤ) * ((m₀ : ℤ) + 1) = ((m₀ * (m₀ + 1) : ℕ) : ℤ) from by push_cast; ring, hnat]
    push_cast; ring
  · rw [hsum, Finset.sum_eq_single_of_mem m₀ hmem
        (fun b _ hb => if_neg (fun hby => hb
          (tri_injective (show b * (b + 1) / 2 = m₀ * (m₀ + 1) / 2 from by rw [hby, htri])))),
        if_pos htri]

/-! ### the vanishing of `(q;q)_∞⁴` coefficients at `≡ 4 (mod 5)` -/

private lemma Ψ5_qfac4_eq : Ψ5 (qfacInf ^ 4) = Ψ5 pentSeries * Ψ5 jacobiCubeSum := by
  rw [← map_mul, show qfacInf ^ 4 = qfacInf * qfacInf ^ 3 from by ring, jacobi_cube_identity,
      euler_pentagonal]

/-- **`(q;q)_∞⁴` vanishes mod 5 in every exponent `≡ 4 (mod 5)`.** -/
lemma coeff_qfac4_mod5 {a : ℕ} (ha : a % 5 = 4) : coeff a (Ψ5 (qfacInf ^ 4)) = 0 := by
  rw [Ψ5_qfac4_eq, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  obtain ⟨x, y⟩ := p
  have hxy : x + y = a := Finset.mem_antidiagonal.mp hp
  rw [Ψ5, PowerSeries.coeff_map, PowerSeries.coeff_map]
  -- if either factor's coefficient is 0, done; else invoke the heart
  by_cases hx : coeff x pentSeries = 0
  · rw [hx, map_zero, zero_mul]
  by_cases hy : coeff y jacobiCubeSum = 0
  · rw [hy, map_zero, mul_zero]
  obtain ⟨k, hk⟩ := coeff_pentSeries_support hx
  obtain ⟨m, hm, hmval⟩ := coeff_jacobiCubeSum_value hy
  -- exponent congruence: k(3k−1) + m(m+1) = 2(x+y) = 2a ≡ 3 (mod 5)
  have hexp : (k * (3 * k - 1) + (m : ℤ) * ((m : ℤ) + 1)) ≡ 3 [ZMOD 5] := by
    rw [hk, hm, show 2 * (x : ℤ) + 2 * (y : ℤ) = 2 * (a : ℤ) from by rw [← hxy]; push_cast; ring]
    have haa : ((a : ℤ)) % 5 = 4 := by omega
    unfold Int.ModEq; omega
  have hwt : (2 * (m : ℤ) + 1) ≡ 0 [ZMOD 5] :=
    RamanujanTau.PartitionCongruenceMod5.jacobi_weight_dvd_of_exponent hexp
  have hz : (Int.castRingHom (ZMod 5)) (2 * (m : ℤ) + 1) = 0 := by
    show ((2 * (m : ℤ) + 1 : ℤ) : ZMod 5) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.modEq_zero_iff_dvd.mp hwt
  rw [hmval, map_mul, hz, mul_zero, mul_zero]

end MockTheta5.JTP
