import RamanujanTau.BLBound.Main
import RamanujanTau.FiniteArithmetic.FormalSturm

/-! Clearing the Hasse denominator in a finite-precision Katz envelope.
This is the infinite-series comparison needed by finite reconstruction methods. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.FiniteArithmetic
open PowerSeries AtkinOBrien AtkinOBrienFinal

noncomputable section
variable {p : ℕ} [Fact p.Prime]

abbrev reducePow (m : ℕ) : PS p →+* PowerSeries (ZMod (p ^ m)) :=
  PowerSeries.map (PadicInt.toZModPow (p := p) m)

/-- The vanishing of all Katz digits beyond `N` at precision `p^m` makes
`E^N F` an actual homogeneous polynomial in E4 and E6 modulo `p^m`. -/
theorem envelope_clear_denominator (hp5 : 5 ≤ p) (m N : ℕ) (c : ℤ) (γ : ℕ → ℤ)
    (hγ : ∀ i, N < i → (m : ℤ) ≤ γ i - c)
    (F : PS p) (hF : Env p hp5 c γ F) :
    ∃ P : MvPolynomial (Fin 2) (ZMod (p ^ m)), ModP.Iso P (N * (p - 1)) ∧
      ModP.ev (ZMod (p ^ m)) P = reducePow m ((E p hp5) ^ N * F) := by
  obtain ⟨I₀, a₀, ha₀, hA₀, hab₀⟩ := hF m
  let I := max I₀ (N + 1)
  let a := trunc I₀ a₀
  have ha : ∀ i, a i ∈ Kpiece p hp5 i := trunc_mem hp5 ha₀
  have hA : Approx p hp5 m I a F := approx_trunc hp5 hA₀ (le_max_left _ _)
  let φ := PadicInt.toZModPow (p := p) m
  let ai := fun i => MvPolynomial.map φ (a i)
  let A := MvPolynomial.map φ (ModP.hasseA p hp5)
  let e := reducePow m (E p hp5)
  let v := reducePow m (Einv p hp5)
  have hzero : ∀ i, N < i → ai i = 0 := by
    intro i hi
    have hd : Dvd (p : ℤ_[p]) m (a i) := Dvd_mono (by have := hγ i hi; omega)
      (trunc_dvd i (hab₀ i))
    obtain ⟨z, hz⟩ := hd
    dsimp [ai]
    rw [hz, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_pow, map_natCast]
    have hmod : (p : ZMod (p ^ m)) ^ m = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [hmod, map_zero, zero_mul]
  have hFbar : reducePow m F = ∑ i ∈ Finset.range (N + 1), ModP.ev (ZMod (p ^ m)) (ai i) * v ^ i := by
    obtain ⟨g, hg⟩ := hA
    have heq : F = (∑ i ∈ Finset.range I, ModP.ev ℤ_[p] (a i) * Einv p hp5 ^ i) +
        (p : ℤ_[p]) ^ m • g := by rw [← hg]; abel
    have hmod : (p : ZMod (p ^ m)) ^ m = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [heq, map_add, map_sum, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C,
      map_pow, map_natCast, hmod, map_zero, zero_mul, add_zero]
    simp only [map_mul, map_pow, ModP.map_ev]
    rw [← Finset.sum_range_add_sum_Ico _ (le_max_right I₀ (N + 1))]
    have hz : ∑ i ∈ Finset.Ico (N + 1) I,
        ModP.ev (ZMod (p ^ m)) (ai i) * v ^ i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hzero i (by have := (Finset.mem_Ico.mp hi).1; omega), map_zero, zero_mul]
    change (∑ i ∈ Finset.range (N + 1), ModP.ev (ZMod (p ^ m)) (ai i) * v ^ i) + _ = _
    rw [hz, add_zero]
  have hai : ∀ i, ModP.Iso (ai i) (i * (p - 1)) := by
    intro i
    apply ModP.iso_map
    intro d hd
    have hmem := (mem_Kpiece hp5).mp (ha i) (MvPolynomial.mem_support_iff.mpr hd)
    rw [ModP.weight_wt]
    exact hmem.1
  have hAA : ModP.Iso A (p - 1) := ModP.iso_map φ (ModP.iso_hasseA hp5)
  have hAe : ModP.ev (ZMod (p ^ m)) A = e := by
    dsimp [A, e, reducePow]
    rw [← ModP.map_ev, ModP.ev_hasseA]
    rfl
  have hev : e * v = 1 := by
    dsimp [e, v]
    rw [← map_mul, E_mul_Einv, map_one]
  have hpow : ∀ i ≤ N, e ^ N * v ^ i = e ^ (N - i) := by
    intro i hi
    calc
      _ = e ^ (N - i) * (e ^ i * v ^ i) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
      _ = _ := by rw [← mul_pow, hev, one_pow, mul_one]
  refine ⟨∑ i ∈ Finset.range (N + 1), ai i * A ^ (N - i), ?_, ?_⟩
  · apply MvPolynomial.IsWeightedHomogeneous.sum
    intro i hi
    exact ModP.iso_of_eq ((hai i).mul (hAA.pow (N - i))) (by
      have hi' : i ≤ N := by simpa using hi
      simpa only [nsmul_eq_mul, Nat.cast_id, ← Nat.add_mul, Nat.add_sub_of_le hi'])
  · rw [map_sum, map_mul, map_pow, hFbar, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [map_mul, map_pow, hAe]
    have hi' : i ≤ N := by simpa using hi
    change _ = e ^ N * (ModP.ev (ZMod (p ^ m)) (ai i) * v ^ i)
    rw [mul_left_comm, hpow i hi']

/-- The two envelopes vanish beyond Katz index two modulo `p^2`. -/
theorem envelopes_ge_three (hp : 13 ≤ p) (i : ℕ) (hi : 3 ≤ i) :
    3 ≤ α p i ∧ 3 ≤ β p i := by
  have hp' : (13 : ℚ) ≤ p := by exact_mod_cast hp
  have hi' : (3 : ℚ) ≤ i := by exact_mod_cast hi
  have hpos : (0 : ℚ) < p + 1 := by linarith
  have h1 : (2 : ℚ) < ((p : ℚ) * i - 2 - s p) / (p + 1) := by
    rw [lt_div_iff₀ hpos]; unfold s; nlinarith
  have h2 : ((p : ℚ) * i - 2 - s p) / (p + 1) ≤ ((p : ℚ) * i - 2) / (p + 1) := by
    apply div_le_div_of_nonneg_right _ hpos.le; unfold s; linarith
  constructor
  · have : (2 : ℤ) < α p i := Int.lt_ceil.mpr (by push_cast; linarith)
    omega
  · have : (2 : ℤ) < β p i := Int.lt_ceil.mpr (by push_cast; linarith)
    omega

/-- Every positive odd partition iterate satisfies the beta envelope. -/
theorem odd_partition_envelope (h13 : 13 ≤ p) (h5 : 5 ≤ p) (n : ℕ) :
    Env p h5 1 (β p) (Ll p (2 * n + 1)) := by
  have hmem : Ll p (2 * n + 1) ∈ BLBound.B h5 1 := by
    induction n with
    | zero => simpa using BLBound.L_one_mem h13 h5
    | succ n ih =>
      rw [BLBound.odd_succ]
      exact BLBound.X_mem h13 h5 (by norm_num) ih
  exact hmem.2

/-- Every positive even partition iterate satisfies the alpha envelope. -/
theorem even_partition_envelope (h13 : 13 ≤ p) (h5 : 5 ≤ p) (n : ℕ) :
    Env p h5 1 (α p) (Ll p (2 * n + 2)) := by
  rw [BLBound.even_U]
  exact U_env h5 h13 (BLBound.bounds h13 h5).1 1 (by norm_num) _
    (odd_partition_envelope h13 h5 n)

/-- Every positive partition iterate, after clearing `E^2`, is a modular
form of weight `2(p-1)` modulo `p^2`. No finite truncation assumption occurs. -/
theorem partition_clear_denominator_two (h13 : 13 ≤ p) (h5 : 5 ≤ p)
    (b : ℕ) (hb : 1 ≤ b) :
    ∃ P : MvPolynomial (Fin 2) (ZMod (p ^ 2)), ModP.Iso P (2 * (p - 1)) ∧
      ModP.ev (ZMod (p ^ 2)) P = reducePow 2 ((E p h5) ^ 2 * Ll p b) := by
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · have he : b = 2 * ((b - 2) / 2) + 2 := by omega
    rw [he]
    exact envelope_clear_denominator h5 2 2 1 (α p)
      (fun i hi => by have := (envelopes_ge_three h13 i (by omega)).1; omega)
      _ (even_partition_envelope h13 h5 _)
  · have he : b = 2 * (b / 2) + 1 := by omega
    rw [he]
    exact envelope_clear_denominator h5 2 2 1 (β p)
      (fun i hi => by have := (envelopes_ge_three h13 i (by omega)).2; omega)
      _ (odd_partition_envelope h13 h5 _)

/-- A series with homogeneous numerator and a fixed unit denominator is
determined by the same coefficient prefix as its numerator. -/
theorem quotient_eq_of_coeff_prefix {R : Type*} [CommRing R]
    (h1728 : IsUnit (1728 : R)) {k : ℕ} {e f g : PowerSeries R} (he : IsUnit e)
    {P Q : MvPolynomial (Fin 2) R} (hP : ModP.Iso P k) (hQ : ModP.Iso Q k)
    (hPf : ModP.ev R P = e * f) (hQg : ModP.ev R Q = e * g)
    (hc : ∀ n ≤ k / 12, coeff n f = coeff n g) : f = g := by
  have hd : PowerSeries.X ^ (k / 12 + 1) ∣ f - g :=
    PowerSeries.X_pow_dvd_iff.mpr fun n hn => by rw [map_sub, hc n (by omega), sub_self]
  have hd' : PowerSeries.X ^ (k / 12 + 1) ∣ ModP.ev R P - ModP.ev R Q := by
    rw [hPf, hQg, ← mul_sub]
    exact Dvd.dvd.mul_left hd _
  have heq := ModP.ev_eq_of_coeff_prefix h1728 hP hQ (fun n hn => by
    have := PowerSeries.X_pow_dvd_iff.mp hd' n (by omega)
    simpa only [map_sub, sub_eq_zero] using this)
  exact he.mul_left_cancel (hPf.symm.trans (heq.trans hQg))

/-- Reconstruction of an actual partition iterate at precision two from
its first `floor(2(p-1)/12)+1` coefficients and a homogeneous numerator. -/
theorem partition_two_eq_of_coeff_prefix (h13 : 13 ≤ p) (h5 : 5 ≤ p)
    (h1728 : IsUnit (1728 : ZMod (p ^ 2))) (b : ℕ) (hb : 1 ≤ b)
    (g : PowerSeries (ZMod (p ^ 2)))
    (Q : MvPolynomial (Fin 2) (ZMod (p ^ 2))) (hQ : ModP.Iso Q (2 * (p - 1)))
    (hQg : ModP.ev (ZMod (p ^ 2)) Q = (reducePow 2 (E p h5)) ^ 2 * g)
    (hc : ∀ n ≤ 2 * (p - 1) / 12, coeff n (reducePow 2 (Ll p b)) = coeff n g) :
    reducePow 2 (Ll p b) = g := by
  obtain ⟨P, hP, hPf⟩ := partition_clear_denominator_two h13 h5 b hb
  have he : IsUnit (reducePow 2 (E p h5)) := isUnit_iff_exists_inv.mpr
    ⟨reducePow 2 (Einv p h5), by rw [← map_mul, E_mul_Einv, map_one]⟩
  apply quotient_eq_of_coeff_prefix h1728 (he.pow 2) hP hQ _ hQg hc
  simpa only [map_mul, map_pow] using hPf

end
end RamanujanTau.FiniteArithmetic
