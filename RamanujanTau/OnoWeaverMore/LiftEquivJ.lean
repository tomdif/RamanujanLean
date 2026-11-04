import RamanujanTau.AtkinSporadic.LiftEquivariance

/-!
# Hecke equivariance of the explicit Shimura lift, for every prime `ℓ ≥ 13`

`AtkinSporadic.Equivariance.lift_heckeHalf` is stated for `ℓ < 24`, where `j = ℓ mod 24 = ℓ`.
Here the same formal identity is proved with the operator `T(Q²)` taken in the `N`-coordinate of
`η^{−j}`, `j = jj ℓ = ℓ mod 24` (`heckeHalf Q (jj ℓ)`), which is the coordinate of
`TheoremA.HalfIntegral.coordOf ℓ` for every `ℓ`:

  `S_t (T(Q²) A) = χ₁₂(Q) · T_Q (S_t A)`   (`lift_heckeHalfJ`).

The proof is the one of `AtkinSporadic.LiftEquivariance` with `ℓ` replaced by `jj ℓ` in the
index arithmetic; the parity `(−1/t) = (−1)^λ`, `λ = (ℓ−3)/2`, uses `ℓ ≡ jj ℓ (mod 4)`.
-/

set_option autoImplicit false

namespace RamanujanTau.OnoWeaverMore.EquivarianceJ
open PowerSeries RamanujanTau.TheoremA.HalfIntegral RamanujanTau.TheoremA.SignLattice
open RamanujanTau.AtkinSporadic RamanujanTau.AtkinSporadic.Equivariance

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-! ### The pointwise relation -/

section Pointwise

variable (h13 : 13 ≤ ℓ) {Q : ℕ} [hQ : Fact Q.Prime] (hQ5 : 5 ≤ Q)
  {t : ℕ} (hsf : Squarefree t) (ht : 24 ∣ t + jj ℓ)

include h13 hQ5 hsf ht in
/-- `χ₁₂(e)·(T(Q²)A)[te²] = χ₁₂(Q)·(c(Qe) + ψ(Q)[Q∤e]c(e) + Q^{2λ−1}[Q∣e]c(e/Q))`. -/
theorem pointwiseJ (A : PowerSeries ℤ) (e : ℕ) (he : e ≠ 0) :
    chi12 e * (heckeHalf Q (jj ℓ) (halfWt ℓ) (heckeSign Q (halfWt ℓ)) A).coeff (latIndex ℓ t e) =
      chi12 Q * ((chi12 (Q * e) * A.coeff (latIndex ℓ t (Q * e))) +
        psi t (halfWt ℓ) Q * (if Q ∣ e then 0 else chi12 e * A.coeff (latIndex ℓ t e)) +
        (Q : ℤ) ^ (2 * halfWt ℓ - 1) *
          (if Q ∣ e then chi12 (e / Q) * A.coeff (latIndex ℓ t (e / Q)) else 0)) := by
  obtain ⟨hQ2, hQ3⟩ := prime_ge_five hQ.out hQ5
  have hl2 : ¬ 2 ∣ ℓ := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ.out).mp h; omega
  have hcQ := chi12_sq hQ2 hQ3
  by_cases hbad : 2 ∣ e ∨ 3 ∣ e
  · -- every term vanishes
    have h0 : chi12 e = 0 := by
      rcases hbad with h | h
      · exact chi12_eq_zero_of_two h
      · exact chi12_eq_zero_of_three h
    have h1 : chi12 (Q * e) = 0 := by rw [chi12_mul, h0, mul_zero]
    have h2 : Q ∣ e → chi12 (e / Q) = 0 := by
      intro hd
      obtain ⟨k, hk⟩ := hd
      rw [hk, Nat.mul_div_cancel_left _ hQ.out.pos]
      have : chi12 Q * chi12 k = 0 := by rw [← chi12_mul, ← hk, h0]
      rcases mul_eq_zero.mp this with h | h
      · rcases chi12_ne_zero hQ2 hQ3 with h' | h' <;> rw [h'] at h <;> norm_num at h
      · exact h
    rw [h0, h1]
    split_ifs with hd
    · rw [h2 hd]; ring
    · ring
  simp only [not_or] at hbad
  obtain ⟨he2, he3⟩ := hbad
  set N := latIndex ℓ t e with hNdef
  have hN := latIndex_spec (ℓ := ℓ) ht he2 he3
  rw [← hNdef] at hN
  have hd := hshift_spec hQ2 hQ3 (jj ℓ)
  have hQ1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ.out.pos
  have hQe2 : ¬ 2 ∣ Q * e := fun h => (Nat.Prime.dvd_mul Nat.prime_two).mp h |>.elim hQ2 he2
  have hQe3 : ¬ 3 ∣ Q * e := fun h => (Nat.Prime.dvd_mul Nat.prime_three).mp h |>.elim hQ3 he3
  have hNQ := latIndex_spec (ℓ := ℓ) ht hQe2 hQe3
  -- first term
  have hle : hshift Q (jj ℓ) ≤ Q ^ 2 * N := by
    have : 24 * hshift Q (jj ℓ) ≤ 24 * (Q ^ 2 * N) := by
      rw [hd, show 24 * (Q ^ 2 * N) = Q ^ 2 * (24 * N) by ring, hN, Nat.sub_mul, one_mul]
      have : jj ℓ ≤ t * e ^ 2 + jj ℓ := by omega
      calc Q ^ 2 * jj ℓ - jj ℓ ≤ Q ^ 2 * jj ℓ := Nat.sub_le _ _
        _ ≤ Q ^ 2 * (t * e ^ 2 + jj ℓ) := Nat.mul_le_mul_left _ this
    omega
  have hidx1 : Q ^ 2 * N - hshift Q (jj ℓ) = latIndex ℓ t (Q * e) := by
    have : 24 * (Q ^ 2 * N - hshift Q (jj ℓ)) = 24 * latIndex ℓ t (Q * e) := by
      rw [hNQ, Nat.mul_sub, hd, show 24 * (Q ^ 2 * N) = Q ^ 2 * (24 * N) by ring, hN]
      rw [show (Q * e) ^ 2 = Q ^ 2 * e ^ 2 by ring, Nat.sub_mul, one_mul]
      have h1 : Q ^ 2 * (t * e ^ 2 + jj ℓ) = t * (Q ^ 2 * e ^ 2) + Q ^ 2 * jj ℓ := by ring
      have h2 : jj ℓ ≤ Q ^ 2 * jj ℓ := Nat.le_mul_of_pos_left _ (by omega)
      rw [h1]
      omega
    omega
  -- middle term
  have hleg : legendreSym Q (24 * (N : ℤ) - (jj ℓ : ℕ)) = legendreSym Q t * (if Q ∣ e then 0 else 1) := by
    have e1 : (24 * (N : ℤ) - (jj ℓ : ℕ)) = (t : ℤ) * (e : ℤ) ^ 2 := by
      have : ((24 * N : ℕ) : ℤ) = ((t * e ^ 2 + jj ℓ : ℕ) : ℤ) := by rw [hN]
      push_cast at this
      linarith
    rw [e1, legendreSym.mul]
    split_ifs with hQe
    · have : legendreSym Q ((e : ℤ) ^ 2) = 0 := by
        rw [legendreSym.eq_zero_iff]
        have : ((e : ℤ) : ZMod Q) = 0 := by
          rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff]; exact hQe
        push_cast at this ⊢
        rw [this]; ring
      rw [this]
    · rw [legendreSym.sq_one', mul_one]
      intro h0
      apply hQe
      rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff] at h0
      exact h0
  have ht4 : t % 4 = 1 ∨ t % 4 = 3 := by
    have : ¬ 2 ∣ t := by unfold jj at ht; omega
    omega
  have hpar : t % 4 = 1 ↔ Even (halfWt ℓ) := by
    unfold jj at ht
    unfold halfWt
    constructor
    · intro h
      have : ℓ % 4 = 3 := by omega
      exact Nat.even_iff.mpr (by omega)
    · intro h
      have := Nat.even_iff.mp h
      omega
  have hmid : heckeSign Q (halfWt ℓ) * legendreSym Q (24 * (N : ℤ) - (jj ℓ : ℕ)) *
      (Q : ℤ) ^ (halfWt ℓ - 1) = chi12 Q * psi t (halfWt ℓ) Q * (if Q ∣ e then 0 else 1) := by
    rw [hleg, heckeSign, legendre_twelve hQ5, psi]
    have hr := recip (Q := Q) (t := t) (lam := halfWt ℓ) hQ2 ht4 hpar
    calc chi12 Q * legendreSym Q ((-1) ^ halfWt ℓ) * (legendreSym Q t * (if Q ∣ e then 0 else 1)) *
          (Q : ℤ) ^ (halfWt ℓ - 1) =
        chi12 Q * (legendreSym Q ((-1) ^ halfWt ℓ) * legendreSym Q t) * (Q : ℤ) ^ (halfWt ℓ - 1) *
          (if Q ∣ e then 0 else 1) := by ring
      _ = _ := by rw [hr]; ring
  -- third term
  have hthird : Q ^ 2 ∣ N + hshift Q (jj ℓ) ↔ Q ∣ e := by
    have h24' : 24 * (N + hshift Q (jj ℓ)) = t * e ^ 2 + Q ^ 2 * jj ℓ := by
      rw [mul_add, hN, hd, Nat.sub_mul, one_mul]
      have h2 : jj ℓ ≤ Q ^ 2 * jj ℓ := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hcop : Nat.Coprime (Q ^ 2) 24 := by
      apply Nat.Coprime.pow_left
      rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num]
      apply Nat.Coprime.mul_right
      · exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hQ.out).mpr
          (fun h => hQ2 ((Nat.prime_dvd_prime_iff_eq hQ.out Nat.prime_two).mp h ▸ dvd_refl _)))
      · exact (Nat.Prime.coprime_iff_not_dvd hQ.out).mpr
          (fun h => hQ3 ((Nat.prime_dvd_prime_iff_eq hQ.out Nat.prime_three).mp h ▸ dvd_refl _))
    constructor
    · intro hdv
      have h1 : Q ^ 2 ∣ t * e ^ 2 := by
        have : Q ^ 2 ∣ 24 * (N + hshift Q (jj ℓ)) := hdv.mul_left 24
        rw [h24'] at this
        exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp (by rwa [add_comm] at this)
      by_contra hQe
      have hcop' : Nat.Coprime Q (e ^ 2) :=
        Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hQ.out).mpr hQe)
      have : Q * Q ∣ t := by
        rw [← pow_two]
        exact (Nat.Coprime.pow_left 2 hcop').dvd_of_dvd_mul_right h1
      have := hsf Q this
      exact hQ.out.one_lt.ne' (Nat.isUnit_iff.mp this)
    · rintro ⟨k, rfl⟩
      have : Q ^ 2 ∣ 24 * (N + hshift Q (jj ℓ)) := by
        rw [h24']
        exact dvd_add ⟨t * k ^ 2, by ring⟩ (dvd_mul_right _ _)
      exact hcop.dvd_of_dvd_mul_left this
  have hidx3 : Q ∣ e → (N + hshift Q (jj ℓ)) / Q ^ 2 = latIndex ℓ t (e / Q) := by
    rintro ⟨k, rfl⟩
    rw [Nat.mul_div_cancel_left _ hQ.out.pos]
    have hk2 : ¬ 2 ∣ k := fun h => he2 (h.mul_left Q)
    have hk3 : ¬ 3 ∣ k := fun h => he3 (h.mul_left Q)
    have hK := latIndex_spec (ℓ := ℓ) ht hk2 hk3
    have h24' : 24 * (N + hshift Q (jj ℓ)) = Q ^ 2 * (24 * latIndex ℓ t k) := by
      rw [mul_add, hN, hd, Nat.sub_mul, one_mul, hK]
      have h2 : jj ℓ ≤ Q ^ 2 * jj ℓ := Nat.le_mul_of_pos_left _ (by omega)
      have : t * (Q * k) ^ 2 = Q ^ 2 * (t * k ^ 2) := by ring
      rw [this]
      have : Q ^ 2 * (t * k ^ 2 + jj ℓ) = Q ^ 2 * (t * k ^ 2) + Q ^ 2 * jj ℓ := by ring
      omega
    have : N + hshift Q (jj ℓ) = Q ^ 2 * latIndex ℓ t k := by
      have : 24 * (N + hshift Q (jj ℓ)) = 24 * (Q ^ 2 * latIndex ℓ t k) := by rw [h24']; ring
      omega
    rw [this, Nat.mul_div_cancel_left _ (by positivity)]
  -- assemble
  rw [coeff_heckeHalf, if_pos hle, hidx1, hmid]
  simp only [Int.cast_id]
  have hce : chi12 e = chi12 Q * chi12 (Q * e) := by
    rw [chi12_mul, ← mul_assoc, hcQ, one_mul]
  by_cases hQe : Q ∣ e
  · have hc3 : chi12 e = chi12 Q * chi12 (e / Q) := by
      rw [← chi12_mul, Nat.mul_div_cancel' hQe]
    rw [if_pos (hthird.mpr hQe), hidx3 hQe]
    simp only [if_pos hQe, mul_zero, zero_mul, add_zero]
    linear_combination A.coeff (latIndex ℓ t (Q * e)) * hce +
      (Q : ℤ) ^ (2 * halfWt ℓ - 1) * A.coeff (latIndex ℓ t (e / Q)) * hc3
  · rw [if_neg (mt hthird.mp hQe)]
    simp only [if_neg hQe, mul_zero, mul_one, add_zero]
    linear_combination A.coeff (latIndex ℓ t (Q * e)) * hce

include h13 hQ5 hsf ht in
/-- **Hecke equivariance of the lift**: `S_t(T(Q²)A) = χ₁₂(Q) · T_Q(S_t A)`. -/
theorem lift_heckeHalfJ (A : PowerSeries ℤ) :
    liftSeries ℓ t (heckeHalf Q (jj ℓ) (halfWt ℓ) (heckeSign Q (halfWt ℓ)) A) =
      chi12 Q • HeckeQExp.Tq Q ((Q : ℤ) ^ (2 * halfWt ℓ - 1)) (liftSeries ℓ t A) := by
  ext n
  rw [coeff_liftSeries, map_zsmul, HeckeQExp.coeff_Tq, coeff_liftSeries, smul_eq_mul]
  have hc := conv_hecke hQ.out (psi t (halfWt ℓ)) (fun a b => psi_mul t _ a b)
    (fun e => chi12 e * A.coeff (latIndex ℓ t e))
    (fun e => chi12 (Q * e) * A.coeff (latIndex ℓ t (Q * e)) +
        psi t (halfWt ℓ) Q * (if Q ∣ e then 0 else chi12 e * A.coeff (latIndex ℓ t e)) +
        (Q : ℤ) ^ (2 * halfWt ℓ - 1) *
          (if Q ∣ e then chi12 (e / Q) * A.coeff (latIndex ℓ t (e / Q)) else 0))
    ((Q : ℤ) ^ (2 * halfWt ℓ - 1)) (fun e _ => rfl) n
  have e1 : ∑ x ∈ n.divisorsAntidiagonal, psi t (halfWt ℓ) x.1 *
      (chi12 x.2 * (heckeHalf Q (jj ℓ) (halfWt ℓ) (heckeSign Q (halfWt ℓ)) A).coeff (latIndex ℓ t x.2)) =
      chi12 Q * ∑ x ∈ n.divisorsAntidiagonal, psi t (halfWt ℓ) x.1 *
        (chi12 (Q * x.2) * A.coeff (latIndex ℓ t (Q * x.2)) +
        psi t (halfWt ℓ) Q * (if Q ∣ x.2 then 0 else chi12 x.2 * A.coeff (latIndex ℓ t x.2)) +
        (Q : ℤ) ^ (2 * halfWt ℓ - 1) *
          (if Q ∣ x.2 then chi12 (x.2 / Q) * A.coeff (latIndex ℓ t (x.2 / Q)) else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx2 : x.2 ≠ 0 := fun h0 => (Nat.mem_divisorsAntidiagonal.mp hx).2 (by rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1, h0, mul_zero])
    rw [pointwiseJ h13 hQ5 hsf ht A x.2 hx2]
    ring
  rw [e1, hc]
  congr 1
  congr 1
  split_ifs
  · rw [coeff_liftSeries]
  · rfl

end Pointwise

end RamanujanTau.OnoWeaverMore.EquivarianceJ
