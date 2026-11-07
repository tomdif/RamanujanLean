import RamanujanTau.FiniteArithmetic.RankRMain
import RamanujanTau.FiniteArithmetic.Orbit
import RamanujanTau.FiniteArithmetic.SeedSurvival

/-!
# The order-`r` finite route with seed survival in place of invertibility

`RankR.Data2.bEll_eq` asks for a left inverse of the observed error operator `θ`
and a nonzero initial error. By `FiniteArithmetic.orbit_nonzero_iff`, the exact
condition is weaker: the orbit of the initial error survives forever iff
`θ^s e₀ ≠ 0`, where `s` is the dimension. `Data2.bEll_eq_of_survival` replaces the
two hypotheses `θi, hθi, hinit` by this one condition; everything else is the
original argument verbatim. A singular `θ` is therefore no obstruction as long as
the actual seed has a component in its invertible Fitting summand.
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.RankR
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal
open RankS (bounds B odd_mem even_U odd_D odd_succ Xop toZMod_prime_zmod L_env)

variable {ℓ s r : ℕ} [hℓ : Fact ℓ.Prime]
variable (D : Data2 ℓ s r) (h29 : 29 ≤ ℓ) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)

omit [Fact ℓ.Prime] in
lemma toLin'_pow {R : Type*} [CommRing R] (A : Matrix (Fin s) (Fin s) R) (n : ℕ) :
    Matrix.toLin' A ^ n = Matrix.toLin' (A ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.toLin'_one]; rfl
  | succ n ih => rw [pow_succ, ih, pow_succ, Matrix.toLin'_mul]; rfl

include h29 h24 in
/-- **`b_ℓ(m) = 2m − 1` from order-`r` data, assuming only seed survival `θ^s e₀ ≠ 0`.** -/
theorem Data2.bEll_eq_of_survival (hr : 0 < r) {k : Fin r → ZMod ℓ} (hcay : D.odd r = ∑ j, k j • D.odd j.val)
    (hcomp : (comp k).det ≠ 0) (hdet₀ : D.det 0 ≠ 0) (zL2 : Fin s → ℤ)
    (hL2 : ∀ a, ∃ t : ℤ_[ℓ], obs (D.w a) (Ll ℓ 2) = (ℓ : ℤ_[ℓ]) * ((zL2 a : ℤ_[ℓ]) + ℓ * t))
    (hsurv : ((Matrix.of D.θ) ^ s).mulVec (D.init k zL2) ≠ 0) (m : ℕ) (hm : 1 ≤ m) :
    BLBound.bEll ℓ m = 2 * m - 1 := by
  have hdet : ∀ n, D.det n ≠ 0 := fun n => by
    rw [D.det_eq hcay n]; exact mul_ne_zero hdet₀ (pow_ne_zero _ hcomp)
  obtain ⟨κ, hκ, h⟩ := odd_padicR h29 D.hlow h24 D.toData hcay hdet
  choose G hGm hG using h
  have hodd : ∀ n, Xop (Ll ℓ (2 * n + 1)) = Ll ℓ (2 * (n + 1) + 1) := fun n => (odd_succ n).symm
  -- `X Gₙ = ℓ Gₙ₊₁`
  have hX : ∀ n, Dlin ℓ (Ulin ℓ (G n)) = (ℓ : ℤ_[ℓ]) • G (n + 1) := by
    intro n
    have hh := congrArg Xop (hG n)
    rw [map_sub, map_sum, map_smul, hodd] at hh
    simp only [map_smul, hodd] at hh
    have hs := hG (n + 1)
    rw [show (ℓ : ℤ_[ℓ]) ^ (n + 1 + 1) = (ℓ : ℤ_[ℓ]) ^ (n + 1) * ℓ from pow_succ _ _, mul_smul,
      show 2 * (n + 1 + r) + 1 = 2 * (n + r + 1) + 1 by ring] at hs
    simp only [show ∀ j : Fin r, 2 * (n + 1 + j.val) + 1 = 2 * (n + j.val + 1) + 1 from
      fun j => by ring] at hs
    apply sub_eq_zero.mp
    apply cancel_pow (ℓ : ℤ_[ℓ]) PS_reg (n + 1)
    rw [smul_sub]
    change (ℓ : ℤ_[ℓ]) ^ (n + 1) • Xop (G n) - _ = 0
    rw [← hh, hs, sub_self]
  -- the initial observations
  have hinit' : ∀ a, PadicInt.toZMod (obs (D.w a) (Ulin ℓ (G 0))) = D.init k zL2 a := by
    intro a
    have hU := congrArg (Ulin ℓ) (hG 0)
    rw [map_sub, map_sum, map_smul, ← even_U] at hU
    simp only [map_smul, ← even_U, Nat.zero_add, zero_add, pow_one] at hU
    have hO := congrArg (obs (D.w a)) hU
    rw [map_sub, map_sum, map_smul, smul_eq_mul] at hO
    simp only [map_smul, smul_eq_mul] at hO
    choose x hx t ht using fun j => D.obs_even h29 h24 zL2 hL2 j a
    simp only [ht] at hO
    have hO' : obs (D.w a) (Ulin ℓ (G 0)) = (x r + ℓ * t r) - ∑ j, κ j * (x j.val + ℓ * t j.val) := by
      apply mul_left_cancel₀ (Data2.ell_ne (ℓ := ℓ))
      rw [← hO, mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hO', Data2.init]
    simp only [map_sub, map_mul, map_add, map_sum, toZMod_prime_zmod, zero_mul, add_zero, hx, hκ]
  set e : ℕ → Fin s → ZMod ℓ := fun n a => PadicInt.toZMod (obs (D.w a) (Ulin ℓ (G n))) with he
  have hstep : ∀ n, e (n + 1) = mv D.θ (e n) := fun n => by
    ext a
    exact D.divided_step h29 h24 a _ _ (D.U_mem h29 _ (hGm n)) (hX n)
  have hmv : ∀ v, mv D.θ v = (Matrix.of D.θ).mulVec v := fun v => by
    ext a; simp [mv, Matrix.mulVec, dotProduct]
  have hpow : ∀ n, e n = ((Matrix.of D.θ) ^ n).mulVec (e 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hstep, ih, hmv, Matrix.mulVec_mulVec, ← pow_succ']
  have he0 : e 0 = D.init k zL2 := funext hinit'
  have herr : ∀ n, e n ≠ 0 := by
    have hall := (FiniteArithmetic.orbit_nonzero_iff (Matrix.toLin' (Matrix.of D.θ))
      (D.init k zL2)).mpr (by
        rw [Module.finrank_fin_fun, toLin'_pow, Matrix.toLin'_apply]; exact hsurv)
    intro n
    rw [hpow n, he0, ← Matrix.toLin'_apply, ← toLin'_pow]
    exact hall n
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  refine BLBound.bEll_eq_of_not_mem (by omega) m hm fun K hK => ?_
  obtain ⟨a, ha⟩ : ∃ a, e K a ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact herr K (funext hc)
  set k' : ℕ → ℤ_[ℓ] := fun j => if h : j < q + 1 then κ ⟨j, h⟩ else 0
  have hrec : ∀ n, Ll ℓ (2 * n + 2 * q + 3) -
      ∑ j ∈ Finset.range (q + 1), k' j • Ll ℓ (2 * (n + j) + 1) = (ℓ : ℤ_[ℓ]) ^ (n + 1) • G n := by
    intro n
    rw [← hG n, show 2 * (n + (q + 1)) + 1 = 2 * n + 2 * q + 3 by ring,
      ← Fin.sum_univ_eq_sum_range (fun j => k' j • Ll ℓ (2 * (n + j) + 1))]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by simp only [k', dif_pos j.isLt]
  refine BLBound.not_mem_of_errorsR q k' G (fun i => PowerSeries.coeff (s + 1 + i.val)) (obs (D.w a))
    hrec (fun n => ?_) m K hK ?_ ha
  · -- `obs_a ∘ U` kills the odd series
    rw [obs_reduce, reduce_U, D.odd_reduction h24, D.U_comb, D.obsBar_comb]
    exact D.obs_U_low a _ fun t => lin_zero_odd h29 D.hlow h24 D.toData n _ (by simp)
  · -- separation
    rw [RingHom.map_det]
    have : (PadicInt.toZMod (p := ℓ)).mapMatrix
        (fun i j : Fin (q + 1) => PowerSeries.coeff (s + 1 + i.val) (Ll ℓ (2 * (K + j.val) + 1))) =
        D.oddM K := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Data.oddM]
      rw [← coeff_map, D.odd_reduction h24, show s + 1 + i.val = (high s i).val + 1 by
        simp [high]; ring, D.coeff_comb]
      rfl
    rw [this]
    exact hdet K

omit [Fact ℓ.Prime] in
/-- The old hypotheses imply the new one: a left inverse and a nonzero seed give survival. -/
lemma survival_of_left_inverse {R : Type*} [CommRing R] (θ θi : Fin s → Fin s → R)
    (hθi : ∀ a c, ∑ b, θi a b * θ b c = if a = c then 1 else 0) (v : Fin s → R) (hv : v ≠ 0) :
    ((Matrix.of θ) ^ s).mulVec v ≠ 0 := by
  apply FiniteArithmetic.matrix_seed_survives _ (Matrix.of θi) _ v hv
  ext a c
  simp [Matrix.mul_apply, hθi, Matrix.one_apply]

end RamanujanTau.FiniteArithmetic.RankR
