import RamanujanTau.TheoremA.ModularWeightEightAction
import RamanujanTau.TheoremA.BinaryOrdinarity

/-!
# The `U_p`-kernel in weight `p - 5`

The analogue of `U_ne_zero_of_binary_sign_eigenvalues` one weight down. A nonzero series represented in weight `p-5`, with the prescribed
bad-prime eigenvalues and killed by `U_p`, reaches weight eight after `θ⁶`, with eigenvalues `8, 27`. Unlike weight six, this eigensystem
occurs: it is the newform `h₈ = q + 8q² + 27q³ + ⋯` (`6.8.a.a`). So the kernel forces `p ∣ a_p(h₈)`.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open Matrix

private lemma not_dvd_between' {p r : ℤ} (hr : 0 < r) (hrp : r < p) : ¬ p ∣ r := by
  intro h
  have := Int.le_of_dvd hr h
  omega

/-- The weight `p - 5` case of Lemma T. -/
theorem theta_cycle_weight_eight (p : ℕ) (hp : 13 ≤ p) (w d : ℕ → ℤ)
    (hw : ∀ i ≤ p - 1, 0 ≤ w i)
    (hd : ∀ i < p - 1, 0 ≤ d i)
    (hstep : ∀ i < p - 1,
      w (i + 1) = w i + p + 1 - d i * (p - 1 : ℤ))
    (hdrop : ∀ i < p - 1, ¬ (p : ℤ) ∣ w i → d i = 0)
    (hstart : w 0 = (p : ℤ) - 5) (hclose : w (p - 1) = w 0) : w 6 = 8 := by
  have hpz : (13 : ℤ) ≤ p := by exact_mod_cast hp
  have rise : ∀ i < 5, w i = (i + 1) * (p : ℤ) - (5 - i) := by
    intro i
    induction i with
    | zero => intro _; simp [hstart]
    | succ i ih =>
      intro hi
      have hwi := ih (by omega)
      have hdi : d i = 0 := hdrop i (by omega) (by
        rw [hwi]
        intro h
        have hr : (p : ℤ) ∣ 5 - i := by
          have := dvd_sub (dvd_mul_left (p : ℤ) ((i : ℤ) + 1)) h
          convert this using 1
          ring
        exact not_dvd_between' (by omega) (by omega) hr)
      have hs := hstep i (by omega)
      rw [hdi, zero_mul, sub_zero, hwi] at hs
      rw [hs]
      push_cast
      ring
  have h4 := rise 4 (by omega)
  have hd4 : d 4 = 0 := hdrop 4 (by omega) (by
    rw [h4]
    intro h
    have hr : (p : ℤ) ∣ 1 := by
      have := dvd_sub (dvd_mul_left (p : ℤ) 5) h
      convert this using 1
      norm_num
    exact not_dvd_between' (by norm_num) (by omega) hr)
  have h5 : w 5 = 6 * (p : ℤ) := by
    have := hstep 4 (by omega)
    rw [hd4, zero_mul, sub_zero, h4] at this
    rw [this]
    push_cast
    ring
  have h6 : w 6 = 7 * (p : ℤ) + 1 - d 5 * (p - 1 : ℤ) := by
    have := hstep 5 (by omega)
    rw [h5] at this
    rw [this]
    ring
  have ds0 : 0 ≤ d 5 := hd 5 (by omega)
  have ds7 : d 5 ≤ 7 := by
    have := hw 6 (by omega)
    rw [h6] at this
    by_contra hn
    have : 8 ≤ d 5 := by omega
    nlinarith
  have ds : d 5 = 7 := by
    by_contra hn
    have ds6 : d 5 ≤ 6 := by omega
    have run : ∀ n ≤ p - 7, w (6 + n) = w 6 + n * ((p : ℤ) + 1) := by
      intro n hn
      induction n with
      | zero => simp
      | succ n ih =>
        have hn' : n ≤ p - 7 := by omega
        have hi : 6 + n < p - 1 := by omega
        have hdn : d (6 + n) = 0 := hdrop _ hi (by
          rw [ih hn', h6]
          intro h
          have hrem : (p : ℤ) ∣ d 5 + 1 + n := by
            have hmultiple : (p : ℤ) ∣ (7 - d 5 + n) * p := dvd_mul_left _ _
            have := dvd_sub h hmultiple
            convert this using 1
            ring
          exact not_dvd_between' (by positivity) (by omega) hrem)
        have hs := hstep (6 + n) hi
        rw [hdn, zero_mul, sub_zero, ih hn'] at hs
        push_cast
        rw [show 6 + (n + 1) = 6 + n + 1 by ring, hs]
        ring
    have hend := run (p - 7) (by omega)
    have heq : 6 + (p - 7) = p - 1 := by omega
    rw [heq, hclose, hstart, h6] at hend
    have hc : ((p - 7 : ℕ) : ℤ) = (p : ℤ) - 7 := by omega
    rw [hc] at hend
    nlinarith
  rw [h6, ds]
  ring

section Cycle
variable {p : ℕ} [hp : Fact p.Prime] {F : Type*} [Field F] [CharP F p]

/-- The sixth theta iterate reaches weight eight. -/
theorem binaryCycle_weight_eight (hp13 : 13 ≤ p) (f : PowerSeries F)
    (hf : BinaryRep f ((p - 5) / 2)) (hf0 : f ≠ 0) (hu : BoylanWebb.U p f = 0) :
    binaryCycleHalfWeight p ((p - 5) / 2) f 6 = 4 := by
  have hp5 : 5 ≤ p := by omega
  have hperiod := hasse_degree_even hp5
  have hodd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr (by omega)
  have hstartDegree : 2 * ((p - 5) / 2) = p - 5 := by omega
  have hstartLt : (p - 5) / 2 < (p - 1) / 2 := by omega
  choose d hd using binaryCycleHalfWeight_step hp5 hf
  have hw8 := theta_cycle_weight_eight p hp13
    (fun i => (2 * binaryCycleHalfWeight p ((p - 5) / 2) f i : ℕ))
    (fun i => (d i : ℤ))
    (fun _ _ => by positivity) (fun _ _ => by positivity)
    (fun i _ => by
      have h := hd i
      have hz : (binaryCycleHalfWeight p ((p - 5) / 2) f i : ℤ) + ((p - 1) / 2 : ℕ) + 1 =
          (binaryCycleHalfWeight p ((p - 5) / 2) f (i + 1) : ℤ) + ((p - 1) / 2 : ℕ) * d i := by
        exact_mod_cast h
      have hpz : (2 : ℤ) * ((p - 1) / 2 : ℕ) = (p : ℤ) - 1 := by
        calc
          _ = ((2 * ((p - 1) / 2) : ℕ) : ℤ) := by push_cast; rfl
          _ = ((p - 1 : ℕ) : ℤ) := by rw [hperiod]
          _ = _ := by rw [Nat.cast_sub (by omega), Nat.cast_one]
      push_cast
      nlinarith)
    (fun i hi hnd => by
      have he := binaryCycleHalfWeight_no_drop hp5 hf i
        (theta_pow_ne_zero_of_closed_cycle f hf0 hu (by omega)) hnd
      have h := hd i
      rw [he] at h
      have hz : d i = 0 := by nlinarith
      simp [hz])
    (by
      dsimp only
      rw [binaryCycleHalfWeight_zero hf hstartLt, hstartDegree,
        Nat.cast_sub (by omega), Nat.cast_ofNat])
    (by dsimp only; rw [binaryCycleHalfWeight_closed hp5 _ f hu])
  dsimp only at hw8
  omega

/-- A nonzero weight-(p−5) series killed by `U_p` has a weight-eight representative after `θ⁶`. -/
theorem theta_six_binaryRep (hp13 : 13 ≤ p) (f : PowerSeries F)
    (hf : BinaryRep f ((p - 5) / 2)) (hf0 : f ≠ 0) (hu : BoylanWebb.U p f = 0) :
    BinaryRep ((theta ^ 6) f) 4 := by
  have h := binaryCycleHalfWeight_rep (by omega : 5 ≤ p) hf 6
  rwa [binaryCycle_weight_eight hp13 f hf hf0 hu] at h

/-- For `q = 2, 3`, the eigenvalues after `θ⁶` are `8, 27`. -/
theorem theta_six_eigenvalue (hp13 : 13 ≤ p) (q : ℕ) :
    (q : F) ^ 6 * ((legendreSym p (q : ℤ) : F) * (q : F) ^ ((p - 7) / 2)) = (q : F) ^ 3 := by
  have he : (legendreSym p (q : ℤ) : F) = (q : F) ^ (p / 2) := by
    have h := congrArg (ZMod.castHom (dvd_refl p) F) (legendreSym.eq_pow p (q : ℤ))
    simpa only [map_intCast, map_pow, Int.cast_natCast, map_natCast] using h
  have hpodd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr (by omega)
  have hexp : 6 + (p / 2 + (p - 7) / 2) = p + 2 := by omega
  have hfermat : (q : F) ^ p = q := by
    have h := congrArg (ZMod.castHom (dvd_refl p) F) (ZMod.pow_card (q : ZMod p))
    simpa only [map_pow, map_natCast] using h
  rw [he, ← pow_add, ← pow_add, hexp, pow_add, hfermat]
  ring

end Cycle

/-- The newform `h₈ = q + 8q² + 27q³ + ⋯` in the integral model. -/
noncomputable def hEight : PowerSeries ℤ := evenCombination 4 modularWeightEightH

def fullWeightEightPolynomial {S : Type*} [Ring S] (A B : S) : S :=
  (A - 1) * (A - 128) * (A + 8) * (B + 27)

theorem fullWeightEightPolynomial_intertwines {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (E : V →ₗ[R] W) (A B : Module.End R W) (a b : Module.End R V)
    (hA : ∀ v, A (E v) = E (a v)) (hB : ∀ v, B (E v) = E (b v)) (v : V) :
    fullWeightEightPolynomial A B (E v) = E (fullWeightEightPolynomial a b v) := by
  simp only [fullWeightEightPolynomial, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.add_apply, Module.End.one_apply, Module.End.ofNat_apply,
    map_sub, map_add, map_nsmul, hA, hB]

/-- On weight eight, the polynomial has rank one, with image the line of `h₈`. -/
theorem weightEight_rank_one {R : Type*} [CommRing R] (c : Fin 9 → R) :
    fullWeightEightPolynomial (uOperator 2) (uOperator 3) (evenCombination 4 c) =
      (∑ i, (modularWeightEightV i : R) * c i) •
        evenCombination 4 (fun i => ((modularWeightEightH i : ℤ) : R)) := by
  let A := (Int.castRingHom R).mapMatrix modularWeightEightU2
  let B := (Int.castRingHom R).mapMatrix modularWeightEightU3
  have hM : fullWeightEightPolynomial A B = Matrix.vecMulVec (fun i => ((modularWeightEightH i : ℤ) : R))
      (fun i => ((modularWeightEightV i : ℤ) : R)) := by
    have h := congrArg ((Int.castRingHom R).mapMatrix) modularWeightEight_matrix_identity
    simp only [map_mul, map_sub, map_one, map_ofNat, map_add] at h
    rw [show fullWeightEightPolynomial A B = _ from h]
    ext i j
    simp [Matrix.vecMulVec_apply]
  let a : Module.End R (Fin 9 → R) := Matrix.toLinAlgEquiv' A
  let b : Module.End R (Fin 9 → R) := Matrix.toLinAlgEquiv' B
  have hL : fullWeightEightPolynomial a b = Matrix.toLinAlgEquiv' (fullWeightEightPolynomial A B) := by
    simp only [fullWeightEightPolynomial, a, b, map_mul, map_sub, map_one, map_ofNat, map_add]
  have h := fullWeightEightPolynomial_intertwines (evenCombinationLinear (R := R) 4)
    (uOperator 2) (uOperator 3) a b
    (fun v => modularWeightEight_U2_action v) (fun v => modularWeightEight_U3_action v) c
  rw [hL, hM] at h
  change _ = evenCombination 4 _ at h
  refine h.trans ?_
  have hv : (Matrix.toLinAlgEquiv' (Matrix.vecMulVec (fun i => ((modularWeightEightH i : ℤ) : R))
      (fun i => ((modularWeightEightV i : ℤ) : R)))) c =
      (∑ i, (modularWeightEightV i : R) * c i) • fun i => ((modularWeightEightH i : ℤ) : R) := by
    ext i
    simp only [Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hv]
  exact map_smul (evenCombinationLinear (R := R) 4) _ _

theorem fullWeightEightPolynomial_on_eigenvector {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] (A B : Module.End F V) (v : V)
    (hA : A v = (8 : F) • v) (hB : B v = (27 : F) • v) :
    fullWeightEightPolynomial A B v = (-725760 : F) • v := by
  simp only [fullWeightEightPolynomial, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.add_apply, Module.End.one_apply, Module.End.ofNat_apply,
    map_sub, map_add, map_nsmul, map_smul, hA, hB]
  module

theorem fullWeightEight_scalar_ne_zero {F : Type*} [Field F] {p : ℕ} [CharP F p]
    (hp13 : 13 ≤ p) : (-725760 : F) ≠ 0 := by
  have h2 : (2 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two (by omega : p ≠ 2)
  have h3 : (3 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_three (by omega : p ≠ 3)
  have h5 : (5 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F (by decide : Nat.Prime 5) (by omega : p ≠ 5)
  have h7 : (7 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F (by decide : Nat.Prime 7) (by omega : p ≠ 7)
  have he : (-725760 : F) = -(2 ^ 8 * 3 ^ 4 * 5 * 7) := by ring
  rw [he]
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)) h5) h7)

/-- The joint eigenspace for `(8, 27)` in weight eight is the line of `h₈`. -/
theorem binary_weightEight_eigenline {F : Type*} [Field F] {p : ℕ} [CharP F p] (hp13 : 13 ≤ p)
    (f : PowerSeries F) (hf : BinaryRep f 4)
    (h2 : uOperator 2 f = (8 : F) • f) (h3 : uOperator 3 f = (27 : F) • f) :
    ∃ c : F, f = c • PowerSeries.map (Int.castRingHom F) hEight := by
  have key : ∀ c' : Fin 9 → F, uOperator 2 (evenCombination 4 c') = (8 : F) • evenCombination 4 c' →
      uOperator 3 (evenCombination 4 c') = (27 : F) • evenCombination 4 c' →
      ∃ c : F, evenCombination 4 c' = c • PowerSeries.map (Int.castRingHom F) hEight := by
    intro c' h2 h3
    have h := fullWeightEightPolynomial_on_eigenvector (F := F) (uOperator 2 : Module.End F (PowerSeries F))
      (uOperator 3 : Module.End F (PowerSeries F)) (evenCombination 4 c') h2 h3
    rw [weightEight_rank_one] at h
    have hne := fullWeightEight_scalar_ne_zero (F := F) hp13
    have hmap : evenCombination 4 (fun i => ((modularWeightEightH i : ℤ) : F)) =
        PowerSeries.map (Int.castRingHom F) hEight := by
      rw [hEight, evenCombination_map]
      rfl
    refine ⟨(-725760 : F)⁻¹ * ∑ i, (modularWeightEightV i : F) * c' i, ?_⟩
    rw [← hmap, mul_smul, h, smul_smul, inv_mul_cancel₀ hne, one_smul]
  obtain ⟨P, hP, rfl⟩ := hf
  rw [homogeneous_eq_binaryPolynomial 4 P hP, binaryEv_binaryPolynomial] at h2 h3 ⊢
  exact key _ h2 h3

/-- **The `U_p`-kernel in weight `p - 5`.** A nonzero series in weight `p-5` with the prescribed bad-prime eigenvalues and killed by `U_p`
forces `p ∣ a_p(h₈)`. So weight `p-5` of this sign class is ordinary, unless `h₈` is not. -/
theorem dvd_coeff_hEight_of_binary_kernel (p : ℕ) [hp : Fact p.Prime] (hp13 : 13 ≤ p)
    {F : Type*} [Field F] [CharP F p] (f : PowerSeries F)
    (hf : BinaryRep f ((p - 5) / 2)) (hf0 : f ≠ 0)
    (hU2 : BoylanWebb.U 2 f = ((legendreSym p 2 : F) * (2 : F) ^ ((p - 7) / 2)) • f)
    (hU3 : BoylanWebb.U 3 f = ((legendreSym p 3 : F) * (3 : F) ^ ((p - 7) / 2)) • f)
    (hu : BoylanWebb.U p f = 0) :
    (p : ℤ) ∣ hEight.coeff p := by
  have h8 := theta_six_binaryRep hp13 f hf hf0 hu
  have h2 : uOperator 2 ((theta ^ 6) f) = (8 : F) • ((theta ^ 6) f) := by
    rw [uOperator_apply, U_theta_pow, hU2, map_smul, smul_smul]
    have h := theta_six_eigenvalue (p := p) (F := F) hp13 2
    norm_num at h ⊢
    rw [h]
  have h3 : uOperator 3 ((theta ^ 6) f) = (27 : F) • ((theta ^ 6) f) := by
    rw [uOperator_apply, U_theta_pow, hU3, map_smul, smul_smul]
    have h := theta_six_eigenvalue (p := p) (F := F) hp13 3
    norm_num at h ⊢
    rw [h]
  obtain ⟨c, hc⟩ := binary_weightEight_eigenline hp13 _ h8 h2 h3
  have hne : (theta ^ 6) f ≠ 0 := theta_pow_ne_zero_of_closed_cycle f hf0 hu (by omega : 6 ≤ p - 1)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by rw [hc, zero_smul])
  have hU : BoylanWebb.U p ((theta ^ 6) f) = 0 := by
    rw [U_theta_pow, hu, map_zero, smul_zero]
  rw [hc] at hU
  have h1 := congrArg (PowerSeries.coeff 1) hU
  rw [BoylanWebb.coeff_U, mul_one, map_smul, smul_eq_mul, PowerSeries.coeff_map, map_zero] at h1
  have h4 := (mul_eq_zero.mp h1).resolve_left hc0
  simpa using (CharP.intCast_eq_zero_iff F p _).mp h4

end RamanujanTau.TheoremA
