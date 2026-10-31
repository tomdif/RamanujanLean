import RamanujanTau.ThetaLift.LamSeries
import RamanujanTau.TheoremA.LiftReduction

/-!
# Modularity of the lift, for `t ≠ 1`

The double sum is a modular object on `Γ₀(6t)` and is the series of the lift. So the lift is a modular form.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex
open UpperHalfPlane hiding I
open ModularForm CongruenceSubgroup Rademacher
open RamanujanTau.TheoremA.HalfIntegral RamanujanTau.TheoremA.SignLattice
open scoped Real ComplexConjugate MatrixGroups

noncomputable section

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma chi12_eq_chiZ (e : ℕ) : chi12 e = chiZ (e : ℤ) := by
  have h : ((e : ℤ) % 12) = ((e % 12 : ℕ) : ℤ) := by omega
  unfold chi12 chiZ
  rw [h]
  have hlt : e % 12 < 12 := Nat.mod_lt _ (by norm_num)
  generalize e % 12 = r at *
  interval_cases r <;> norm_num

/-- The coefficients of the lift are `bC`. -/
lemma coeff_lift (t : ℕ) (A : PowerSeries ℤ) (n : ℕ) :
    ((PowerSeries.map (Int.castRingHom ℂ) (liftSeries ℓ t A)).coeff n : ℂ) =
      bC (halfWt ℓ) t (jj ℓ) (fun m => A.coeff m) n := by
  rw [PowerSeries.coeff_map, coeff_liftSeries, map_sum]
  unfold bC
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold eT psi jN latIndex latI
  rw [chi12_eq_chiZ]
  simp only [eq_intCast]
  push_cast
  ring

/-- The arithmetic of `ℓ`, for `ℓ ≥ 5`. -/
structure ArithData (ℓ t : ℕ) where
  hj : jj ℓ < 24
  ht2 : ¬ 2 ∣ t
  ht3 : ¬ 3 ∣ t
  hNj : (24 : ℤ) ∣ (t : ℤ) * jj ℓ + 1
  hjw : jj ℓ + 1 = 2 * ((jj ℓ + 1) / 2)
  hk : kPrime ℓ = ((halfWt ℓ + (jj ℓ + 1) / 2 : ℕ) : ℤ)
  hlam : halfWt ℓ ≠ 0
  hneg : ∀ g, jN t (-g) = (-1) ^ halfWt ℓ * jN t g

/-- The arithmetic facts hold. -/
def arithData (h5 : 5 ≤ ℓ) {t : ℕ} (ht : 24 ∣ t + jj ℓ) : ArithData ℓ t := by
  have hp := hℓ.out
  have h2 : ¬ 2 ∣ ℓ := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h
    omega
  have h3 : ¬ 3 ∣ ℓ := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
    omega
  have hjlt : jj ℓ < 24 := Nat.mod_lt _ (by norm_num)
  have hj2 : ¬ 2 ∣ jj ℓ := by unfold jj; omega
  have hj3 : ¬ 3 ∣ jj ℓ := by unfold jj; omega
  have ht2 : ¬ 2 ∣ t := by omega
  have ht3 : ¬ 3 ∣ t := by omega
  refine ⟨hjlt, ht2, ht3, ?_, by omega, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := ht
    have hsq := sq_mod_24 hj2 hj3
    obtain ⟨v, hv⟩ : (24 : ℤ) ∣ ((jj ℓ : ℤ) ^ 2 - 1) := by
      have h : (((jj ℓ) ^ 2 : ℕ) : ℤ) % 24 = 1 := by exact_mod_cast hsq
      push_cast at h
      generalize (jj ℓ : ℤ) ^ 2 = s at h ⊢
      omega
    refine ⟨u * jj ℓ - v, ?_⟩
    have hu' : (t : ℤ) + jj ℓ = 24 * u := by exact_mod_cast hu
    linear_combination (jj ℓ : ℤ) * hu' - hv
  · unfold kPrime halfWt
    have hl : ℓ % 2 = 1 := by omega
    have hjo : jj ℓ % 2 = 1 := by unfold jj; omega
    congr 1
    omega
  · unfold halfWt
    omega
  · intro g
    have hodd : Odd t := Nat.odd_iff.mpr (by omega)
    have hm : jN t (-1) = (-1) ^ halfWt ℓ := by
      unfold jN
      rw [jacobiSym.at_neg_one hodd]
      have hmod4 : (t + ℓ) % 4 = 0 := by unfold jj at ht; omega
      unfold halfWt
      rcases (by omega : ℓ % 4 = 1 ∨ ℓ % 4 = 3) with h | h
      · have ht4 : t % 4 = 3 := by omega
        have hodd2 : Odd ((ℓ - 3) / 2) := Nat.odd_iff.mpr (by omega)
        rw [ZMod.χ₄_nat_three_mod_four ht4, hodd2.neg_one_pow]
        simp
      · have ht4 : t % 4 = 1 := by omega
        have heven : Even ((ℓ - 3) / 2) := Nat.even_iff.mpr (by omega)
        rw [ZMod.χ₄_nat_one_mod_four ht4, heven.neg_one_pow]
        simp
    have e : -g = -1 * g := by ring
    rw [e, jN_mul, hm]

/-- The bound on the coefficients of the coordinate. -/
lemma coord_bound {k' : ℤ} (G : CuspForm 𝒮ℒ k') {j : ℕ} (hj : j < 24) {A : ℕ → ℤ}
    (hA : ∀ m, cA G j m = ((A m : ℤ) : ℂ)) :
    ∃ (C : ℝ) (E : ℕ), ∀ m : ℕ, ‖((A m : ℤ) : ℂ)‖ ≤ C * ((m : ℝ) + 1) ^ E := by
  obtain ⟨C, hC0, hC⟩ := norm_cA_le G hj
  obtain ⟨E, hE⟩ := exists_nat_ge ((k' : ℝ) / 2 - j / 4)
  refine ⟨C + ‖((A 0 : ℤ) : ℂ)‖, E, fun m => ?_⟩
  have hn0 := norm_nonneg ((A 0 : ℤ) : ℂ)
  by_cases hm : m = 0
  · subst hm
    simp only [Nat.cast_zero, zero_add, one_pow, mul_one]
    linarith
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have h1 := hC m hm1
  rw [hA] at h1
  have h2 : (m : ℝ) ^ ((k' : ℝ) / 2 - j / 4) ≤ ((m : ℝ) + 1) ^ E := by
    calc _ ≤ (m : ℝ) ^ (E : ℝ) := Real.rpow_le_rpow_of_exponent_le hmR hE
      _ = (m : ℝ) ^ E := Real.rpow_natCast _ _
      _ ≤ _ := by gcongr; linarith
  have h3 : 0 ≤ ((m : ℝ) + 1) ^ E := by positivity
  calc _ ≤ C * (m : ℝ) ^ ((k' : ℝ) / 2 - j / 4) := h1
    _ ≤ C * ((m : ℝ) + 1) ^ E := by gcongr
    _ ≤ _ := by nlinarith

/-- The relation between `q` and its power. -/
lemma qN_eq (N : ℕ) (z : ℍ) :
    qN N (z : ℂ).re (z : ℂ).im = Function.Periodic.qParam (1 : ℝ) (z : ℂ) ^ N := by
  unfold qN
  rw [Complex.re_add_im, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **The series of the raised lift, as `fS`.** -/
lemma fS_eq {N : ℕ} (hN : 0 < N) (b : ℕ → ℂ) (z : ℍ) :
    fS (fun k => (PowerSeries.expand N hN.ne' (PowerSeries.mk b)).coeff k) z =
      ∑' n : ℕ, b n * qN N (z : ℂ).re (z : ℂ).im ^ n := by
  unfold fS qS
  have hinj : Function.Injective (fun n : ℕ => N * n) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left hN h
  have hsupp : Function.support (fun k : ℕ => (PowerSeries.expand N hN.ne' (PowerSeries.mk b)).coeff k *
      Function.Periodic.qParam (1 : ℝ) (z : ℂ) ^ k) ⊆ Set.range fun n : ℕ => N * n := by
    intro k hk
    by_contra hc
    apply hk
    have hnd : ¬ N ∣ k := fun ⟨n, hn⟩ => hc ⟨n, hn.symm⟩
    simp [PowerSeries.coeff_expand_of_not_dvd N hN.ne' _ hnd]
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun n => ?_
  rw [qN_eq, PowerSeries.coeff_expand_mul, PowerSeries.coeff_mk, ← pow_mul]

/-- **The lift is modular, once the double sum is covariant.** -/
theorem raised_of_covariant (h5 : 5 ≤ ℓ) {a : PowerSeries ℤ} (G : CuspForm 𝒮ℒ (kPrime ℓ))
    (hG : PowerSeries.map (Int.castRingHom ℂ) a = qExpansion (1 : ℝ) G) {t : ℕ}
    (hsf : Squarefree t) (ht : 24 ∣ t + jj ℓ) [NeZero t] [NeZero (6 * t)]
    (hcov : ∀ (γ : SL(2, ℤ)) {E : ℤ}, γ 1 0 = 6 * (t : ℤ) * E → ∀ {w : ℂ}, 0 < w.im →
      lamSum G (jj ℓ) (N := t) (jN t) (halfWt ℓ) (mob γ w).re (mob γ w).im =
        lin γ w ^ (2 * halfWt ℓ) * lamSum G (jj ℓ) (N := t) (jN t) (halfWt ℓ) w.re w.im) :
    ∃ g : ModularForm (Gamma0 (6 * t) : Subgroup (GL (Fin 2) ℝ)) ((2 * halfWt ℓ : ℕ) : ℤ),
      qExpansion 1 g = PowerSeries.expand t (NeZero.ne t)
        (PowerSeries.map (Int.castRingHom ℂ) (liftSeries ℓ t (coordOf ℓ a))) := by
  have hN : 0 < t := Nat.pos_of_ne_zero (NeZero.ne t)
  obtain ⟨hj, ht2, ht3, hNj, hjw, hk, hlam, hneg⟩ := arithData (ℓ := ℓ) h5 ht
  set j := jj ℓ with hjdef
  set lam := halfWt ℓ with hlamdef
  set w := (j + 1) / 2 with hwdef
  set A : ℕ → ℤ := fun m => (coordOf ℓ a).coeff m with hAdef
  have hA : ∀ m, cA G j m = ((A m : ℤ) : ℂ) := by
    intro m
    have h := qExp_hP G j hG
    unfold cA
    have e : coordOf ℓ a = a * MockTheta5.JTP.partitionGF ^ j := by
      simp [coordOf, hjdef]
    rw [h, PowerSeries.coeff_map]
    simp [hAdef, e]
  obtain ⟨C, E, hAb⟩ := coord_bound G hj hA
  obtain ⟨Cb, hCb0, hCb⟩ := sum_bound (A := A) hlam hAb t j
  set b : ℕ → ℂ := bC lam t j A with hb
  have hmap : PowerSeries.map (Int.castRingHom ℂ) (liftSeries ℓ t (coordOf ℓ a)) = PowerSeries.mk b := by
    ext n
    rw [PowerSeries.coeff_mk]
    exact coeff_lift t (coordOf ℓ a) n
  rw [hmap]
  set c : ℕ → ℂ := fun k => (PowerSeries.expand t (NeZero.ne t) (PowerSeries.mk b)).coeff k with hc
  have hcbd : ∀ k : ℕ, 1 ≤ k → ‖c k‖ ≤ Cb * (k : ℝ) ^ (lam + 2 * E) := by
    intro k hk
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    by_cases hd : t ∣ k
    · obtain ⟨n, rfl⟩ := hd
      have hn : 1 ≤ n := by
        by_contra h0
        have : n = 0 := by omega
        simp [this] at hk
      have h1 : c (t * n) = b n := by
        simp only [hc]
        rw [PowerSeries.coeff_expand_mul, PowerSeries.coeff_mk]
      rw [h1]
      have h2 : ‖b n‖ ≤ Cb * (n : ℝ) ^ (lam + 2 * E) := (norm_sum_le _ _).trans (hCb n hn)
      refine h2.trans ?_
      have hle : (n : ℝ) ≤ ((t * n : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_mul_of_pos_left n hN
      gcongr
    · have h1 : c k = 0 := by
        simp only [hc]
        exact PowerSeries.coeff_expand_of_not_dvd t (NeZero.ne t) _ hd
      rw [h1, norm_zero]
      positivity
  have hval : ∀ z : ℍ, lamSum G j (N := t) (jN t) lam (z : ℂ).re (z : ℂ).im =
      (chiZ (t : ℤ) : ℂ) * fS c z := by
    intro z
    rw [lamSum_eq G j (A := A) hlam hN hsf ht hA hAb _ z.2]
    congr 1
    exact (fS_eq hN b z).symm
  have hχ : ((chiZ (t : ℤ) : ℤ) : ℂ) ≠ 0 := by exact_mod_cast chiZ_ne_zero ht2 ht3
  have hinv : ∀ ε : SL(2, ℤ), ((6 * t : ℕ) : ℤ) ∣ ε 1 0 →
      fS c ∣[((2 * lam : ℕ) : ℤ)] ε = fS c := by
    rintro ε ⟨E', hE'⟩
    ext z
    rw [ModularForm.SL_slash_apply]
    have hE : ε 1 0 = 6 * (t : ℤ) * E' := by rw [hE']; push_cast; rfl
    have h := hcov ε hE z.2
    have hmob : mob ε (z : ℂ) = ((ε • z : ℍ) : ℂ) := mob_eq ε z
    rw [hmob, hval, hval] at h
    have hden : denom ε z = lin ε (z : ℂ) := by simp [denom, lin]
    rw [hden]
    have hj' : lin ε (z : ℂ) ≠ 0 := denom_ne_zero' ε z.2
    have h2 := mul_left_cancel₀ hχ (h.trans (by ring :
      lin ε (z : ℂ) ^ (2 * lam) * ((chiZ (t : ℤ) : ℂ) * fS c z) =
        (chiZ (t : ℤ) : ℂ) * (lin ε (z : ℂ) ^ (2 * lam) * fS c z)))
    rw [h2, zpow_neg, zpow_natCast]
    field_simp
  obtain ⟨g, hg⟩ := exists_form c (k := 2 * lam) (M := 6 * t) hcbd hinv
  refine ⟨g, ?_⟩
  rw [hg]
  ext k
  simp [hc]

/-- **`AADRaisedModularity` for `t ≠ 1`.** -/
theorem raised_of_ne_one (h5 : 5 ≤ ℓ) {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ) {t : ℕ}
    (hsf : Squarefree t) (ht : 24 ∣ t + jj ℓ) (ht1 : t ≠ 1) [NeZero t] [NeZero (6 * t)] :
    ∃ g : ModularForm (Gamma0 (6 * t) : Subgroup (GL (Fin 2) ℝ)) ((2 * halfWt ℓ : ℕ) : ℤ),
      qExpansion 1 g = PowerSeries.expand t (NeZero.ne t)
        (PowerSeries.map (Int.castRingHom ℂ) (liftSeries ℓ t (coordOf ℓ a))) := by
  obtain ⟨G, hG⟩ := ha
  have hN : 0 < t := Nat.pos_of_ne_zero (NeZero.ne t)
  obtain ⟨hj, ht2, ht3, hNj, hjw, hk, hlam, hneg⟩ := arithData (ℓ := ℓ) h5 ht
  have hψ0 : jN t 0 = 0 := by
    unfold jN
    have h0 : jacobiSym 0 t = 0 := jacobiSym.eq_zero_iff.mpr ⟨hN.ne', by simpa using ht1⟩
    simp [h0]
  refine raised_of_covariant h5 G hG hsf ht fun γ E hE w hw => ?_
  exact lamSum_covariant G (jj ℓ) hN (halfWt ℓ) hlam hj hNj ht2 ht3 ht hjw hk hψ0 hneg γ hE hw

end

end RamanujanTau.ThetaLift
