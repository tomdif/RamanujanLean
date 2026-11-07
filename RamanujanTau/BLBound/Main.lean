import RamanujanTau.BLBound.Vbar
import RamanujanTau.AtkinOBrienFinal.Main
import RamanujanTau.OrdQuot.Prod
import RamanujanTau.QuotE.Combine

/-!
# The Boylan–Webb bound for every prime

For every prime `ℓ ≥ 13` there is a monic `χ ∈ ℤ[x]` with `χ(0)` prime to `ℓ` such that
`χ(X)^m L(2m-1) ≡ 0 (mod ℓ^m)`. Theorem A gives `χ(0)` prime to `ℓ`, and Lemma 2 keeps the reduction inside
`V̄` at each step.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BLBound
open PowerSeries AtkinOBrien AtkinOBrienFinal BoylanWebb
open RamanujanTau.TheoremA.HalfIntegral

noncomputable section

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- (UB) and (DB) for every prime `ℓ ≥ 13`. -/
theorem bounds (h13 : 13 ≤ ℓ) (h5 : 5 ≤ ℓ) : UB ℓ h5 ∧ DB ℓ h5 := by
  classical
  have hE := QuotE.quotEBound_C_of_ord (ℓ := ℓ) h5 (OrdQuot.ordEBound_C' h5)
  have hU := UBSharp.UB_of_E_C h5 hE
  have hQ := SharpHQ.HQ_of_conj_C h5 (by omega)
    (UBSharp.HConj_of_quot_C h5 (UBSharp.quotBound_of_E_C h5 hE))
  exact ⟨hU, VLayer.DB_of_UB_HQ h5 hU hQ⟩

/-- `X = D ∘ U` on `ℤ_ℓ⟦q⟧`. -/
def Xop (ℓ : ℕ) [Fact ℓ.Prime] : Module.End ℤ_[ℓ] (PS ℓ) := (Dlin ℓ).comp (Ulin ℓ)

/-- Reduction modulo `ℓ`. -/
abbrev red (ℓ : ℕ) [Fact ℓ.Prime] : PS ℓ →+* PowerSeries (ZMod ℓ) :=
  PowerSeries.map (PadicInt.toZMod (p := ℓ))

lemma red_Φ : red ℓ (Φl ℓ) = Ψ ℓ (Φ ℓ) := map_map_int _

lemma red_D (f : PS ℓ) : red ℓ (Dlin ℓ f) = U ℓ (Ψ ℓ (Φ ℓ) * red ℓ f) := by
  rw [Dlin_apply, map_U, map_mul, red_Φ]

lemma red_X (f : PS ℓ) : red ℓ (Xop ℓ f) = Xbar ℓ (red ℓ f) := by
  change red ℓ (Dlin ℓ (Ulin ℓ f)) = _
  rw [red_D, Ulin_apply, map_U]
  rfl

lemma red_pow_X (n : ℕ) (f : PS ℓ) : red ℓ ((Xop ℓ ^ n) f) = (Xbar ℓ ^ n) (red ℓ f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, red_X]

lemma red_aeval (p : Polynomial ℤ) (f : PS ℓ) :
    red ℓ (Polynomial.aeval (Xop ℓ) p f) =
      Polynomial.aeval (Xbar ℓ) (p.map (Int.castRingHom (ZMod ℓ))) (red ℓ f) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.map_add, LinearMap.add_apply, hp, hq]
  | monomial n c =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_zsmul, red_pow_X, eq_intCast]
    exact (Int.cast_smul_eq_zsmul (ZMod ℓ) c _).symm

/-- **An element of a first envelope reduces to a form of weight `ℓ - 1`.** -/
theorem env_formBar (h5 : 5 ≤ ℓ) (γ : ℕ → ℤ) (hγ : ∀ i, 2 ≤ i → 2 ≤ γ i) (F : PS ℓ)
    (hFe : Env ℓ h5 1 γ F) : FormBar ℓ (ℓ - 1) (red ℓ F) := by
  obtain ⟨I₀, a₀, haK₀, hA₀, hab₀⟩ := hFe 1
  set I := max I₀ 2 with hI
  set a := trunc I₀ a₀ with ha
  have haK : ∀ i, a i ∈ Kpiece ℓ h5 i := trunc_mem h5 haK₀
  have hA : Approx ℓ h5 1 I a F := approx_trunc h5 hA₀ (le_max_left _ _)
  have hab : ∀ i, Dvd (ℓ : ℤ_[ℓ]) (max 0 (γ i - 1)).toNat (a i) := fun i => trunc_dvd i (hab₀ i)
  have hz : ∀ i, 2 ≤ i → MvPolynomial.map (PadicInt.toZMod (p := ℓ)) (a i) = 0 := by
    intro i hi
    obtain ⟨z, hz⟩ := Dvd_mono (a := 1) (by have := hγ i hi; omega) (hab i)
    rw [hz, pow_one, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_natCast,
      ZMod.natCast_self, map_zero, zero_mul]
  set P₀ := MvPolynomial.map (PadicInt.toZMod (p := ℓ)) (a 0)
  set P₁ := MvPolynomial.map (PadicInt.toZMod (p := ℓ)) (a 1)
  have hFbar : PowerSeries.map (PadicInt.toZMod (p := ℓ)) F = ModP.ev (ZMod ℓ) P₀ + ModP.ev (ZMod ℓ) P₁ := by
    obtain ⟨g, hg⟩ := hA
    have e : F = ∑ i ∈ Finset.range I, ModP.ev ℤ_[ℓ] (a i) * Einv ℓ h5 ^ i + (ℓ : ℤ_[ℓ]) ^ 1 • g := by
      rw [← hg]; abel
    rw [e, map_add, map_katzSum, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_pow,
      map_natCast, ZMod.natCast_self, zero_pow one_ne_zero, map_zero, zero_mul, add_zero,
      ← Finset.sum_range_add_sum_Ico _ (le_max_right I₀ 2 : 2 ≤ I)]
    rw [Finset.sum_eq_zero (s := Finset.Ico 2 I) (fun i hi => by
      rw [hz i (Finset.mem_Ico.mp hi).1, map_zero]), add_zero, Finset.sum_range_succ,
      Finset.sum_range_one]
  have hiso0 : ModP.Iso P₀ 0 := by
    have := iso_of_mem h5 (i := 0) (P := P₀) ((Finset.coe_subset.mpr (MvPolynomial.support_map_subset _ _)).trans
      ((mem_Kpiece h5).mp (haK 0)))
    simpa using this
  have hiso1 : ModP.Iso P₁ (ℓ - 1) := by
    have := iso_of_mem h5 (i := 1) (P := P₁) ((Finset.coe_subset.mpr (MvPolynomial.support_map_subset _ _)).trans
      ((mem_Kpiece h5).mp (haK 1)))
    simpa using this
  refine ⟨P₀ * ModP.hasseBar ℓ h5 + P₁, ?_, ?_⟩
  · refine MvPolynomial.IsWeightedHomogeneous.add ?_ hiso1
    exact ModP.iso_of_eq (hiso0.mul (ModP.iso_hasseBar h5)) (by simp)
  · rw [map_add, map_mul, ModP.ev_hasseBar, mul_one]
    exact hFbar.symm

/-- The envelopes. -/
def B (h5 : 5 ≤ ℓ) (c : ℤ) : Submodule ℤ_[ℓ] (PS ℓ) := envSub h5 c (β ℓ)

lemma coeff_zero_D (hℓ5 : 5 ≤ ℓ) (F : PS ℓ) : coeff 0 (Dlin ℓ F) = 0 := by
  have hδ : δ ℓ ≠ 0 := by
    unfold δ
    have : 24 ≤ ℓ ^ 2 - 1 := by
      have : 25 ≤ ℓ ^ 2 := by nlinarith
      omega
    omega
  rw [Dlin_apply, coeff_U, Φl, BoylanWebb.Φ, mul_zero]
  simp only [map_mul, map_pow, PowerSeries.map_X]
  rw [mul_assoc, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]

lemma X_mem (h13 : 13 ≤ ℓ) (h5 : 5 ≤ ℓ) {c : ℤ} (hc : c ≤ 2) {F : PS ℓ} (hF : F ∈ B h5 c) :
    Xop ℓ F ∈ B h5 1 := by
  obtain ⟨hU, hD⟩ := bounds h13 h5
  exact ⟨coeff_zero_D h5 _, D_env h5 h13 hD 1 (by norm_num) _ (U_env h5 h13 hU c hc _ hF.2)⟩

lemma B_div (h5 : 5 ≤ ℓ) {F G : PS ℓ} (hF : F ∈ B h5 1) (h : F = (ℓ : ℤ_[ℓ]) • G) : G ∈ B h5 2 := by
  refine ⟨?_, by simpa using env_div h5 1 (β ℓ) hF.2 h⟩
  have hz := hF.1
  rw [h, coeff_smul, smul_eq_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left ell_ne_zero

/-- A polynomial in `X` preserves the first envelope. -/
lemma aeval_mem (h13 : 13 ≤ ℓ) (h5 : 5 ≤ ℓ) (p : Polynomial ℤ) {F : PS ℓ} (hF : F ∈ B h5 1) :
    Polynomial.aeval (Xop ℓ) p F ∈ B h5 1 := by
  have hpow : ∀ n : ℕ, ∀ {G : PS ℓ}, G ∈ B h5 1 → (Xop ℓ ^ n) G ∈ B h5 1 := by
    intro n
    induction n with
    | zero => intro G hG; simpa using hG
    | succ n ih =>
      intro G hG
      rw [pow_succ, Module.End.mul_apply]
      exact ih (X_mem h13 h5 (by norm_num) hG)
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hp hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact Submodule.smul_of_tower_mem _ c (hpow n hF)

/-- **One step of the induction.** -/
theorem chi_step (h13 : 13 ≤ ℓ) (h5 : 5 ≤ ℓ) {χ : Polynomial ℤ}
    (hχ : ∀ v ∈ Vbar ℓ, Polynomial.aeval (Xbar ℓ) (χ.map (Int.castRingHom (ZMod ℓ))) v = 0)
    {y : PS ℓ} (hy : y ∈ B h5 1) (hV : red ℓ y ∈ Vbar ℓ) :
    ∃ w ∈ B h5 2, Polynomial.aeval (Xop ℓ) χ y = (ℓ : ℤ_[ℓ]) • w := by
  have h0 : red ℓ (Polynomial.aeval (Xop ℓ) χ y) = 0 := by
    rw [red_aeval]
    exact hχ _ hV
  obtain ⟨w, hw⟩ := PS_dvd_of_map _ h0
  exact ⟨w, B_div h5 (aeval_mem h13 h5 χ hy) hw, hw⟩

/-- The reduction of `D F` lies in `V̄`, when `F` reduces to weight `ℓ - 1`. -/
lemma red_D_mem (h13 : 13 ≤ ℓ) {F : PS ℓ} (hF : FormBar ℓ (ℓ - 1) (red ℓ F)) :
    red ℓ (Dlin ℓ F) ∈ Vbar ℓ := by
  obtain ⟨a, ha, he⟩ := D_image h13 hF
  rw [red_D]
  exact ⟨a, ha, he⟩

lemma odd_D (n : ℕ) : Ll ℓ (2 * n + 1) = Dlin ℓ (Ll ℓ (2 * n)) := by
  rw [Ll_succ, Tl, if_pos (even_2b n)]

lemma even_U (n : ℕ) : Ll ℓ (2 * n + 2) = Ulin ℓ (Ll ℓ (2 * n + 1)) := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Ll_succ, Tl, if_neg (not_even_2b1 n)]

lemma odd_succ (n : ℕ) : Ll ℓ (2 * (n + 1) + 1) = Xop ℓ (Ll ℓ (2 * n + 1)) := by
  rw [odd_D, show 2 * (n + 1) = 2 * n + 2 by omega, even_U]
  rfl

lemma odd_eq (n : ℕ) : Ll ℓ (2 * n + 1) = (Xop ℓ ^ n) (Ll ℓ 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [odd_succ, ih, pow_succ', Module.End.mul_apply]

lemma L_one_mem (h13 : 13 ≤ ℓ) (h5 : 5 ≤ ℓ) : Ll ℓ 1 ∈ B h5 1 := by
  obtain ⟨hU, hD⟩ := bounds h13 h5
  have e : Ll ℓ 1 = Dlin ℓ 1 := by
    have := odd_D (ℓ := ℓ) 0
    simpa [Ll, L] using this
  rw [e]
  refine ⟨coeff_zero_D h5 _, D_env h5 h13 hD 1 (by norm_num) _ (env_one h5)⟩

/-- **The main induction.** -/
theorem chi_main (h13 : 13 ≤ ℓ) (h5 : 5 ≤ ℓ) {χ : Polynomial ℤ}
    (hχ : ∀ v ∈ Vbar ℓ, Polynomial.aeval (Xbar ℓ) (χ.map (Int.castRingHom (ZMod ℓ))) v = 0) (m : ℕ) :
    ∃ w ∈ B h5 2, Polynomial.aeval (Xop ℓ) (χ ^ (m + 1)) (Ll ℓ (2 * m + 1)) = (ℓ : ℤ_[ℓ]) ^ (m + 1) • w := by
  obtain ⟨hU, hD⟩ := bounds h13 h5
  induction m with
  | zero =>
    have hV : red ℓ (Ll ℓ 1) ∈ Vbar ℓ := by
      have e : Ll ℓ 1 = Dlin ℓ 1 := by
        have := odd_D (ℓ := ℓ) 0
        simpa [Ll, L] using this
      rw [e]
      refine red_D_mem h13 ⟨ModP.hasseBar ℓ h5, ModP.iso_hasseBar h5, ?_⟩
      rw [ModP.ev_hasseBar, map_one]
    obtain ⟨w, hw, he⟩ := chi_step h13 h5 hχ (L_one_mem h13 h5) hV
    exact ⟨w, hw, by simpa using he⟩
  | succ m ih =>
    obtain ⟨w, hw, he⟩ := ih
    have hy : Xop ℓ w ∈ B h5 1 := X_mem h13 h5 (by norm_num) hw
    have hV : red ℓ (Xop ℓ w) ∈ Vbar ℓ := by
      have hUe : Env ℓ h5 1 (α ℓ) (Ulin ℓ w) := U_env h5 h13 hU 2 le_rfl _ hw.2
      exact red_D_mem h13 (env_formBar h5 (α ℓ) (fun i hi => (envelopes_ge_two h13 i hi).1) _ hUe)
    obtain ⟨w', hw', he'⟩ := chi_step h13 h5 hχ hy hV
    refine ⟨w', hw', ?_⟩
    have hcomm : Polynomial.aeval (Xop ℓ) (χ ^ (m + 1 + 1)) (Ll ℓ (2 * (m + 1) + 1)) =
        Polynomial.aeval (Xop ℓ) χ (Xop ℓ (Polynomial.aeval (Xop ℓ) (χ ^ (m + 1)) (Ll ℓ (2 * m + 1)))) := by
      rw [odd_succ, pow_succ' χ, map_mul, Module.End.mul_apply]
      congr 1
      have hc : Polynomial.aeval (Xop ℓ) (χ ^ (m + 1)) * Xop ℓ =
          Xop ℓ * Polynomial.aeval (Xop ℓ) (χ ^ (m + 1)) := by
        have e := congrArg (Polynomial.aeval (R := ℤ) (Xop ℓ)) (mul_comm (χ ^ (m + 1)) Polynomial.X)
        rwa [map_mul, map_mul, Polynomial.aeval_X] at e
      exact congrFun (congrArg DFunLike.coe hc) _
    rw [hcomm, he, map_smul, map_smul, he', smul_smul]
    congr 1
    ring

/-- Commutation of a polynomial in `X` with powers of `X`. -/
lemma aeval_pow_comm (p : Polynomial ℤ) (k : ℕ) (f : PS ℓ) :
    Polynomial.aeval (Xop ℓ) p ((Xop ℓ ^ k) f) = (Xop ℓ ^ k) (Polynomial.aeval (Xop ℓ) p f) := by
  have e := congrArg (Polynomial.aeval (R := ℤ) (Xop ℓ)) (mul_comm p (Polynomial.X ^ k))
  rw [map_mul, map_mul, map_pow, Polynomial.aeval_X] at e
  exact congrFun (congrArg DFunLike.coe e) f

/-- A polynomial in `X` applied to an odd term is a linear combination of later terms. -/
lemma aeval_odd (p : Polynomial ℤ) (n : ℕ) :
    Polynomial.aeval (Xop ℓ) p (Ll ℓ (2 * n + 1)) =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • Ll ℓ (2 * (n + i) + 1) := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, odd_eq n, odd_eq (n + i), ← Module.End.mul_apply, ← pow_add, add_comm i n]

/-- **The congruence for the series, on both parities.** -/
theorem chi_series (h13 : 13 ≤ ℓ) (h5 : 5 ≤ ℓ) {χ : Polynomial ℤ}
    (hχ : ∀ v ∈ Vbar ℓ, Polynomial.aeval (Xbar ℓ) (χ.map (Int.castRingHom (ZMod ℓ))) v = 0)
    (m b : ℕ) (hb : 2 * m + 1 ≤ b) :
    ∃ y : PS ℓ, ∑ i ∈ Finset.range ((χ ^ (m + 1)).natDegree + 1),
        (χ ^ (m + 1)).coeff i • Ll ℓ (b + 2 * i) = (ℓ : ℤ_[ℓ]) ^ (m + 1) • y := by
  obtain ⟨w, -, he⟩ := chi_main h13 h5 hχ m
  have hodd : ∀ k, m ≤ k → ∃ y : PS ℓ, ∑ i ∈ Finset.range ((χ ^ (m + 1)).natDegree + 1),
      (χ ^ (m + 1)).coeff i • Ll ℓ (2 * (k + i) + 1) = (ℓ : ℤ_[ℓ]) ^ (m + 1) • y := by
    intro k hk
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
    refine ⟨(Xop ℓ ^ r) w, ?_⟩
    rw [← aeval_odd]
    have e : Ll ℓ (2 * (m + r) + 1) = (Xop ℓ ^ r) (Ll ℓ (2 * m + 1)) := by
      rw [odd_eq, odd_eq m, add_comm m r, pow_add, Module.End.mul_apply]
    rw [e, aeval_pow_comm, he, map_smul]
  rcases Nat.even_or_odd' b with ⟨k, rfl | rfl⟩
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨y, hy⟩ := hodd k' (by omega)
    refine ⟨Ulin ℓ y, ?_⟩
    have := congrArg (Ulin ℓ) hy
    rw [map_sum, map_smul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← even_U]
    congr 2
    ring
  · obtain ⟨y, hy⟩ := hodd k (by omega)
    refine ⟨y, ?_⟩
    rw [← hy]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ring

/-- The partition series has one unit factor along each parity class. -/
lemma L_factor_all (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (b : ℕ) :
    ∃ Q : PowerSeries ℤ, IsUnit Q ∧ ∀ i, L ℓ (b + 2 * i) = Q * Pser ℓ (b + 2 * i) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' b
  · refine ⟨_, MockTheta5.JTP.isUnit_qfacInf, fun i => ?_⟩
    rw [show 2 * k + 2 * i = 2 * (k + i) by ring]
    exact (L_eq_partition ℓ h24 (k + i)).1
  · refine ⟨_, MockTheta5.JTP.isUnit_qfacInf.map (RankProof.Ea ℓ (hℓ0 ℓ)), fun i => ?_⟩
    rw [show 2 * k + 1 + 2 * i = 2 * (k + i) + 1 by ring]
    exact (L_eq_partition ℓ h24 (k + i)).2

/-- The index shift along a parity class. -/
lemma index_shift_all (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (b n : ℕ) (hn : (24 : ℤ) ∣ (ℓ : ℤ) ^ b * n + 1) :
    ∃ t : ℕ, ∀ i : ℕ, ((ℓ : ℤ) ^ (b + 2 * i) * n + 1) / 24 =
      (ℓ : ℤ) ^ (b + 2 * i) * t - eB ℓ (b + 2 * i) := by
  set k := (b + 1) / 2 with hk
  have hkb : b ≤ 2 * k := by omega
  set r : ℤ := (ℓ : ℤ) ^ (2 * k - b) with hr
  have hlr : (ℓ : ℤ) ^ b * r = (ℓ : ℤ) ^ (2 * k) := by rw [hr, ← pow_add]; congr 1; omega
  have hr0 : 0 ≤ r := by positivity
  have he := ek_mul ℓ h24 k
  have hdiv : (24 : ℤ) ∣ n + r := by
    obtain ⟨u, hu⟩ := hn
    refine ⟨r * u - ek ℓ k * n, ?_⟩
    linear_combination r * hu + (n : ℤ) * he - (n : ℤ) * hlr
  obtain ⟨t, ht⟩ := hdiv
  have ht0 : 0 ≤ t := by
    have : (0 : ℤ) ≤ n + r := by positivity
    omega
  lift t to ℕ using ht0
  refine ⟨t, fun i => ?_⟩
  have he' := ek_mul ℓ h24 (k + i)
  have hlr' : (ℓ : ℤ) ^ (b + 2 * i) * r = (ℓ : ℤ) ^ (2 * (k + i)) := by
    rw [show 2 * (k + i) = 2 * k + 2 * i by ring, pow_add, pow_add, ← hlr]
    ring
  rw [eB, show (b + 2 * i + 1) / 2 = k + i by omega]
  have : (ℓ : ℤ) ^ (b + 2 * i) * n + 1 = 24 * ((ℓ : ℤ) ^ (b + 2 * i) * t - ek ℓ (k + i)) := by
    linear_combination (ℓ : ℤ) ^ (b + 2 * i) * ht + he' - hlr'
  rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]

/-- **The Boylan–Webb bound, as a congruence among partition numbers.** -/
theorem partition_bound (h13 : 13 ≤ ℓ) : ∃ χ : Polynomial ℤ, χ.Monic ∧ ¬ (ℓ : ℤ) ∣ χ.coeff 0 ∧
    ∀ m, 1 ≤ m → ∀ b, 2 * m - 1 ≤ b → ∀ n : ℕ, 24 ∣ ℓ ^ b * n + 1 →
      (ℓ : ℤ) ^ m ∣ ∑ i ∈ Finset.range ((χ ^ m).natDegree + 1), (χ ^ m).coeff i *
        (Fintype.card (Nat.Partition ((ℓ ^ (b + 2 * i) * n + 1) / 24)) : ℤ) := by
  have h5 : 5 ≤ ℓ := by omega
  have h24' := RamanujanTau.TheoremA.HalfIntegral.h24 (ℓ := ℓ) h13
  obtain ⟨χ, hm, hc, hχ⟩ := exists_chi (ℓ := ℓ) h13
  refine ⟨χ, hm, hc, fun m hm1 b hb n hn => ?_⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨y, hy⟩ := chi_series h13 h5 hχ m' b (by omega)
  obtain ⟨Q, hQ, hQe⟩ := L_factor_all (ℓ := ℓ) h24' b
  set φ := PowerSeries.map (Int.castRingHom ℤ_[ℓ]) with hφ
  obtain ⟨u, hu⟩ := hQ.map φ
  set p := χ ^ (m' + 1) with hp
  have hL : ∀ i, Ll ℓ (b + 2 * i) = (u : PS ℓ) * φ (Pser ℓ (b + 2 * i)) := by
    intro i
    change φ (L ℓ (b + 2 * i)) = _
    rw [hQe, map_mul, hu]
  have hsum : (u : PS ℓ) * ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • φ (Pser ℓ (b + 2 * i)) =
      (ℓ : ℤ_[ℓ]) ^ (m' + 1) • y := by
    rw [← hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hL, mul_smul_comm]
  have hd : ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • φ (Pser ℓ (b + 2 * i)) =
      (ℓ : ℤ_[ℓ]) ^ (m' + 1) • (↑u⁻¹ * y) := by
    rw [← mul_smul_comm, ← hsum, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨t, ht⟩ := index_shift_all (ℓ := ℓ) h24' b n (by exact_mod_cast hn)
  have hc2 := congrArg (coeff t) hd
  rw [map_sum, coeff_smul, smul_eq_mul] at hc2
  have hval : ∀ i, coeff t (p.coeff i • φ (Pser ℓ (b + 2 * i))) =
      ((p.coeff i * (Fintype.card (Nat.Partition ((ℓ ^ (b + 2 * i) * n + 1) / 24)) : ℤ) : ℤ) : ℤ_[ℓ]) := by
    intro i
    have e1 : ((ℓ : ℤ) ^ (b + 2 * i) * n + 1) / 24 = (((ℓ ^ (b + 2 * i) * n + 1) / 24 : ℕ) : ℤ) := by
      push_cast
      rfl
    rw [map_zsmul, hφ, coeff_map, Pser, coeff_mk, ← ht i, e1, pZ_natCast, eq_intCast]
    simp
  simp only [hval] at hc2
  have hdvd : (ℓ : ℤ_[ℓ]) ^ (m' + 1) ∣ ((∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i *
      (Fintype.card (Nat.Partition ((ℓ ^ (b + 2 * i) * n + 1) / 24)) : ℤ) : ℤ) : ℤ_[ℓ]) := by
    push_cast at hc2 ⊢
    exact ⟨_, hc2⟩
  exact (PadicInt.pow_p_dvd_int_iff _ _).mp hdvd

/-- **`b_ℓ(m) ≤ 2m - 1` for every prime `ℓ ≥ 13`.** From index `2m-1` on, each term of the partition chain
is, modulo `ℓ^m`, a fixed integer combination of later terms in its parity class. So the chain of spans is
constant from there on. -/
theorem chain_stable (h13 : 13 ≤ ℓ) (m : ℕ) (hm : 1 ≤ m) : ∃ (N : ℕ) (d : ℕ → ℤ),
    ∀ b, 2 * m - 1 ≤ b → ∀ n : ℕ, 24 ∣ ℓ ^ b * n + 1 →
      (ℓ : ℤ) ^ m ∣ (Fintype.card (Nat.Partition ((ℓ ^ b * n + 1) / 24)) : ℤ) -
        ∑ i ∈ Finset.range N, d i *
          (Fintype.card (Nat.Partition ((ℓ ^ (b + 2 * (i + 1)) * n + 1) / 24)) : ℤ) := by
  obtain ⟨χ, hmon, hc, hχ⟩ := partition_bound (ℓ := ℓ) h13
  set p := χ ^ m with hp
  have hc0 : p.coeff 0 = χ.coeff 0 ^ m := by
    rw [hp, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, ← Polynomial.coeff_zero_eq_eval_zero]
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ.out
  have hcop : IsCoprime (χ.coeff 0) (ℓ : ℤ) :=
    ((Prime.coprime_iff_not_dvd hprime).mpr hc).symm
  have hcopm : IsCoprime (p.coeff 0) ((ℓ : ℤ) ^ m) := by
    rw [hc0]
    exact hcop.pow
  obtain ⟨u, v, huv⟩ := hcopm
  refine ⟨p.natDegree, fun i => -(u * p.coeff (i + 1)), fun b hb n hn => ?_⟩
  obtain ⟨z, hz⟩ := hχ m hm b hb n hn
  rw [Finset.sum_range_succ' _ p.natDegree] at hz
  simp only [mul_zero, add_zero] at hz
  set A := (Fintype.card (Nat.Partition ((ℓ ^ b * n + 1) / 24)) : ℤ) with hA
  set T := ∑ i ∈ Finset.range p.natDegree, p.coeff (i + 1) *
    (Fintype.card (Nat.Partition ((ℓ ^ (b + 2 * (i + 1)) * n + 1) / 24)) : ℤ) with hT
  have hsum : ∑ i ∈ Finset.range p.natDegree, -(u * p.coeff (i + 1)) *
      (Fintype.card (Nat.Partition ((ℓ ^ (b + 2 * (i + 1)) * n + 1) / 24)) : ℤ) = -(u * T) := by
    rw [hT, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  refine ⟨u * z + v * A, ?_⟩
  linear_combination u * hz + (1 - v * (ℓ : ℤ) ^ m - u * p.coeff 0) * A - A * huv + A * (1 - u * p.coeff 0 - v * (ℓ : ℤ) ^ m)

/-- **`d_ℓ = 0` for every prime `ℓ ≥ 13`.** There is a space of reductions of weight `ℓ - 1` cusp forms on
which `X̄` is bijective and which contains `D̄ f` for every reduction `f` of a form of weight `ℓ - 1`. -/
theorem d_ell_zero (h13 : 13 ≤ ℓ) : ∃ S : Submodule (ZMod ℓ) (PowerSeries (ZMod ℓ)),
    FiniteDimensional (ZMod ℓ) S ∧
      (∀ v ∈ S, FormBar ℓ (ℓ - 1) v ∧ PowerSeries.coeff 0 v = 0) ∧ Set.BijOn (Xbar ℓ) S S ∧
      ∀ f, FormBar ℓ (ℓ - 1) f → Dbar ℓ f ∈ S := by
  haveI := finite_Vbar (ℓ := ℓ) h13
  have h5 : 5 ≤ ℓ := by omega
  refine ⟨Vbar ℓ, finite_Vbar h13, ?_, ⟨fun v hv => Xbar_mem h13 hv, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨formBar_of_intForm ℓ h5 ℓ (ℓ - 1) (by omega) _ (intForm_V h13 ha), ?_⟩
    rw [PowerSeries.coeff_map, coeff_zero_V ha, map_zero]
  · intro x hx y hy hxy
    have h0 := Xbar_inj h13 (Submodule.sub_mem _ hx hy) (by rw [map_sub, hxy, sub_self])
    exact sub_eq_zero.mp h0
  · have hinj : Function.Injective (Tv (ℓ := ℓ) h13) := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨v, hv⟩ h
      apply Subtype.ext
      exact Xbar_inj h13 hv (congrArg Subtype.val h)
    have hsurj := LinearMap.injective_iff_surjective.mp hinj
    intro v hv
    obtain ⟨w, hw⟩ := hsurj ⟨v, hv⟩
    exact ⟨w, w.2, congrArg Subtype.val hw⟩
  · intro f hf
    obtain ⟨a, ha, he⟩ := D_image h13 hf
    exact ⟨a, ha, he⟩

end

end RamanujanTau.BLBound
