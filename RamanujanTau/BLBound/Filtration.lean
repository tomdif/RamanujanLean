import RamanujanTau.BoylanWebb.Series
import RamanujanTau.TheoremA.HasseSeparation
import RamanujanTau.RamanujanODE.Main

/-!
# The filtration of `U_ℓ` in level one

Serre's bound: if `f` has weight `K` modulo `ℓ`, then `U_ℓ f` has a weight `w` with `w ≡ K (mod ℓ-1)` and
`ℓ w ≤ K + ℓ² - 1`. The proof uses `(U f)^ℓ = f - θ^(ℓ-1) f`, the raising of weight by `θ`, and the fact
that the Hasse polynomial is squarefree.
-/

set_option autoImplicit false

namespace RamanujanTau.BLBound
open MvPolynomial ModP Igusa

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `f` is the reduction of a form of weight `k`. -/
def FormBar (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) (f : PowerSeries (ZMod ℓ)) : Prop :=
  ∃ P : MvPolynomial (Fin 2) (ZMod ℓ), Iso P k ∧ ev (ZMod ℓ) P = f

lemma FormBar.up (h5 : 5 ≤ ℓ) {k : ℕ} {f : PowerSeries (ZMod ℓ)} (h : FormBar ℓ k f) (m : ℕ) :
    FormBar ℓ (k + m * (ℓ - 1)) f := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨hasseBar ℓ h5 ^ m * P, iso_of_eq (((iso_hasseBar h5).pow m).mul hP) ?_, ?_⟩
  · rw [smul_eq_mul]
    ring
  · rw [map_mul, map_pow, ev_hasseBar, one_pow, one_mul]

lemma FormBar.sub {k : ℕ} {f g : PowerSeries (ZMod ℓ)} (hf : FormBar ℓ k f) (hg : FormBar ℓ k g) :
    FormBar ℓ k (f - g) := by
  obtain ⟨P, hP, rfl⟩ := hf
  obtain ⟨Q, hQ, rfl⟩ := hg
  exact ⟨P - Q, iso_sub hP hQ, map_sub _ _ _⟩

lemma twelve_unit (h5 : 5 ≤ ℓ) : (12 : ZMod ℓ) ≠ 0 := by
  have h := ne_zero_1728 (p := ℓ) h5
  intro h0
  apply h
  have : (1728 : ZMod ℓ) = 12 * 144 := by norm_num
  rw [this, h0, zero_mul]

/-- `θ` raises the weight by `ℓ + 1`. -/
lemma FormBar.theta (h5 : 5 ≤ ℓ) {k : ℕ} {f : PowerSeries (ZMod ℓ)} (h : FormBar ℓ k f) :
    FormBar ℓ (k + (ℓ + 1)) (Igusa.theta f) := by
  obtain ⟨P, hP, rfl⟩ := h
  have hs := ev_serreD (R := ZMod ℓ) RamanujanODEProof.ramanujanODE hP
  have h12 := twelve_unit (ℓ := ℓ) h5
  set R : MvPolynomial (Fin 2) (ZMod ℓ) :=
    C (12 : ZMod ℓ)⁻¹ * (C (k : ZMod ℓ) * hasseB ℓ h5 * P + hasseBar ℓ h5 * serreD P) with hR
  refine ⟨R, ?_, ?_⟩
  · have h1 : Iso (C (k : ZMod ℓ) * hasseB ℓ h5 * P) (k + (ℓ + 1)) := by
      have := ((iso_hasseB h5).C_mul (k : ZMod ℓ)).mul hP
      exact iso_of_eq this (by ring)
    have h2 : Iso (hasseBar ℓ h5 * serreD P) (k + (ℓ + 1)) := by
      have := (iso_hasseBar h5).mul (iso_serreD hP)
      refine iso_of_eq this ?_
      have := hℓ.out.two_le
      omega
    exact (h1.add h2).C_mul _
  · have hE2 := ev_hasseB (p := ℓ) RamanujanODEProof.ramanujanODE h5
    have hunit : (PowerSeries.C (12 : ZMod ℓ)⁻¹) * (12 : PowerSeries (ZMod ℓ)) = 1 := by
      have : (12 : PowerSeries (ZMod ℓ)) = PowerSeries.C (12 : ZMod ℓ) :=
        (map_ofNat (PowerSeries.C (R := ZMod ℓ)) 12).symm
      rw [this, ← map_mul, inv_mul_cancel₀ h12, map_one]
    have hC : ∀ c : ZMod ℓ, ev (ZMod ℓ) (C c) = PowerSeries.C c := ev_C
    rw [hR, map_mul, map_add, map_mul, map_mul, map_mul, hC, hC, hE2, ev_hasseBar, one_mul]
    have e : Igusa.theta (ev (ZMod ℓ) P) = PowerSeries.C (12 : ZMod ℓ)⁻¹ *
        (12 * Igusa.theta (ev (ZMod ℓ) P)) := by
      rw [← mul_assoc, hunit, one_mul]
    rw [e, hs]
    simp

lemma FormBar.theta_iter (h5 : 5 ≤ ℓ) {k : ℕ} {f : PowerSeries (ZMod ℓ)} (h : FormBar ℓ k f) (n : ℕ) :
    FormBar ℓ (k + n * (ℓ + 1)) (Igusa.theta^[n] f) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have := ih.theta h5
    convert this using 1
    ring

/-- The `ℓ`-th power of a series over `𝔽_ℓ`. -/
lemma coeff_pow_char (f : PowerSeries (ZMod ℓ)) (n : ℕ) :
    PowerSeries.coeff n (f ^ ℓ) =
      if ℓ ∣ n then PowerSeries.coeff (n / ℓ) f else 0 := by
  have hp := hℓ.out
  set T : Polynomial (ZMod ℓ) := PowerSeries.trunc (n + 1) f with hT
  obtain ⟨g, hg⟩ : (PowerSeries.X : PowerSeries (ZMod ℓ)) ^ (n + 1) ∣ f - (T : PowerSeries (ZMod ℓ)) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, hT, PowerSeries.coeff_trunc, if_pos hm, sub_self]
  have hf : f = (T : PowerSeries (ZMod ℓ)) + PowerSeries.X ^ (n + 1) * g := by
    rw [← hg]
    ring
  have hpow : f ^ ℓ = ((T ^ ℓ : Polynomial (ZMod ℓ)) : PowerSeries (ZMod ℓ)) +
      PowerSeries.X ^ ((n + 1) * ℓ) * g ^ ℓ := by
    conv_lhs => rw [hf]
    rw [add_pow_char, mul_pow, ← pow_mul, Polynomial.coe_pow]
  have hlow : (PowerSeries.coeff n) (PowerSeries.X ^ ((n + 1) * ℓ) * g ^ ℓ : PowerSeries (ZMod ℓ)) = 0 := by
    rw [PowerSeries.coeff_X_pow_mul', if_neg]
    have : n + 1 ≤ (n + 1) * ℓ := Nat.le_mul_of_pos_right _ hp.pos
    omega
  have hexp : T ^ ℓ = Polynomial.expand (ZMod ℓ) ℓ T := by
    have h := Polynomial.expand_char (R := ZMod ℓ) ℓ T
    rw [← h]
    have hfr : frobenius (ZMod ℓ) ℓ = RingHom.id _ := by
      ext x
      exact ZMod.frobenius_zmod ℓ ▸ rfl
    rw [hfr, Polynomial.map_id]
  rw [hpow, map_add, hlow, add_zero, Polynomial.coeff_coe, hexp, Polynomial.coeff_expand hp.pos]
  split_ifs with hd
  · rw [hT, PowerSeries.coeff_trunc, if_pos]
    have := Nat.div_le_self n ℓ
    omega
  · rfl

/-- **`(U f)^ℓ = f - θ^(ℓ-1) f`.** -/
theorem U_pow_char (f : PowerSeries (ZMod ℓ)) :
    (BoylanWebb.U ℓ f) ^ ℓ = f - Igusa.theta^[ℓ - 1] f := by
  have hp := hℓ.out
  have hit : ∀ (m : ℕ) (n : ℕ), PowerSeries.coeff n (Igusa.theta^[m] f) =
      (n : ZMod ℓ) ^ m * PowerSeries.coeff n f := by
    intro m n
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', coeff_theta, ih, pow_succ]
      ring
  ext n
  rw [coeff_pow_char, map_sub, hit]
  by_cases hd : ℓ ∣ n
  · obtain ⟨c, rfl⟩ := hd
    have hz : ((ℓ * c : ℕ) : ZMod ℓ) = 0 := by simp
    have hpos : ℓ - 1 ≠ 0 := by have := hp.two_le; omega
    rw [if_pos (dvd_mul_right ℓ c), Nat.mul_div_cancel_left _ hp.pos, BoylanWebb.coeff_U, hz,
      zero_pow hpos, zero_mul, sub_zero]
  · have hne : (n : ZMod ℓ) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff]
    rw [if_neg hd, ZMod.pow_card_sub_one_eq_one hne, one_mul, sub_self]

/-- A polynomial in one variable without a root takes one value. -/
lemma poly_const_of_no_root {K : Type*} [Field K] [IsAlgClosed K] (p : Polynomial K)
    (h : ∀ x : K, p.eval x ≠ 0) (a b : K) : p.eval a = p.eval b := by
  have hd : p.degree = 0 ∨ p = 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p (by simpa using hc.1)
    exact h x hx
  rcases hd with hd | rfl
  · rw [Polynomial.eq_C_of_degree_eq_zero hd]
    simp
  · simp

lemma eval_sec1 {K : Type*} [Field K] (P : MvPolynomial (Fin 2) K) (x y : K) :
    (aeval (![Polynomial.X, Polynomial.C y] : Fin 2 → Polynomial K) P).eval x = eval ![x, y] P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp => fin_cases i <;> simp [hp]

lemma eval_sec2 {K : Type*} [Field K] (P : MvPolynomial (Fin 2) K) (x y : K) :
    (aeval (![Polynomial.C x, Polynomial.X] : Fin 2 → Polynomial K) P).eval y = eval ![x, y] P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp => fin_cases i <;> simp [hp]

/-- A polynomial without a nonzero zero is constant. -/
lemma const_of_no_zero {K : Type*} [Field K] [IsAlgClosed K] (P : MvPolynomial (Fin 2) K)
    (h : ∀ x y : K, (x ≠ 0 ∨ y ≠ 0) → eval ![x, y] P ≠ 0) : ∃ c : K, P = C c := by
  have hinf : Infinite K := IsAlgClosed.instInfinite
  have hx : ∀ (y₀ : K), y₀ ≠ 0 → ∀ a b : K, eval ![a, y₀] P = eval ![b, y₀] P := by
    intro y₀ hy a b
    rw [← eval_sec1, ← eval_sec1]
    refine poly_const_of_no_root _ (fun x => ?_) a b
    rw [eval_sec1]
    exact h x y₀ (Or.inr hy)
  have hy : ∀ (x₀ : K), x₀ ≠ 0 → ∀ a b : K, eval ![x₀, a] P = eval ![x₀, b] P := by
    intro x₀ hx₀ a b
    rw [← eval_sec2, ← eval_sec2]
    refine poly_const_of_no_root _ (fun y => ?_) a b
    rw [eval_sec2]
    exact h x₀ y (Or.inl hx₀)
  set c := eval ![(1 : K), 1] P with hc
  refine ⟨c, ?_⟩
  have hzero : X 0 * (P - C c) = 0 := by
    apply MvPolynomial.funext
    intro v
    have hv : v = ![v 0, v 1] := by
      ext i
      fin_cases i <;> rfl
    simp only [map_mul, eval_X, map_sub, eval_C, map_zero]
    by_cases h0 : v 0 = 0
    · rw [h0, zero_mul]
    · have e1 : eval v P = c := by
        rw [hv, hy (v 0) h0 (v 1) 1, hx 1 one_ne_zero (v 0) 1]
      rw [e1, sub_self, mul_zero]
  have hX : (X 0 : MvPolynomial (Fin 2) K) ≠ 0 := X_ne_zero 0
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hX)

/-- `serreD` is a derivation. -/
lemma serreD_mul {R : Type*} [CommRing R] (f g : MvPolynomial (Fin 2) R) :
    serreD (f * g) = serreD f * g + f * serreD g := by
  unfold serreD
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

/-- **The Hasse polynomial is squarefree.** -/
theorem hasse_squarefree (h5 : 5 ≤ ℓ) : Squarefree (hasseBar ℓ h5) := by
  intro D hD
  obtain ⟨R, hR⟩ := hD
  let K := AlgebraicClosure (ZMod ℓ)
  let φ : ZMod ℓ →+* K := ZMod.castHom (dvd_refl ℓ) K
  have hA : hasseBar ℓ h5 = D * (D * R) := by rw [hR]; ring
  have hB : hasseB ℓ h5 = D * (serreD D * R + (serreD D * R + D * serreD R)) := by
    unfold hasseB
    rw [hA, serreD_mul, serreD_mul]
    ring
  have hno : ∀ x y : K, (x ≠ 0 ∨ y ≠ 0) → eval ![x, y] (map φ D) ≠ 0 := by
    intro x y hxy h0
    have hAz : eval ![x, y] (AF K ℓ h5) = 0 := by
      have e : AF K ℓ h5 = map φ (hasseBar ℓ h5) := rfl
      rw [e, hA, map_mul, map_mul, h0, zero_mul]
    have hBz : eval ![x, y] (BF K ℓ h5) = 0 := by
      have e : BF K ℓ h5 = map φ (hasseB ℓ h5) := rfl
      rw [e, hB, map_mul, map_mul, h0, zero_mul]
    exact RamanujanTau.TheoremA.hasse_companion_separation h5 x y hxy hAz hBz
  obtain ⟨c, hc⟩ := const_of_no_zero _ hno
  have hinj : Function.Injective φ := φ.injective
  have hD0 : D = C (coeff 0 D) := by
    apply MvPolynomial.map_injective φ hinj
    rw [map_C, hc]
    have h0 : φ (coeff 0 D) = c := by
      have := congrArg (coeff 0) hc
      rw [coeff_map] at this
      simpa using this
    rw [h0]
  have hne : coeff 0 D ≠ 0 := by
    intro h0
    apply hasseBar_ne_zero (p := ℓ) h5
    rw [hA, hD0, h0]
    simp
  rw [hD0]
  exact (isUnit_iff_ne_zero.mpr hne).map C

/-- The Hasse polynomial divides `Q` as soon as it divides a power of `Q`. -/
lemma hasse_dvd_of_pow (h5 : 5 ≤ ℓ) {Q : MvPolynomial (Fin 2) (ZMod ℓ)} {n : ℕ} (hn : n ≠ 0)
    (h : hasseBar ℓ h5 ∣ Q ^ n) : hasseBar ℓ h5 ∣ Q :=
  ((hasse_squarefree h5).dvd_pow_iff_dvd hn).mp h

/-- Division by a homogeneous polynomial preserves homogeneity. -/
lemma iso_quotient {F : Type*} [Field F] {A Q R : MvPolynomial (Fin 2) F} {a w : ℕ} (hA : Iso A a)
    (hQ : Iso Q w) (hQ0 : Q ≠ 0) (h : Q = A * R) :
    a ≤ w ∧ ∃ R' : MvPolynomial (Fin 2) F, Iso R' (w - a) ∧ Q = A * R' := by
  classical
  let 𝒜 := weightedHomogeneousSubmodule F wt
  haveI : GradedAlgebra 𝒜 := weightedGradedAlgebra F wt
  have hAm : A ∈ 𝒜 a := hA
  have hQm : Q ∈ 𝒜 w := hQ
  have hdec : ((DirectSum.decompose 𝒜 Q) w : MvPolynomial (Fin 2) F) = Q :=
    DirectSum.decompose_of_mem_same 𝒜 hQm
  by_cases hle : a ≤ w
  · refine ⟨hle, ((DirectSum.decompose 𝒜 R) (w - a) : MvPolynomial (Fin 2) F),
      ((DirectSum.decompose 𝒜 R) (w - a)).2, ?_⟩
    have hk := DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (a := A) (b := R) (i := a) (j := w - a) hAm
    rw [Nat.add_sub_cancel' hle, ← h, hdec] at hk
    exact hk
  · exfalso
    have hk := DirectSum.coe_decompose_mul_of_left_mem_of_not_le 𝒜 (a := A) (b := R) (i := a) (n := w) hAm hle
    rw [← h, hdec] at hk
    exact hQ0 hk

/-- **Serre's bound for `U_ℓ`.** -/
theorem U_filtration (h5 : 5 ≤ ℓ) {K : ℕ} {f : PowerSeries (ZMod ℓ)} (hf : FormBar ℓ K f)
    (hU : FormBar ℓ K (BoylanWebb.U ℓ f)) :
    ∃ w : ℕ, w % (ℓ - 1) = K % (ℓ - 1) ∧ ℓ * w ≤ K + (ℓ - 1) * (ℓ + 1) ∧
      FormBar ℓ w (BoylanWebb.U ℓ f) := by
  classical
  have hp := hℓ.out
  have hl1 : 1 ≤ ℓ - 1 := by omega
  by_cases hzero : BoylanWebb.U ℓ f = 0
  · refine ⟨K % (ℓ - 1), by simp, ?_, ?_⟩
    · have := Nat.mod_lt K hl1
      have h2 : ℓ * (K % (ℓ - 1)) ≤ ℓ * (ℓ - 1) := Nat.mul_le_mul_left _ this.le
      have h3 : ℓ * (ℓ - 1) ≤ (ℓ - 1) * (ℓ + 1) := by nlinarith
      omega
    · rw [hzero]
      exact ⟨0, isWeightedHomogeneous_zero _ _ _, map_zero _⟩
  let S : ℕ → Prop := fun w => w % (ℓ - 1) = K % (ℓ - 1) ∧ FormBar ℓ w (BoylanWebb.U ℓ f)
  have hS : ∃ w, S w := ⟨K, rfl, hU⟩
  set w := Nat.find hS with hw
  obtain ⟨hwmod, P, hP, hPe⟩ := Nat.find_spec hS
  have hP0 : P ≠ 0 := by
    rintro rfl
    apply hzero
    rw [← hPe, map_zero]
  have hnd : ¬ hasseBar ℓ h5 ∣ P := by
    rintro ⟨R, hR⟩
    obtain ⟨hle, R', hR', hRe⟩ := iso_quotient (iso_hasseBar h5) hP hP0 hR
    have hlt : Nat.find hS - (ℓ - 1) < Nat.find hS := by
      have hpos : 0 < Nat.find hS := lt_of_lt_of_le hl1 hle
      omega
    refine Nat.find_min hS hlt ⟨?_, R', hR', ?_⟩
    · have e : Nat.find hS - (ℓ - 1) + (ℓ - 1) = Nat.find hS := Nat.sub_add_cancel hle
      have := Nat.add_mod_right (Nat.find hS - (ℓ - 1)) (ℓ - 1)
      rw [e] at this
      exact this.symm.trans hwmod
    · rw [← hPe, hRe, map_mul, ev_hasseBar, one_mul]
  refine ⟨w, hwmod, ?_, P, hP, hPe⟩
  by_contra hcon
  push_neg at hcon
  have hg : FormBar ℓ (K + (ℓ - 1) * (ℓ + 1)) (f - Igusa.theta^[ℓ - 1] f) := by
    refine FormBar.sub ?_ (hf.theta_iter h5 (ℓ - 1))
    have := hf.up h5 (ℓ + 1)
    convert this using 2
    ring
  obtain ⟨R, hR, hRe⟩ := hg
  have hpowe : ev (ZMod ℓ) (P ^ ℓ) = ev (ZMod ℓ) R := by
    rw [map_pow, hPe, U_pow_char, hRe]
  have hPpow : Iso (P ^ ℓ) (ℓ * w) := iso_of_eq (hP.pow ℓ) (by rw [smul_eq_mul])
  have hmod : (ℓ * w) % (ℓ - 1) = (K + (ℓ - 1) * (ℓ + 1)) % (ℓ - 1) := by
    have h1 : ℓ * w = (ℓ - 1) * w + w := by
      have : ℓ = (ℓ - 1) + 1 := by omega
      nth_rewrite 1 [this]
      ring
    rw [h1, Nat.mul_add_mod, Nat.add_mul_mod_self_left, hwmod]
  obtain ⟨m, hm⟩ := (Nat.modEq_iff_exists_eq_add hcon.le).mp hmod.symm
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  have hiso : Iso (P ^ ℓ) (K + (ℓ - 1) * (ℓ + 1) + m * (ℓ - 1)) :=
    iso_of_eq hPpow (by rw [hm]; ring)
  have heq := eq_hasseBar_pow_mul h5 hR hiso hpowe.symm
  exact hnd (hasse_dvd_of_pow h5 hp.ne_zero (heq ▸ dvd_mul_of_dvd_left (dvd_pow_self _ hm0) _))

end RamanujanTau.BLBound
