import RamanujanTau.VLayer.DBQ
import RamanujanTau.UpContraction.ThmB

/-!
# Pointwise bounds on the break region give the sharp class

Let `K` be a complete, ultrametric, algebraically closed field with an integral `φ : ℤ_[ℓ] →+* K`
and `0 < ‖ℓ‖ < 1`. Let `P ∈ ℤ_ℓ[X₀, X₁]` be isobaric of weight `n(ℓ−1)`, so that `ℓ^e P/E^n` is a finite
weight-0 Katz series.

* **`decompP`**: the polynomial-level Katz decomposition mod `ℓ^N`:
  `P = Σ_{m ≤ n} A^{n−m} c_m + ℓ^N P'`, `c_m ∈ B_m`.
* **`Ap_Bp_of_pointwise`**: if `‖ℓ‖^e · ‖P(W)‖ ≤ ‖E(W)‖^n` at every test curve `W` of the break region
  `v(E(W)) < ℓ/(ℓ+1)` (`UpContraction.Brk`), then `ℓ^e P/E^n` lies in the sharp class
  (`Ap (Bp ℓ)`, `v_m ≥ ⌈ℓm/(ℓ+1)⌉`).

  Proof: step (K) (`Igusa.katz_iff_hasse'`) at every radius `s` with `v(s) = (ℓM−1)/((ℓ+1)M)`, applied to
  the decomposition mod `ℓ^N`, `N ≥ n` (the error `ℓ^N P'/E^n` is pointwise `≤ 1` because
  `‖E(W)‖ ≥ ‖ℓ‖` on the break region). Then `M → ∞`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SharpHQ
open MvPolynomial ModP AtkinOBrienFinal AtkinOBrien DBound VLayer KatzForms Igusa Filter Topology

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-! ### the polynomial-level decomposition -/

/-- **Katz decomposition of one weight, mod `ℓ^N`, as a polynomial identity.** -/
theorem decompP (N : ℕ) : ∀ (n : ℕ) (P : Poly ℓ), Iso P (n * (ℓ - 1)) →
    ∃ (c : ℕ → Poly ℓ) (P' : Poly ℓ), (∀ m, c m ∈ Kpiece ℓ hℓ m) ∧ (∀ m, n < m → c m = 0) ∧
      Iso P' (n * (ℓ - 1)) ∧
      P = ∑ m ∈ Finset.range (n + 1), hasseA ℓ hℓ ^ (n - m) * c m + (ℓ : ℤ_[ℓ]) ^ N • P' := by
  induction N with
  | zero =>
    intro n P hP
    refine ⟨0, P, fun m => Submodule.zero_mem _, fun _ _ => rfl, hP, ?_⟩
    simp
  | succ N ih =>
    intro n P hP
    obtain ⟨c1, P1, hc1, hP1, he1⟩ := decomp1 hℓ n P hP
    obtain ⟨c2, P2, hc2, hc20, hP2, he2⟩ := ih n P1 hP1
    refine ⟨fun m => if m ≤ n then c1 m + (ℓ : ℤ_[ℓ]) • c2 m else 0, P2, fun m => ?_,
      fun m hm => by simp only [if_neg (by omega : ¬ m ≤ n)], hP2, ?_⟩
    · dsimp only
      split_ifs
      · exact Submodule.add_mem _ (hc1 m) (Submodule.smul_mem _ _ (hc2 m))
      · exact Submodule.zero_mem _
    · have hs : ∑ m ∈ Finset.range (n + 1), hasseA ℓ hℓ ^ (n - m) *
          (if m ≤ n then c1 m + (ℓ : ℤ_[ℓ]) • c2 m else 0) =
          ∑ m ∈ Finset.range (n + 1), hasseA ℓ hℓ ^ (n - m) * c1 m +
            (ℓ : ℤ_[ℓ]) • ∑ m ∈ Finset.range (n + 1), hasseA ℓ hℓ ^ (n - m) * c2 m := by
        rw [Finset.smul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)), mul_add, mul_smul_comm]
      rw [hs, he1, he2, smul_add, smul_smul, ← pow_succ', add_assoc]

/-! ### coefficientwise divisibility -/

lemma Dvd_of_coeff {B : ℕ} (x : Poly ℓ) (h : ∀ d, (ℓ : ℤ_[ℓ]) ^ B ∣ x.coeff d) :
    Dvd (ℓ : ℤ_[ℓ]) B x := by
  classical
  choose z hz using h
  refine ⟨∑ d ∈ x.support, monomial d (z d), ?_⟩
  rw [Finset.smul_sum]
  conv_lhs => rw [x.as_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [smul_monomial, smul_eq_mul, ← hz]

/-- `‖φ x‖ = ‖ℓ‖^{v(x)}` for `x ≠ 0`. -/
lemma norm_phi_eq {K : Type*} [NormedField K] [IsUltrametricDist K] (φ : ℤ_[ℓ] →+* K)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) {x : ℤ_[ℓ]} (hx : x ≠ 0) :
    ‖φ x‖ = ‖(ℓ : K)‖ ^ x.valuation := by
  have hu : ‖φ (PadicInt.unitCoeff hx : ℤ_[ℓ])‖ = 1 := norm_phi_unit φ hφ (Units.isUnit _)
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [map_mul, map_pow, map_natCast, norm_mul, hu, one_mul, norm_pow]

/-- **The radius limit**: `‖φ x‖ ≤ ‖s‖^m` for every radius with `‖s‖^{(ℓ+1)M} = ‖ℓ‖^{ℓM−1}` gives
`ℓ^{⌈ℓm/(ℓ+1)⌉} ∣ x`. -/
lemma dvd_of_radius {K : Type*} [NormedField K] [IsUltrametricDist K] (φ : ℤ_[ℓ] →+* K)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖) (hpK : ‖(ℓ : K)‖ < 1) (x : ℤ_[ℓ]) (m : ℕ)
    (h : ∀ M : ℕ, 0 < M → ‖φ x‖ ^ ((ℓ + 1) * M) ≤ ‖(ℓ : K)‖ ^ ((ℓ * M - 1) * m)) :
    (ℓ : ℤ_[ℓ]) ^ Bp ℓ m ∣ x := by
  by_cases hx : x = 0
  · rw [hx]; exact dvd_zero _
  set v := x.valuation with hv
  have hv' : ∀ M : ℕ, 0 < M → (ℓ * M - 1) * m ≤ v * ((ℓ + 1) * M) := by
    intro M hM
    have := h M hM
    rw [norm_phi_eq φ hφ hx, ← pow_mul] at this
    exact (pow_le_pow_iff_right_of_lt_one₀ hε hpK).mp this
  have hkey : ℓ * m ≤ (ℓ + 1) * v := by
    by_contra hc
    push Not at hc
    have h1 := hv' (m + 1) (Nat.succ_pos _)
    have hl : 1 ≤ ℓ * (m + 1) := by have := hℓp.out.two_le; nlinarith
    have e : (ℓ * (m + 1) - 1) * m + m = ℓ * (m + 1) * m := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (by nlinarith)]
    nlinarith
  have hB : Bp ℓ m ≤ v := by
    unfold Bp
    have : ⌈(ℓ : ℚ) * m / ((ℓ : ℚ) + 1)⌉ ≤ (v : ℤ) := by
      rw [Int.ceil_le, div_le_iff₀ (by positivity)]
      have : ((ℓ * m : ℕ) : ℚ) ≤ (((ℓ + 1) * v : ℕ) : ℚ) := by exact_mod_cast hkey
      push_cast at this ⊢; linarith
    omega
  conv_rhs => rw [PadicInt.unitCoeff_spec hx]
  exact Dvd.dvd.mul_left (pow_dvd_pow _ hB) _

/-! ### the main bridge -/

section Bridge
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

lemma norm_E_le_one (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) {W : WeierstrassCurve K}
    (hW : IsTest W) : ‖eval (pt W) (Eh φ hℓ)‖ ≤ 1 :=
  (norm_eval_le (integral_pt hW) _).trans (gnorm_le zero_le_one (Eh_integral φ hφ hℓ))

lemma norm_map_eval_le_one (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) {W : WeierstrassCurve K}
    (hW : IsTest W) (P : Poly ℓ) : ‖eval (pt W) (MvPolynomial.map φ P)‖ ≤ 1 :=
  (norm_eval_le (integral_pt hW) _).trans (gnorm_le zero_le_one fun d => by
    rw [coeff_map]; exact hφ _)

/-- on the break region `‖ℓ‖ ≤ ‖E(W)‖`. -/
lemma le_of_brk (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖)
    {W : WeierstrassCurve K} (hW : IsTest W) (hB : UpContraction.Brk ℓ (Eh φ hℓ) W) :
    ‖(ℓ : K)‖ ≤ ‖eval (pt W) (Eh φ hℓ)‖ := by
  unfold UpContraction.Brk at hB
  by_contra hc
  push Not at hc
  have h1 := norm_E_le_one hℓ φ hφ hW
  have : ‖eval (pt W) (Eh φ hℓ)‖ ^ (ℓ + 1) ≤ ‖(ℓ : K)‖ ^ ℓ := by
    calc ‖eval (pt W) (Eh φ hℓ)‖ ^ (ℓ + 1) ≤ ‖(ℓ : K)‖ ^ (ℓ + 1) :=
          pow_le_pow_left₀ (norm_nonneg _) hc.le _
      _ ≤ ‖(ℓ : K)‖ ^ ℓ := pow_le_pow_of_le_one hε.le (by simpa using hφ (ℓ : ℤ_[ℓ]))
          (Nat.le_succ ℓ)
  linarith

/-- **Pointwise bounds on the break region give the sharp class.** If `P` is isobaric of weight
`n(ℓ−1)` and `‖ℓ‖^e·‖P(W)‖ ≤ ‖E(W)‖^n` at every test curve `W` with `v(E(W)) < ℓ/(ℓ+1)`, then
`ℓ^e P/E^n` has Katz coordinates `v_m ≥ ⌈ℓm/(ℓ+1)⌉` (in approximation form). -/
theorem Ap_Bp_of_pointwise [CompleteSpace K] [IsAlgClosed K] (φ : ℤ_[ℓ] →+* K)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖) (hpK : ‖(ℓ : K)‖ < 1) {n e : ℕ} {P : Poly ℓ}
    (hP : Iso P (n * (ℓ - 1)))
    (hpt : ∀ W : WeierstrassCurve K, IsTest W → UpContraction.Brk ℓ (Eh φ hℓ) W →
      ‖(ℓ : K)‖ ^ e * ‖eval (pt W) (MvPolynomial.map φ P)‖ ≤ ‖eval (pt W) (Eh φ hℓ)‖ ^ n) :
    Ap hℓ (Bp ℓ) ((ℓ : ℤ_[ℓ]) ^ e • (ModP.ev ℤ_[ℓ] P * Einv ℓ hℓ ^ n)) := by
  intro N0
  obtain ⟨c, P', hc, hc0, hP', hPe⟩ := decompP hℓ (N0 + n) n P hP
  set a : ℕ → Poly ℓ := fun m => (ℓ : ℤ_[ℓ]) ^ e • c m with ha
  set t := ‖(ℓ : K)‖ with ht
  refine ⟨n + 1, a, fun m => Submodule.smul_mem _ _ (hc m), ?_, ?_⟩
  · -- the approximation
    have key : ModP.ev ℤ_[ℓ] P * Einv ℓ hℓ ^ n =
        ∑ m ∈ Finset.range (n + 1), ModP.ev ℤ_[ℓ] (c m) * Einv ℓ hℓ ^ m +
          (ℓ : ℤ_[ℓ]) ^ (N0 + n) • (ModP.ev ℤ_[ℓ] P' * Einv ℓ hℓ ^ n) := by
      have hs : ∑ m ∈ Finset.range (n + 1), ModP.ev ℤ_[ℓ] (hasseA ℓ hℓ ^ (n - m) * c m) *
          Einv ℓ hℓ ^ n = ∑ m ∈ Finset.range (n + 1), ModP.ev ℤ_[ℓ] (c m) * Einv ℓ hℓ ^ m := by
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [map_mul, map_pow, ev_hasseA_E, mul_comm (E ℓ hℓ ^ (n - m)), mul_assoc,
          E_pow_mul_Einv_pow hℓ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]
      conv_lhs => rw [hPe]
      rw [map_add, map_sum, add_mul, Finset.sum_mul, map_smul, smul_mul_assoc, hs]
    refine ⟨(ℓ : ℤ_[ℓ]) ^ (e + n) • (ModP.ev ℤ_[ℓ] P' * Einv ℓ hℓ ^ n), ?_⟩
    rw [key]
    simp only [ha, map_smul, smul_mul_assoc]
    rw [← Finset.smul_sum, smul_add, add_sub_cancel_left, smul_smul, smul_smul, ← pow_add,
      ← pow_add]
    congr 2; ring
  · intro m
    by_cases hm : n < m
    · simp only [ha, hc0 m hm, smul_zero]; exact Dvd_zero _
    push Not at hm
    refine Dvd_of_coeff _ fun d => dvd_of_radius φ hφ hε hpK _ m fun M hM => ?_
    -- the radius `s`, `‖s‖^{(ℓ+1)M} = ‖ℓ‖^{ℓM−1}`
    have hb0 : 0 < (ℓ + 1) * M := by positivity
    have hl1 : 2 ≤ ℓ * M := by have := hℓp.out.two_le; nlinarith
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((ℓ : K) ^ (ℓ * M - 1)) hb0
    have hs' : ‖s‖ ^ ((ℓ + 1) * M) = t ^ (ℓ * M - 1) := by rw [← norm_pow, hs, norm_pow]
    have hs0 : 0 < ‖s‖ := by
      rcases (norm_nonneg s).eq_or_lt with h | h
      · rw [← h, zero_pow hb0.ne'] at hs'
        exact absurd hs'.symm (pow_ne_zero _ hε.ne')
      · exact h
    have hs1 : ‖s‖ < 1 := by
      have : ‖s‖ ^ ((ℓ + 1) * M) < 1 := by
        rw [hs']; exact pow_lt_one₀ hε.le hpK (by omega)
      exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hb0.ne').mp this
    have hsB : t ^ ℓ < ‖s‖ ^ (ℓ + 1) := by
      have : (t ^ ℓ) ^ M < (‖s‖ ^ (ℓ + 1)) ^ M := by
        rw [← pow_mul, ← pow_mul, hs']
        exact pow_lt_pow_right_of_lt_one₀ hε hpK (by omega)
      exact (pow_lt_pow_iff_left₀ (pow_nonneg hε.le _) (pow_nonneg (norm_nonneg _) _)
        (by omega)).mp this
    -- step (K)
    set b : ℕ → MvPolynomial (Fin 2) K := fun i => MvPolynomial.map φ (a i) with hbdef
    have hbB : ∀ i, b i ∈ katzPiece φ (Bz ℓ hℓ 0) i := by
      intro i
      have hai : a i ∈ Kpiece ℓ hℓ i := Submodule.smul_mem _ _ (hc i)
      rw [mem_Kpiece] at hai
      simp only [hbdef]
      have has := (a i).as_sum
      rw [has, map_sum]
      refine Submodule.sum_mem _ fun d hd => ?_
      rw [map_monomial, show monomial d (φ ((a i).coeff d)) = φ ((a i).coeff d) • monomial d 1 by
        rw [smul_monomial, smul_eq_mul, mul_one]]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨monomial d 1, ⟨d, ?_, rfl⟩, ?_⟩)
      · rw [zero_add]; exact hai (Finset.mem_coe.mpr hd)
      · rw [map_monomial, map_one]
    have hb_zero : ∀ i, n < i → b i = 0 := fun i hi => by
      simp only [hbdef, ha, hc0 i hi, smul_zero, map_zero]
    have hdec : Tendsto (fun i => gnorm (b i) / ‖s‖ ^ i) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop n] with i hi
      rw [hb_zero i hi]; simp [gnorm]
    have hK := (katz_iff_hasse' φ hφ hpK hℓ 0 s hs0 hs1 b hbB hdec).mpr (by
      intro W hW hsW
      set Ev := eval (pt W) (Eh φ hℓ) with hEv
      have hEv0 : Ev ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hsW; linarith
      have hBrk : UpContraction.Brk ℓ (Eh φ hℓ) W := by
        unfold UpContraction.Brk
        exact hsB.trans_le (pow_le_pow_left₀ hs0.le hsW _)
      set ψ : Poly ℓ →+* K := (eval (pt W)).comp (MvPolynomial.map φ) with hψ
      have hψA : ψ (hasseA ℓ hℓ) = Ev := rfl
      have hψb : ∀ i, eval (pt W) (b i) = ψ (a i) := fun i => rfl
      have hψa : ∀ i, ψ (a i) = (ℓ : K) ^ e * ψ (c i) := by
        intro i
        simp only [ha, smul_eq_C_mul, map_mul, hψ, RingHom.comp_apply, map_pow,
          map_natCast]
      have hval : kval (Eh φ hℓ) b (pt W) =
          (ℓ : K) ^ e * (ψ P - (ℓ : K) ^ (N0 + n) * ψ P') / Ev ^ n := by
        unfold kval
        rw [tsum_eq_sum (s := Finset.range (n + 1)) fun i hi => by
          rw [hb_zero i (by simpa using hi), map_zero, zero_div]]
        have hPψ : ψ P = ∑ m ∈ Finset.range (n + 1), Ev ^ (n - m) * ψ (c m) +
            (ℓ : K) ^ (N0 + n) * ψ P' := by
          conv_lhs => rw [hPe]
          rw [map_add, map_sum, smul_eq_C_mul, map_mul]
          simp only [map_mul, map_pow, hψA]
          congr 1
          simp [hψ]
        rw [hPψ, add_sub_cancel_right, Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [hψb, hψa, ← Nat.sub_add_cancel hi', pow_add, Nat.add_sub_cancel, ← hEv]
        field_simp
      rw [hval, norm_div, norm_pow, div_le_one (pow_pos (norm_pos_iff.mpr hEv0) _), norm_mul,
        norm_pow]
      have hte : 0 ≤ t ^ e := pow_nonneg hε.le _
      refine (mul_le_mul_of_nonneg_left (show ‖ψ P - (ℓ : K) ^ (N0 + n) * ψ P'‖ ≤
          max ‖ψ P‖ ‖(ℓ : K) ^ (N0 + n) * ψ P'‖ by
        rw [sub_eq_add_neg, ← norm_neg ((ℓ : K) ^ (N0 + n) * ψ P')]
        exact IsUltrametricDist.norm_add_le_max _ _) hte).trans ?_
      rw [mul_max_of_nonneg _ _ hte]
      refine max_le ?_ ?_
      · exact hpt W hW hBrk
      · rw [norm_mul, norm_pow]
        have h1 := norm_map_eval_le_one φ hφ hW P'
        have h2 := le_of_brk hℓ φ hφ hε hW hBrk
        have a1 : t ^ e ≤ 1 := pow_le_one₀ hε.le hpK.le
        have a2 : t ^ (N0 + n) ≤ t ^ n := pow_le_pow_of_le_one hε.le hpK.le (by omega)
        calc t ^ e * (t ^ (N0 + n) * ‖ψ P'‖) ≤ 1 * (t ^ n * 1) :=
              mul_le_mul a1 (mul_le_mul a2 h1 (norm_nonneg _) (pow_nonneg hε.le _))
                (by positivity) zero_le_one
          _ ≤ ‖Ev‖ ^ n := by rw [one_mul, mul_one]; exact pow_le_pow_left₀ hε.le h2 _)
    -- extract the coefficient
    have hc1 : ‖φ ((a m).coeff d)‖ ≤ ‖s‖ ^ m := by
      have := (norm_coeff_le_gnorm (b m) d).trans (hK m)
      simpa [hbdef, coeff_map] using this
    calc ‖φ ((a m).coeff d)‖ ^ ((ℓ + 1) * M) ≤ (‖s‖ ^ m) ^ ((ℓ + 1) * M) :=
          pow_le_pow_left₀ (norm_nonneg _) hc1 _
      _ = t ^ ((ℓ * M - 1) * m) := by rw [← pow_mul, mul_comm m, pow_mul, hs', ← pow_mul]

end Bridge

end SharpHQ
