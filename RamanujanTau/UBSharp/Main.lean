import RamanujanTau.UBSharp.Basic

/-!
# (UB) from the pointwise quotient bound

**`UB_of_quot`**: `QuotBound φ → UB ℓ hℓ`, for every prime `ℓ ≥ 5`, over any complete algebraically
closed ultrametric `K` with integral `φ : ℤ_[ℓ] →+* K` and `0 < ‖ℓ‖ < 1`.

Proof (no overconvergence of `U f` and no evaluation of infinite Katz series is needed):
fix the precision `N` and one radius `‖s‖^{(ℓ+1)M} = ‖ℓ‖^{ℓM−1}`, `M = 2(N+j+1)+1`, and `θ` with
`θ^ℓ = s^j`. Take `R = (j+1)ℓ^n` with `n = N + M`.

1. `f = b/E^j ≡ F := b·E^{R−j} (mod ℓ^{n+1})` and `U F ≡ T_ℓ F =: PT (mod ℓ^N)`; also
   `PT ≡ PT/E^R`. So `U f ≡ PT/E^R`, a *finite* Katz series `Σ_{m ≤ R} c_m/E^m` (`decompP`).
2. Pointwise, on `{‖E(W)‖ ≥ ‖s‖}` (inside the break region):
   `ℓ·PT(W) = Σ_C F(V_C)` (`QuotBound`, Hecke; `V_C` the Vélu-normalized quotients), with
   `‖b(V_C)‖^{12} ≤ ‖Δ(V_C)‖^{j(ℓ−1)}` (`norm_eval_pow_le`), and
   * `C ≠ H`: `(‖θ‖‖F(V_C)‖)^{12ℓ} ≤ ‖E(W)‖^{12ℓR}`, so `‖θ‖·‖F(V_C)‖ ≤ ‖E(W)‖^R`;
   * `C = H`: `‖b(V_H)‖ ≤ 1`, `‖E(V_H)‖ ≤ ρ‖E(W)‖` with `ρ^M ≤ ‖ℓ‖`, and `R − j ≥ Mj`, so the canonical
     term is `≤ ‖E(W)‖^R` as well. Raising `E` to the power `ℓ^n` makes the canonical term negligible on
     every closed sub-annulus of the break region; that is where the cancellation `ℓUf = Tr f − Vf` is
     replaced.
3. Step (K) (`katz_iff_hasse'`) at the radius `s` for `θℓc_m` gives `‖θ‖‖ℓ c_m‖ ≤ ‖s‖^m`, hence
   `ℓ^{u(m,j)} ∣ c_m` for `m < M` and `ℓ^N ∣ c_m` for `m ≥ M` (`dvd_of_radius_u`, `le_u`).
4. `Ap u (U f)`, and `DBound.isKatz_of_Ap` gives `UB`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UBSharp
open PowerSeries ModP AtkinOBrienFinal AtkinOBrien DBound HeckeQExp KatzForms Igusa Filter Topology

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-! ### the two real bounds -/

omit hℓp in
/-- the non-canonical terms. -/
lemma C_term {θn e sn X D h : ℝ} {j m' : ℕ} (hl : ℓ ≠ 0) (hθ0 : 0 ≤ θn) (hX0 : 0 ≤ X)
    (hD0 : 0 ≤ D) (hh0 : 0 ≤ h) (he0 : 0 ≤ e) (hθ : θn ^ ℓ = sn ^ j) (hsn0 : 0 ≤ sn)
    (hse : sn ≤ e) (hX : X ^ 12 ≤ D ^ (j * (ℓ - 1))) (hD : D ^ ℓ ≤ e ^ 12) (hh : h ≤ e) :
    θn * (X * h ^ m') ≤ e ^ (j + m') := by
  have hl12 : 12 * ℓ ≠ 0 := by omega
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) hl12).mp ?_
  calc (θn * (X * h ^ m')) ^ (12 * ℓ)
      = (θn ^ ℓ) ^ 12 * ((X ^ 12) ^ ℓ * (h ^ m') ^ (12 * ℓ)) := by
        ring
    _ ≤ (e ^ j) ^ 12 * (((D ^ ℓ) ^ (j * (ℓ - 1))) * (e ^ m') ^ (12 * ℓ)) := by
        rw [hθ]
        have hX' : (X ^ 12) ^ ℓ ≤ (D ^ ℓ) ^ (j * (ℓ - 1)) := by
          calc (X ^ 12) ^ ℓ ≤ (D ^ (j * (ℓ - 1))) ^ ℓ := pow_le_pow_left₀ (by positivity) hX ℓ
            _ = _ := by rw [← pow_mul, ← pow_mul, mul_comm]
        gcongr
    _ ≤ (e ^ j) ^ 12 * (((e ^ 12) ^ (j * (ℓ - 1))) * (e ^ m') ^ (12 * ℓ)) := by gcongr
    _ = (e ^ (j + m')) ^ (12 * ℓ) := by
        simp only [← pow_mul, ← pow_add]
        congr 1
        obtain ⟨r, rfl⟩ : ∃ r, ℓ = r + 1 := ⟨ℓ - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring

omit hℓp in
/-- the canonical term. -/
lemma H_term {t e σ h : ℝ} {M j m' : ℕ} (hl : 2 ≤ ℓ) (hM : 1 ≤ M) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hte : t ≤ e) (hσ0 : 0 < σ) (hσe : σ ≤ e ^ (ℓ + 1)) (hσM : σ ^ M = t ^ (ℓ * M - 1))
    (hh0 : 0 ≤ h) (hh : h * e ^ ℓ ≤ max (t ^ (ℓ - 1) * e ^ (ℓ + 1)) (t ^ ℓ))
    (hm' : M * j ≤ m') : h ^ m' ≤ e ^ (j + m') := by
  have he0 : 0 < e := ht0.trans_le hte
  set ρ := max (t ^ (ℓ - 1)) (t ^ ℓ / σ) with hρ
  have htσ : t ^ ℓ ≤ σ := by
    have : (t ^ ℓ) ^ M ≤ σ ^ M := by
      rw [hσM, ← pow_mul]
      exact pow_le_pow_of_le_one ht0.le ht1 (by omega)
    exact (pow_le_pow_iff_left₀ (by positivity) hσ0.le (by omega)).mp this
  have hρ0 : 0 ≤ ρ := le_max_of_le_left (by positivity)
  have hρ1 : ρ ≤ 1 := max_le (pow_le_one₀ ht0.le ht1) ((div_le_one hσ0).mpr htσ)
  have hρM : ρ ^ M ≤ t := by
    have hA : (t ^ (ℓ - 1)) ^ M ≤ t := by
      rw [← pow_mul]
      calc t ^ ((ℓ - 1) * M) ≤ t ^ 1 :=
            pow_le_pow_of_le_one ht0.le ht1 (Nat.mul_pos (by omega) (by omega))
        _ = t := pow_one t
    have hB : (t ^ ℓ / σ) ^ M ≤ t := by
      rw [div_pow, hσM, ← pow_mul, div_le_iff₀ (by positivity), ← pow_succ']
      have : 2 ≤ ℓ * M := by nlinarith
      exact le_of_eq (by congr 1; omega)
    rcases le_total (t ^ (ℓ - 1)) (t ^ ℓ / σ) with h | h
    · rw [hρ, max_eq_right h]; exact hB
    · rw [hρ, max_eq_left h]; exact hA
  have key : h ≤ ρ * e := by
    refine le_of_mul_le_mul_right ?_ (pow_pos he0 ℓ)
    refine hh.trans (max_le ?_ ?_)
    · rw [mul_assoc, ← pow_succ']
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · rw [mul_assoc, ← pow_succ']
      calc t ^ ℓ = t ^ ℓ / σ * σ := by rw [div_mul_cancel₀ _ hσ0.ne']
        _ ≤ ρ * e ^ (ℓ + 1) := mul_le_mul (le_max_right _ _) hσe hσ0.le hρ0
  calc h ^ m' ≤ (ρ * e) ^ m' := pow_le_pow_left₀ hh0 key _
    _ = ρ ^ m' * e ^ m' := mul_pow _ _ _
    _ ≤ ρ ^ (M * j) * e ^ m' :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hρ0 hρ1 hm') (by positivity)
    _ ≤ t ^ j * e ^ m' := by
        rw [pow_mul]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hρM _) (by positivity)
    _ ≤ e ^ j * e ^ m' :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0.le hte _) (by positivity)
    _ = e ^ (j + m') := by rw [pow_add]

/-! ### the main theorem -/

section Main
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **The `U`-column bound in approximation form**: `U(b/E^j)` has approximate Katz expansions with
`v_i ≥ u(i, j)`. -/
theorem Ap_U_of_quot [CompleteSpace K] [IsAlgClosed K] (φ : ℤ_[ℓ] →+* K)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖) (hpK : ‖(ℓ : K)‖ < 1)
    (hQ : QuotBound ℓ hℓ φ) (j : ℕ) {x : Poly ℓ} (hx : x ∈ Kpiece ℓ hℓ j) :
    Ap hℓ (fun i => (u ℓ i j).toNat) (BoylanWebb.U ℓ (ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j)) := by
  classical
  intro N
  set M := 2 * (N + j + 1) + 1 with hMdef
  have hM0 : 0 < M := by omega
  set n := N + M with hn
  set R := (j + 1) * ℓ ^ n with hR
  set m' := R - j with hm'
  set k := R * (ℓ - 1) with hk
  have hl2 : 2 ≤ ℓ := hℓp.out.two_le
  have hnl : n < ℓ ^ n := Nat.lt_pow_self (by omega)
  have hRl : ℓ ^ n ≤ R := Nat.le_mul_of_pos_left _ (by omega)
  have hm'M : M * j ≤ m' := by
    have : (j + 1) * (M + 1) ≤ R := Nat.mul_le_mul_left _ (by omega)
    have : M * j + j ≤ (j + 1) * (M + 1) := by nlinarith
    omega
  have hk1 : N + 1 ≤ k - 1 := by
    have : 4 * R ≤ k := by rw [hk, mul_comm 4 R]; exact Nat.mul_le_mul_left R (by omega)
    omega
  have hjm : j + m' = R := by omega
  have hF : Iso (x * hasseA ℓ hℓ ^ m') k := by
    refine iso_of_eq ((UBound.iso_of_Kpiece hℓ hx).mul ((iso_hasseA hℓ).pow m')) ?_
    rw [smul_eq_mul, hk, ← hjm]; ring
  obtain ⟨PT, hPT, hPTe⟩ := UBound.exists_hecke_Zp hℓ (by omega) hF
  /- step 1: `U f ≡ PT/E^R (mod ℓ^N)` -/
  have hEE : ∀ q, E ℓ hℓ ^ q * Einv ℓ hℓ ^ q = 1 := fun q => by
    rw [← mul_pow, E_mul_Einv, one_pow]
  have hER : Dvd (ℓ : ℤ_[ℓ]) N (E ℓ hℓ ^ R - 1) :=
    Dvd_mono (by omega) (UBound.Dvd_E_pow_sub_one hℓ n (j + 1))
  set Fs := ev ℤ_[ℓ] (x * hasseA ℓ hℓ ^ m') with hFs
  have h1 : Dvd (ℓ : ℤ_[ℓ]) N
      (BoylanWebb.U ℓ (ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j) - BoylanWebb.U ℓ Fs) := by
    rw [← BoylanWebb.U_sub]
    apply UBound.Dvd_U
    have e : ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j - Fs =
        -(ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j * (E ℓ hℓ ^ R - 1)) := by
      simp only [hFs, map_mul, map_pow, ev_hasseA_E hℓ]
      rw [← hjm, pow_add]
      linear_combination (ev ℤ_[ℓ] x * E ℓ hℓ ^ m') * hEE j
    rw [e]; exact UBound.Dvd_neg' (UBound.Dvd_mul_left' _ hER)
  have h2 : Dvd (ℓ : ℤ_[ℓ]) N (BoylanWebb.U ℓ Fs - ev ℤ_[ℓ] PT) := by
    rw [hPTe, Tq_eq ℓ (VLayer.ell_ne_zero' ℓ), ← UBound.U_eq_Up, sub_add_cancel_left]
    apply UBound.Dvd_neg'
    rw [mul_comm]
    refine UBound.Dvd_mul_left' _ ⟨(ℓ : ℤ_[ℓ]) ^ (k - 1 - N) • 1, ?_⟩
    rw [smul_smul, ← pow_add, show N + (k - 1 - N) = k - 1 by omega, smul_eq_C_mul, mul_one]
  have h3 : Dvd (ℓ : ℤ_[ℓ]) N (ev ℤ_[ℓ] PT - ev ℤ_[ℓ] PT * Einv ℓ hℓ ^ R) := by
    have e : ev ℤ_[ℓ] PT - ev ℤ_[ℓ] PT * Einv ℓ hℓ ^ R =
        ev ℤ_[ℓ] PT * Einv ℓ hℓ ^ R * (E ℓ hℓ ^ R - 1) := by
      linear_combination (-ev ℤ_[ℓ] PT) * hEE R
    rw [e]; exact UBound.Dvd_mul_left' _ hER
  /- the finite Katz decomposition of `PT/E^R` -/
  have hPT' : Iso PT (R * (ℓ - 1)) := hPT
  obtain ⟨c, P', hc, hc0, -, hPe⟩ := SharpHQ.decompP hℓ (N + R) R PT hPT'
  have key : ev ℤ_[ℓ] PT * Einv ℓ hℓ ^ R =
      ∑ m ∈ Finset.range (R + 1), ev ℤ_[ℓ] (c m) * Einv ℓ hℓ ^ m +
        (ℓ : ℤ_[ℓ]) ^ (N + R) • (ev ℤ_[ℓ] P' * Einv ℓ hℓ ^ R) := by
    have hs : ∑ m ∈ Finset.range (R + 1), ev ℤ_[ℓ] (hasseA ℓ hℓ ^ (R - m) * c m) *
        Einv ℓ hℓ ^ R = ∑ m ∈ Finset.range (R + 1), ev ℤ_[ℓ] (c m) * Einv ℓ hℓ ^ m := by
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [map_mul, map_pow, ev_hasseA_E, mul_comm (E ℓ hℓ ^ (R - m)), mul_assoc,
        E_pow_mul_Einv_pow hℓ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]
    conv_lhs => rw [hPe]
    rw [map_add, map_sum, add_mul, Finset.sum_mul, map_smul, smul_mul_assoc, hs]
  /- the radius `s` and `θ` -/
  set t := ‖(ℓ : K)‖ with ht
  have hb0 : 0 < (ℓ + 1) * M := by positivity
  have hlM : 2 ≤ ℓ * M := by nlinarith
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
  have hts : t ≤ ‖s‖ := by
    have : t ^ ((ℓ + 1) * M) ≤ ‖s‖ ^ ((ℓ + 1) * M) := by
      have : ℓ * M ≤ (ℓ + 1) * M := Nat.mul_le_mul_right _ (by omega)
      rw [hs']; exact pow_le_pow_of_le_one hε.le hpK.le (by omega)
    exact (pow_le_pow_iff_left₀ hε.le hs0.le hb0.ne').mp this
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_pow_nat_eq (s ^ j) hℓp.out.pos
  have hθ' : ‖θ‖ ^ ℓ = ‖s‖ ^ j := by rw [← norm_pow, hθ, norm_pow]
  have hθ1 : ‖θ‖ ≤ 1 := by
    have : ‖θ‖ ^ ℓ ≤ 1 := by rw [hθ']; exact pow_le_one₀ hs0.le hs1.le
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp this
  /- step (K) at the radius `s` -/
  set b : ℕ → MvPolynomial (Fin 2) K := fun i => θ • MvPolynomial.map φ ((ℓ : ℤ_[ℓ]) • c i)
    with hbdef
  have hbB : ∀ i, b i ∈ katzPiece φ (Bz ℓ hℓ 0) i := fun i =>
    Submodule.smul_mem _ θ (UBound.map_mem_katzPiece hℓ φ (Submodule.smul_mem _ _ (hc i)))
  have hb_zero : ∀ i, R < i → b i = 0 := fun i hi => by
    simp only [hbdef, hc0 i hi, smul_zero, map_zero]
  have hdec : Tendsto (fun i => gnorm (b i) / ‖s‖ ^ i) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop R] with i hi
    rw [hb_zero i hi]; simp [gnorm]
  have hK := (katz_iff_hasse' φ hφ hpK hℓ 0 s hs0 hs1 b hbB hdec).mpr (by
    intro W hW hsW
    set Ev := MvPolynomial.eval (pt W) (Eh φ hℓ) with hEv
    have hEv0 : 0 < ‖Ev‖ := hs0.trans_le hsW
    have hBrk : UpContraction.Brk ℓ (Eh φ hℓ) W := by
      unfold UpContraction.Brk
      exact hsB.trans_le (pow_le_pow_left₀ hs0.le hsW _)
    obtain ⟨V, hHk, hVint, hΔH, hΔC, hEH, hEC⟩ := hQ W hW hBrk
    have hsum := hHk k (x * hasseA ℓ hℓ ^ m') PT (by omega) hF hPT hPTe
    set ψ : Poly ℓ →+* K := (MvPolynomial.eval (pt W)).comp (MvPolynomial.map φ) with hψ
    have hψA : ψ (hasseA ℓ hℓ) = Ev := rfl
    have hψb : ∀ i, MvPolynomial.eval (pt W) (b i) = θ * ((ℓ : K) * ψ (c i)) := by
      intro i
      simp only [hbdef, MvPolynomial.smul_eval, hψ, RingHom.comp_apply]
      simp [MvPolynomial.smul_eval, Algebra.smul_def]
    have hval : kval (Eh φ hℓ) b (pt W) =
        θ * ((ℓ : K) * ψ PT - (ℓ : K) ^ (N + R + 1) * ψ P') / Ev ^ R := by
      unfold kval
      rw [tsum_eq_sum (s := Finset.range (R + 1)) fun i hi => by
        rw [hb_zero i (by simpa using hi), map_zero, zero_div]]
      have hPψ : ψ PT = ∑ m ∈ Finset.range (R + 1), Ev ^ (R - m) * ψ (c m) +
          (ℓ : K) ^ (N + R) * ψ P' := by
        conv_lhs => rw [hPe]
        rw [map_add, map_sum, MvPolynomial.smul_eq_C_mul, map_mul]
        simp only [map_mul, map_pow, hψA]
        congr 1
        simp [hψ]
      rw [hPψ, mul_add, pow_succ', mul_assoc (ℓ : K) ((ℓ : K) ^ (N + R)), add_sub_cancel_right,
        Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hEvne : Ev ≠ 0 := norm_pos_iff.mp hEv0
      rw [hψb, ← Nat.sub_add_cancel hi', pow_add, Nat.add_sub_cancel, ← hEv]
      field_simp
    -- the pointwise bound
    have hσM : (‖s‖ ^ (ℓ + 1)) ^ M = t ^ (ℓ * M - 1) := by rw [← pow_mul]; exact hs'
    have hσ : ‖s‖ ^ (ℓ + 1) ≤ ‖Ev‖ ^ (ℓ + 1) := pow_le_pow_left₀ hs0.le hsW _
    have hθPT : ‖θ‖ * ‖(ℓ : K) * ψ PT‖ ≤ ‖Ev‖ ^ R := by
      have hψPT : ψ PT = MvPolynomial.eval (pt W) (MvPolynomial.map φ PT) := rfl
      rw [hψPT, hsum, ← norm_mul, Finset.mul_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun C _ => ?_
      have hFe : MvPolynomial.eval (pt (V C)) (MvPolynomial.map φ (x * hasseA ℓ hℓ ^ m')) =
          MvPolynomial.eval (pt (V C)) (MvPolynomial.map φ x) *
            MvPolynomial.eval (pt (V C)) (Eh φ hℓ) ^ m' := by
        simp only [map_mul, map_pow]; rfl
      rw [hFe, norm_mul, norm_mul, norm_pow]
      have hX : ‖MvPolynomial.eval (pt (V C)) (MvPolynomial.map φ x)‖ ^ 12 ≤
          ‖(V C).Δ‖ ^ (j * (ℓ - 1)) :=
        norm_eval_pow_le (iso_map φ (UBound.iso_of_Kpiece hℓ hx))
          (fun d => by rw [MvPolynomial.coeff_map]; exact hφ _) (norm_nonneg _)
          (by simpa [pt] using (hVint C).1) (by simpa [pt] using (hVint C).2)
      rw [← hjm]
      cases C with
      | none =>
        have hD1 : ‖(V none).Δ‖ ≤ 1 := by
          have h12 : ‖(V none).Δ‖ * ‖Ev‖ ^ 12 ≤ 1 * ‖Ev‖ ^ 12 :=
            hΔH.trans (by rw [one_mul]; exact pow_le_pow_left₀ hε.le (hts.trans hsW) _)
          exact le_of_mul_le_mul_right h12 (pow_pos hEv0 _)
        have hX1 : ‖MvPolynomial.eval (pt (V none)) (MvPolynomial.map φ x)‖ ≤ 1 := by
          have : ‖MvPolynomial.eval (pt (V none)) (MvPolynomial.map φ x)‖ ^ 12 ≤ 1 :=
            hX.trans (pow_le_one₀ (norm_nonneg _) hD1)
          exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
        calc ‖θ‖ * (‖MvPolynomial.eval (pt (V none)) (MvPolynomial.map φ x)‖ *
              ‖MvPolynomial.eval (pt (V none)) (Eh φ hℓ)‖ ^ m')
            ≤ 1 * (1 * ‖MvPolynomial.eval (pt (V none)) (Eh φ hℓ)‖ ^ m') := by gcongr
          _ ≤ ‖Ev‖ ^ (j + m') := by
            rw [one_mul, one_mul]
            exact H_term hl2 (by omega) hε hpK.le (hts.trans hsW) (pow_pos hs0 _) hσ hσM
              (norm_nonneg _) hEH hm'M
      | some c =>
        exact C_term (by omega) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
          (norm_nonneg _) hθ' (norm_nonneg _) hsW hX (hΔC c) (hEC c)
    have hP'b : ‖θ‖ * ‖(ℓ : K) ^ (N + R + 1) * ψ P'‖ ≤ ‖Ev‖ ^ R := by
      rw [norm_mul, norm_pow]
      have h1' : ‖ψ P'‖ ≤ 1 := SharpHQ.norm_map_eval_le_one φ hφ hW P'
      have h2' : t ^ (N + R + 1) ≤ t ^ R := pow_le_pow_of_le_one hε.le hpK.le (by omega)
      have h3' : t ^ R ≤ ‖Ev‖ ^ R := pow_le_pow_left₀ hε.le (hts.trans hsW) _
      calc ‖θ‖ * (t ^ (N + R + 1) * ‖ψ P'‖) ≤ 1 * (t ^ R * 1) :=
            mul_le_mul hθ1 (mul_le_mul h2' h1' (norm_nonneg _) (by positivity)) (by positivity)
              zero_le_one
        _ ≤ ‖Ev‖ ^ R := by rw [one_mul, mul_one]; exact h3'
    rw [hval, norm_div, norm_pow, div_le_one (pow_pos hEv0 _), norm_mul]
    refine (mul_le_mul_of_nonneg_left (show ‖(ℓ : K) * ψ PT - (ℓ : K) ^ (N + R + 1) * ψ P'‖ ≤
        max ‖(ℓ : K) * ψ PT‖ ‖(ℓ : K) ^ (N + R + 1) * ψ P'‖ by
      rw [sub_eq_add_neg, ← norm_neg ((ℓ : K) ^ (N + R + 1) * ψ P')]
      exact IsUltrametricDist.norm_add_le_max _ _) (norm_nonneg θ)).trans ?_
    rw [mul_max_of_nonneg _ _ (norm_nonneg θ)]
    exact max_le hθPT hP'b)
  /- the coefficients -/
  have hcoef : ∀ m d, ‖θ‖ * ‖φ ((ℓ : ℤ_[ℓ]) * (c m).coeff d)‖ ≤ ‖s‖ ^ m := by
    intro m d
    have := (norm_coeff_le_gnorm (b m) d).trans (hK m)
    simp only [hbdef, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul,
      norm_mul] at this
    exact this
  have hdiv : ∀ m d, (ℓ : ℤ_[ℓ]) ^ (u ℓ (min m (M - 1)) j).toNat ∣ (c m).coeff d := fun m d =>
    dvd_of_radius_u φ hφ hε hpK hM0 hs' hθ' _ (hcoef m d)
  /- the output -/
  refine ⟨R + 1, fun m => if m < M then c m else 0, fun m => ?_, ?_, fun m => ?_⟩
  · dsimp only
    split_ifs
    · exact hc m
    · exact Submodule.zero_mem _
  · unfold Approx
    have hdrop : Dvd (ℓ : ℤ_[ℓ]) N
        (∑ m ∈ Finset.range (R + 1), ev ℤ_[ℓ] (c m) * Einv ℓ hℓ ^ m -
          ∑ m ∈ Finset.range (R + 1), ev ℤ_[ℓ] (if m < M then c m else 0) * Einv ℓ hℓ ^ m) := by
      rw [← Finset.sum_sub_distrib]
      refine Dvd.sum _ _ fun m _ => ?_
      split_ifs with hm
      · rw [sub_self]; exact Dvd_zero _
      · rw [map_zero, zero_mul, sub_zero]
        have hmin : min m (M - 1) = 2 * (N + j + 1) := by omega
        have hcm : Dvd (ℓ : ℤ_[ℓ]) N (c m) := Poly_Dvd_of_coeff _ fun d => Dvd_iff_dvd.mpr
          ((pow_dvd_pow _ (le_u N j)).trans (by rw [← hmin]; exact hdiv m d))
        obtain ⟨z, hz⟩ := hcm
        exact ⟨ev ℤ_[ℓ] z * Einv ℓ hℓ ^ m, by rw [hz, map_smul, smul_mul_assoc]⟩
    have h4 : Dvd (ℓ : ℤ_[ℓ]) N ((ℓ : ℤ_[ℓ]) ^ (N + R) • (ev ℤ_[ℓ] P' * Einv ℓ hℓ ^ R)) :=
      ⟨(ℓ : ℤ_[ℓ]) ^ R • (ev ℤ_[ℓ] P' * Einv ℓ hℓ ^ R), by rw [smul_smul, ← pow_add]⟩
    have := Dvd_add (Dvd_add (Dvd_add (Dvd_add h1 h2) h3) hdrop) h4
    convert this using 1
    rw [key]
    abel
  · dsimp only
    split_ifs with hm
    · refine Poly_Dvd_of_coeff _ fun d => Dvd_iff_dvd.mpr ?_
      have := hdiv m d
      rwa [min_eq_left (by omega)] at this
    · exact Dvd_zero _

/-- **(UB) from the pointwise quotient bound**, every prime `ℓ ≥ 5`. -/
theorem UB_of_quot [CompleteSpace K] [IsAlgClosed K] (φ : ℤ_[ℓ] →+* K)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖) (hpK : ‖(ℓ : K)‖ < 1)
    (hQ : QuotBound ℓ hℓ φ) : UB ℓ hℓ := by
  intro j x hx
  obtain ⟨c, hc, hd⟩ := isKatz_of_Ap (Ap_U_of_quot hℓ φ hφ hε hpK hQ j hx)
  exact ⟨c, hc, hd⟩

end Main

end UBSharp
