import RamanujanTau.ThetaLift.KernelFold
import RamanujanTau.ThetaLift.AbstractForm

/-!
# The double sum as a `q`-series

When `N` is squarefree, the sum over `x` is supported on the multiples of `N`, and grouping the double sum by
divisors gives the coefficients of the lift.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex
open UpperHalfPlane hiding I
open scoped Real ComplexConjugate MatrixGroups

noncomputable section

variable {k' : ℤ} (G : CuspForm 𝒮ℒ k') (j : ℕ) {N : ℕ} (A : ℕ → ℤ)

/-- The index `(Ne² + j)/24`. -/
def latI (j N e : ℕ) : ℕ := (N * e ^ 2 + j) / 24

/-- The value of `cX` at a multiple of `N`. -/
lemma cX_mul (hN : 0 < N) (hjN : 24 ∣ N + j) (hA : ∀ m, cA G j m = ((A m : ℤ) : ℂ)) {e : ℕ}
    (hχ : chiZ (e : ℤ) ≠ 0) :
    cX G j N ((N : ℤ) * e) = ((A (latI j N e) : ℤ) : ℂ) := by
  classical
  have hNZ : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨u, hu⟩ := sq_sub_one_of_chi (e : ℤ) hχ
  obtain ⟨w, hw⟩ := hjN
  have hdiv : 24 * latI j N e = N * e ^ 2 + j := by
    unfold latI
    apply Nat.mul_div_cancel'
    have h1 : ((24 : ℤ)) ∣ (N : ℤ) * e ^ 2 + j := by
      refine ⟨N * u + w, ?_⟩
      have hw' : (N : ℤ) + j = 24 * w := by exact_mod_cast hw
      linear_combination (N : ℤ) * hu + hw'
    exact_mod_cast h1
  have hsq : ((N : ℤ) * e) ^ 2 = (N : ℤ) * (24 * (latI j N e : ℤ) - j) := by
    have h2 : (24 : ℤ) * (latI j N e : ℤ) = N * e ^ 2 + j := by exact_mod_cast hdiv
    rw [h2]
    ring
  have hex : ∃ m : ℕ, ((N : ℤ) * e) ^ 2 = (N : ℤ) * (24 * m - j) := ⟨_, hsq⟩
  have huniq : hex.choose = latI j N e := by
    have h2 := hex.choose_spec
    have h3 := mul_left_cancel₀ hNZ (h2.symm.trans hsq)
    have h4 : (hex.choose : ℤ) = latI j N e := by linarith
    exact_mod_cast h4
  unfold cX
  rw [dif_pos hex, huniq, hA]
  simp

/-- A nonzero term of the sum in `x` has `N ∣ x`. -/
lemma dvd_of_lTerm (hsf : Squarefree N) {ξ y : ℝ} {g x : ℤ} (h : lTerm G j (N := N) ξ y g x ≠ 0) :
    (N : ℤ) ∣ x := by
  classical
  have h1 : cX G j N x ≠ 0 := by
    intro h0
    apply h
    simp [lTerm, h0]
  have hex : ∃ m : ℕ, x ^ 2 = (N : ℤ) * (24 * m - j) := by
    by_contra hc
    apply h1
    simp [cX, dif_neg hc]
  obtain ⟨m, hm⟩ := hex
  have hd : (N : ℤ) ∣ x ^ 2 := ⟨_, hm⟩
  have hsfZ : Squarefree (N : ℤ) := Int.squarefree_natCast.mpr hsf
  exact (hsfZ.dvd_pow_iff_dvd (by norm_num)).mp hd

/-- The chosen power. -/
def qN (N : ℕ) (ξ y : ℝ) : ℂ := cexp (2 * π * I * N * ((ξ : ℂ) + y * I))

/-- The term at a multiple of `N`. -/
lemma lTerm_mul (hN : 0 < N) (hjN : 24 ∣ N + j) (hA : ∀ m, cA G j m = ((A m : ℤ) : ℂ)) (ξ y : ℝ)
    (g e : ℕ) :
    lTerm G j (N := N) ξ y (g : ℤ) ((N : ℤ) * e) =
      (chiZ (N : ℤ) : ℂ) * ((chiZ (e : ℤ) : ℂ) * ((A (latI j N e) : ℤ) : ℂ) * qN N ξ y ^ (g * e)) := by
  by_cases hχ : chiZ (e : ℤ) = 0
  · simp [lTerm, chiZ_mul, hχ]
  unfold lTerm
  rw [chiZ_mul, cX_mul G j A hN hjN hA hχ]
  have e1 : cexp (2 * π * I * (((N : ℤ) * (e : ℤ) : ℤ) : ℂ) * ((g : ℤ) : ℂ) * ((ξ : ℂ) + y * I)) =
      qN N ξ y ^ (g * e) := by
    unfold qN
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e1]
  push_cast
  ring

/-- **The sum over `x` is a sum over multiples of `N`.** -/
theorem tsum_lTerm (hN : 0 < N) (hsf : Squarefree N) (hjN : 24 ∣ N + j)
    (hA : ∀ m, cA G j m = ((A m : ℤ) : ℂ)) (ξ y : ℝ) (g : ℕ) :
    ∑' m : ℕ, lTerm G j (N := N) ξ y (g : ℤ) ((m : ℤ) + 1) =
      (chiZ (N : ℤ) : ℂ) * ∑' e : ℕ, (chiZ ((e + 1 : ℕ) : ℤ) : ℂ) *
        ((A (latI j N (e + 1)) : ℤ) : ℂ) * qN N ξ y ^ (g * (e + 1)) := by
  have hNpos : 1 ≤ N := hN
  let φ : ℕ → ℕ := fun e => N * (e + 1) - 1
  have hφ : ∀ e : ℕ, ((φ e : ℤ) + 1) = (N : ℤ) * ((e + 1 : ℕ) : ℤ) := by
    intro e
    have h1 : 1 ≤ N * (e + 1) := Nat.mul_pos hN (by omega)
    simp only [φ]
    push_cast [Nat.cast_sub h1]
    ring
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 := hφ a
    have h2 := hφ b
    rw [hab, h2] at h1
    have hNZ : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
    have := mul_left_cancel₀ hNZ h1
    have h3 : ((a + 1 : ℕ) : ℤ) = ((b + 1 : ℕ) : ℤ) := this.symm
    have h4 : a + 1 = b + 1 := by exact_mod_cast h3
    omega
  have hsupp : Function.support (fun m : ℕ => lTerm G j (N := N) ξ y (g : ℤ) ((m : ℤ) + 1)) ⊆
      Set.range φ := by
    intro m hm
    obtain ⟨d, hd⟩ := dvd_of_lTerm G j hsf hm
    have hdpos : 0 < d := by
      have h1 : (0 : ℤ) < (N : ℤ) * d := by rw [← hd]; omega
      have hNp : (0 : ℤ) < N := by exact_mod_cast hN
      exact (mul_pos_iff_of_pos_left hNp).mp h1
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = ((e + 1 : ℕ) : ℤ) := ⟨(d - 1).toNat, by push_cast; omega⟩
    refine ⟨e, ?_⟩
    have h2 := hφ e
    rw [← hd] at h2
    have : (φ e : ℤ) = m := by linarith
    exact_mod_cast this
  rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
  refine tsum_congr fun e => ?_
  simp only [hφ]
  exact lTerm_mul G j A hN hjN hA ξ y g (e + 1)

/-- The coefficient attached to a factorization. -/
def eT (lam N j : ℕ) (A : ℕ → ℤ) (x : ℕ × ℕ) : ℂ :=
  jN N x.1 * ((x.1 : ℂ) ^ (lam - 1) * ((chiZ (x.2 : ℤ) : ℂ) * ((A (latI j N x.2) : ℤ) : ℂ)))

/-- The coefficient of the lift. -/
def bC (lam N j : ℕ) (A : ℕ → ℤ) (n : ℕ) : ℂ := ∑ x ∈ n.divisorsAntidiagonal, eT lam N j A x

lemma card_antidiag_le (n : ℕ) : n.divisorsAntidiagonal.card ≤ n := by
  rw [← Nat.map_div_right_divisors, Finset.card_map]
  exact Nat.card_divisors_le_self n

variable {A}

/-- **The polynomial bound on the coefficients of the lift.** -/
theorem sum_bound {lam : ℕ} (hlam : lam ≠ 0) {C : ℝ} {E : ℕ}
    (hAb : ∀ m : ℕ, ‖((A m : ℤ) : ℂ)‖ ≤ C * ((m : ℝ) + 1) ^ E) (N j : ℕ) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ n : ℕ, 1 ≤ n →
      ∑ x ∈ n.divisorsAntidiagonal, ‖eT lam N j A x‖ ≤ Cb * (n : ℝ) ^ (lam + 2 * E) := by
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hAb 0)
    simpa using h
  refine ⟨C * ((N : ℝ) + j + 1) ^ E, by positivity, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set W : ℝ := C * ((N : ℝ) + j + 1) ^ E * (n : ℝ) ^ (lam - 1 + 2 * E) with hW
  have hW0 : 0 ≤ W := by positivity
  have hterm : ∀ x ∈ n.divisorsAntidiagonal, ‖eT lam N j A x‖ ≤ W := by
    intro x hx
    obtain ⟨hx1, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have h1le : x.1 ≤ n := Nat.le_of_dvd hn ⟨x.2, hx1.symm⟩
    have h2le : x.2 ≤ n := Nat.le_of_dvd hn ⟨x.1, by rw [mul_comm]; exact hx1.symm⟩
    have h1R : (x.1 : ℝ) ≤ n := by exact_mod_cast h1le
    have h2R : (x.2 : ℝ) ≤ n := by exact_mod_cast h2le
    have hlat : (latI j N x.2 : ℝ) + 1 ≤ ((N : ℝ) + j + 1) * (n : ℝ) ^ 2 := by
      have h3 : latI j N x.2 ≤ N * x.2 ^ 2 + j := Nat.div_le_self _ _
      have h4 : (latI j N x.2 : ℝ) ≤ N * (x.2 : ℝ) ^ 2 + j := by exact_mod_cast h3
      have h5 : (x.2 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by gcongr
      have h6 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hnR
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    unfold eT
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    have hjn := norm_jN_le N (x.1 : ℤ)
    have hχ : ‖((chiZ (x.2 : ℤ) : ℤ) : ℂ)‖ ≤ 1 := KData.chiZ_norm _
    have hA1 := hAb (latI j N x.2)
    calc _ ≤ 1 * ((n : ℝ) ^ (lam - 1) * (1 * (C * (((N : ℝ) + j + 1) * (n : ℝ) ^ 2) ^ E))) := by
          gcongr
          exact hA1.trans (by gcongr)
      _ = _ := by
        rw [hW, mul_pow, ← pow_mul, pow_add]
        ring
  have hcard : (n.divisorsAntidiagonal.card : ℝ) ≤ n := by exact_mod_cast card_antidiag_le n
  calc _ ≤ n.divisorsAntidiagonal.card • W := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = n.divisorsAntidiagonal.card * W := nsmul_eq_mul _ _
    _ ≤ n * W := by gcongr
    _ = _ := by
      rw [hW]
      have hl : lam + 2 * E = (lam - 1 + 2 * E) + 1 := by omega
      rw [hl, pow_succ]
      ring

lemma norm_qN (N : ℕ) (ξ y : ℝ) : ‖qN N ξ y‖ = Real.exp (-(2 * π * N * y)) := by
  unfold qN
  rw [Complex.norm_exp]
  congr 1
  have e : 2 * (π : ℂ) * I * N * ((ξ : ℂ) + y * I) =
      ((-(2 * π * N * y) : ℝ) : ℂ) + ((2 * π * N * ξ : ℝ) : ℂ) * I := by
    push_cast
    linear_combination (2 * (π : ℂ) * N * y) * Complex.I_sq
  rw [e]
  simp

/-- The norm of the power is less than one. -/
lemma norm_qN_lt (hN : 0 < N) {y : ℝ} (hy : 0 < y) (ξ : ℝ) : ‖qN N ξ y‖ < 1 := by
  rw [norm_qN]
  apply Real.exp_lt_one_iff.mpr
  have hπ := Real.pi_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have : 0 < 2 * π * N * y := by positivity
  linarith

/-- **The double sum is the series of the lift.** -/
theorem lamSum_eq {lam : ℕ} (hlam : lam ≠ 0) (hN : 0 < N) (hsf : Squarefree N) (hjN : 24 ∣ N + j)
    (hA : ∀ m, cA G j m = ((A m : ℤ) : ℂ)) {C : ℝ} {E : ℕ}
    (hAb : ∀ m : ℕ, ‖((A m : ℤ) : ℂ)‖ ≤ C * ((m : ℝ) + 1) ^ E) (ξ : ℝ) {y : ℝ} (hy : 0 < y) :
    lamSum G j (N := N) (jN N) lam ξ y =
      (chiZ (N : ℤ) : ℂ) * ∑' n : ℕ, bC lam N j A n * qN N ξ y ^ n := by
  obtain ⟨Cb, hCb0, hCb⟩ := sum_bound (A := A) hlam hAb N j
  set Q := qN N ξ y with hQ
  have hQ1 : ‖Q‖ < 1 := norm_qN_lt hN hy ξ
  set K' := lam + 2 * E with hK'
  have hgeo : Summable fun n : ℕ => Cb * ((n : ℝ) ^ K' * ‖Q‖ ^ n) :=
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) K' (r := ‖Q‖)
      (by rwa [Real.norm_of_nonneg (norm_nonneg Q)])).mul_left Cb
  -- the sum over the sigma type
  let Dσ : (Σ n : ℕ+, Nat.divisorsAntidiagonal n) → ℂ := fun s => eT lam N j A s.2.1 * Q ^ (s.1 : ℕ)
  have hDσ : Summable Dσ := by
    refine Summable.of_norm ?_
    refine (summable_sigma_of_nonneg fun _ => norm_nonneg _).mpr ⟨fun n => ?_, ?_⟩
    · exact (hasSum_fintype _).summable
    · have hb : ∀ n : ℕ+, ∑' x : Nat.divisorsAntidiagonal n, ‖Dσ ⟨n, x⟩‖ ≤
          Cb * (((n : ℕ) : ℝ) ^ K' * ‖Q‖ ^ (n : ℕ)) := by
        intro n
        have e : ∑' x : Nat.divisorsAntidiagonal n, ‖Dσ ⟨n, x⟩‖ =
            (∑ x ∈ (n : ℕ).divisorsAntidiagonal, ‖eT lam N j A x‖) * ‖Q‖ ^ (n : ℕ) := by
          rw [Finset.sum_mul, ← Finset.tsum_subtype]
          refine tsum_congr fun x => ?_
          simp only [Dσ, norm_mul, norm_pow]
        rw [e]
        have := hCb n n.2
        have hq : 0 ≤ ‖Q‖ ^ (n : ℕ) := by positivity
        calc _ ≤ (Cb * ((n : ℕ) : ℝ) ^ K') * ‖Q‖ ^ (n : ℕ) := by gcongr
          _ = _ := by ring
      refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun _ => norm_nonneg _) hb ?_
      exact hgeo.comp_injective PNat.coe_injective
  let eqv := sigmaAntidiagonalEquivProd
  let D : ℕ+ × ℕ+ → ℂ := fun p => eT lam N j A ((p.1 : ℕ), (p.2 : ℕ)) * Q ^ ((p.1 : ℕ) * (p.2 : ℕ))
  have hDe : ∀ p, D p = Dσ (eqv.symm p) := fun p => rfl
  have hD : Summable D := by
    have := eqv.symm.summable_iff.mpr hDσ
    exact this.congr fun p => (hDe p).symm
  -- the double sum
  have hstep1 : lamSum G j (N := N) (jN N) lam ξ y =
      (chiZ (N : ℤ) : ℂ) * ∑' n : ℕ, ∑' e : ℕ, eT lam N j A (n + 1, e + 1) *
        Q ^ ((n + 1) * (e + 1)) := by
    unfold lamSum
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    have h1 := tsum_lTerm G j A hN hsf hjN hA ξ y (n + 1)
    have hc : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; rfl
    rw [hc, h1, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun e => ?_
    unfold eT
    push_cast
    ring
  rw [hstep1]
  congr 1
  have hstep2 : ∑' n : ℕ, ∑' e : ℕ, eT lam N j A (n + 1, e + 1) * Q ^ ((n + 1) * (e + 1)) =
      ∑' g : ℕ+, ∑' e : ℕ+, D (g, e) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun g : ℕ => ∑' e : ℕ+, eT lam N j A (g, (e : ℕ)) * Q ^ (g * (e : ℕ)))]
    refine tsum_congr fun n => ?_
    rw [tsum_pnat_eq_tsum_succ (f := fun e : ℕ => eT lam N j A (n + 1, e) * Q ^ ((n + 1) * e))]
  rw [hstep2, ← hD.tsum_prod' fun g => hD.prod_factor g]
  have hstep3 : ∑' p : ℕ+ × ℕ+, D p = ∑' s, Dσ s := by
    simp only [hDe]
    exact eqv.symm.tsum_eq Dσ
  rw [hstep3, hDσ.tsum_sigma']
  · have hinner : ∀ n : ℕ+, ∑' x : Nat.divisorsAntidiagonal n, Dσ ⟨n, x⟩ = bC lam N j A n * Q ^ (n : ℕ) := by
      intro n
      unfold bC
      rw [Finset.sum_mul, ← Finset.tsum_subtype]
    simp only [hinner]
    have hf0 : bC lam N j A 0 * Q ^ 0 = 0 := by simp [bC]
    have hsn : Summable fun n : ℕ => bC lam N j A n * Q ^ n := by
      refine Summable.of_norm_bounded_eventually_nat hgeo ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      rw [norm_mul, norm_pow]
      have h1 : ‖bC lam N j A n‖ ≤ Cb * (n : ℝ) ^ K' :=
        (norm_sum_le _ _).trans (hCb n hn)
      calc _ ≤ (Cb * (n : ℝ) ^ K') * ‖Q‖ ^ n := by gcongr
        _ = _ := by ring
    have hz := tsum_zero_pnat_eq_tsum_nat hsn
    rw [← hz, hf0, zero_add]
  · intro n
    exact (hasSum_fintype _).summable

end

end RamanujanTau.ThetaLift
