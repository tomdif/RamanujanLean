/-
# `SvStripA` step 1: complex closed forms of the local factors `ρ_p(a, s)` (unconditional)

With `x = p^{−s}`, `N_x(a) = Σ_j λ(p^{j+a})λ(p^j) x^j`, `D_x = N_x(0)` (`= DpC`, `NpC` of
`SelbergKey.Arith` at `x = p^{−s}`).  Using only `|λ(n)| ≤ C n^{11/40}` (`HafnerBridge.lam_bound`,
unconditional; **no Deligne**) the series converge absolutely for `‖x‖ p^{11/20} < 1`, i.e. for
`Re s > 11/20`.  There:

* `Nx_succ`: `N(a+1) = λ_{a+1} D − λ_a x N(1)` (Hecke);
* `Dx_mul_P`: `D(x)(1 − (λ²−1)x + (λ²−1)x² − x³) = 1 + x` (the formal identity `Dps_mul_P`, evaluated);
* `Dx_ne_zero`, and the closed forms (`Nx_div_Dx`):
  `N(a)/D = ρ_p(a, x) := rrK x μ_p a`, i.e. `1`, `λ_p/(1+x)`, `(λ_{a+2} − xλ_a)/(1+x)`;
* `rhoC_eq_rhoCF`: `rhoC m s = rhoCF m s := Π_{p^a∥m} ρ_p(a, p^{−s})` for `Re s > 11/20`.

The right-hand side `rhoCF` is a finite product of rational functions of `p^{−s}` with poles only
where `p^{−s} = −1`: it is the holomorphic continuation (`Holo.lean`).  Level 1.
-/
import RamanujanTau.SvStripA.Chol
import RamanujanTau.SelbergKeyDiag2.EvalC
import RamanujanTau.QFProof.Local

set_option autoImplicit false

namespace RamanujanTau.SvStripA

open Complex Finset PowerSeries
open RamanujanTau.HafnerBridge (lam lam_bound lam_one)
open RamanujanTau.SelbergKey (NpC DpC rhoC)
open RamanujanTau.SelbergKeyDiag2 (evC p_cpow_nat_mul evC_mul evC_one)

/-- `N_x(a) = Σ_j λ(p^{j+a})λ(p^j) x^j`. -/
noncomputable def Nx (p a : ℕ) (x : ℂ) : ℂ :=
  ∑' j : ℕ, ((lam (p ^ (j + a)) * lam (p ^ j) : ℝ) : ℂ) * x ^ j

/-- The terms of `N_x(a)`. -/
noncomputable def nt (p a : ℕ) (x : ℂ) (j : ℕ) : ℂ := ((lam (p ^ (j + a)) * lam (p ^ j) : ℝ) : ℂ) * x ^ j

lemma NpC_eq (p a : ℕ) (s : ℂ) : NpC p a s = Nx p a ((p : ℂ) ^ (-s)) := by
  unfold NpC Nx
  exact tsum_congr fun j => by rw [p_cpow_nat_mul]

lemma DpC_eq (p : ℕ) (s : ℂ) : DpC p s = Nx p 0 ((p : ℂ) ^ (-s)) := by
  unfold DpC Nx
  exact tsum_congr fun j => by rw [p_cpow_nat_mul, add_zero, sq]

/-! ### Absolute convergence for `‖x‖ p^{11/20} < 1` -/

lemma lam_pow_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, p.Prime → ∀ m : ℕ,
    |lam (p ^ m)| ≤ C * ((p : ℝ) ^ (11 / 40 : ℝ)) ^ m := by
  obtain ⟨C, hC1, hC⟩ := lam_bound
  refine ⟨C, hC1, fun p hp m => ?_⟩
  have h := hC (p ^ m) (Nat.one_le_pow _ _ hp.pos)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have e : (((p ^ m : ℕ) : ℝ)) ^ (11 / 40 : ℝ) = ((p : ℝ) ^ (11 / 40 : ℝ)) ^ m := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0, ← Real.rpow_mul hp0, mul_comm]
  rwa [e] at h

lemma norm_nt_le {C : ℝ} (hC1 : 1 ≤ C)
    (hC : ∀ p : ℕ, p.Prime → ∀ m : ℕ, |lam (p ^ m)| ≤ C * ((p : ℝ) ^ (11 / 40 : ℝ)) ^ m)
    {p : ℕ} (hp : p.Prime) (a : ℕ) (x : ℂ) (j : ℕ) :
    ‖nt p a x j‖ ≤ C ^ 2 * ((p : ℝ) ^ (11 / 40 : ℝ)) ^ a * (‖x‖ * (p : ℝ) ^ (11 / 20 : ℝ)) ^ j := by
  have hA : (0 : ℝ) ≤ (p : ℝ) ^ (11 / 40 : ℝ) := by positivity
  have hAA : (p : ℝ) ^ (11 / 20 : ℝ) = ((p : ℝ) ^ (11 / 40 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]; norm_num
  unfold nt
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, norm_pow]
  have h1 := hC p hp (j + a)
  have h2 := hC p hp j
  have hC0 : (0 : ℝ) ≤ C := by linarith
  calc |lam (p ^ (j + a))| * |lam (p ^ j)| * ‖x‖ ^ j
      ≤ (C * ((p : ℝ) ^ (11 / 40 : ℝ)) ^ (j + a)) * (C * ((p : ℝ) ^ (11 / 40 : ℝ)) ^ j) * ‖x‖ ^ j := by
        gcongr
    _ = _ := by rw [hAA, mul_pow, ← pow_mul, pow_add]; ring

lemma summable_nt {p : ℕ} (hp : p.Prime) (a : ℕ) {x : ℂ} (hx : ‖x‖ * (p : ℝ) ^ (11 / 20 : ℝ) < 1) :
    Summable fun j => ‖nt p a x j‖ := by
  obtain ⟨C, hC1, hC⟩ := lam_pow_bound
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_nt_le hC1 hC hp a x)
    ((summable_geometric_of_lt_one (by positivity) hx).mul_left _)

/-- `Re s > 11/20` gives `‖p^{−s}‖ p^{11/20} < 1`. -/
lemma norm_xs_lt {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 11 / 20 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ * (p : ℝ) ^ (11 / 20 : ℝ) < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [norm_natCast_cpow_of_pos hp.pos, ← Real.rpow_add (by linarith)]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by simp; linarith)

/-- `Re s > 0` gives `‖p^{−s}‖ < 1`. -/
lemma norm_xs_lt_one {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) : ‖(p : ℂ) ^ (-s)‖ < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [norm_natCast_cpow_of_pos hp.pos]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by simp; linarith)

lemma one_add_ne_zero {x : ℂ} (hx : ‖x‖ < 1) : 1 + x ≠ 0 := by
  intro h
  have : x = -1 := by linear_combination h
  rw [this, norm_neg, norm_one] at hx; exact lt_irrefl _ hx

/-! ### The Hecke recursion `N(a+1) = λ_{a+1} D − λ_a x N(1)` -/

theorem Nx_succ {p : ℕ} (hp : p.Prime) (a : ℕ) {x : ℂ} (hx : ‖x‖ * (p : ℝ) ^ (11 / 20 : ℝ) < 1) :
    Nx p (a + 1) x = (lam (p ^ (a + 1)) : ℂ) * Nx p 0 x - (lam (p ^ a) : ℂ) * x * Nx p 1 x := by
  have sN := (summable_nt hp (a + 1) hx).of_norm
  have sD := (summable_nt hp 0 hx).of_norm
  have sN1 := (summable_nt hp 1 hx).of_norm
  have e1 : Nx p (a + 1) x = ∑' j, nt p (a + 1) x j := rfl
  have e2 : Nx p 0 x = ∑' j, nt p 0 x j := rfl
  have e3 : Nx p 1 x = ∑' j, nt p 1 x j := rfl
  rw [e1, e2, e3, sN.tsum_eq_zero_add, sD.tsum_eq_zero_add]
  have sD' := (summable_nat_add_iff 1).2 sD
  have hterm : ∀ j : ℕ, nt p (a + 1) x (j + 1) =
      (lam (p ^ (a + 1)) : ℂ) * nt p 0 x (j + 1) - (lam (p ^ a) : ℂ) * x * nt p 1 x j := by
    intro j
    have hm := RamanujanTau.QFProof.lamp_mul hp a j
    unfold nt
    rw [show j + 1 + (a + 1) = a + j + 2 by ring, hm, pow_succ]
    push_cast
    ring
  rw [tsum_congr hterm, Summable.tsum_sub (sD'.mul_left _) (sN1.mul_left _), tsum_mul_left,
    tsum_mul_left]
  simp only [nt, pow_zero, zero_add, lam_one, add_zero, mul_one]
  push_cast
  ring

/-! ### `D(x) · P(x) = 1 + x` and `D ≠ 0` -/

lemma summable_coeff_Dps {p : ℕ} (hp : p.Prime) {x : ℂ} (hx : ‖x‖ * (p : ℝ) ^ (11 / 20 : ℝ) < 1) :
    Summable fun j : ℕ => ‖((coeff j (RamanujanTau.HafnerBridge2.Dps p) : ℝ) : ℂ) * x ^ j‖ := by
  refine (summable_nt hp 0 hx).congr fun j => ?_
  simp [nt, RamanujanTau.HafnerBridge2.Dps, sq]

lemma evC_Dps' (p : ℕ) (x : ℂ) : evC x (RamanujanTau.HafnerBridge2.Dps p) = Nx p 0 x := by
  unfold evC Nx
  exact tsum_congr fun j => by simp [RamanujanTau.HafnerBridge2.Dps, sq]

lemma coeff_Pps_eq (p j : ℕ) : coeff j (RamanujanTau.HafnerBridge2.Pps p) =
    if j = 0 then 1 else if j = 1 then -(lam p ^ 2 - 1) else if j = 2 then lam p ^ 2 - 1
      else if j = 3 then -1 else 0 := by
  unfold RamanujanTau.HafnerBridge2.Pps
  rw [map_sub, map_add, map_sub, coeff_C_mul, coeff_C_mul, coeff_X, coeff_X_pow, coeff_X_pow, coeff_one]
  rcases j with _ | _ | _ | _ | j <;> simp

lemma coeff_Pps_zero (p : ℕ) {j : ℕ} (hj : 4 ≤ j) : coeff j (RamanujanTau.HafnerBridge2.Pps p) = 0 := by
  rw [coeff_Pps_eq]
  simp [show j ≠ 0 by omega, show j ≠ 1 by omega, show j ≠ 2 by omega, show j ≠ 3 by omega]

lemma evC_Pps (p : ℕ) (x : ℂ) : evC x (RamanujanTau.HafnerBridge2.Pps p) =
    1 - (lam p ^ 2 - 1 : ℝ) * x + (lam p ^ 2 - 1 : ℝ) * x ^ 2 - x ^ 3 := by
  unfold evC
  rw [tsum_eq_sum (s := range 4) (fun j hj => by
    rw [coeff_Pps_zero p (by simp at hj; omega)]; simp)]
  simp only [sum_range_succ, sum_range_zero, coeff_Pps_eq]
  norm_num
  ring

lemma summable_Pps (p : ℕ) (x : ℂ) :
    Summable fun j : ℕ => ‖((coeff j (RamanujanTau.HafnerBridge2.Pps p) : ℝ) : ℂ) * x ^ j‖ :=
  summable_of_ne_finset_zero (s := range 4) fun j hj => by
    rw [coeff_Pps_zero p (by simp at hj; omega)]; simp

lemma evC_one_add_X (x : ℂ) : evC x (1 + PowerSeries.X) = 1 + x := by
  unfold evC
  rw [tsum_eq_sum (s := range 2) (fun j hj => by
    simp at hj
    rw [map_add, coeff_one, coeff_X, if_neg (by omega), if_neg (by omega)]; simp)]
  simp [sum_range_succ, coeff_one, coeff_X]

/-- **`D(x)(1 − (λ²−1)x + (λ²−1)x² − x³) = 1 + x`** for `‖x‖ p^{11/20} < 1` (no Deligne). -/
theorem Dx_mul_P {p : ℕ} (hp : p.Prime) {x : ℂ} (hx : ‖x‖ * (p : ℝ) ^ (11 / 20 : ℝ) < 1) :
    Nx p 0 x * (1 - (lam p ^ 2 - 1 : ℝ) * x + (lam p ^ 2 - 1 : ℝ) * x ^ 2 - x ^ 3) = 1 + x := by
  rw [← evC_Dps', ← evC_Pps, ← evC_mul' (summable_coeff_Dps hp hx) (summable_Pps p x),
    RamanujanTau.HafnerBridge2.Dps_mul_P hp, evC_one_add_X]
where
  evC_mul' {x : ℂ} {f g : PowerSeries ℝ}
      (hf : Summable fun j : ℕ => ‖((coeff j f : ℝ) : ℂ) * x ^ j‖)
      (hg : Summable fun j : ℕ => ‖((coeff j g : ℝ) : ℂ) * x ^ j‖) :
      evC x (f * g) = evC x f * evC x g := by
    unfold evC
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
    simp_rw [RamanujanTau.SelbergKeyDiag2.coeff_mul_xpowC]

theorem Dx_ne_zero {p : ℕ} (hp : p.Prime) {x : ℂ} (hx : ‖x‖ * (p : ℝ) ^ (11 / 20 : ℝ) < 1)
    (h1 : 1 + x ≠ 0) : Nx p 0 x ≠ 0 := by
  intro h
  have := Dx_mul_P hp hx
  rw [h, zero_mul] at this
  exact h1 this.symm

/-! ### Closed forms -/

/-- `μ_p(k) = λ(p^{k−1})`, `μ_p(0) = 0`, as complex numbers. -/
noncomputable def muC (p k : ℕ) : ℂ := if k = 0 then 0 else (lam (p ^ (k - 1)) : ℂ)

lemma muC_succ (p k : ℕ) : muC p (k + 1) = (lam (p ^ k) : ℂ) := by simp [muC]

lemma muC_zero (p : ℕ) : muC p 0 = 0 := by simp [muC]

lemma muC_one (p : ℕ) : muC p 1 = 1 := by simp [muC, lam_one]

lemma muC_rec {p : ℕ} (hp : p.Prime) (k : ℕ) :
    muC p (k + 2) = (lam p : ℂ) * muC p (k + 1) - muC p k := by
  rcases k with _ | k
  · simp [muC, lam_one]
  · rw [show k + 1 + 2 = (k + 2) + 1 by ring, muC_succ, show k + 1 + 1 = k + 2 by ring, muC_succ,
      muC_succ, RamanujanTau.QFProof.lamp_rec hp k, pow_one]
    push_cast; ring

/-- The closed-form local factor `ρ_p(a, x) = rrK x μ_p a`. -/
noncomputable def rhoPx (p a : ℕ) (x : ℂ) : ℂ := rrK x (muC p) a

lemma rhoPx_zero (p : ℕ) (x : ℂ) : rhoPx p 0 x = 1 := rrK_zero x (muC p)

lemma rhoPx_one (p : ℕ) (x : ℂ) : rhoPx p 1 x = (lam p : ℂ) / (1 + x) := by
  rw [rhoPx, rrK_succ, muC_succ, muC_zero, pow_one]; ring

lemma rhoPx_add_two (p a : ℕ) (x : ℂ) :
    rhoPx p (a + 2) x = ((lam (p ^ (a + 2)) : ℂ) - x * (lam (p ^ a) : ℂ)) / (1 + x) := by
  rw [rhoPx, show a + 2 = (a + 1) + 1 by ring, rrK_succ, show a + 1 + 2 = (a + 2) + 1 by ring,
    muC_succ, muC_succ]

/-- **Complex closed form**: `N_x(a) = ρ_p(a, x) D_x` for `‖x‖ p^{11/20} < 1`. -/
theorem Nx_eq_rhoPx_mul {p : ℕ} (hp : p.Prime) (a : ℕ) {x : ℂ}
    (hx : ‖x‖ * (p : ℝ) ^ (11 / 20 : ℝ) < 1) (h1 : 1 + x ≠ 0) :
    Nx p a x = rhoPx p a x * Nx p 0 x := by
  have hN1 : Nx p 1 x * (1 + x) = (lam p : ℂ) * Nx p 0 x := by
    have h := Nx_succ hp 0 hx
    simp only [zero_add, pow_one, pow_zero, lam_one] at h
    push_cast at h
    linear_combination h
  rcases a with _ | _ | a
  · rw [rhoPx_zero, one_mul]
  · rw [rhoPx_one]; field_simp; linear_combination hN1
  · rw [rhoPx_add_two]
    have h := Nx_succ hp (a + 1) hx
    have hr := RamanujanTau.QFProof.lamp_rec hp a
    rw [pow_one] at hr
    rw [show a + 1 + 1 = a + 2 by ring] at h
    field_simp
    rw [h]
    have hr' : (lam (p ^ (a + 2)) : ℂ) = (lam p : ℂ) * (lam (p ^ (a + 1)) : ℂ) - (lam (p ^ a) : ℂ) := by
      rw [hr]; push_cast; ring
    linear_combination (-(lam (p ^ (a + 1)) : ℂ) * x) * hN1 + (x * Nx p 0 x) * hr'

theorem Nx_div_Dx {p : ℕ} (hp : p.Prime) (a : ℕ) {x : ℂ}
    (hx : ‖x‖ * (p : ℝ) ^ (11 / 20 : ℝ) < 1) (h1 : 1 + x ≠ 0) :
    Nx p a x / Nx p 0 x = rhoPx p a x := by
  rw [Nx_eq_rhoPx_mul hp a hx h1, mul_div_assoc, div_self (Dx_ne_zero hp hx h1), mul_one]

/-- **`D_p(s) ≠ 0` and `N_p(a,s)/D_p(s) = ρ_p(a, p^{−s})` for `Re s > 11/20`.** -/
theorem NpC_div_DpC {p : ℕ} (hp : p.Prime) (a : ℕ) {s : ℂ} (hs : 11 / 20 < s.re) :
    DpC p s ≠ 0 ∧ NpC p a s / DpC p s = rhoPx p a ((p : ℂ) ^ (-s)) := by
  have hx := norm_xs_lt hp hs
  have h1 := one_add_ne_zero (norm_xs_lt_one hp (s := s) (by linarith))
  rw [NpC_eq, DpC_eq]
  exact ⟨Dx_ne_zero hp hx h1, Nx_div_Dx hp a hx h1⟩

/-- `ρ(m, s)` via the closed forms: `Π_{p^a∥m} ρ_p(a, p^{−s})`. -/
noncomputable def rhoCF (m : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ m.primeFactors, rhoPx p (m.factorization p) ((p : ℂ) ^ (-s))

/-- **`rhoC m s = rhoCF m s` for `Re s > 11/20`** (in particular on `Re s = 1`). -/
theorem rhoC_eq_rhoCF (m : ℕ) {s : ℂ} (hs : 11 / 20 < s.re) : rhoC m s = rhoCF m s := by
  unfold rhoC rhoCF
  exact prod_congr rfl fun p hp => (NpC_div_DpC (Nat.prime_of_mem_primeFactors hp) _ hs).2

/-! ### Uniform local bounds for `‖x‖ ≤ 3/5` (e.g. `p^{−s}`, `Re s ≥ 3/4`) -/

lemma norm_one_add_ge {x : ℂ} (hx : ‖x‖ ≤ 3 / 5) : 2 / 5 ≤ ‖1 + x‖ := by
  have := norm_sub_norm_le (1 : ℂ) (-x)
  rw [sub_neg_eq_add, norm_neg, norm_one] at this
  linarith

/-- `‖ρ_p(a, x)‖ ≤ (5/2)(|λ(p^a)| + |λ(p^{a−2})|)` for `‖x‖ ≤ 3/5`. -/
theorem norm_rhoPx_le (p a : ℕ) {x : ℂ} (hx : ‖x‖ ≤ 3 / 5) :
    ‖rhoPx p a x‖ ≤ 5 / 2 * (|lam (p ^ a)| + |lam (p ^ (a - 2))|) := by
  have h1 := norm_one_add_ge hx
  have hpos : (0 : ℝ) < ‖1 + x‖ := by linarith
  have hx1 : ‖x‖ ≤ 1 := by linarith
  rcases a with _ | _ | a
  · rw [rhoPx_zero]; simp [lam_one]; norm_num
  · rw [rhoPx_one, norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hpos]
    have : 0 ≤ |lam (p ^ (1 - 2))| := abs_nonneg _
    rw [pow_one]
    nlinarith [abs_nonneg (lam p)]
  · rw [rhoPx_add_two, norm_div, div_le_iff₀ hpos, show a + 2 - 2 = a by omega]
    have hn : ‖(lam (p ^ (a + 2)) : ℂ) - x * (lam (p ^ a) : ℂ)‖ ≤ |lam (p ^ (a + 2))| + |lam (p ^ a)| := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      gcongr
      exact mul_le_of_le_one_left (abs_nonneg _) hx1
    nlinarith [abs_nonneg (lam (p ^ (a + 2))), abs_nonneg (lam (p ^ a))]

/-- `‖W_e‖ ≤ 7(4 + ‖l‖²)‖x‖^e` for `‖x‖ ≤ 3/5`. -/
theorem norm_WcK_le (l : ℂ) {x : ℂ} (hx : ‖x‖ ≤ 3 / 5) (e : ℕ) :
    ‖WcK l x e‖ ≤ 7 * (4 + ‖l‖ ^ 2) * ‖x‖ ^ e := by
  have h1 := norm_one_add_ge hx
  have hpos : (0 : ℝ) < ‖1 + x‖ := by linarith
  have hx0 := norm_nonneg x
  have hq : ‖qqK l x‖ ≤ 4 + ‖l‖ ^ 2 := by
    unfold qqK
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_mul, norm_pow]
    have : ‖1 + x‖ ≤ 1 + ‖x‖ := by simpa using norm_add_le (1 : ℂ) x
    have h2 : ‖1 + x‖ ^ 2 ≤ (8 / 5) ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) (this.trans (by linarith : 1 + ‖x‖ ≤ 8 / 5)) 2
      exact this
    nlinarith [sq_nonneg ‖l‖]
  have hq0 := norm_nonneg (qqK l x)
  have hl0 : (0 : ℝ) ≤ 4 + ‖l‖ ^ 2 := by positivity
  match e with
  | 0 => simp [WcK]; nlinarith [sq_nonneg ‖l‖]
  | 1 =>
    simp only [WcK, norm_div, norm_mul, norm_pow, pow_one]
    rw [div_le_iff₀ (by positivity)]
    have : (2 / 5 : ℝ) ^ 2 ≤ ‖1 + x‖ ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
    have hxq : ‖x‖ * ‖qqK l x‖ ≤ ‖x‖ * (4 + ‖l‖ ^ 2) := mul_le_mul_of_nonneg_left hq hx0
    nlinarith [mul_nonneg hx0 hl0]
  | (e + 2) =>
    simp only [WcK, norm_div, norm_mul, norm_pow]
    have h1x : ‖1 - x‖ ≤ 8 / 5 := by
      refine (norm_sub_le _ _).trans ?_; rw [norm_one]; linarith
    rw [mul_div_assoc']
    rw [div_le_iff₀ hpos]
    have hxe : (0 : ℝ) ≤ ‖x‖ ^ (e + 2) := by positivity
    have hA : ‖1 - x‖ * ‖qqK l x‖ ≤ 8 / 5 * (4 + ‖l‖ ^ 2) :=
      mul_le_mul h1x hq hq0 (by norm_num)
    have := mul_le_mul_of_nonneg_left hA hxe
    nlinarith [mul_nonneg hxe hl0]

end RamanujanTau.SvStripA
