/-
# The key lemma: anti-periodic Appell–Lerch sums are exponentially small

For `Re α > 0`, `A > 0`, an anti-periodic coefficient sequence `c(n+T) = −c(n)` (`|c| ≤ 1`) and a `T`-periodic
`ω`, put

  `S = Σ_{n∈ℤ} c(n) e^{−α(An²+Bn)} / (1 − ω(n) e^{−α(Dn+E)})`.

If every denominator `1 − ω(n)e^{−α(DU+E)}` stays `≥ m > 0` for `U` in the strip `|Im U| ≤ Y₀` (`Y₀ > 0`), then

  `|S| ≤ (1/m) √(π/(A Re α)) e^{A Y₀² |α|²/Re α + B² Re α/(4A)} / sinh(π Y₀/T)`        (`al_sum_le`).

Proof: split `n = ρ + Tm` into residue classes; on each class `(−1)^m` turns the class sum into
`Σ_m kern_ρ(m)`, Poisson summation gives `Σ_ℓ 𝓕kern_ρ(ℓ)`, and the frequencies are effectively `ℓ − 1/2`, never
`0`. The Mordell-integral bound `fourier_kern_le`, on the line `Im = ∓Y₀/T`, gives `|𝓕kern_ρ(ℓ)| ≤ M e^{−πY₀|2ℓ−1|/T}`,
and `Σ_ℓ e^{−λ|2ℓ−1|} = 1/sinh λ`.

With the optimal `Y₀ = π Re(1/α)/(2TA)` the bound is `≍ e^{−π² Re(1/α)/(4AT²)}`: exactly the decay that cancels the
growth of the eta quotient at the cusp.
-/
import RamanujanTau.MockCusp.Kernel

set_option autoImplicit false

namespace MockCusp
open Complex Filter MeasureTheory Set Asymptotics
open scoped Topology Real FourierTransform

noncomputable section

/-! ### `Σ_ℓ e^{−λ|2ℓ−1|} = 1/sinh λ` -/

lemma hasSum_odd {lam : ℝ} (hl : 0 < lam) :
    HasSum (fun l : ℤ => Real.exp (-lam * |2 * (l : ℝ) - 1|))
      (2 * (Real.exp (-lam) * (1 - Real.exp (-(2 * lam)))⁻¹)) := by
  have hr0 : 0 ≤ Real.exp (-(2 * lam)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(2 * lam)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg : HasSum (fun n : ℕ => Real.exp (-lam) * Real.exp (-(2 * lam)) ^ n)
      (Real.exp (-lam) * (1 - Real.exp (-(2 * lam)))⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left _
  have e : ∀ n : ℕ, Real.exp (-lam) * Real.exp (-(2 * lam)) ^ n = Real.exp (-lam * (2 * n + 1)) := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  set g : ℤ → ℝ := fun l => Real.exp (-lam * |2 * (l : ℝ) - 1|)
  have h1 : HasSum (fun n : ℕ => g ((n : ℤ) + 1)) (Real.exp (-lam) * (1 - Real.exp (-(2 * lam)))⁻¹) := by
    refine hg.congr_fun fun n => ?_
    simp only [g, e]
    congr 2
    push_cast
    rw [abs_of_nonneg (by have := (n.cast_nonneg : (0 : ℝ) ≤ n); linarith)]; ring
  have h2 : HasSum (fun n : ℕ => g (-((n : ℤ) + 1) + 1)) (Real.exp (-lam) * (1 - Real.exp (-(2 * lam)))⁻¹) := by
    refine hg.congr_fun fun n => ?_
    simp only [g, e]
    congr 2
    push_cast
    rw [abs_of_nonpos (by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])]; ring
  have h3 : HasSum (fun l : ℤ => g (l + 1)) _ := HasSum.of_nat_of_neg_add_one h1 h2
  have h4 := ((Equiv.addRight (1 : ℤ)).hasSum_iff (f := g)).mp (by exact h3)
  rw [two_mul]
  exact h4

lemma odd_sum_eq {lam : ℝ} (hl : 0 < lam) :
    2 * (Real.exp (-lam) * (1 - Real.exp (-(2 * lam)))⁻¹) = 1 / Real.sinh lam := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-(2 * lam)) = Real.exp (-lam) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have h2 : Real.exp lam = (Real.exp (-lam))⁻¹ := by rw [Real.exp_neg, inv_inv]
  have hp := Real.exp_pos (-lam)
  have hlt : Real.exp (-lam) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [h1, h2]
  have h3 : 1 - Real.exp (-lam) ^ 2 ≠ 0 := by nlinarith
  have h4 : (Real.exp (-lam))⁻¹ - Real.exp (-lam) = (1 - Real.exp (-lam) ^ 2) / Real.exp (-lam) := by
    field_simp
  rw [h4]
  field_simp

/-! ### one residue class: Poisson summation and the Fourier bound -/

variable {α : ℂ} {A B D E : ℝ} {T : ℕ} {ρ : ℤ} {w : ℂ}

lemma kern_norm_le (hα : 0 < α.re) (hA : 0 < A) (hT : 0 < T) {m : ℝ} (hm : 0 < m) (x : ℝ)
    (hd : m ≤ ‖kD α D E T ρ w x‖) :
    ‖kern α A B D E T ρ w x‖ ≤ (1 / m) * Real.exp (-(A * α.re * T ^ 2) * (x - kx0 α A B T ρ 0) ^ 2 +
      (kC α A B T 0 + 2 * π * 0 * 0)) := by
  have h := norm_kG_le (B := B) hα hA hT hm 0 x 0 (by simpa using hd)
  simpa [kG] using h

theorem class_sum (hα : 0 < α.re) (hA : 0 < A) (hT : 0 < T) {m : ℝ} (hm : 0 < m) {y0 : ℝ} (hy0 : 0 < y0)
    (hden : ∀ x y' : ℝ, |y'| ≤ y0 → m ≤ ‖kD α D E T ρ w (x + y' * I)‖) :
    HasSum (fun k : ℤ => kern α A B D E T ρ w k) (∑' l : ℤ, 𝓕 (fun x : ℝ => kern α A B D E T ρ w x) l) ∧
    ‖∑' l : ℤ, 𝓕 (fun x : ℝ => kern α A B D E T ρ w x) l‖ ≤
      (1 / m) * (Real.exp (A * (T * y0) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A)) *
        √(π / (A * α.re * T ^ 2))) * (1 / Real.sinh (π * y0)) := by
  set f : ℝ → ℂ := fun x => kern α A B D E T ρ w x with hfdef
  set K0 : ℝ := A * (T * y0) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A)
  set Mc : ℝ := (1 / m) * (Real.exp K0 * √(π / (A * α.re * T ^ 2)))
  have hlam : 0 < π * y0 := by positivity
  have hne0 : ∀ x : ℝ, kD α D E T ρ w x ≠ 0 := fun x h => by
    have := hden x 0 (by simp [hy0.le]); simp [h] at this; linarith
  -- Fourier bound at integers
  have hF : ∀ l : ℤ, ‖𝓕 f l‖ ≤ Mc * Real.exp (-(π * y0) * |2 * (l : ℝ) - 1|) := by
    intro l
    rcases le_or_gt 1 l with hl | hl
    · have hb := fourier_kern_le (B := B) hα hA hT hm (-y0) (fun x y' hy' => hden x y' (by
        have := abs_le_of_mem_uIcc0 hy'; rwa [abs_neg, abs_of_pos hy0] at this)) l
      refine hb.trans (le_of_eq ?_)
      have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
      rw [abs_of_nonneg (by linarith)]
      simp only [Mc, K0, kC]
      rw [show A * (T * -y0) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A) - π * -y0 +
          2 * π * l * -y0 = (A * (T * y0) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A)) +
          (-(π * y0) * (2 * l - 1)) by ring, Real.exp_add]
      ring
    · have hb := fourier_kern_le (B := B) hα hA hT hm y0 (fun x y' hy' => hden x y' (by
        have := abs_le_of_mem_uIcc0 hy'; rwa [abs_of_pos hy0] at this)) l
      refine hb.trans (le_of_eq ?_)
      have hl' : (l : ℝ) ≤ 0 := by exact_mod_cast (by omega : l ≤ 0)
      rw [abs_of_nonpos (by linarith)]
      simp only [Mc, K0, kC]
      rw [show A * (T * y0) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A) - π * y0 +
          2 * π * l * y0 = (A * (T * y0) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A)) +
          (-(π * y0) * -(2 * l - 1)) by ring, Real.exp_add]
      ring
  have hsum := hasSum_odd hlam
  have hFs : Summable fun l : ℤ => 𝓕 f l :=
    Summable.of_norm_bounded (hsum.summable.mul_left Mc) hF
  -- continuity and decay of `f`
  have hcont : Continuous f := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    have h1 : ContinuousAt (kern α A B D E T ρ w) (x : ℂ) := by
      unfold kern
      exact (kE_cont.continuousAt.cexp).div kD_cont.continuousAt (hne0 x)
    exact h1.comp (by fun_prop)
  set P : ℝ := A * α.re * T ^ 2 with hPd
  have hP : 0 < P := by positivity
  set x0 := kx0 α A B T ρ 0 with hx0d
  set c0 := kC α A B T 0 + 2 * π * 0 * 0 with hc0d
  have hdecay : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
    have hq := cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (a := ((-P : ℝ) : ℂ))
      (by simp; linarith) ((2 * P * x0 : ℝ) : ℂ) (-2)
    refine IsBigO.trans ?_ hq.isBigO
    refine IsBigO.of_bound ((1 / m) * Real.exp (c0 - P * x0 ^ 2)) (Eventually.of_forall fun x => ?_)
    refine (kern_norm_le hα hA hT hm x (by simpa using hden x 0 (by simp [hy0.le]))).trans (le_of_eq ?_)
    rw [Complex.norm_exp]
    have : ((((-P : ℝ) : ℂ) * (x : ℂ) ^ 2 + ((2 * P * x0 : ℝ) : ℂ) * x)).re = -P * x ^ 2 + 2 * P * x0 * x := by
      simp [pow_two]
    rw [this, mul_assoc (1 / m), ← Real.exp_add]
    congr 2
    rw [hPd]; ring
  have hfsum : Summable fun k : ℤ => f k :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) (hdecay.comp_tendsto Int.tendsto_coe_cofinite)
  have hpois := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hcont one_lt_two hdecay hFs 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hpois
  refine ⟨?_, ?_⟩
  · have := hfsum.hasSum
    rw [hpois] at this
    exact this
  · refine (tsum_of_norm_bounded (hsum.mul_left Mc) hF).trans (le_of_eq ?_)
    rw [odd_sum_eq hlam]

/-! ### the anti-periodic Appell–Lerch sum -/

/-- the `n`-th term of the Appell–Lerch sum. -/
def alTerm (α : ℂ) (A B D E : ℝ) (c ω : ℤ → ℂ) (n : ℤ) : ℂ :=
  c n * cexp (-(α * (A * (n : ℂ) ^ 2 + B * n))) / (1 - ω n * cexp (-(α * (D * (n : ℂ) + E))))

lemma anti_shift {T : ℕ} {c : ℤ → ℂ} (hc : ∀ n, c (n + T) = -c n) (n k : ℤ) :
    c (n + T * k) = (-1) ^ k * c n := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show n + T * ((k : ℤ) + 1) = (n + T * k) + T by ring, hc, ih, zpow_add_one₀ (by norm_num)]; ring
  | pred k ih =>
    have h := hc (n + T * (-(k : ℤ) - 1))
    rw [show n + T * (-(k : ℤ) - 1) + T = n + T * (-(k : ℤ)) by ring, ih] at h
    rw [zpow_sub_one₀ (by norm_num)]
    linear_combination h

lemma per_shift {T : ℕ} {ω : ℤ → ℂ} (hω : ∀ n, ω (n + T) = ω n) (n k : ℤ) : ω (n + T * k) = ω n := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih => rw [show n + T * ((k : ℤ) + 1) = (n + T * k) + T by ring, hω, ih]
  | pred k ih =>
    have h := hω (n + T * (-(k : ℤ) - 1))
    rw [show n + T * (-(k : ℤ) - 1) + T = n + T * (-(k : ℤ)) by ring, ih] at h
    exact h.symm

lemma alTerm_class {T : ℕ} {c ω : ℤ → ℂ} (hc : ∀ n, c (n + T) = -c n) (hω : ∀ n, ω (n + T) = ω n)
    (ρ k : ℤ) : alTerm α A B D E c ω (ρ + T * k) = c ρ * kern α A B D E T ρ (ω ρ) k := by
  unfold alTerm kern kE kD
  rw [anti_shift hc, per_shift hω]
  have he : cexp (π * I * (k : ℂ)) = (-1) ^ k := by
    rw [show π * I * (k : ℂ) = (k : ℂ) * (π * I) by ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [show π * I * (k : ℂ) - α * (A * ((ρ : ℂ) + T * k) ^ 2 + B * ((ρ : ℂ) + T * k)) =
      π * I * (k : ℂ) + -(α * (A * ((ρ : ℂ) + T * k) ^ 2 + B * ((ρ : ℂ) + T * k))) by ring,
    Complex.exp_add, he]
  push_cast
  ring

/-- **Key lemma**: the anti-periodic Appell–Lerch sum is small. -/
theorem al_sum_le (hα : 0 < α.re) (hA : 0 < A) (hT : 0 < T) {c ω : ℤ → ℂ}
    (hc : ∀ n, c (n + T) = -c n) (hc1 : ∀ n, ‖c n‖ ≤ 1) (hω : ∀ n, ω (n + T) = ω n)
    {m Y0 : ℝ} (hm : 0 < m) (hY0 : 0 < Y0)
    (hden : ∀ n : ℤ, ∀ x y : ℝ, |y| ≤ Y0 → m ≤ ‖1 - ω n * cexp (-(α * (D * ((x : ℂ) + y * I) + E)))‖) :
    Summable (alTerm α A B D E c ω) ∧
    ‖∑' n, alTerm α A B D E c ω n‖ ≤
      (1 / m) * (Real.exp (A * Y0 ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A)) *
        √(π / (A * α.re))) * (1 / Real.sinh (π * Y0 / T)) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  set y0 := Y0 / T
  have hy0 : 0 < y0 := by positivity
  -- class hypotheses
  have hdc : ∀ ρ : ℤ, ∀ x y' : ℝ, |y'| ≤ y0 → m ≤ ‖kD α D E T ρ (ω ρ) (x + y' * I)‖ := by
    intro ρ x y' hy'
    have h := hden ρ (ρ + T * x) (T * y') (by
      rw [abs_mul, abs_of_pos hT']
      calc T * |y'| ≤ T * y0 := by gcongr
        _ = Y0 := by simp only [y0]; field_simp)
    unfold kD
    convert h using 6
    push_cast; ring
  set S : ℤ → ℂ := fun ρ => ∑' l : ℤ, 𝓕 (fun x : ℝ => kern α A B D E T ρ (ω ρ) x) l
  have hcls : ∀ ρ : ℤ, HasSum (fun k : ℤ => alTerm α A B D E c ω (ρ + T * k)) (c ρ * S ρ) := by
    intro ρ
    have := ((class_sum (B := B) hα hA hT hm hy0 (hdc ρ)).1).mul_left (c ρ)
    exact this.congr_fun fun k => alTerm_class hc hω ρ k
  -- spread each class over `ℤ`
  set Fc : ℕ → ℤ → ℂ := fun ρ n => if n % (T : ℤ) = ρ then alTerm α A B D E c ω n else 0
  have hTz : (0 : ℤ) < T := by exact_mod_cast hT
  have hFc : ∀ ρ ∈ Finset.range T, HasSum (Fc ρ) (c ρ * S ρ) := by
    intro ρ hρ
    have hρT : (ρ : ℤ) < T := by exact_mod_cast Finset.mem_range.mp hρ
    set g : ℤ → ℤ := fun k => (ρ : ℤ) + T * k
    have hg : Function.Injective g := fun a b h => by
      simp only [g] at h
      exact (mul_right_injective₀ hTz.ne').eq_iff.mp (by linarith)
    have hmod : ∀ k, (g k) % (T : ℤ) = ρ := fun k => by
      simp only [g]; rw [Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt (by positivity) hρT
    refine (hg.hasSum_iff fun n hn => ?_).mp ?_
    · simp only [Fc]
      rw [if_neg]
      intro h
      apply hn
      refine ⟨n / T, ?_⟩
      simp only [g]
      have := Int.emod_add_mul_ediv n T
      rw [h] at this; exact this
    · refine (hcls ρ).congr_fun fun k => ?_
      simp only [Function.comp, Fc, hmod k, if_true]
      rfl
  have hall := hasSum_sum hFc
  have hsumF : ∀ n : ℤ, ∑ ρ ∈ Finset.range T, Fc ρ n = alTerm α A B D E c ω n := by
    intro n
    have h0 : 0 ≤ n % (T : ℤ) := Int.emod_nonneg _ hTz.ne'
    have h1 : n % (T : ℤ) < T := Int.emod_lt_of_pos _ hTz
    have hc' : ∀ ρ : ℕ, (n % (T : ℤ) = ρ) ↔ ((n % (T : ℤ)).toNat = ρ) := fun ρ => by omega
    simp only [Fc, hc']
    rw [Finset.sum_ite_eq (Finset.range T) ((n % (T : ℤ)).toNat)]
    rw [if_pos (Finset.mem_range.mpr (by omega))]
  have hfull : HasSum (alTerm α A B D E c ω) (∑ ρ ∈ Finset.range T, c ρ * S ρ) :=
    hall.congr_fun fun n => (hsumF n).symm
  refine ⟨hfull.summable, ?_⟩
  rw [hfull.tsum_eq]
  set Mc : ℝ := (1 / m) * (Real.exp (A * (T * y0) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A)) *
        √(π / (A * α.re * T ^ 2))) * (1 / Real.sinh (π * y0))
  have hb : ∀ ρ ∈ Finset.range T, ‖c ρ * S ρ‖ ≤ Mc := by
    intro ρ _
    rw [norm_mul]
    have := (class_sum (B := B) hα hA hT hm hy0 (hdc ρ)).2
    have hn := hc1 ρ
    calc ‖c ρ‖ * ‖S ρ‖ ≤ 1 * Mc := by gcongr
      _ = Mc := one_mul _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hb).trans (le_of_eq ?_))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [Mc, y0]
  have hs : √(π / (A * α.re * T ^ 2)) = √(π / (A * α.re)) / T := by
    rw [show π / (A * α.re * T ^ 2) = (π / (A * α.re)) / T ^ 2 by field_simp, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq hT'.le]
  rw [hs, show (T : ℝ) * (Y0 / T) = Y0 by field_simp, show π * (Y0 / T) = π * Y0 / T by ring]
  field_simp

end

end MockCusp
