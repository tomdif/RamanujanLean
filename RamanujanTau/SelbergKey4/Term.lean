/-
# M2.5a: one term of the lag expansion, integrated against the window

For `m, n ≥ 1` and a quadruple `(a,b,c,d)`, with `u = t + x`, `ξ = 4π²mn` and the frequency
`ω = log(bdn/(acm)) = log b + log d + log n − log a − log c − log m`:

    U(u,u+v) (b/a)^{iu} (d/c)^{i(u+v)} sTerm(u, u+v; m, n)
      = κ(v) · U(u,u+v) W̃_{u,u+v}(ξ) e^{iωu},
    κ(v) = τ(m)τ(n)(mn)^{−6} e^{iv(log d − log c + log n)}                   (`term_eq`)

so its `t`-integral against `φ_T` is `κ(v) e^{iωx} J` with `J` the integral of `FarTerm`, and
(`term_integral_bound`)

    |∫_{T/2}^{3T} φ_T(t) · term(t+x, x'−x) dt| ≤ |τ(m)τ(n)|(mn)^{−6} · C min(T, (ω²T)^{−1}) (1+ξ/T²)^{−A}.

The off-diagonal terms are exactly those with `ω ≠ 0` (`isDiag` ⟺ `bdn = acm`).
Level 1.
-/
import RamanujanTau.SelbergKey4.FarTerm

set_option autoImplicit false

namespace RamanujanTau.SelbergKey4

open Complex MeasureTheory Set Filter RamanujanTau.HeckeAFE RamanujanTau.HeckeL
  RamanujanTau.SelbergKey RamanujanTau.SelbergKey2 RamanujanTau.SelbergKey3
open scoped Real

/-- `log(bdn/(acm))` as a sum of logarithms. -/
noncomputable def omg (a b c d m n : ℕ) : ℝ :=
  Real.log b + Real.log d + Real.log n - Real.log a - Real.log c - Real.log m

/-- The `t`-independent coefficient `κ(v)`. -/
noncomputable def kap4 (c d m n : ℕ) (v : ℝ) : ℂ :=
  tauC m * tauC n * cexp (-(6 * ((Real.log m + Real.log n : ℝ) : ℂ))) *
    cexp ((v : ℂ) * I * ((Real.log d - Real.log c + Real.log n : ℝ) : ℂ))

lemma natCast_cpow_eq {m : ℕ} (hm : 1 ≤ m) (s : ℂ) :
    (m : ℂ) ^ s = cexp (s * ((Real.log m : ℝ) : ℂ)) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hm0, mul_comm,
    show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_log (Nat.cast_nonneg _)]

/-- **One term of the lag expansion, factored.** -/
theorem term_eq (a b c d : ℕ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (u v : ℝ) :
    Ush u (u + v) * (eph a b u * eph c d (u + v) * sTerm u (u + v) (m, n)) =
      kap4 c d m n v * (FW v (4 * π ^ 2 * m * n) u * cexp ((omg a b c d m n * u : ℝ) * I)) := by
  unfold sTerm kap4 FW Ulag Wv eph
  simp only
  rw [natCast_cpow_eq hm, natCast_cpow_eq hn]
  have key : cexp (u * I * ((Real.log b - Real.log a : ℝ) : ℂ)) *
      cexp (((u + v : ℝ) : ℂ) * I * ((Real.log d - Real.log c : ℝ) : ℂ)) *
      cexp (-(6 + u * I) * ((Real.log m : ℝ) : ℂ)) *
      cexp (-(6 - ((u + v : ℝ) : ℂ) * I) * ((Real.log n : ℝ) : ℂ)) =
      cexp (-(6 * ((Real.log m + Real.log n : ℝ) : ℂ))) *
        cexp ((v : ℂ) * I * ((Real.log d - Real.log c + Real.log n : ℝ) : ℂ)) *
        cexp ((omg a b c d m n * u : ℝ) * I) := by
    simp only [← Complex.exp_add]
    congr 1
    unfold omg
    simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
    ring
  calc Ush u (u + v) * (cexp (u * I * ((Real.log b - Real.log a : ℝ) : ℂ)) *
        cexp (((u + v : ℝ) : ℂ) * I * ((Real.log d - Real.log c : ℝ) : ℂ)) *
        (tauC m * tauC n * cexp (-(6 + u * I) * ((Real.log m : ℝ) : ℂ)) *
          cexp (-(6 - ((u + v : ℝ) : ℂ) * I) * ((Real.log n : ℝ) : ℂ)) *
            Wsh u (u + v) (4 * π ^ 2 * m * n)))
      = tauC m * tauC n * (Ush u (u + v) * Wsh u (u + v) (4 * π ^ 2 * m * n)) *
        (cexp (u * I * ((Real.log b - Real.log a : ℝ) : ℂ)) *
          cexp (((u + v : ℝ) : ℂ) * I * ((Real.log d - Real.log c : ℝ) : ℂ)) *
          cexp (-(6 + u * I) * ((Real.log m : ℝ) : ℂ)) *
          cexp (-(6 - ((u + v : ℝ) : ℂ) * I) * ((Real.log n : ℝ) : ℂ))) := by
        ring
    _ = _ := by rw [key]; ring

lemma norm_kap4 (c d : ℕ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (v : ℝ) :
    ‖kap4 c d m n v‖ = |(tau m : ℝ)| * |(tau n : ℝ)| * ((m : ℝ) * n) ^ (-6 : ℝ) := by
  unfold kap4
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
  have r1 : (-(6 * ((Real.log m + Real.log n : ℝ) : ℂ))).re = -(6 * (Real.log m + Real.log n)) := by
    rw [show (-(6 * ((Real.log m + Real.log n : ℝ) : ℂ))) =
      ((-(6 * (Real.log m + Real.log n)) : ℝ) : ℂ) by
        simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat], Complex.ofReal_re]
  have r2 : ((v : ℂ) * I * ((Real.log d - Real.log c + Real.log n : ℝ) : ℂ)).re = 0 := by
    rw [show (v : ℂ) * I * ((Real.log d - Real.log c + Real.log n : ℝ) : ℂ) =
      ((v * (Real.log d - Real.log c + Real.log n) : ℝ) : ℂ) * I by
        rw [Complex.ofReal_mul]; ring, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  rw [r1, r2, Real.exp_zero, mul_one, Real.rpow_def_of_pos (by positivity),
    Real.log_mul hmr.ne' hnr.ne']
  simp only [tauC, Complex.norm_intCast]
  ring_nf

/-- **The windowed `t`-integral of one term.** -/
theorem term_integral_eq (a b c d : ℕ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (T x v : ℝ) :
    ∫ t in (T / 2)..(3 * T), ((phiT T t : ℝ) : ℂ) *
        (Ush (t + x) (t + x + v) * (eph a b (t + x) * eph c d (t + x + v) *
          sTerm (t + x) (t + x + v) (m, n))) =
      kap4 c d m n v * cexp ((omg a b c d m n * x : ℝ) * I) *
        ∫ t in (T / 2)..(3 * T), gT T x v (4 * π ^ 2 * m * n) t *
          cexp ((omg a b c d m n * t : ℝ) * I) := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [term_eq a b c d hm hn (t + x) v]
  unfold gT
  have e : cexp ((omg a b c d m n * (t + x) : ℝ) * I) =
      cexp ((omg a b c d m n * x : ℝ) * I) * cexp ((omg a b c d m n * t : ℝ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]; ring

/-- **M2.5a: one off-diagonal term, integrated against the window.** For `ω ≠ 0` the bound
`C (ω² T)^{−1}`, always `C T`, times `|τ(m)τ(n)|(mn)^{−6}(1 + ξ/T²)^{−A}`, `ξ = 4π²mn`. -/
theorem term_integral_bound (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b c d m n : ℕ) (T x v : ℝ), 1 ≤ m → 1 ≤ n → 1 ≤ T → 0 ≤ x → x ≤ 1 →
      |v| ≤ 1 →
      ‖∫ t in (T / 2)..(3 * T), ((phiT T t : ℝ) : ℂ) *
          (Ush (t + x) (t + x + v) * (eph a b (t + x) * eph c d (t + x + v) *
            sTerm (t + x) (t + x + v) (m, n)))‖ ≤
        |(tau m : ℝ)| * |(tau n : ℝ)| * ((m : ℝ) * n) ^ (-6 : ℝ) *
          (C * (1 + 4 * π ^ 2 * m * n / T ^ 2) ^ (-A)) *
          min T (if omg a b c d m n = 0 then T else 1 / (omg a b c d m n ^ 2 * T)) := by
  obtain ⟨C, hC0, hC⟩ := farTerm_bound A hA
  refine ⟨C, hC0, fun a b c d m n T x v hm hn hT hx0 hx1 hv => ?_⟩
  have hξ : 0 < 4 * π ^ 2 * m * n := by
    have : (0:ℝ) < m := by exact_mod_cast hm
    have : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  obtain ⟨h1, h2⟩ := hC T x v (4 * π ^ 2 * m * n) (omg a b c d m n) hT hx0 hx1 hv hξ
  rw [term_integral_eq a b c d hm hn, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    norm_kap4 c d hm hn]
  have hk0 : 0 ≤ |(tau m : ℝ)| * |(tau n : ℝ)| * ((m : ℝ) * n) ^ (-6 : ℝ) := by positivity
  set S := (1 + 4 * π ^ 2 * m * n / T ^ 2) ^ (-A)
  have hT0 : 0 < T := by linarith
  have hS : 0 ≤ S := Real.rpow_nonneg (by positivity) _
  rw [mul_assoc (|(tau m : ℝ)| * |(tau n : ℝ)| * ((m : ℝ) * n) ^ (-6 : ℝ))]
  refine mul_le_mul_of_nonneg_left ?_ hk0
  set J := ‖∫ t in (T / 2)..(3 * T), gT T x v (4 * π ^ 2 * m * n) t *
      cexp ((omg a b c d m n * t : ℝ) * I)‖
  have hJ1 : J ≤ C * S * T := by
    have := h1; simp only [J, S] at this ⊢; linarith [this]
  split_ifs with hω
  · rw [min_self]; exact hJ1
  · have hJ2 : J ≤ C * S * (1 / (omg a b c d m n ^ 2 * T)) := by
      have := h2 hω; simp only [J, S] at this ⊢
      calc _ ≤ C / (omg a b c d m n ^ 2 * T) * (1 + 4 * π ^ 2 * m * n / T ^ 2) ^ (-A) := this
        _ = _ := by ring
    rcases le_total T (1 / (omg a b c d m n ^ 2 * T)) with h | h
    · rw [min_eq_left h]; exact hJ1
    · rw [min_eq_right h]; exact hJ2

end RamanujanTau.SelbergKey4
