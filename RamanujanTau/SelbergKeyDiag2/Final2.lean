/-
# M3 step 6b: the diagonal in terms of `𝒮⁰`, `𝒮` and the twisted-sum errors (exact)

`diagLag_eq`: `DiagLag(u,v) = 2 Re[U (Σ_q κ e_v (Bs_q − Mn_q) + Xm)]` with
`Xm = c₀e^{−v²/4}/(iv) · G(iv/2)(4π²)^{−iv/2} · 𝒮⁰(v) + L(v)·𝒮(v)`, and
`UXm_sub_Av`: `U·Xm − 𝒜(v,L) = c₀e^{−v²/4}/(iv)(Φ − 1)𝒮⁰ + (U − e^{−ivL})(−c₀/(iv) + γ)𝒮 − U·iv ε(v)·𝒮`,
`Φ = U·G(iv/2)(4π²)^{−iv/2}`.  Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.Final1

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex Finset RamanujanTau.HafnerBridge RamanujanTau.HafnerBridge2 RamanujanTau.SelbergKey
open RamanujanTau.GoodSecondTerm (c0 gammaD)
open scoped Real

/-- `p = iv/2`. -/
noncomputable def pv (v : ℝ) : ℂ := ((v / 2 : ℝ) : ℂ) * I

noncomputable def Xm (u v : ℝ) (y : ℕ) : ℂ :=
  (c0 : ℂ) * (Real.exp (-(v / 2) ^ 2) : ℂ) / ((v : ℂ) * I) *
      (Gsh u (u + v) (pv v) * ((4 * π ^ 2 : ℝ) : ℂ) ^ (-pv v)) * S0v y v +
    Lmain v * Sv y v

lemma sum4_lin (y : ℕ) (A B : ℂ) (f g : ℕ → ℕ → ℕ → ℕ → ℂ) :
    sum4 y (fun a b c d => A * f a b c d + B * g a b c d) = A * sum4 y f + B * sum4 y g := by
  unfold sum4
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

lemma sum4_add (y : ℕ) (f g : ℕ → ℕ → ℕ → ℕ → ℂ) :
    sum4 y (fun a b c d => f a b c d + g a b c d) = sum4 y f + sum4 y g := by
  unfold sum4
  simp only [Finset.sum_add_distrib]

lemma alpha_split (v : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ((4 * π ^ 2 * (n : ℝ) : ℝ) : ℂ) ^ (-(((v / 2 : ℝ) : ℂ) * I)) =
      ((4 * π ^ 2 : ℝ) : ℂ) ^ (-(((v / 2 : ℝ) : ℂ) * I)) * cexp (-((v : ℂ) * I * ((Real.log n / 2 : ℝ) : ℂ))) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rw [cpow_eq_exp (by positivity), cpow_eq_exp (by positivity), ← Complex.exp_add,
    Real.log_mul (by positivity) hn0.ne']
  congr 1; push_cast; ring

/-- **The main terms summed over the quadruples** (exact). -/
theorem sum_Mn (u v : ℝ) (y : ℕ) :
    sum4 y (fun a b c d => (kap y a b c d : ℂ) * SelbergKey.ev a b c d v *
      Mn u v (Q1 a b c d) (P1 a b c d) (4 * π ^ 2 * ((P1 a b c d * Q1 a b c d : ℕ) : ℝ))) = Xm u v y := by
  unfold Xm S0v Sv pv
  rw [← sum4_lin]
  unfold sum4
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb =>
    Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => ?_
  have ha1 := (Finset.mem_Icc.1 ha).1
  have hb1 := (Finset.mem_Icc.1 hb).1
  have hc1 := (Finset.mem_Icc.1 hc).1
  have hd1 := (Finset.mem_Icc.1 hd).1
  have hPQ : 1 ≤ P1 a b c d * Q1 a b c d :=
    Nat.mul_pos (SelbergKeyDiag.P1_pos ha1 hb1 hc1 hd1) (SelbergKeyDiag.Q1_pos ha1 hb1 hc1 hd1)
  beta_reduce
  unfold Mn Pmain
  rw [alpha_split v _ hPQ]
  push_cast
  ring

/-- **The diagonal of the lag product, decomposed** (exact). -/
theorem diagLag_eq (u v : ℝ) (y : ℕ) :
    DiagLag (HafnerMV2.βSel y) y u v =
      2 * (Ush u (u + v) * (sum4 y (fun a b c d => (kap y a b c d : ℂ) * SelbergKey.ev a b c d v *
        (Bs u v (Q1 a b c d) (P1 a b c d) (4 * π ^ 2 * ((P1 a b c d * Q1 a b c d : ℕ) : ℝ)) -
          Mn u v (Q1 a b c d) (P1 a b c d) (4 * π ^ 2 * ((P1 a b c d * Q1 a b c d : ℕ) : ℝ)))) +
        Xm u v y)).re := by
  unfold DiagLag
  rw [diag_quad, ← sum_Mn, ← sum4_add]
  congr 3
  unfold sum4
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  unfold kap; push_cast; ring

/-- **`U·Xm − 𝒜`** (exact). -/
theorem UXm_sub_Av (u v : ℝ) (y : ℕ) :
    Ush u (u + v) * Xm u v y - Av y v (Real.log (u / (2 * π))) =
      (c0 : ℂ) * (Real.exp (-(v / 2) ^ 2) : ℂ) / ((v : ℂ) * I) *
          (Ush u (u + v) * Gsh u (u + v) (pv v) * ((4 * π ^ 2 : ℝ) : ℂ) ^ (-pv v) - 1) * S0v y v +
        (Ush u (u + v) - cexp (-((v * Real.log (u / (2 * π)) : ℝ) : ℂ) * I)) *
          (-(c0 : ℂ) / ((v : ℂ) * I) + gammaD) * Sv y v -
        Ush u (u + v) * ((v : ℂ) * I * epsv v) * Sv y v := by
  unfold Xm Av Lmain
  have hr : (HafnerBridge.r0 : ℂ) = (c0 : ℂ) := rfl
  rw [hr]
  have he : ((Real.exp (-(v ^ 2 / 4)) : ℝ) : ℂ) = (Real.exp (-(v / 2) ^ 2) : ℂ) := by
    congr 2; ring
  rw [he]
  ring

end RamanujanTau.SelbergKeyDiag2
