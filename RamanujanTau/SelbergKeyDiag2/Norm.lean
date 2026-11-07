/-
# M3 step 1: the diagonal of the lag product as a combination of twisted sums

For `a, b, c, d ≥ 1` the ray term `(m, n) = (Q₁r, P₁r)` of the lag series, multiplied by the
mollifier coefficients, is (`ray_term`)

    wc(a,b)(b/a)^{iu} wc(c,d)(d/c)^{i(u+v)} sTerm(Q₁r, P₁r)
      = κ(a,b,c,d) e_v(a,b,c,d) · λ(Q₁r)λ(P₁r) r^{−1} r^{iv} W̃_{u,u+v}(4π²P₁Q₁ r²)

(the `u`-phase cancels because `bd·P₁ = ac·Q₁`; the modulus is `1/[ac,bd]` because
`abcd·P₁Q₁ = [ac,bd]²`).  Hence (`diag_quad`)

    quadSum β y u (u+v) diagS = Σ_{[1,y]⁴} κ e_v · Bs(Q₁, P₁)(4π²P₁Q₁).

Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.Induct3
import RamanujanTau.SelbergKeyDiag.DiagIndex

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex Finset RamanujanTau.HafnerBridge RamanujanTau.HafnerBridge2 RamanujanTau.SelbergKey
  RamanujanTau.HeckeL RamanujanTau.HeckeAFE
open scoped Real

lemma log_natmul {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Real.log ((m * n : ℕ) : ℝ) = Real.log m + Real.log n := by
  push_cast
  exact Real.log_mul (by exact_mod_cast (show m ≠ 0 by omega)) (by exact_mod_cast (show n ≠ 0 by omega))

lemma tauC_eq_lam {n : ℕ} (hn : 1 ≤ n) :
    tauC n = ((lam n * Real.exp ((11 / 2 : ℝ) * Real.log n) : ℝ) : ℂ) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rw [lam_def, mul_assoc]
  have : (n : ℝ) ^ (-(11 / 2 : ℝ)) * Real.exp ((11 / 2 : ℝ) * Real.log n) = 1 := by
    rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]; ring_nf; simp
  rw [this, mul_one]
  simp [tauC]

lemma natcpow_eq_exp {n : ℕ} (hn : 1 ≤ n) (w : ℂ) : (n : ℂ) ^ w = cexp (Real.log n * w) := by
  have := cpow_eq_exp (x := (n : ℝ)) (by exact_mod_cast hn) w
  simpa using this

/-- **The ray term.** -/
theorem ray_term (β : ℕ → ℝ) {a b c d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (u v : ℝ) (r : ℕ) :
    (wc β a b : ℂ) * eph a b u * ((wc β c d : ℂ) * eph c d (u + v)) *
        sTerm u (u + v) (Q1 a b c d * r, P1 a b c d * r) =
      ((β a * β b * β c * β d / (Nat.lcm (a * c) (b * d) : ℝ) : ℝ) : ℂ) * SelbergKey.ev a b c d v *
        (((T (Q1 a b c d) (P1 a b c d) r / r : ℝ) : ℂ) *
          ft u v (4 * π ^ 2 * ((P1 a b c d * Q1 a b c d : ℕ) : ℝ)) r) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [sTerm, tauC_zero, T]
  set P := P1 a b c d with hPdef
  set Q := Q1 a b c d with hQdef
  have hP := SelbergKeyDiag.P1_mul_g ha hb hc hd
  have hQ := SelbergKeyDiag.Q1_mul_g ha hb hc hd
  have hP1 := SelbergKeyDiag.P1_pos ha hb hc hd
  have hQ1 := SelbergKeyDiag.Q1_pos ha hb hc hd
  have hg := SelbergKeyDiag.gcd_PQ_pos ha hb hc hd
  set g := Nat.gcd (a * c) (b * d)
  -- `lcm = P₁ Q₁ g`
  have hl : Nat.lcm (a * c) (b * d) = P * Q * g := by
    have h1 := Nat.gcd_mul_lcm (a * c) (b * d)
    have : g * Nat.lcm (a * c) (b * d) = g * (P * Q * g) := by rw [h1, ← hP, ← hQ]; ring
    exact Nat.eq_of_mul_eq_mul_left hg this
  have hl1 : 1 ≤ Nat.lcm (a * c) (b * d) := Nat.lcm_pos (Nat.mul_pos ha hc) (Nat.mul_pos hb hd)
  -- log identities
  have L1 : Real.log b + Real.log d + Real.log P = Real.log a + Real.log c + Real.log Q := by
    have e : b * d * P = a * c * Q := by
      calc b * d * P = Q * g * P := by rw [hQ]
        _ = P * g * Q := by ring
        _ = a * c * Q := by rw [hP]
    have := congrArg (fun n : ℕ => Real.log (n : ℝ)) e
    simp only at this
    rw [log_natmul (Nat.mul_pos hb hd) hP1, log_natmul hb hd, log_natmul (Nat.mul_pos ha hc) hQ1,
      log_natmul ha hc] at this
    linarith
  have L2 : Real.log a + Real.log b + Real.log c + Real.log d + Real.log P + Real.log Q =
      2 * Real.log (Nat.lcm (a * c) (b * d)) := by
    have e : a * c * (b * d) * (P * Q) = Nat.lcm (a * c) (b * d) * Nat.lcm (a * c) (b * d) := by
      rw [hl, ← hP, ← hQ]; ring
    have := congrArg (fun n : ℕ => Real.log (n : ℝ)) e
    simp only at this
    rw [log_natmul (Nat.mul_pos (Nat.mul_pos ha hc) (Nat.mul_pos hb hd)) (Nat.mul_pos hP1 hQ1),
      log_natmul (Nat.mul_pos ha hc) (Nat.mul_pos hb hd), log_natmul ha hc, log_natmul hb hd,
      log_natmul hP1 hQ1, log_natmul hl1 hl1] at this
    linarith
  have hQr : 1 ≤ Q * r := Nat.mul_pos hQ1 hr
  have hPr : 1 ≤ P * r := Nat.mul_pos hP1 hr
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr
  have hlcm0 : (0:ℝ) < (Nat.lcm (a * c) (b * d) : ℝ) := by exact_mod_cast hl1
  unfold sTerm wc eph SelbergKey.ev ft T
  simp only
  rw [tauC_eq_lam hQr, tauC_eq_lam hPr, natcpow_eq_exp hQr, natcpow_eq_exp hPr,
    cpow_eq_exp hr0, log_natmul hQ1 hr, log_natmul hP1 hr]
  have eW : (4 * π ^ 2 * ((Q * r : ℕ) : ℝ) * ((P * r : ℕ) : ℝ)) =
      4 * π ^ 2 * ((P * Q : ℕ) : ℝ) * (r : ℝ) ^ 2 := by push_cast; ring
  rw [eW]
  -- modulus as exponentials
  have eR : ((β a * β b * β c * β d / (Nat.lcm (a * c) (b * d) : ℝ) : ℝ) : ℂ) =
      ((β a * β b * β c * β d : ℝ) : ℂ) * cexp (-(Real.log (Nat.lcm (a * c) (b * d) : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hlcm0, ← Complex.ofReal_mul]
    rfl
  have eInv : ((1 / (r : ℝ) : ℝ) : ℂ) = cexp (-(Real.log r : ℂ)) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hr0]; push_cast; ring
  rw [eR, show ((lam (Q * r) * lam (P * r) / r : ℝ) : ℂ) =
      ((lam (Q * r) * lam (P * r) : ℝ) : ℂ) * ((1 / (r : ℝ) : ℝ) : ℂ) by push_cast; ring, eInv]
  push_cast
  rw [← hPdef, ← hQdef]
  have L1c := congrArg (fun x : ℝ => (x : ℂ)) L1
  have L2c := congrArg (fun x : ℝ => (x : ℂ)) L2
  push_cast at L1c L2c
  set la := Complex.log (a : ℂ)
  set lb := Complex.log (b : ℂ)
  set lc := Complex.log (c : ℂ)
  set ld := Complex.log (d : ℂ)
  set lP := Complex.log (P : ℂ)
  set lQ := Complex.log (Q : ℂ)
  set lr := Complex.log (r : ℂ)
  set lL := Complex.log ((Nat.lcm (a * c) (b * d) : ℕ) : ℂ)
  set W := Wsh u (u + v) (4 * π ^ 2 * (↑P * ↑Q) * ↑r ^ 2)
  set B : ℂ := (β a : ℂ) * (β b : ℂ) * (β c : ℂ) * (β d : ℂ) * (lam (Q * r) : ℂ) * (lam (P * r) : ℂ) * W
  have hexp : -((la + lb) / 2) + (u : ℂ) * I * (lb - la) + -((lc + ld) / 2) + ((u : ℂ) + v) * I * (ld - lc) +
      11 / 2 * (lQ + lr) + 11 / 2 * (lP + lr) + (lQ + lr) * -(6 + (u : ℂ) * I) +
      (lP + lr) * -(6 - ((u : ℂ) + v) * I) = -lL + (v : ℂ) * I * (lP + ld - lc) + -lr + lr * ((v : ℂ) * I) := by
    linear_combination (-1 / 2 : ℂ) * L2c + ((u : ℂ) * I) * L1c
  calc _ = B * (cexp (-((la + lb) / 2)) * cexp ((u : ℂ) * I * (lb - la)) * cexp (-((lc + ld) / 2)) *
        cexp (((u : ℂ) + v) * I * (ld - lc)) * cexp (11 / 2 * (lQ + lr)) * cexp (11 / 2 * (lP + lr)) *
        cexp ((lQ + lr) * -(6 + (u : ℂ) * I)) * cexp ((lP + lr) * -(6 - ((u : ℂ) + v) * I))) := by
        simp only [B]; ring
    _ = B * cexp (-((la + lb) / 2) + (u : ℂ) * I * (lb - la) + -((lc + ld) / 2) + ((u : ℂ) + v) * I * (ld - lc) +
      11 / 2 * (lQ + lr) + 11 / 2 * (lP + lr) + (lQ + lr) * -(6 + (u : ℂ) * I) +
      (lP + lr) * -(6 - ((u : ℂ) + v) * I)) := by simp only [Complex.exp_add]
    _ = B * cexp (-lL + (v : ℂ) * I * (lP + ld - lc) + -lr + lr * ((v : ℂ) * I)) := by rw [hexp]
    _ = _ := by simp only [Complex.exp_add, B]; ring

/-- **The diagonal quadruple sum as twisted sums** (exact). -/
theorem diag_quad (β : ℕ → ℝ) (y : ℕ) (u v : ℝ) :
    quadSum β y u (u + v) (fun a b c d => diagS a b c d u (u + v)) =
      sum4 y fun a b c d => ((β a * β b * β c * β d / (Nat.lcm (a * c) (b * d) : ℝ) : ℝ) : ℂ) *
        SelbergKey.ev a b c d v *
        Bs u v (Q1 a b c d) (P1 a b c d) (4 * π ^ 2 * ((P1 a b c d * Q1 a b c d : ℕ) : ℝ)) := by
  unfold quadSum sum4
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb =>
    Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => ?_
  have ha1 := (Finset.mem_Icc.1 ha).1
  have hb1 := (Finset.mem_Icc.1 hb).1
  have hc1 := (Finset.mem_Icc.1 hc).1
  have hd1 := (Finset.mem_Icc.1 hd).1
  simp only
  rw [SelbergKeyDiag.diagS_eq_tsum_ray ha1 hb1 hc1 hd1, ← tsum_mul_left]
  unfold Bs
  rw [← tsum_mul_left]
  exact tsum_congr fun r => ray_term β ha1 hb1 hc1 hd1 u v r

end RamanujanTau.SelbergKeyDiag2
