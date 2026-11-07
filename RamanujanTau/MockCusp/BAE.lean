/-
# Ramanujan's `b(q)` as an eta quotient on the disc

`bA_eq_bE`: for `|q| < 1`,

  `(q;q²)_∞ · Σ_{n∈ℤ}(−1)ⁿ q^{n²} = (q;q)_∞³/(q²;q²)_∞²`,

i.e. `MockTheta3.Radial.bA = Andrews66.bE` on the disc. The formal input is Gauss's
`Σ_ℤ(−1)ⁿq^{n²} = (q;q²)_∞²(q²;q²)_∞`, which is the Jacobi triple product `RankProof.jtp_ab 2 1`; the
transfer to the disc is `Taylor.eq_of_T`, and the eta quotient is rewritten with `(q;q)_∞ = (q;q²)_∞(q²;q²)_∞`.
-/
import RamanujanTau.MockTheta3Radial
import RamanujanTau.RankTheta
import RamanujanTau.Andrews66.Cusps
import RamanujanTau.Dragonette.Odd

set_option autoImplicit false

namespace MockCusp
open Complex Metric Finset PowerSeries Taylor

noncomputable section

local notation "ψC" => MockTheta5.JTP.ψC

lemma T_of_realizes {f : ℂ → ℂ} {F : PowerSeries ℤ} (hf : Realize.Realizes f F) : T f = ψC F := by
  ext n
  rw [coeff_T, hf.iteratedDeriv_zero n]
  have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [show ψC = PowerSeries.map (Int.castRingHom ℂ) from rfl, PowerSeries.coeff_map]
  field_simp; simp

/-- `Θ = Σ_ℤ (−1)ⁿ q^{n²}` of `MockTheta3Watson` is the theta series `thetaS 2 1` of `RankTheta`. -/
lemma Θ_eq_thetaS : MockTheta3.Watson3.Θ = RankProof.thetaS 2 1 := by
  have e1 : ∀ d : ℕ, 2 * d.choose 2 + 1 * d = d ^ 2 := fun d => by
    have h := Nat.choose_two_right d
    have h2 : 2 * d.choose 2 = d * (d - 1) := by
      rw [h]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self d).two_dvd
    rcases d with _ | d
    · simp
    · rw [h2]; simp; ring
  have e2 : ∀ d : ℕ, 2 * (d + 1).choose 2 + (2 - 1) * (d + 1) = (d + 1) ^ 2 := fun d => by
    have := e1 (d + 1); simpa using this
  ext k
  have key : RankProof.thetaTr 2 1 k = 2 * ∑ n ∈ range (k + 1), ((-1 : PowerSeries ℤ) ^ n * X ^ (n ^ 2)) - 1
      + C ((-1 : ℤ) ^ (k + 1)) * X ^ ((k + 1) ^ 2) := by
    rw [RankProof.thetaTr]
    simp only [e1, map_pow, map_neg, map_one]
    rw [Finset.sum_range_succ (fun d => (-1 : PowerSeries ℤ) ^ (d + 1) * X ^ ((d + 1) ^ 2)),
      show ∑ x ∈ range k, (-1 : PowerSeries ℤ) ^ (x + 1) * X ^ ((x + 1) ^ 2) =
        ∑ x ∈ range (k + 1), (-1 : PowerSeries ℤ) ^ x * X ^ (x ^ 2) - 1 by
        rw [Finset.sum_range_succ']; simp]
    ring
  have hΘ : coeff k MockTheta3.Watson3.Θ =
      coeff k (2 * ∑ n ∈ range (k + 1), ((-1 : PowerSeries ℤ) ^ n * X ^ (n ^ 2)) - 1) := by
    rw [MockTheta3.Watson3.Θ, two_mul, two_mul, map_sub, map_sub, map_add, map_add,
      MockTheta3.Radial.osum_eq_mk (fun n k hk => by
        rw [mul_comm]; exact MockTheta3.Watson3.coeff_Xpow_mul_zero (by nlinarith) _), coeff_mk]
  rw [hΘ, RankProof.thetaS, coeff_mk, key, map_add (coeff k), coeff_C_mul, coeff_X_pow, if_neg (by nlinarith),
    mul_zero, add_zero]

/-- `(q²;q²)_∞ = ∏(1 − q^{2+2n})`. -/
lemma Pq_sq (q : ℂ) : HardyRamanujan.Pq (q ^ 2) = Realize.Pfun 2 2 q := by
  simp only [HardyRamanujan.Pq, Realize.Pfun]
  congr 1; funext n; rw [← pow_mul]; ring_nf

/-- `(q;q)_∞ = (q;q²)_∞ (q²;q²)_∞`. -/
lemma Pq_split {q : ℂ} (hq : ‖q‖ < 1) : HardyRamanujan.Pq q = Realize.Pfun 1 2 q * Realize.Pfun 2 2 q := by
  have h1 : HardyRamanujan.Pq q = (∏' k : ℕ, (1 - q ^ (2 * k + 1))) * HardyRamanujan.Pq (q ^ 2) := by
    rw [HardyRamanujan.Pq_eq, HardyRamanujan.Pq_eq, ← tprod_even_mul_odd (f := fun n : ℕ => 1 - q ^ (n + 1))
      (Dragonette.mult_one_sub_pow hq (fun k => 2 * k + 1) (fun k => by dsimp only; omega))
      (by simpa using Dragonette.mult_one_sub_pow hq (fun k => 2 * k + 1 + 1) (fun k => by dsimp only; omega))]
    congr 1
    congr 1; funext k; rw [← pow_mul]; ring_nf
  rw [h1, Pq_sq]
  congr 1
  simp only [Realize.Pfun]; congr 1; funext k; ring_nf

/-- **`b = (q;q²)_∞ ϑ₄(q) = (q;q)³_∞/(q²;q²)²_∞` on the disc.** -/
theorem bA_eq_bE {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) : MockTheta3.Radial.bA q = Andrews66.bE q := by
  have h12 := Realize.realizes_Pinf 1 2 le_rfl (by norm_num)
  have h22 := Realize.realizes_Pinf 2 2 (by norm_num) (by norm_num)
  have hg := (h12.pow 3).mul h22
  have hT : T MockTheta3.Radial.bA = T (fun q => Realize.Pfun 1 2 q ^ 3 * Realize.Pfun 2 2 q) := by
    rw [MockTheta3.Radial.bA_T, T_of_realizes hg, MockTheta3.Watson3.bR, MockTheta3.Radial.IP_eq,
      Θ_eq_thetaS, ← RankProof.jtp_ab (a := 2) (b := 1) le_rfl (by norm_num)]
    congr 1; norm_num; ring
  rw [eq_of_T MockTheta3.Radial.bA_hol hg.diff hT hq]
  have hq1 : ‖q‖ < 1 := by simpa using hq
  have hq2 : q ^ 2 ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq1 (by norm_num)
  have h0 : Realize.Pfun 2 2 q ≠ 0 := by rw [← Pq_sq]; exact HardyRamanujan.Pq_ne_zero hq2
  rw [Andrews66.bE, HardyRamanujan.F, HardyRamanujan.F, Pq_sq, Pq_split hq1]
  field_simp

end

end MockCusp
