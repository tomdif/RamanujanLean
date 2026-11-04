/-
# `ψ(−q) + 1` near roots of unity of order `K = 4T`, with `|z|^{−1}`

`aA_cusp_bound'`: `|ψ(−q)+1| ≤ 18(1+C₀) CstP(16√(3/(2π))) |z|^{−1}`.
The phases are `θS = 2πh₀((4n+1) mod K)/K`; the class separation is `δS(ρ) = (2π/K)·min(r, K−r)`,
`r = h₀(4ρ+1) mod K`, which is injective on `ρ < T` because `(h₀, T) = 1` (`psi_phase_sum`).
-/
import RamanujanTau.MockCusp.SharpOdd
import RamanujanTau.MockCusp.PsiCusp

set_option autoImplicit false

namespace MockCusp
open Complex Filter Metric Set
open scoped Topology Real

noncomputable section

/-- the constant of `sumJb_le` for `(A, D) = (6, 4)`, `N₁ = 4`, `c₁ = c₂ = 1/π`. -/
def CstP (G₀ : ℝ) : ℝ := 6 * √2 + 2 * √(18 * (1 + 4) * (1 / π) / 4) + 2 * √(18 * (1 + 4) * (1 / π) / 4) * G₀

/-- the separation of `ψ`'s phases. -/
def δS (h K : ℕ) (n : ℤ) : ℝ :=
  2 * π / K * (min ((h * ((4 * n + 1) % (K : ℤ))) % (K : ℤ)) (K - (h * ((4 * n + 1) % (K : ℤ))) % (K : ℤ)) : ℤ)

lemma δS_sep {h K : ℕ} (hK : 0 < K) (n k : ℤ) : δS h K n ≤ |θS h K n - 2 * π * k| := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hM : (0 : ℤ) < K := by exact_mod_cast hK
  have e : θS h K n - 2 * π * k = 2 * π / K * (((h * ((4 * n + 1) % (K : ℤ))) - k * K : ℤ) : ℝ) := by
    simp only [θS]; push_cast; field_simp; try ring
  rw [e, abs_mul, abs_of_pos (by positivity), δS]
  gcongr
  exact_mod_cast int_dist _ k hM

lemma δS_ge {h T K : ℕ} (hT : 0 < T) (hKT : K = 4 * T) (hh : Odd h) (n : ℤ) : 2 * π / K ≤ δS h K n := by
  have hK0 : (0 : ℝ) < K := by rw [hKT]; push_cast; positivity
  have hM : (0 : ℤ) < K := by rw [hKT]; push_cast; omega
  have h2K : (2 : ℤ) ∣ K := ⟨2 * T, by rw [hKT]; push_cast; ring⟩
  have hr : ((4 * n + 1) % (K : ℤ)) % 2 = 1 := by
    rw [Int.emod_emod_of_dvd _ h2K]; omega
  have hodd : ((h : ℤ) * ((4 * n + 1) % (K : ℤ))) % 2 = 1 := by
    have h1 : Odd (h : ℤ) := by exact_mod_cast hh
    have h2 : Odd ((4 * n + 1) % (K : ℤ)) := Int.odd_iff.mpr hr
    exact Int.odd_iff.mp (h1.mul h2)
  obtain ⟨h1, h2⟩ := odd_emod_bounds hM hodd h2K
  have : (1 : ℝ) ≤ ((min ((h * ((4 * n + 1) % (K : ℤ))) % (K : ℤ))
      (K - (h * ((4 * n + 1) % (K : ℤ))) % (K : ℤ)) : ℤ) : ℝ) := by exact_mod_cast le_min h1 h2
  unfold δS
  nlinarith [div_pos (by positivity : (0 : ℝ) < 2 * π) hK0]

/-- **the phase sum for `ψ`**. -/
lemma psi_phase_sum {h T K : ℕ} (hT : 0 < T) (hKT : K = 4 * T) (hh : Odd h) (hcop : Nat.Coprime h T) :
    ∑ ρ ∈ Finset.range T, 1 / √(δS h K ρ - π * 4 / (2 * T * 6)) ≤ 16 * √(3 / (2 * π)) * T := by
  have hKr : (0 : ℝ) < K := by rw [hKT]; push_cast; positivity
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hKr4 : (K : ℝ) = 4 * T := by rw [hKT]; push_cast; ring
  have hM : (0 : ℤ) < K := by rw [hKT]; push_cast; omega
  have hKz : (K : ℤ) = 4 * T := by rw [hKT]; push_cast; ring
  set r : ℕ → ℕ := fun ρ => (((h : ℤ) + 4 * h * ρ) % (K : ℤ)).toNat
  have hrz : ∀ ρ < T, ((r ρ : ℕ) : ℤ) = ((h : ℤ) + 4 * h * ρ) % (K : ℤ) := fun ρ _ =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hM.ne')
  have hδ : ∀ ρ < T, δS h K ρ = 2 * π / K * min ((r ρ : ℕ) : ℝ) ((K : ℝ) - (r ρ : ℕ)) := by
    intro ρ hρ
    have e : ((h : ℤ) * ((4 * (ρ : ℤ) + 1) % (K : ℤ))) % (K : ℤ) = ((h : ℤ) + 4 * h * ρ) % (K : ℤ) := by
      rw [Int.mul_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.mul_emod]; ring_nf
    unfold δS
    rw [e, ← hrz ρ hρ]; push_cast; rfl
  have hc : (0 : ℝ) < 2 * π / (3 * K) := by positivity
  have hh' : Odd h := hh
  have key := class_phase_sum (T := T) (M := K) hc r
    (fun ρ hρ => by
      have h1 := δS_ge (h := h) hT hKT hh ρ
      rw [hδ ρ hρ] at h1
      have : (1 : ℝ) ≤ min ((r ρ : ℕ) : ℝ) ((K : ℝ) - (r ρ : ℕ)) := by
        by_contra hcon; push Not at hcon
        have : 2 * π / K * min ((r ρ : ℕ) : ℝ) ((K : ℝ) - (r ρ : ℕ)) < 2 * π / K * 1 :=
          mul_lt_mul_of_pos_left hcon (by positivity)
        linarith
      have := (min_le_left _ _).trans' this
      exact_mod_cast this)
    (fun ρ hρ => by
      have := Int.emod_lt_of_pos ((h : ℤ) + 4 * h * ρ) hM
      have h' : ((r ρ : ℕ) : ℤ) < (K : ℤ) := by rw [hrz ρ hρ]; exact this
      exact_mod_cast h')
    (fun ρ hρ ρ' hρ' heq => by
      have e : ((h : ℤ) + 4 * h * ρ) % (4 * T : ℤ) = ((h : ℤ) + 4 * h * ρ') % (4 * T : ℤ) := by
        rw [← hKz, ← hrz ρ hρ, ← hrz ρ' hρ', heq]
      exact emod_inj_of_coprime hT hcop (a := 4) (by norm_num) hρ hρ' e)
    (fun ρ => δS h K ρ - π * 4 / (2 * T * 6))
    (fun ρ hρ => by
      have hge := δS_ge (h := h) hT hKT hh ρ
      simp only
      rw [hδ ρ hρ] at hge ⊢
      set mn := min ((r ρ : ℕ) : ℝ) ((K : ℝ) - (r ρ : ℕ))
      have hgap : π * 4 / (2 * T * 6) = (2 / 3) * (2 * π / K) := by rw [hKr4]; field_simp; ring
      have : π * 4 / (2 * T * 6) ≤ (2 / 3) * (2 * π / K * mn) := by rw [hgap]; gcongr
      have e : 2 * π / (3 * K) * mn = (1 / 3) * (2 * π / K * mn) := by field_simp; try ring
      linarith)
  refine key.trans (le_of_eq ?_)
  rw [mul_div_assoc, ← Real.sqrt_div' _ hc.le, show (K : ℝ) / (2 * π / (3 * K)) = (3 / (2 * π)) * K ^ 2 by
    field_simp, Real.sqrt_mul (by positivity), Real.sqrt_sq hKr.le, hKr4]
  ring

set_option maxHeartbeats 2000000 in
/-- **`ψ(−q) + 1` near a root of unity of order `K = 4T`, `D = 1`.** -/
theorem aA_cusp_bound' {T K : ℕ} (hT : 0 < T) (hKT : K = 4 * T) {h : ℕ} (hcop : Nat.Coprime h K) {z : ℂ}
    (hz : 0 < z.re) (hR : (K : ℝ) / 2 ≤ (1 / z).re) :
    ‖aA (Rademacher.qp h K z)‖ ≤ 18 * (1 + HardyRamanujan.C0) * CstP (16 * √(3 / (2 * π))) * ‖z‖ ^ (-(1 : ℝ)) := by
  have hK0 : 0 < K := by omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  have hKr4 : (K : ℝ) = 4 * T := by rw [hKT]; push_cast; ring
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK0
  have hK4 : (4 : ℝ) ≤ K := by rw [hKr4]; have : (1 : ℝ) ≤ T := by exact_mod_cast hT
                               linarith
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr fun h0 => by rw [h0] at hz; simp at hz
  have hRpos : 0 < (1 / z).re := by linarith
  have hh : Odd h := by
    have h2 : Nat.Coprime h 2 := Nat.Coprime.coprime_dvd_right ⟨2 * T, by omega⟩ hcop
    exact Nat.coprime_two_right.mp h2
  set h₀ := h + 2 * T with hh₀
  have hh₀o : Odd h₀ := hh.add_even ⟨T, by ring⟩
  have hcopT : Nat.Coprime h₀ T := by
    rw [hh₀, Nat.coprime_add_mul_right_left]
    exact Nat.Coprime.coprime_dvd_right ⟨4, by omega⟩ hcop
  have hKc : (K : ℂ) = 4 * T := by rw [hKT]; push_cast; ring
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hQ : cexp (LK h₀ K z) = -Rademacher.qp h K z := by
    rw [qp_eq_LK, show LK h₀ K z = LK h K z + π * I by
      unfold LK; simp only [hh₀]; push_cast; rw [hKc]; field_simp; ring, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hQ4 : (-Rademacher.qp h K z) ^ 4 = Rademacher.qp h₀ T z := by
    rw [← hQ, ← Complex.exp_nat_mul, qp_eq_LK]; congr 1; unfold LK; push_cast; rw [hKc]; field_simp
  have hq := Rademacher.qp_mem hK0 hz (h' := h)
  have hq1 : ‖Rademacher.qp h K z‖ < 1 := by simpa using hq
  have hq0 : Rademacher.qp h K z ≠ 0 := by rw [Rademacher.qp]; exact Complex.exp_ne_zero _
  have hRe : z.re = (1 / z).re * ‖z‖ ^ 2 := by
    rw [one_div, inv_re, Complex.normSq_eq_norm_sq]; field_simp
  have hzle : ‖z‖ ≤ 2 / K := by
    have h1 : (1 / z).re ≤ 1 / ‖z‖ := by
      rw [one_div, inv_re, Complex.normSq_eq_norm_sq]
      rw [div_le_div_iff₀ (by positivity) hzn]
      nlinarith [Complex.re_le_norm z]
    rw [le_div_iff₀ hKr]
    have := hR.trans h1
    rw [le_div_iff₀ hzn] at this; linarith
  have hz2 : ‖z‖ ≤ 2 := hzle.trans (by rw [div_le_iff₀ hKr]; linarith)
  set α := αK K z with hαd
  have hα : 0 < α.re := by
    simp only [α, αK]
    rw [show (2 * π * z / K : ℂ) = ((2 * π / K : ℝ) : ℂ) * z by push_cast; ring, re_ofReal_mul]
    positivity
  have hαR : (1 / α).re = K * (1 / z).re / (2 * π) := by
    simp only [α, αK]
    rw [show 1 / (2 * π * z / K : ℂ) = ((K / (2 * π) : ℝ) : ℂ) * (1 / z) by
      push_cast; field_simp, re_ofReal_mul]; ring
  have hαn : ‖α‖ = 2 * π * ‖z‖ / K := by
    simp only [α, αK]; rw [norm_div, norm_mul, norm_mul]; simp [abs_of_pos Real.pi_pos]
  have hαre : α.re = 2 * π * z.re / K := by
    simp only [α, αK]
    rw [show (2 * π * z / K : ℂ) = ((2 * π / K : ℝ) : ℂ) * z by push_cast; ring, re_ofReal_mul]; ring
  have hgap : ∀ n, π * 4 / (2 * T * 6) < δS h₀ K n := fun n => by
    refine lt_of_lt_of_le ?_ (δS_ge hT hKT hh₀o n)
    rw [hKr4, div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [Real.pi_pos]
  obtain ⟨hs, hb⟩ := al_sum_cusp' (B := 2) (E := 1) hα (by norm_num : (0 : ℝ) < 6) (by norm_num : (0 : ℝ) < 4) hT
    (cP_anti hT hKT hh₀o) (cP_norm h₀ K) (θS_per hKT) (δS_sep hK0) hgap
  set c0 := π * (1 / z).re / (12 * T) with hc0
  have hc0' : π ^ 2 * (1 / α).re / (4 * 6 * T ^ 2) = c0 := by
    rw [hαR, hc0, hKr4]; field_simp; ring
  have hc0'' : π ^ 2 * (1 / α).re / (2 * 6 * T ^ 2) = 2 * c0 := by
    rw [hαR, hc0, hKr4]; field_simp; ring
  rw [hc0', hc0''] at hb
  have hc0lb : π / 24 ≤ c0 := by
    rw [hc0, le_div_iff₀ (by positivity)]; rw [hKr4] at hR; nlinarith [Real.pi_pos]
  -- the sum of `Jb`
  have hW : √(π / (6 * α.re)) ≤ 1 / ‖z‖ := by
    rw [hαre, hRe]
    have : π / (6 * (2 * π * ((1 / z).re * ‖z‖ ^ 2) / K)) = K / (12 * (1 / z).re * ‖z‖ ^ 2) := by
      field_simp; ring
    rw [this, show 1 / ‖z‖ = √(1 / ‖z‖ ^ 2) by rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hzn.le,
      Real.sqrt_one]]
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ‖z‖, mul_pos hzn hzn]
  have hαn0 : ‖α‖ ≠ 0 := by rw [hαn]; positivity
  have hn2 : ‖α‖ ^ 2 * (1 / α).re = α.re := by
    rw [one_div, inv_re, Complex.normSq_eq_norm_sq]; field_simp
  have hR1 : 4 / π ≤ (1 / α).re := by
    have hKR : (8 : ℝ) ≤ K * (1 / z).re := by nlinarith
    rw [hαR, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [Real.pi_pos]
  have hN : 16 * ‖α‖ ^ 2 * 4 ^ 2 / (π ^ 2 * 6 * α.re) ≤ 4 := by
    rw [div_le_iff₀ (by positivity), ← hn2]
    have ha2 : 0 ≤ ‖α‖ ^ 2 := sq_nonneg _
    have h3 : ‖α‖ ^ 2 * (4 / π) ≤ ‖α‖ ^ 2 * (1 / α).re := mul_le_mul_of_nonneg_left hR1 ha2
    have h4 : ‖α‖ ^ 2 * (4 / π) * (4 * (π ^ 2 * 6)) = ‖α‖ ^ 2 * (96 * π) := by field_simp; ring
    have h5 : 16 * ‖α‖ ^ 2 * 4 ^ 2 ≤ ‖α‖ ^ 2 * (96 * π) := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 4 * (π ^ 2 * 6))]
  have hKz : (K : ℝ) * ‖z‖ ≤ 2 := by rw [le_div_iff₀ hKr] at hzle; linarith
  have h1 : ‖z‖ ^ 2 ≤ 1 / π * ‖α‖ := by
    rw [hαn, show 1 / π * (2 * π * ‖z‖ / K) = 2 * ‖z‖ / K by field_simp, le_div_iff₀ hKr]
    have := mul_le_mul_of_nonneg_left hKz hzn.le
    linarith [show ‖z‖ ^ 2 * K = ‖z‖ * (K * ‖z‖) by ring]
  have h2 : ‖z‖ ^ 2 ≤ 1 / π * α.re := by
    rw [hαre, hRe, show 1 / π * (2 * π * ((1 / z).re * ‖z‖ ^ 2) / K) = 2 * (1 / z).re * ‖z‖ ^ 2 / K by
      field_simp, le_div_iff₀ hKr]
    have := mul_le_mul_of_nonneg_left (show (K : ℝ) ≤ 2 * (1 / z).re by linarith) (sq_nonneg ‖z‖)
    linarith [show 2 * (1 / z).re * ‖z‖ ^ 2 = ‖z‖ ^ 2 * (2 * (1 / z).re) by ring]
  have hgρ : ∀ ρ : ℕ, 0 < δS h₀ K ρ - π * 4 / (2 * T * 6) := fun ρ => by linarith [hgap ρ]
  have hS := sumJb_le (g := fun ρ : ℕ => δS h₀ K ρ - π * 4 / (2 * T * 6)) hα (by norm_num : (0 : ℝ) < 6)
    (by norm_num : (0 : ℝ) < 4) hT hgρ hzn hz2 hW hN h1 h2 (psi_phase_sum hT hKT hh₀o hcopT)
  have he : Real.exp (2 ^ 2 * α.re / (4 * 6)) ≤ 3 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) (Real.exp_one_lt_d9.le.trans (by norm_num))
    rw [hαre]
    have : z.re ≤ 2 := (Complex.re_le_norm z).trans hz2
    rw [div_le_one (by norm_num)]
    have h1 : 2 * π * z.re / K ≤ π := by
      rw [div_le_iff₀ hKr]; nlinarith [Real.pi_pos]
    nlinarith [Real.pi_lt_d2]
  have hsinh : 0 < 1 / Real.sinh (2 * c0) := by
    have : 0 < c0 := by positivity
    exact one_div_pos.mpr (Real.sinh_pos_iff.mpr (by linarith))
  set SJ := ∑ ρ ∈ Finset.range T, Jb α 6 4 T (min 1 (‖α‖ * ((1 / α).re * (δS h₀ K ρ - π * 4 / (2 * T * 6))))
    / 3) with hSJ
  have hSJ0 : 0 ≤ SJ := Finset.sum_nonneg fun ρ _ => by unfold Jb; positivity
  set Cs := CstP (16 * √(3 / (2 * π)))
  have hS' : SJ ≤ Cs / (‖z‖ * √‖z‖) := hS
  rw [Real.exp_add] at hb
  have hb' : ‖∑' n, alTerm α 6 2 4 1 (cP h₀ K) (fun n => cexp (I * θS h₀ K n)) n‖ ≤
      3 * Real.exp c0 * (1 / Real.sinh (2 * c0)) * (Cs / (‖z‖ * √‖z‖)) := by
    refine hb.trans ?_
    have he' : Real.exp c0 * Real.exp (2 ^ 2 * α.re / (4 * 6)) ≤ Real.exp c0 * 3 :=
      mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
    calc Real.exp c0 * Real.exp (2 ^ 2 * α.re / (4 * 6)) * SJ * (1 / Real.sinh (2 * c0))
        ≤ Real.exp c0 * 3 * (Cs / (‖z‖ * √‖z‖)) * (1 / Real.sinh (2 * c0)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul he' hS' hSJ0 (by positivity)) hsinh.le
      _ = _ := by ring
  -- the identity `aA = F(Q⁴)·Σ`
  have e : alTerm α 6 2 4 1 (cP h₀ K) (fun n => cexp (I * θS h₀ K n)) = tmL (cexp (LK h₀ K z)) (4 * LK h₀ K z) := by
    funext n; exact alTerm_psi hK0 z n
  have hsum : Summable (tmL (cexp (LK h₀ K z)) (4 * LK h₀ K z)) := by rw [← e]; exact hs
  have hden : ∀ n : ℤ, 1 - cexp (LK h₀ K z) * cexp (n * (4 * LK h₀ K z)) ≠ 0 := by
    intro n h0
    rw [← Complex.exp_add, show LK h₀ K z + n * (4 * LK h₀ K z) = (((4 * n + 1 : ℤ) : ℝ) : ℂ) * LK h₀ K z by
      push_cast; ring] at h0
    have h1 : cexp ((((4 * n + 1 : ℤ) : ℝ) : ℂ) * LK h₀ K z) = 1 := by linear_combination -h0
    exact norm_exp_nLK_ne_one hK0 hz (x := ((4 * n + 1 : ℤ) : ℝ)) (by exact_mod_cast (by omega : 4 * n + 1 ≠ 0))
      (by rw [h1, norm_one])
  rw [aA_eq_F hq0 hq1 hQ hden hsum, norm_mul, hQ4, ← e]
  have hFb := F_bound hT hcopT hz (by rw [hKr4] at hR; linarith)
  rw [← hc0] at hFb
  have hC0 := HardyRamanujan.C0_nonneg
  have hCst : 0 ≤ Cs := by simp only [Cs]; unfold CstP; positivity
  have hsz : 0 < √‖z‖ := Real.sqrt_pos.mpr hzn
  have hfin := exp_sinh_le' hc0lb (Cs / (‖z‖ * √‖z‖)) (by positivity)
  calc ‖HardyRamanujan.F (Rademacher.qp h₀ T z)‖ * ‖∑' n, alTerm α 6 2 4 1 (cP h₀ K) (fun n => cexp (I * θS h₀ K n)) n‖
      ≤ ((1 + HardyRamanujan.C0) * √‖z‖ * Real.exp c0) *
          (3 * Real.exp c0 * (1 / Real.sinh (2 * c0)) * (Cs / (‖z‖ * √‖z‖))) :=
        mul_le_mul hFb hb' (norm_nonneg _) (by positivity)
    _ = (1 + HardyRamanujan.C0) * √‖z‖ *
          (Real.exp c0 * (3 * Real.exp c0 * (1 / Real.sinh (2 * c0))) * (Cs / (‖z‖ * √‖z‖))) := by ring
    _ ≤ (1 + HardyRamanujan.C0) * √‖z‖ * (18 * (Cs / (‖z‖ * √‖z‖))) := by gcongr
    _ = 18 * (1 + HardyRamanujan.C0) * Cs * ‖z‖ ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg_one]; field_simp

end

end MockCusp
