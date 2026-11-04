/-
# `f` and `φ` near odd-order roots of unity, with `|z|^{−1}`

`sharp_odd_AL`: for odd `K`, the Appell–Lerch sum `Σ c_K(n) q^{n(3n+1)/2}/(1 − e^{iθ(n)}qⁿ)` with any `K`-periodic
phases `θ` whose per-class separations `δ(ρ)` exceed `π/(3K)` and satisfy `Σ_ρ (δ(ρ) − π/(3K))^{−1/2} ≤ G₀K` is
`≤ 3 e^{c₀}/sinh(2c₀) · Cst(G₀)/(|z|√|z|)`, `c₀ = π Re(1/z)/(12K)` (`al_sum_cusp'` + `sumJb_le`).

* `f`: `θ = θK`, `δ(ρ) = (π/K)·min(r, 2K−r)`, `r = (K + 2hρ) mod 2K`; `G₀ = 4√(3/π)` (`f_phase_sum`).
* `φ`: `θ = θP`, `δ(ρ) = (π/(2K))·min(r, 4K−r)`, `r = (K + 4hρ) mod 4K`; `G₀ = 4√(24/π)` (`phi_phase_sum`).

`f_odd_bound'`: `|f(q)| ≤ 36(1+C₀) Cst(4√(3/π)) |z|^{−1}`;  `phi_odd_bound'`: `|φ(q)| ≤ 36(1+C₀) Cst(4√(24/π)) |z|^{−1}`.
-/
import RamanujanTau.MockCusp.SharpCusp
import RamanujanTau.MockCusp.OddCusp
import RamanujanTau.MockCusp.PhiCusp

set_option autoImplicit false

namespace MockCusp
open Complex Filter Metric Set
open scoped Topology Real

noncomputable section

/-- the constant of `sumJb_le` for `(A, D) = (3/2, 1)`, `N₁ = 15`, `c₁ = c₂ = 1/π`. -/
def CstO (G₀ : ℝ) : ℝ := 6 * √2 + 2 * √(18 * (1 + 15) * (1 / π) / 1) + 2 * √(18 * (1 + 15) * (1 / π) / 1) * G₀

set_option maxHeartbeats 1000000 in
/-- **the sharp Appell–Lerch bound at an odd cusp**, for any admissible phases. -/
theorem sharp_odd_AL {K : ℕ} (hK : Odd K) {h : ℕ} {z : ℂ} (hz : 0 < z.re) (hR : (K : ℝ) / 2 ≤ (1 / z).re)
    {θ δ : ℤ → ℝ} (hθp : ∀ n, θ (n + K) = θ n) (hθ : ∀ n k : ℤ, δ n ≤ |θ n - 2 * π * k|)
    (hgap : ∀ n, π / (3 * K) < δ n) {G₀ : ℝ}
    (hG : ∑ ρ ∈ Finset.range K, 1 / √(δ ρ - π / (3 * K)) ≤ G₀ * K) :
    Summable (alTerm (αK K z) (3 / 2) (1 / 2) 1 0 (cK h K) (fun n => cexp (I * θ n))) ∧
    ‖∑' n, alTerm (αK K z) (3 / 2) (1 / 2) 1 0 (cK h K) (fun n => cexp (I * θ n)) n‖ ≤
      3 * Real.exp (π * (1 / z).re / (12 * K)) * (1 / Real.sinh (2 * (π * (1 / z).re / (12 * K)))) *
        (CstO G₀ / (‖z‖ * √‖z‖)) := by
  have hK0 : 0 < K := hK.pos
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK0
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr fun h0 => by rw [h0] at hz; simp at hz
  have hRpos : 0 < (1 / z).re := by linarith
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
  have hgap' : ∀ n, π * 1 / (2 * K * (3 / 2)) < δ n := fun n => by
    have := hgap n; rwa [show π * 1 / (2 * K * (3 / 2)) = π / (3 * K) by ring]
  obtain ⟨hs, hb⟩ := al_sum_cusp' (B := 1 / 2) (E := 0) hα (by norm_num : (0 : ℝ) < 3 / 2) one_pos hK0
    (cK_anti hK) (cK_norm h K) hθp hθ hgap'
  refine ⟨hs, hb.trans ?_⟩
  set c0 := π * (1 / z).re / (12 * K) with hc0
  have hc0' : π ^ 2 * (1 / α).re / (4 * (3 / 2) * K ^ 2) = c0 := by
    rw [hαR, hc0]; field_simp; ring_nf
  have hc0'' : π ^ 2 * (1 / α).re / (2 * (3 / 2) * K ^ 2) = 2 * c0 := by
    rw [hαR, hc0]; field_simp; ring_nf
  rw [hc0', hc0'']
  -- the sum of `Jb`
  have hW : √(π / (3 / 2 * α.re)) ≤ 1 / ‖z‖ := by
    rw [hαre, hRe]
    have : π / (3 / 2 * (2 * π * ((1 / z).re * ‖z‖ ^ 2) / K)) = K / (3 * (1 / z).re * ‖z‖ ^ 2) := by
      field_simp
    rw [this, show 1 / ‖z‖ = √(1 / ‖z‖ ^ 2) by rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hzn.le,
      Real.sqrt_one]]
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ‖z‖, mul_pos hzn hzn]
  have hαn0 : ‖α‖ ≠ 0 := by rw [hαn]; positivity
  have hn2 : ‖α‖ ^ 2 * (1 / α).re = α.re := by
    rw [one_div, inv_re, Complex.normSq_eq_norm_sq]; field_simp
  have hR1 : 1 / (4 * π) ≤ (1 / α).re := by
    have hKR : (1 : ℝ) / 2 ≤ K * (1 / z).re := by nlinarith
    rw [hαR, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [Real.pi_pos]
  have hN : 16 * ‖α‖ ^ 2 * 1 ^ 2 / (π ^ 2 * (3 / 2) * α.re) ≤ 15 := by
    rw [div_le_iff₀ (by positivity), ← hn2]
    have ha2 : 0 ≤ ‖α‖ ^ 2 := sq_nonneg _
    have h3 : ‖α‖ ^ 2 * (1 / (4 * π)) ≤ ‖α‖ ^ 2 * (1 / α).re := mul_le_mul_of_nonneg_left hR1 ha2
    have h4 : ‖α‖ ^ 2 * (1 / (4 * π)) * (15 * π ^ 2 * (3 / 2)) = ‖α‖ ^ 2 * (45 * π / 8) := by
      field_simp; ring
    have h5 : 16 * ‖α‖ ^ 2 ≤ ‖α‖ ^ 2 * (45 * π / 8) := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 15 * π ^ 2 * (3 / 2))]
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
  have hgρ : ∀ ρ : ℕ, 0 < δ ρ - π * 1 / (2 * K * (3 / 2)) := fun ρ => by linarith [hgap' ρ]
  have hG' : ∑ ρ ∈ Finset.range K, 1 / √(δ ρ - π * 1 / (2 * K * (3 / 2))) ≤ G₀ * K := by
    have e : π * 1 / (2 * K * (3 / 2)) = π / (3 * K) := by ring
    rw [e]; exact hG
  have hS := sumJb_le (g := fun ρ : ℕ => δ ρ - π * 1 / (2 * K * (3 / 2))) hα (by norm_num : (0 : ℝ) < 3 / 2)
    one_pos hK0 hgρ hzn hz2 hW hN h1 h2 hG'
  -- the remaining constants
  have he : Real.exp ((1 / 2) ^ 2 * α.re / (4 * (3 / 2))) ≤ 3 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) (Real.exp_one_lt_d9.le.trans (by norm_num))
    rw [hαre]
    have : z.re ≤ 2 := (Complex.re_le_norm z).trans hz2
    rw [div_le_one (by norm_num)]
    have h1 : 2 * π * z.re / K ≤ 2 * π * 2 := by
      rw [div_le_iff₀ hKr]; nlinarith [Real.pi_pos]
    nlinarith [Real.pi_lt_d2]
  have hsinh : 0 < 1 / Real.sinh (2 * c0) := by
    have : 0 < c0 := by positivity
    exact one_div_pos.mpr (Real.sinh_pos_iff.mpr (by linarith))
  rw [Real.exp_add]
  set SJ := ∑ ρ ∈ Finset.range K,
      Jb α (3 / 2) 1 K (min 1 (‖α‖ * ((1 / α).re * (δ ρ - π * 1 / (2 * K * (3 / 2))))) / 3) with hSJ
  have hSJ0 : 0 ≤ SJ := Finset.sum_nonneg fun ρ _ => by unfold Jb; positivity
  have hS' : SJ ≤ CstO G₀ / (‖z‖ * √‖z‖) := hS
  have he' : Real.exp c0 * Real.exp ((1 / 2) ^ 2 * α.re / (4 * (3 / 2))) ≤ Real.exp c0 * 3 :=
    mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
  calc Real.exp c0 * Real.exp ((1 / 2) ^ 2 * α.re / (4 * (3 / 2))) * SJ * (1 / Real.sinh (2 * c0))
      ≤ Real.exp c0 * 3 * (CstO G₀ / (‖z‖ * √‖z‖)) * (1 / Real.sinh (2 * c0)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul he' hS' hSJ0 (by positivity)) hsinh.le
    _ = _ := by ring

/-! ### the phases of `f` and `φ` -/

lemma odd_emod_bounds {N M : ℤ} (hM : 0 < M) (hN : N % 2 = 1) (hM2 : (2 : ℤ) ∣ M) :
    1 ≤ N % M ∧ 1 ≤ M - N % M := by
  have h0 : 0 ≤ N % M := Int.emod_nonneg _ hM.ne'
  have h1 : N % M < M := Int.emod_lt_of_pos _ hM
  have h2 : N % M % 2 = 1 := by rw [Int.emod_emod_of_dvd _ hM2]; exact hN
  obtain ⟨M', rfl⟩ := hM2
  omega

lemma emod_inj_of_coprime {K : ℕ} (hK : 0 < K) {h : ℕ} (hcop : Nat.Coprime h K) {a : ℤ} (ha : a ≠ 0)
    {c₀ : ℤ} {ρ ρ' : ℕ} (hρ : ρ < K) (hρ' : ρ' < K)
    (heq : (c₀ + a * h * ρ) % (a * K) = (c₀ + a * h * ρ') % (a * K)) : ρ = ρ' := by
  have hd : (a * K : ℤ) ∣ (c₀ + a * h * ρ') - (c₀ + a * h * ρ) := Int.ModEq.dvd heq
  rw [show (c₀ + a * h * ρ') - (c₀ + a * h * ρ) = a * (h * ((ρ' : ℤ) - ρ)) by ring] at hd
  have hd2 : (K : ℤ) ∣ h * ((ρ' : ℤ) - ρ) := (mul_dvd_mul_iff_left ha).mp hd
  have hc : IsCoprime (K : ℤ) (h : ℤ) := (Nat.isCoprime_iff_coprime.mpr hcop).symm
  have hd3 : (K : ℤ) ∣ (ρ' : ℤ) - ρ := hc.dvd_of_dvd_mul_left hd2
  have hlt : |(ρ' : ℤ) - ρ| < K := by rw [abs_lt]; constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hd3 hlt
  omega

/-- the separation of `f`'s phases. -/
def δK (h K : ℕ) (n : ℤ) : ℝ :=
  π / K * (min ((K + 2 * h * (n % (K : ℤ))) % (2 * K : ℤ)) (2 * K - (K + 2 * h * (n % (K : ℤ))) % (2 * K : ℤ)) : ℤ)

lemma δK_sep {h K : ℕ} (hK : Odd K) (n k : ℤ) : δK h K n ≤ |θK h K n - 2 * π * k| := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK.pos
  have hM : (0 : ℤ) < 2 * K := by have := hK.pos; omega
  have e : θK h K n - 2 * π * k = π / K * (((K + 2 * h * (n % (K : ℤ))) - k * (2 * K) : ℤ) : ℝ) := by
    simp only [θK]; push_cast; field_simp; try ring
  rw [e, abs_mul, abs_of_pos (by positivity), δK]
  gcongr
  exact_mod_cast int_dist _ k hM

lemma δK_ge {h K : ℕ} (hK : Odd K) (n : ℤ) : π / K ≤ δK h K n := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK.pos
  have hM : (0 : ℤ) < 2 * K := by have := hK.pos; omega
  have hodd : ((K : ℤ) + 2 * h * (n % (K : ℤ))) % 2 = 1 := by
    rw [show (K : ℤ) + 2 * h * (n % (K : ℤ)) = K + 2 * (h * (n % (K : ℤ))) by ring, Int.add_mul_emod_self_left]
    exact Int.odd_iff.mp (by exact_mod_cast hK)
  obtain ⟨h1, h2⟩ := odd_emod_bounds hM hodd ⟨K, by ring⟩
  have : (1 : ℝ) ≤ ((min ((K + 2 * h * (n % (K : ℤ))) % (2 * K : ℤ))
      (2 * K - (K + 2 * h * (n % (K : ℤ))) % (2 * K : ℤ)) : ℤ) : ℝ) := by exact_mod_cast le_min h1 h2
  unfold δK
  nlinarith [div_pos Real.pi_pos hK0]

/-- **the phase sum for `f`**. -/
lemma f_phase_sum {h K : ℕ} (hK : Odd K) (hcop : Nat.Coprime h K) :
    ∑ ρ ∈ Finset.range K, 1 / √(δK h K ρ - π / (3 * K)) ≤ 4 * √(3 / π) * K := by
  have hK0 : 0 < K := hK.pos
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  have hM : (0 : ℤ) < 2 * K := by omega
  set r : ℕ → ℕ := fun ρ => (((K : ℤ) + 2 * h * ρ) % (2 * K : ℤ)).toNat
  have hrz : ∀ ρ < K, ((r ρ : ℕ) : ℤ) = ((K : ℤ) + 2 * h * ρ) % (2 * K : ℤ) := fun ρ _ =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hM.ne')
  have hmod : ∀ ρ < K, ((ρ : ℤ) % (K : ℤ)) = ρ := fun ρ hρ => Int.emod_eq_of_lt (by omega) (by omega)
  have hodd : ∀ ρ : ℕ, ((K : ℤ) + 2 * h * ρ) % 2 = 1 := by
    intro ρ
    rw [show (K : ℤ) + 2 * h * ρ = K + 2 * (h * ρ) by ring, Int.add_mul_emod_self_left]
    exact Int.odd_iff.mp (by exact_mod_cast hK)
  have hc : (0 : ℝ) < 2 * π / (3 * K) := by positivity
  have key := class_phase_sum (T := K) (M := 2 * K) hc r
    (fun ρ hρ => by
      have := (odd_emod_bounds hM (hodd ρ) ⟨K, by ring⟩).1
      have h' : (1 : ℤ) ≤ ((r ρ : ℕ) : ℤ) := by rw [hrz ρ hρ]; exact this
      exact_mod_cast h')
    (fun ρ hρ => by
      have := Int.emod_lt_of_pos ((K : ℤ) + 2 * h * ρ) hM
      have h' : ((r ρ : ℕ) : ℤ) < ((2 * K : ℕ) : ℤ) := by rw [hrz ρ hρ]; push_cast; exact this
      exact_mod_cast h')
    (fun ρ hρ ρ' hρ' heq => by
      have e : ((K : ℤ) + 2 * h * ρ) % (2 * K : ℤ) = ((K : ℤ) + 2 * h * ρ') % (2 * K : ℤ) := by
        rw [← hrz ρ hρ, ← hrz ρ' hρ', heq]
      exact emod_inj_of_coprime hK0 hcop (a := 2) two_ne_zero hρ hρ' e)
    (fun ρ => δK h K ρ - π / (3 * K))
    (fun ρ hρ => by
      have hge := δK_ge (h := h) hK ρ
      simp only [δK]
      rw [hmod ρ hρ, ← hrz ρ hρ]
      push_cast
      set mn := min ((r ρ : ℕ) : ℝ) (2 * (K : ℝ) - (r ρ : ℕ))
      have hd : δK h K ρ = π / K * mn := by
        simp only [δK, mn]; rw [hmod ρ hρ, ← hrz ρ hρ]; push_cast; rfl
      rw [hd] at hge
      have : π / (3 * K) ≤ (1 / 3) * (π / K * mn) := by
        rw [show π / (3 * K) = (1 / 3) * (π / K) by ring]; gcongr; try linarith
      have e : 2 * π / (3 * K) * mn = (2 / 3) * (π / K * mn) := by ring
      linarith)
  refine key.trans (le_of_eq ?_)
  push_cast
  rw [mul_div_assoc, ← Real.sqrt_div' _ hc.le, show 2 * (K : ℝ) / (2 * π / (3 * K)) = (3 / π) * K ^ 2 by field_simp,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hKr.le]
  ring

/-- the separation of `φ`'s phases. -/
def δP (h K : ℕ) (n : ℤ) : ℝ :=
  π / (2 * K) * (min ((K + 4 * h * (n % (K : ℤ))) % (4 * K : ℤ)) (4 * K - (K + 4 * h * (n % (K : ℤ))) % (4 * K : ℤ)) : ℤ)

lemma δP_sep {h K : ℕ} (hK : Odd K) (n k : ℤ) : δP h K n ≤ |θP h K n - 2 * π * k| := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK.pos
  have hM : (0 : ℤ) < 4 * K := by have := hK.pos; omega
  have e : θP h K n - 2 * π * k = π / (2 * K) * (((K + 4 * h * (n % (K : ℤ))) - k * (4 * K) : ℤ) : ℝ) := by
    simp only [θP]; push_cast; field_simp; try ring
  rw [e, abs_mul, abs_of_pos (by positivity), δP]
  gcongr
  exact_mod_cast int_dist _ k hM

lemma δP_ge {h K : ℕ} (hK : Odd K) (n : ℤ) : π / (2 * K) ≤ δP h K n := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK.pos
  have hM : (0 : ℤ) < 4 * K := by have := hK.pos; omega
  have hodd : ((K : ℤ) + 4 * h * (n % (K : ℤ))) % 2 = 1 := by
    rw [show (K : ℤ) + 4 * h * (n % (K : ℤ)) = K + 2 * (2 * h * (n % (K : ℤ))) by ring, Int.add_mul_emod_self_left]
    exact Int.odd_iff.mp (by exact_mod_cast hK)
  obtain ⟨h1, h2⟩ := odd_emod_bounds hM hodd ⟨2 * K, by ring⟩
  have : (1 : ℝ) ≤ ((min ((K + 4 * h * (n % (K : ℤ))) % (4 * K : ℤ))
      (4 * K - (K + 4 * h * (n % (K : ℤ))) % (4 * K : ℤ)) : ℤ) : ℝ) := by exact_mod_cast le_min h1 h2
  unfold δP
  nlinarith [div_pos Real.pi_pos (by positivity : (0 : ℝ) < 2 * K)]

/-- **the phase sum for `φ`**. -/
lemma phi_phase_sum {h K : ℕ} (hK : Odd K) (hcop : Nat.Coprime h K) :
    ∑ ρ ∈ Finset.range K, 1 / √(δP h K ρ - π / (3 * K)) ≤ 4 * √(24 / π) * K := by
  have hK0 : 0 < K := hK.pos
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  have hM : (0 : ℤ) < 4 * K := by omega
  set r : ℕ → ℕ := fun ρ => (((K : ℤ) + 4 * h * ρ) % (4 * K : ℤ)).toNat
  have hrz : ∀ ρ < K, ((r ρ : ℕ) : ℤ) = ((K : ℤ) + 4 * h * ρ) % (4 * K : ℤ) := fun ρ _ =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hM.ne')
  have hmod : ∀ ρ < K, ((ρ : ℤ) % (K : ℤ)) = ρ := fun ρ hρ => Int.emod_eq_of_lt (by omega) (by omega)
  have hodd : ∀ ρ : ℕ, ((K : ℤ) + 4 * h * ρ) % 2 = 1 := by
    intro ρ
    rw [show (K : ℤ) + 4 * h * ρ = K + 2 * (2 * h * ρ) by ring, Int.add_mul_emod_self_left]
    exact Int.odd_iff.mp (by exact_mod_cast hK)
  have hc : (0 : ℝ) < π / (6 * K) := by positivity
  have key := class_phase_sum (T := K) (M := 4 * K) hc r
    (fun ρ hρ => by
      have := (odd_emod_bounds hM (hodd ρ) ⟨2 * K, by ring⟩).1
      have h' : (1 : ℤ) ≤ ((r ρ : ℕ) : ℤ) := by rw [hrz ρ hρ]; exact this
      exact_mod_cast h')
    (fun ρ hρ => by
      have := Int.emod_lt_of_pos ((K : ℤ) + 4 * h * ρ) hM
      have h' : ((r ρ : ℕ) : ℤ) < ((4 * K : ℕ) : ℤ) := by rw [hrz ρ hρ]; push_cast; exact this
      exact_mod_cast h')
    (fun ρ hρ ρ' hρ' heq => by
      have e : ((K : ℤ) + 4 * h * ρ) % (4 * K : ℤ) = ((K : ℤ) + 4 * h * ρ') % (4 * K : ℤ) := by
        rw [← hrz ρ hρ, ← hrz ρ' hρ', heq]
      exact emod_inj_of_coprime hK0 hcop (a := 4) (by norm_num) hρ hρ' e)
    (fun ρ => δP h K ρ - π / (3 * K))
    (fun ρ hρ => by
      have hge := δP_ge (h := h) hK ρ
      set mn := min ((r ρ : ℕ) : ℝ) (4 * (K : ℝ) - (r ρ : ℕ))
      have hd : δP h K ρ = π / (2 * K) * mn := by
        simp only [δP, mn]; rw [hmod ρ hρ, ← hrz ρ hρ]; push_cast; rfl
      rw [hd] at hge
      simp only
      rw [hd]
      have : π / (3 * K) ≤ (2 / 3) * (π / (2 * K) * mn) := by
        rw [show π / (3 * K) = (2 / 3) * (π / (2 * K)) by field_simp; try ring]; gcongr
      have e : π / (6 * K) * mn = (1 / 3) * (π / (2 * K) * mn) := by field_simp; ring
      push_cast
      linarith)
  refine key.trans (le_of_eq ?_)
  push_cast
  rw [mul_div_assoc, ← Real.sqrt_div' _ hc.le, show 4 * (K : ℝ) / (π / (6 * K)) = (24 / π) * K ^ 2 by field_simp; ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hKr.le]
  ring

/-! ### the bounds -/

lemma exp_sinh_le' {c : ℝ} (hc : π / 24 ≤ c) (C : ℝ) (hC : 0 ≤ C) :
    Real.exp c * (3 * Real.exp c * (1 / Real.sinh (2 * c))) * C ≤ 18 * C := by
  have := exp_sq_div_sinh_le hc
  nlinarith

/-- **`f` near an odd-order root of unity, `D = 1`**. -/
theorem f_odd_bound' {K : ℕ} (hK : Odd K) {h : ℕ} (hcop : Nat.Coprime h K) {z : ℂ} (hz : 0 < z.re)
    (hR : (K : ℝ) / 2 ≤ (1 / z).re) :
    ‖MockTheta3.Radial.fA (Rademacher.qp h K z)‖ ≤
      36 * (1 + HardyRamanujan.C0) * CstO (4 * √(3 / π)) * ‖z‖ ^ (-(1 : ℝ)) := by
  have hK0 : 0 < K := hK.pos
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr fun h0 => by rw [h0] at hz; simp at hz
  obtain ⟨hs, hb⟩ := sharp_odd_AL (h := h) hK hz hR (θK_per h K) (δK_sep hK)
    (fun n => lt_of_lt_of_le (by rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [Real.pi_pos])
      (δK_ge hK n)) (f_phase_sum hK hcop)
  set c0 := π * (1 / z).re / (12 * K) with hc0
  have hc0lb : π / 24 ≤ c0 := by
    rw [hc0, le_div_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
  have hG : ‖fG (Rademacher.qp h K z)‖ ≤ 2 * (3 * Real.exp c0 * (1 / Real.sinh (2 * c0)) *
      (CstO (4 * √(3 / π)) / (‖z‖ * √‖z‖))) := by
    rw [fG_eq_al hK0 hz hs, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have hq : Rademacher.qp h K z ∈ ball (0 : ℂ) 1 := Rademacher.qp_mem hK0 hz
  have hfa : MockTheta3.Radial.fA (Rademacher.qp h K z) =
      fG (Rademacher.qp h K z) * HardyRamanujan.F (Rademacher.qp h K z) := by
    rw [← f_AL hq, HardyRamanujan.F, mul_assoc, mul_inv_cancel₀ (HardyRamanujan.Pq_ne_zero hq), mul_one]
  rw [hfa, norm_mul]
  have hFb := F_bound hK0 hcop hz hR
  rw [← hc0] at hFb
  have hC0 := HardyRamanujan.C0_nonneg
  have hCst : 0 ≤ CstO (4 * √(3 / π)) := by unfold CstO; positivity
  have hsz : 0 < √‖z‖ := Real.sqrt_pos.mpr hzn
  have hfin := exp_sinh_le' hc0lb (CstO (4 * √(3 / π)) / (‖z‖ * √‖z‖)) (by positivity)
  calc ‖fG (Rademacher.qp h K z)‖ * ‖HardyRamanujan.F (Rademacher.qp h K z)‖
      ≤ (2 * (3 * Real.exp c0 * (1 / Real.sinh (2 * c0)) * (CstO (4 * √(3 / π)) / (‖z‖ * √‖z‖)))) *
          ((1 + HardyRamanujan.C0) * √‖z‖ * Real.exp c0) :=
        mul_le_mul hG hFb (norm_nonneg _) ((norm_nonneg _).trans hG)
    _ = 2 * (1 + HardyRamanujan.C0) * √‖z‖ *
          (Real.exp c0 * (3 * Real.exp c0 * (1 / Real.sinh (2 * c0))) *
            (CstO (4 * √(3 / π)) / (‖z‖ * √‖z‖))) := by ring
    _ ≤ 2 * (1 + HardyRamanujan.C0) * √‖z‖ * (18 * (CstO (4 * √(3 / π)) / (‖z‖ * √‖z‖))) := by gcongr
    _ = 36 * (1 + HardyRamanujan.C0) * CstO (4 * √(3 / π)) * ‖z‖ ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg_one]; field_simp; ring

set_option maxHeartbeats 1000000 in
/-- **`φ` near an odd-order root of unity, `D = 1`**. -/
theorem phi_odd_bound' {K : ℕ} (hK : Odd K) {h : ℕ} (hcop : Nat.Coprime h K) {z : ℂ} (hz : 0 < z.re)
    (hR : (K : ℝ) / 2 ≤ (1 / z).re) :
    ‖Rd I (Rademacher.qp h K z)‖ ≤ 36 * (1 + HardyRamanujan.C0) * CstO (4 * √(24 / π)) * ‖z‖ ^ (-(1 : ℝ)) := by
  have hK0 : 0 < K := hK.pos
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr fun h0 => by rw [h0] at hz; simp at hz
  obtain ⟨hs, hb⟩ := sharp_odd_AL (h := h) hK hz hR (θP_per h K) (δP_sep hK)
    (fun n => lt_of_lt_of_le (by rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [Real.pi_pos])
      (δP_ge hK n)) (phi_phase_sum hK hcop)
  set c0 := π * (1 / z).re / (12 * K) with hc0
  have hc0lb : π / 24 ≤ c0 := by
    rw [hc0, le_div_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
  have hsum : Summable (tmL I (LK h K z)) := by
    have e : alTerm (αK K z) (3 / 2) (1 / 2) 1 0 (cK h K) (fun n => cexp (I * θP h K n)) = tmL I (LK h K z) := by
      funext n; exact alTerm_phi hK0 z n
    rw [← e]; exact hs
  have hG : ‖Ad I (Rademacher.qp h K z)‖ ≤ 2 * (3 * Real.exp c0 * (1 / Real.sinh (2 * c0)) *
      (CstO (4 * √(24 / π)) / (‖z‖ * √‖z‖))) := by
    rw [qp_eq_LK, Ad_bilateral I_ne_zero (by simp [Complex.ext_iff]) (den_phi hK0 hz) hsum, norm_mul]
    have e : ∑' n, tmL I (LK h K z) n = ∑' n, alTerm (αK K z) (3 / 2) (1 / 2) 1 0 (cK h K)
        (fun n => cexp (I * θP h K n)) n := tsum_congr fun n => (alTerm_phi hK0 z n).symm
    rw [e]
    have h1I : ‖(1 : ℂ) - I‖ ≤ 2 := (norm_sub_le _ _).trans (by simp; norm_num)
    exact mul_le_mul h1I hb (norm_nonneg _) (by norm_num)
  have hq : Rademacher.qp h K z ∈ ball (0 : ℂ) 1 := Rademacher.qp_mem hK0 hz
  have hq1 : ‖Rademacher.qp h K z‖ < 1 := by simpa using hq
  have hfa : Rd I (Rademacher.qp h K z) =
      Ad I (Rademacher.qp h K z) * HardyRamanujan.F (Rademacher.qp h K z) := by
    rw [← rank_disc I_ne_zero (by simpa using hq1) (by simpa using hq1), HardyRamanujan.F, mul_comm,
      ← mul_assoc, inv_mul_cancel₀ (HardyRamanujan.Pq_ne_zero hq), one_mul]
  rw [hfa, norm_mul]
  have hFb := F_bound hK0 hcop hz hR
  rw [← hc0] at hFb
  have hC0 := HardyRamanujan.C0_nonneg
  have hCst : 0 ≤ CstO (4 * √(24 / π)) := by unfold CstO; positivity
  have hsz : 0 < √‖z‖ := Real.sqrt_pos.mpr hzn
  have hfin := exp_sinh_le' hc0lb (CstO (4 * √(24 / π)) / (‖z‖ * √‖z‖)) (by positivity)
  calc ‖Ad I (Rademacher.qp h K z)‖ * ‖HardyRamanujan.F (Rademacher.qp h K z)‖
      ≤ (2 * (3 * Real.exp c0 * (1 / Real.sinh (2 * c0)) * (CstO (4 * √(24 / π)) / (‖z‖ * √‖z‖)))) *
          ((1 + HardyRamanujan.C0) * √‖z‖ * Real.exp c0) :=
        mul_le_mul hG hFb (norm_nonneg _) ((norm_nonneg _).trans hG)
    _ = 2 * (1 + HardyRamanujan.C0) * √‖z‖ *
          (Real.exp c0 * (3 * Real.exp c0 * (1 / Real.sinh (2 * c0))) *
            (CstO (4 * √(24 / π)) / (‖z‖ * √‖z‖))) := by ring
    _ ≤ 2 * (1 + HardyRamanujan.C0) * √‖z‖ * (18 * (CstO (4 * √(24 / π)) / (‖z‖ * √‖z‖))) := by gcongr
    _ = 36 * (1 + HardyRamanujan.C0) * CstO (4 * √(24 / π)) * ‖z‖ ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg_one]; field_simp; ring

end

end MockCusp
