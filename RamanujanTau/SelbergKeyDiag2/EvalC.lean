/-
# M3 step 2a: complex evaluation of the local power series on `Re s = 1`

`evC x f = Σ_j coeff_j(f) x^j` at `x = p^{−s}`, `Re s = 1` (so `|x| = 1/p`), with the absolute
summability of `HafnerBridge2.Eval` (`SN`).  Since `g_p(a)·D_p = U_p(a)` and `ε_p·D_p = 1` as power
series (`gps_mul_Dps`, `eps_mul_Dps`):

    Σ_j g_j p^{−js} = N_p(a, s)/D_p(s)        (`evC_gps`),

the complex local factor of `SelbergKey.Arith.rhoC`.  Level 1.
-/
import RamanujanTau.SelbergKey.Arith
import RamanujanTau.HafnerBridge2.Eval

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex Finset PowerSeries RamanujanTau.HafnerBridge RamanujanTau.HafnerBridge2
open RamanujanTau.SelbergKey (NpC DpC rhoC lamK)

/-- `evC x f = Σ_j coeff_j(f) x^j`. -/
noncomputable def evC (x : ℂ) (f : PowerSeries ℝ) : ℂ := ∑' j : ℕ, ((coeff j f : ℝ) : ℂ) * x ^ j

lemma norm_term_evC {x : ℂ} {p : ℕ} (hx : ‖x‖ = (p : ℝ)⁻¹) (f : PowerSeries ℝ) (j : ℕ) :
    ‖((coeff j f : ℝ) : ℂ) * x ^ j‖ = ‖coeff j f * ((p : ℝ)⁻¹) ^ j‖ := by
  rw [norm_mul, norm_mul, Complex.norm_real, norm_pow, norm_pow, hx]
  simp

lemma SNC {x : ℂ} {p : ℕ} (hx : ‖x‖ = (p : ℝ)⁻¹) {f : PowerSeries ℝ} (hf : SN ((p : ℝ)⁻¹) f) :
    Summable fun j : ℕ => ‖((coeff j f : ℝ) : ℂ) * x ^ j‖ :=
  hf.congr fun j => (norm_term_evC hx f j).symm

lemma coeff_mul_xpowC (x : ℂ) (f g : PowerSeries ℝ) (n : ℕ) :
    ((coeff n (f * g) : ℝ) : ℂ) * x ^ n =
      ∑ kl ∈ antidiagonal n, (((coeff kl.1 f : ℝ) : ℂ) * x ^ kl.1) * (((coeff kl.2 g : ℝ) : ℂ) * x ^ kl.2) := by
  rw [coeff_mul, Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [mem_antidiagonal] at hkl
  rw [← hkl, pow_add]; push_cast; ring

lemma evC_mul {x : ℂ} {p : ℕ} (hx : ‖x‖ = (p : ℝ)⁻¹) {f g : PowerSeries ℝ}
    (hf : SN ((p : ℝ)⁻¹) f) (hg : SN ((p : ℝ)⁻¹) g) : evC x (f * g) = evC x f * evC x g := by
  unfold evC
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (f := fun k => ((coeff k f : ℝ) : ℂ) * x ^ k)
    (g := fun k => ((coeff k g : ℝ) : ℂ) * x ^ k) (SNC hx hf) (SNC hx hg)]
  simp_rw [coeff_mul_xpowC]

lemma evC_one (x : ℂ) : evC x 1 = 1 := by
  unfold evC
  rw [tsum_eq_single 0 (fun j hj => by rw [coeff_one, if_neg hj]; simp)]
  simp

lemma norm_p_cpow {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : s.re = 1) : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ)⁻¹ := by
  rw [norm_natCast_cpow_of_pos hp.pos]
  simp [hs, Real.rpow_neg_one]

lemma p_cpow_nat_mul (p : ℕ) (s : ℂ) (j : ℕ) : (p : ℂ) ^ (-((j : ℂ) * s)) = ((p : ℂ) ^ (-s)) ^ j := by
  rw [← Complex.cpow_nat_mul]; congr 1; ring

lemma evC_Ups {p : ℕ} (a : ℕ) (s : ℂ) : evC ((p : ℂ) ^ (-s)) (Ups p a) = NpC p a s := by
  unfold evC NpC
  refine tsum_congr fun j => ?_
  rw [Ups, coeff_mk, p_cpow_nat_mul]

lemma evC_Dps {p : ℕ} (s : ℂ) : evC ((p : ℂ) ^ (-s)) (Dps p) = DpC p s := by
  unfold evC DpC
  refine tsum_congr fun j => ?_
  rw [Dps, coeff_mk, p_cpow_nat_mul]

/-- **`Σ_j g_j p^{−js} = N_p(a,s)/D_p(s)`** on `Re s = 1`, and `D_p(s) ≠ 0` there. -/
theorem evC_gps {p : ℕ} (hp : p.Prime) (a : ℕ) {s : ℂ} (hs : s.re = 1) :
    DpC p s ≠ 0 ∧ evC ((p : ℂ) ^ (-s)) (gps p a) = NpC p a s / DpC p s := by
  obtain ⟨C, hC1, hC⟩ := lam_bound
  have hx := norm_p_cpow hp hs
  have hD := SN_Dps hC1 hC hp
  have hE := SN_eps hp
  have hU := SN_Ups hC1 hC hp a
  have h1 : evC ((p : ℂ) ^ (-s)) (eps p) * DpC p s = 1 := by
    rw [← evC_Dps, ← evC_mul hx hE hD, eps_mul_Dps, evC_one]
  have hD0 : DpC p s ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
  refine ⟨hD0, ?_⟩
  have h2 : evC ((p : ℂ) ^ (-s)) (gps p a) = evC ((p : ℂ) ^ (-s)) (Ups p a) * evC ((p : ℂ) ^ (-s)) (eps p) := by
    rw [gps, evC_mul hx hU hE]
  rw [h2, evC_Ups, eq_div_iff hD0, mul_assoc, h1, mul_one]

end RamanujanTau.SelbergKeyDiag2
