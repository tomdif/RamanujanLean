/-
# Evaluating the local power series at `X = 1/p`: `G = ρ_p(a)`, `log p · G' = −ρ_p'(a)`

With `ev f = Σ coeff_j(f) p^{−j}` and `θ f = Σ j coeff_j(f) X^j`:

* `ev_Ups = N_p(a)`, `ev_Dps = D_p`, `−log p · ev(θ U) = N_p'(a)`, `−log p · ev(θ D) = D_p'`;
* `ev_eps = 1/D_p` (from `e·D = 1`), `ev(θ e) = −ev(θ D)/D_p²` (from `θ(e·D) = 0`);
* `ev_gps : ev g = ρ_p(a)` and `log_mul_ev_theta_gps : log p · ev(θ g) = −ρ_p'(a)`.
* `Sg_gps_le`: `Σ (1 + j log p)|g_j| p^{−4j/5} ≤ W p^{3a}` with `W` depending only on the constant of
  `|λ(n)| ≤ C n^{11/40}`.
-/
import RamanujanTau.HafnerBridge2.Peel

set_option autoImplicit false

namespace RamanujanTau.HafnerBridge2

open Finset PowerSeries
open RamanujanTau.HafnerBridge

/-- `ev f = Σ_j coeff_j(f) x^j`. -/
noncomputable def ev (x : ℝ) (f : PowerSeries ℝ) : ℝ := ∑' j : ℕ, coeff j f * x ^ j

/-- absolute convergence at `x`. -/
def SN (x : ℝ) (f : PowerSeries ℝ) : Prop := Summable fun j : ℕ => ‖coeff j f * x ^ j‖

lemma coeff_mul_xpow (x : ℝ) (f g : PowerSeries ℝ) (n : ℕ) :
    coeff n (f * g) * x ^ n = ∑ kl ∈ antidiagonal n, (coeff kl.1 f * x ^ kl.1) * (coeff kl.2 g * x ^ kl.2) := by
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [mem_antidiagonal] at hkl
  rw [← hkl, pow_add]; ring

lemma SN_mul {x : ℝ} {f g : PowerSeries ℝ} (hf : SN x f) (hg : SN x g) : SN x (f * g) := by
  unfold SN
  simp_rw [coeff_mul_xpow]
  exact summable_norm_sum_mul_antidiagonal_of_summable_norm (f := fun k => coeff k f * x ^ k)
    (g := fun k => coeff k g * x ^ k) hf hg

lemma ev_mul {x : ℝ} {f g : PowerSeries ℝ} (hf : SN x f) (hg : SN x g) : ev x (f * g) = ev x f * ev x g := by
  unfold ev
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (f := fun k => coeff k f * x ^ k)
    (g := fun k => coeff k g * x ^ k) hf hg]
  simp_rw [coeff_mul_xpow]

lemma SN_add {x : ℝ} {f g : PowerSeries ℝ} (hf : SN x f) (hg : SN x g) : SN x (f + g) := by
  unfold SN
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_) (hf.add hg)
  rw [map_add, add_mul]; exact norm_add_le _ _

lemma ev_add {x : ℝ} {f g : PowerSeries ℝ} (hf : SN x f) (hg : SN x g) : ev x (f + g) = ev x f + ev x g := by
  unfold ev
  simp_rw [map_add, add_mul]
  exact Summable.tsum_add hf.of_norm hg.of_norm

lemma ev_one (x : ℝ) : ev x 1 = 1 := by
  unfold ev
  rw [tsum_eq_single 0 (fun j hj => by rw [coeff_one, if_neg hj, zero_mul])]
  simp

lemma ev_zero (x : ℝ) : ev x 0 = 0 := by simp [ev]

/-- `θ f = Σ j coeff_j(f) X^j`. -/
noncomputable def θ (f : PowerSeries ℝ) : PowerSeries ℝ := PowerSeries.mk fun j => (j : ℝ) * coeff j f

lemma θ_mul (f g : PowerSeries ℝ) : θ (f * g) = θ f * g + f * θ g := by
  ext n
  simp only [θ, map_add, coeff_mk, coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [mem_antidiagonal] at hkl
  rw [← hkl]; push_cast; ring

lemma θ_one : θ 1 = 0 := by
  ext n; simp only [θ, coeff_mk, coeff_one, map_zero]; split_ifs with h <;> simp [h]

/-! ### Bounds and absolute convergence at `x = 1/p` -/

lemma rpow_neg_nat_eq {p : ℕ} (hp : p.Prime) (j : ℕ) : (p : ℝ) ^ (-(j : ℝ)) = ((p : ℝ)⁻¹) ^ j := by
  rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast, inv_pow]

section
variable {C : ℝ} (hC1 : 1 ≤ C) (hC : ∀ n : ℕ, 1 ≤ n → |lam n| ≤ C * (n : ℝ) ^ (11 / 40 : ℝ))
include hC1 hC

lemma abs_coeff_Ups_le {p : ℕ} (hp : p.Prime) (a j : ℕ) :
    |coeff j (Ups p a)| * ((p : ℝ)⁻¹) ^ j ≤ C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a) * ((p : ℝ) ^ (-(9 / 20 : ℝ))) ^ j := by
  have := term_bound hC1 hC hp a j
  rw [rpow_neg_nat_eq hp] at this
  simpa [Ups, coeff_mk] using this

omit hC1 hC in
lemma ratio_norm {p : ℕ} (hp : p.Prime) : ‖(p : ℝ) ^ (-(9 / 20 : ℝ))‖ < 1 := by
  rw [Real.norm_of_nonneg (by positivity)]; exact ratio_lt hp

lemma SN_Ups {p : ℕ} (hp : p.Prime) (a : ℕ) : SN ((p : ℝ)⁻¹) (Ups p a) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
    ((summable_geometric_of_lt_one (by positivity) (ratio_lt hp)).mul_left
      (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a)))
  rw [norm_mul, Real.norm_eq_abs, norm_pow, norm_inv, Real.norm_natCast]
  exact abs_coeff_Ups_le hC1 hC hp a j

lemma SN_θUps {p : ℕ} (hp : p.Prime) (a : ℕ) : SN ((p : ℝ)⁻¹) (θ (Ups p a)) := by
  have hg := summable_pow_mul_geometric_of_norm_lt_one 1 (ratio_norm hp)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
    (hg.mul_left (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a)))
  simp only [θ, coeff_mk, norm_mul, Real.norm_eq_abs, abs_pow, abs_inv, Nat.abs_cast, pow_one]
  have := abs_coeff_Ups_le hC1 hC hp a j
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  calc (j : ℝ) * |coeff j (Ups p a)| * ((p : ℝ)⁻¹) ^ j = (j : ℝ) * (|coeff j (Ups p a)| * ((p : ℝ)⁻¹) ^ j) := by
        ring
    _ ≤ (j : ℝ) * (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a) * ((p : ℝ) ^ (-(9 / 20 : ℝ))) ^ j) :=
        mul_le_mul_of_nonneg_left this hj
    _ = _ := by ring

end

lemma Dps_eq_Ups (p : ℕ) : Dps p = Ups p 0 := by
  ext j; simp [Dps, Ups, sq]

lemma inv_p_lt_one {p : ℕ} (hp : p.Prime) : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

lemma SN_eps {p : ℕ} (hp : p.Prime) : SN ((p : ℝ)⁻¹) (eps p) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
    ((summable_geometric_of_lt_one (by positivity) (inv_p_lt_one hp)).mul_left (4 + 2 * lam p ^ 2))
  rw [norm_mul, Real.norm_eq_abs, norm_pow, norm_inv, Real.norm_natCast]
  exact mul_le_mul_of_nonneg_right (abs_coeff_eps_le hp j) (by positivity)

lemma SN_θeps {p : ℕ} (hp : p.Prime) : SN ((p : ℝ)⁻¹) (θ (eps p)) := by
  have hg := summable_pow_mul_geometric_of_norm_lt_one 1
    (show ‖(p : ℝ)⁻¹‖ < 1 by rw [Real.norm_of_nonneg (by positivity)]; exact inv_p_lt_one hp)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_) (hg.mul_left (4 + 2 * lam p ^ 2))
  simp only [θ, coeff_mk, norm_mul, Real.norm_eq_abs, abs_pow, abs_inv, Nat.abs_cast, pow_one]
  have := abs_coeff_eps_le hp j
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hx : (0 : ℝ) ≤ ((p : ℝ)⁻¹) ^ j := by positivity
  calc (j : ℝ) * |coeff j (eps p)| * ((p : ℝ)⁻¹) ^ j ≤ (j : ℝ) * (4 + 2 * lam p ^ 2) * ((p : ℝ)⁻¹) ^ j := by
        gcongr
    _ = _ := by ring

/-! ### The evaluations -/

lemma ev_Ups {p : ℕ} (hp : p.Prime) (a : ℕ) : ev ((p : ℝ)⁻¹) (Ups p a) = Np p a := by
  unfold ev Np
  refine tsum_congr fun j => ?_
  rw [Ups, coeff_mk, rpow_neg_nat_eq hp]

lemma ev_Dps {p : ℕ} (hp : p.Prime) : ev ((p : ℝ)⁻¹) (Dps p) = Dp p := by
  unfold ev Dp
  refine tsum_congr fun j => ?_
  rw [Dps, coeff_mk, rpow_neg_nat_eq hp]

lemma ev_θUps {p : ℕ} (hp : p.Prime) (a : ℕ) : -(Real.log p * ev ((p : ℝ)⁻¹) (θ (Ups p a))) = Np' p a := by
  unfold ev Np'
  rw [← tsum_mul_left]
  congr 1
  refine tsum_congr fun j => ?_
  rw [θ, coeff_mk, Ups, coeff_mk, rpow_neg_nat_eq hp]; ring

lemma ev_θDps {p : ℕ} (hp : p.Prime) : -(Real.log p * ev ((p : ℝ)⁻¹) (θ (Dps p))) = Dp' p := by
  unfold ev Dp'
  rw [← tsum_mul_left]
  congr 1
  refine tsum_congr fun j => ?_
  rw [θ, coeff_mk, Dps, coeff_mk, rpow_neg_nat_eq hp]; ring

section
variable {C : ℝ} (hC1 : 1 ≤ C) (hC : ∀ n : ℕ, 1 ≤ n → |lam n| ≤ C * (n : ℝ) ^ (11 / 40 : ℝ))
include hC1 hC

lemma SN_Dps {p : ℕ} (hp : p.Prime) : SN ((p : ℝ)⁻¹) (Dps p) := by
  rw [Dps_eq_Ups]; exact SN_Ups hC1 hC hp 0

lemma SN_θDps {p : ℕ} (hp : p.Prime) : SN ((p : ℝ)⁻¹) (θ (Dps p)) := by
  rw [Dps_eq_Ups]; exact SN_θUps hC1 hC hp 0

lemma ev_eps {p : ℕ} (hp : p.Prime) : ev ((p : ℝ)⁻¹) (eps p) = 1 / Dp p := by
  have h := ev_mul (SN_eps hp) (SN_Dps hC1 hC hp)
  rw [eps_mul_Dps, ev_one, ev_Dps hp] at h
  have hD : 0 < Dp p := lt_of_lt_of_le one_pos (one_le_Dp hp)
  rw [eq_div_iff hD.ne']; exact h.symm

lemma ev_gps {p : ℕ} (hp : p.Prime) (a : ℕ) : ev ((p : ℝ)⁻¹) (gps p a) = rhoP p a := by
  rw [gps, ev_mul (SN_Ups hC1 hC hp a) (SN_eps hp), ev_Ups hp, ev_eps hC1 hC hp, rhoP]; ring

lemma ev_θeps {p : ℕ} (hp : p.Prime) :
    ev ((p : ℝ)⁻¹) (θ (eps p)) = -(ev ((p : ℝ)⁻¹) (θ (Dps p))) / Dp p ^ 2 := by
  have h0 : θ (eps p * Dps p) = 0 := by rw [eps_mul_Dps, θ_one]
  rw [θ_mul] at h0
  have h := congrArg (ev ((p : ℝ)⁻¹)) h0
  rw [ev_add (SN_mul (SN_θeps hp) (SN_Dps hC1 hC hp)) (SN_mul (SN_eps hp) (SN_θDps hC1 hC hp)),
    ev_mul (SN_θeps hp) (SN_Dps hC1 hC hp), ev_mul (SN_eps hp) (SN_θDps hC1 hC hp), ev_zero,
    ev_Dps hp, ev_eps hC1 hC hp] at h
  have hD : 0 < Dp p := lt_of_lt_of_le one_pos (one_le_Dp hp)
  field_simp
  field_simp at h
  linarith

lemma log_mul_ev_θgps {p : ℕ} (hp : p.Prime) (a : ℕ) :
    Real.log p * ev ((p : ℝ)⁻¹) (θ (gps p a)) = -rhoP' p a := by
  rw [gps, θ_mul, ev_add (SN_mul (SN_θUps hC1 hC hp a) (SN_eps hp)) (SN_mul (SN_Ups hC1 hC hp a) (SN_θeps hp)),
    ev_mul (SN_θUps hC1 hC hp a) (SN_eps hp), ev_mul (SN_Ups hC1 hC hp a) (SN_θeps hp),
    ev_eps hC1 hC hp, ev_θeps hC1 hC hp, ev_Ups hp, rhoP', ← ev_θUps hp, ← ev_θDps hp]
  have hD : 0 < Dp p := lt_of_lt_of_le one_pos (one_le_Dp hp)
  field_simp
  ring

/-- The sequence `g_j`. -/
noncomputable def gseq (p a : ℕ) (j : ℕ) : ℝ := coeff j (gps p a)

lemma Gg_gseq {p : ℕ} (hp : p.Prime) (a : ℕ) : Gg p (gseq p a) = rhoP p a := by
  rw [← ev_gps hC1 hC hp a]; rfl

lemma G1g_gseq {p : ℕ} (hp : p.Prime) (a : ℕ) : G1g p (gseq p a) = -rhoP' p a := by
  rw [← log_mul_ev_θgps hC1 hC hp a, ev, G1g, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  simp only [gseq, θ, coeff_mk]; ring

end

/-! ### The weight `S` -/

/-- `W₀ = Σ (j+1)² (2^{−1/4})^j`. -/
noncomputable def r2 : ℝ := (2 : ℝ) ^ (-(1 / 4 : ℝ))

lemma r2_pos : 0 < r2 := by unfold r2; positivity

lemma r2_lt_one : r2 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma summable_W0 : Summable fun j : ℕ => ((j : ℝ) + 1) ^ 2 * r2 ^ j := by
  have hn : ‖r2‖ < 1 := by rw [Real.norm_of_nonneg r2_pos.le]; exact r2_lt_one
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have h0 := summable_pow_mul_geometric_of_norm_lt_one 0 hn
  refine ((h2.add (h1.mul_left 2)).add h0).congr fun j => ?_
  simp only [pow_zero, one_mul, pow_one]; ring

noncomputable def W0 : ℝ := ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * r2 ^ j

lemma W0_nonneg : 0 ≤ W0 := tsum_nonneg fun j => by have := r2_pos; positivity

section
variable {C : ℝ} (hC1 : 1 ≤ C) (hC : ∀ n : ℕ, 1 ≤ n → |lam n| ≤ C * (n : ℝ) ^ (11 / 40 : ℝ))
include hC1 hC

lemma abs_lam_prime_pow_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |lam (p ^ k)| ≤ C * (p : ℝ) ^ ((11 / 40 : ℝ) * k) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have := hC (p ^ k) (Nat.one_le_pow _ _ hp.pos)
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, mul_comm (k : ℝ)] at this
  exact this

lemma abs_Ucoeff_le {p : ℕ} (hp : p.Prime) (a k : ℕ) :
    |coeff k (Ups p a)| ≤ C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a) * (p : ℝ) ^ ((11 / 20 : ℝ) * k) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Ups, coeff_mk, abs_mul]
  have h1 := abs_lam_prime_pow_le hC1 hC hp (k + a)
  have h2 := abs_lam_prime_pow_le hC1 hC hp k
  calc |lam (p ^ (k + a))| * |lam (p ^ k)| ≤ (C * (p : ℝ) ^ ((11 / 40 : ℝ) * ((k + a : ℕ) : ℝ))) *
        (C * (p : ℝ) ^ ((11 / 40 : ℝ) * k)) := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = _ := by
        rw [show C * (p : ℝ) ^ ((11 / 40 : ℝ) * ((k + a : ℕ) : ℝ)) * (C * (p : ℝ) ^ ((11 / 40 : ℝ) * k)) =
          C ^ 2 * ((p : ℝ) ^ ((11 / 40 : ℝ) * ((k + a : ℕ) : ℝ)) * (p : ℝ) ^ ((11 / 40 : ℝ) * k)) by ring,
          ← Real.rpow_add hp0, mul_assoc, ← Real.rpow_add hp0]
        congr 2; push_cast; ring

lemma abs_gseq_le {p : ℕ} (hp : p.Prime) (a j : ℕ) :
    |gseq p a j| ≤ (j + 1) * (4 + 2 * lam p ^ 2) * (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a) *
      (p : ℝ) ^ ((11 / 20 : ℝ) * j)) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  unfold gseq gps
  rw [coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ kl ∈ antidiagonal j, |coeff kl.1 (Ups p a) * coeff kl.2 (eps p)| ≤
      (4 + 2 * lam p ^ 2) * (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a) * (p : ℝ) ^ ((11 / 20 : ℝ) * j)) := by
    intro kl hkl
    rw [mem_antidiagonal] at hkl
    rw [abs_mul]
    have h1 := abs_Ucoeff_le hC1 hC hp a kl.1
    have h2 := abs_coeff_eps_le hp kl.2
    have h3 : (p : ℝ) ^ ((11 / 20 : ℝ) * kl.1) ≤ (p : ℝ) ^ ((11 / 20 : ℝ) * j) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by
        have : (kl.1 : ℝ) ≤ j := by exact_mod_cast (show kl.1 ≤ j by omega)
        linarith)
    calc |coeff kl.1 (Ups p a)| * |coeff kl.2 (eps p)| ≤
        (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a) * (p : ℝ) ^ ((11 / 20 : ℝ) * j)) * (4 + 2 * lam p ^ 2) := by
          refine mul_le_mul (h1.trans ?_) h2 (abs_nonneg _) (by positivity)
          gcongr
      _ = _ := by ring
  refine (Finset.sum_le_sum hb).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]; push_cast; ring

/-- The weighted term bound: `(1 + j log p)|g_j| q^j ≤ 6C⁴ p^{3a} (j+1)² r₂^j` for `a ≥ 1`. -/
lemma Sterm_le {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a) (j : ℕ) :
    (1 + j * Real.log p) * |gseq p a j| * qp p ^ j ≤ 6 * C ^ 4 * (p : ℝ) ^ (3 * a) * (((j : ℝ) + 1) ^ 2 * r2 ^ j) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : Real.log p ≤ p := (Real.log_le_sub_one_of_pos hp0).trans (by linarith)
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  -- λ_p² ≤ C² p^{11/20}
  have hlp : lam p ^ 2 ≤ C ^ 2 * (p : ℝ) ^ (11 / 20 : ℝ) := by
    have h := hC p hp.one_lt.le
    have h' : lam p ^ 2 ≤ (C * (p : ℝ) ^ (11 / 40 : ℝ)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [mul_pow, ← Real.rpow_natCast ((p : ℝ) ^ (11 / 40 : ℝ)), ← Real.rpow_mul hp0.le] at h'
    norm_num at h'; exact h'
  have hp1120 : 1 ≤ (p : ℝ) ^ (11 / 20 : ℝ) := Real.one_le_rpow hp1 (by norm_num)
  have hC2 : 1 ≤ C ^ 2 := one_le_pow₀ hC1
  have hKe : 4 + 2 * lam p ^ 2 ≤ 6 * C ^ 2 * (p : ℝ) ^ (11 / 20 : ℝ) := by nlinarith
  have hg := abs_gseq_le hC1 hC hp a j
  have h1j : 1 + j * Real.log p ≤ (j + 1) * p := by nlinarith
  -- combine the powers of p
  have hq : qp p ^ j = (p : ℝ) ^ (-(4 / 5 : ℝ) * j) := by
    unfold qp; rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
  have hpow : (p : ℝ) * (p : ℝ) ^ (11 / 20 : ℝ) * (p : ℝ) ^ ((11 / 40 : ℝ) * a) * (p : ℝ) ^ ((11 / 20 : ℝ) * j) *
      (p : ℝ) ^ (-(4 / 5 : ℝ) * j) = (p : ℝ) ^ ((1 + 11 / 20 + (11 / 40 : ℝ) * a)) * ((p : ℝ) ^ (-(1 / 4 : ℝ))) ^ j := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 4 : ℝ))), ← Real.rpow_mul hp0.le]
    rw [mul_comm (p : ℝ) ((p : ℝ) ^ (11 / 20 : ℝ)), ← Real.rpow_add_one hp0.ne', ← Real.rpow_add hp0,
      ← Real.rpow_add hp0, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
    congr 1; ring
  have hexp : (p : ℝ) ^ ((1 + 11 / 20 + (11 / 40 : ℝ) * a)) ≤ (p : ℝ) ^ (3 * a) := by
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    push_cast; linarith
  have hr : ((p : ℝ) ^ (-(1 / 4 : ℝ))) ^ j ≤ r2 ^ j := by
    unfold r2
    exact pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)) j
  have hP0 : 0 ≤ (p : ℝ) ^ ((11 / 40 : ℝ) * a) * (p : ℝ) ^ ((11 / 20 : ℝ) * j) := by positivity
  calc (1 + j * Real.log p) * |gseq p a j| * qp p ^ j
      ≤ ((j + 1) * p) * ((j + 1) * (6 * C ^ 2 * (p : ℝ) ^ (11 / 20 : ℝ)) * (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a) *
          (p : ℝ) ^ ((11 / 20 : ℝ) * j))) * qp p ^ j := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_pos (qp_pos hp.two_le) j).le
        refine mul_le_mul h1j (hg.trans ?_) (abs_nonneg _) (by positivity)
        gcongr
    _ = 6 * C ^ 4 * ((j : ℝ) + 1) ^ 2 * ((p : ℝ) * (p : ℝ) ^ (11 / 20 : ℝ) * (p : ℝ) ^ ((11 / 40 : ℝ) * a) *
          (p : ℝ) ^ ((11 / 20 : ℝ) * j) * (p : ℝ) ^ (-(4 / 5 : ℝ) * j)) := by rw [hq]; ring
    _ = 6 * C ^ 4 * ((j : ℝ) + 1) ^ 2 * ((p : ℝ) ^ ((1 + 11 / 20 + (11 / 40 : ℝ) * a)) *
          ((p : ℝ) ^ (-(1 / 4 : ℝ))) ^ j) := by rw [hpow]
    _ ≤ 6 * C ^ 4 * ((j : ℝ) + 1) ^ 2 * ((p : ℝ) ^ (3 * a) * r2 ^ j) := by gcongr
    _ = _ := by ring

lemma summable_Sg {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a) :
    Summable fun j : ℕ => (1 + j * Real.log p) * |gseq p a j| * qp p ^ j := by
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  refine Summable.of_nonneg_of_le (fun j => ?_) (Sterm_le hC1 hC hp ha) (summable_W0.mul_left _)
  have := qp_pos hp.two_le
  positivity

lemma Sg_le {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a) :
    Sg p (gseq p a) ≤ 6 * C ^ 4 * W0 * (p : ℝ) ^ (3 * a) := by
  unfold Sg
  calc _ ≤ ∑' j : ℕ, 6 * C ^ 4 * (p : ℝ) ^ (3 * a) * (((j : ℝ) + 1) ^ 2 * r2 ^ j) :=
        Summable.tsum_le_tsum (Sterm_le hC1 hC hp ha) (summable_Sg hC1 hC hp ha) (summable_W0.mul_left _)
    _ = _ := by rw [tsum_mul_left, W0]; ring

end

end RamanujanTau.HafnerBridge2
