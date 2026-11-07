/-
# M3 step 2d: the twisted sum for all coprime `(h, k)`, by induction on `hk`

`Inv Z h k`: `|Bs(h,k)(α) − Mn(h,k)(α)| ≤ Z·Er(α/T(u)T(u+v))`, `Er(r) = r^{1/20} + r^{1/6}`,
uniformly in `u`, `0 < |v| ≤ 1`, `α > 0`.

* base `(1,1)`: `BaseFull.base_full`;
* step: peeling `p^a ∥ h` multiplies `Z` by `Gp(p,a) = Σ_j |g_j| p^{−2j/3} ≤ M p^{2a}`
  (`Er(rp^{2j}) ≤ p^{j/3} Er(r)`), `Inv_peel`;
* `twisted_eval`: `Inv (Z₀ M^{ω(hk)} (hk)²) h k` for all coprime `h, k ≥ 1`.
Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.Induct1

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex Finset PowerSeries RamanujanTau.HafnerBridge RamanujanTau.HafnerBridge2
open RamanujanTau.SelbergKey (NpC DpC rhoC)
open RamanujanTau.GoodSecondTerm (c0 gammaD bb)
open scoped Real

noncomputable def Er (r : ℝ) : ℝ := r ^ (1 / 20 : ℝ) + r ^ (1 / 6 : ℝ)

lemma Er_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ Er r := by unfold Er; positivity

def Inv (Z : ℝ) (h k : ℕ) : Prop :=
  ∀ u v α : ℝ, 0 < α → v ≠ 0 → |v| ≤ 1 → ‖Bs u v h k α - Mn u v h k α‖ ≤ Z * Er (α / TT u v)

lemma Inv_mono {Z Z' : ℝ} (hZ : Z ≤ Z') {h k : ℕ} (H : Inv Z h k) : Inv Z' h k := by
  intro u v α hα hv0 hv
  exact (H u v α hα hv0 hv).trans
    (mul_le_mul_of_nonneg_right hZ (Er_nonneg (div_pos hα (TT_pos u v)).le))

lemma Inv_swap {Z : ℝ} {h k : ℕ} (H : Inv Z h k) : Inv Z k h := by
  intro u v α hα hv0 hv
  have e1 : Bs u v k h α = Bs u v h k α := by
    unfold Bs T; exact tsum_congr fun r => by ring_nf
  have e2 : Mn u v k h α = Mn u v h k α := by unfold Mn; push_cast; ring
  rw [e1, e2]; exact H u v α hα hv0 hv

lemma Inv_base : ∃ Z : ℝ, 0 ≤ Z ∧ Inv Z 1 1 := by
  obtain ⟨K, hK0, hK⟩ := base_full
  refine ⟨K, hK0, fun u v α hα hv0 hv => ?_⟩
  have e1 : Bs u v 1 1 α = ∑' n : ℕ, cA n * ft u v α n := by
    unfold Bs cA
    refine tsum_congr fun r => ?_
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    rw [T, one_mul, ← sq, lam_sq_eq_bb hr]
  have e2 : Mn u v 1 1 α = baseMain u v α := by
    unfold Mn; rw [baseMain_eq, rhoC_one, rho_one]; push_cast; ring
  rw [e1, e2]; exact hK u v α hα hv0 hv

lemma Er_scale {r : ℝ} (hr : 0 ≤ r) {p : ℝ} (hp : 1 ≤ p) (j : ℕ) :
    Er (r * p ^ (2 * j)) ≤ (p ^ (1 / 3 : ℝ)) ^ j * Er r := by
  have hp0 : 0 < p := by linarith
  unfold Er
  have hpj : 0 ≤ p ^ (2 * j) := by positivity
  rw [Real.mul_rpow hr hpj, Real.mul_rpow hr hpj]
  have e : ∀ c : ℝ, (p ^ (2 * j)) ^ c = p ^ (2 * c * j) := by
    intro c; rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; push_cast; ring_nf
  have e3 : (p ^ (1 / 3 : ℝ)) ^ j = p ^ (1 / 3 * (j : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
  rw [e, e, e3]
  have h1 : p ^ (2 * (1 / 20 : ℝ) * j) ≤ p ^ (1 / 3 * (j : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hp (by have := Nat.cast_nonneg (α := ℝ) j; nlinarith)
  have h2 : p ^ (2 * (1 / 6 : ℝ) * j) = p ^ (1 / 3 * (j : ℝ)) := by congr 1; ring
  rw [h2]
  have ha := Real.rpow_nonneg hr (1 / 20 : ℝ)
  nlinarith [Real.rpow_nonneg hr (1 / 6 : ℝ), Real.rpow_nonneg hp0.le (1 / 3 * (j : ℝ))]

/-- `Gp(p,a) = Σ_j |g_j| p^{−2j/3}`. -/
noncomputable def Gp (p a : ℕ) : ℝ := ∑' j : ℕ, |gseq p a j| * ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j

lemma Gp_terms_le {C : ℝ} (hC1 : 1 ≤ C) (hC : ∀ n : ℕ, 1 ≤ n → |lam n| ≤ C * (n : ℝ) ^ (11 / 40 : ℝ))
    {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a) (j : ℕ) :
    |gseq p a j| * ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j ≤
      6 * C ^ 4 * ((p : ℝ) ^ a) ^ 2 * (((j : ℝ) + 1) * ((2 : ℝ) ^ (-(7 / 60 : ℝ))) ^ j) := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h0 := abs_gseq_le hC1 hC hp a j
  have hlam : lam p ^ 2 ≤ C ^ 2 * p := by
    have h1 := hC p hp.pos
    have h2 : ((p : ℝ) ^ (11 / 40 : ℝ)) ^ 2 ≤ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      calc (p : ℝ) ^ ((11 / 40 : ℝ) * ((2:ℕ):ℝ)) ≤ (p : ℝ) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
        _ = p := Real.rpow_one _
    calc lam p ^ 2 = |lam p| ^ 2 := (sq_abs _).symm
      _ ≤ (C * (p : ℝ) ^ (11 / 40 : ℝ)) ^ 2 := by gcongr
      _ = C ^ 2 * ((p : ℝ) ^ (11 / 40 : ℝ)) ^ 2 := by ring
      _ ≤ C ^ 2 * p := by gcongr
  have hC2p : 1 ≤ C ^ 2 * p := by nlinarith
  have h4 : 4 + 2 * lam p ^ 2 ≤ 6 * (C ^ 2 * p) := by nlinarith
  have hpow : (p : ℝ) ^ ((11 / 20 : ℝ) * j) * ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j =
      ((p : ℝ) ^ (-(7 / 60 : ℝ))) ^ j := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-(2 / 3 : ℝ))), ← Real.rpow_mul hp0.le,
      ← Real.rpow_natCast ((p : ℝ) ^ (-(7 / 60 : ℝ))), ← Real.rpow_mul hp0.le, ← Real.rpow_add hp0]
    congr 1; ring
  have hpow2 : ((p : ℝ) ^ (-(7 / 60 : ℝ))) ^ j ≤ ((2 : ℝ) ^ (-(7 / 60 : ℝ))) ^ j :=
    pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)) j
  have hpa : (p : ℝ) ^ ((11 / 40 : ℝ) * a) ≤ (p : ℝ) ^ a := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by nlinarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a)])
  have hpa2 : (p : ℝ) * (p : ℝ) ^ a ≤ ((p : ℝ) ^ a) ^ 2 := by
    rw [sq]; gcongr; exact le_self_pow₀ hp1 (by omega)
  have hj0 : (0:ℝ) ≤ (j : ℝ) + 1 := by positivity
  calc |gseq p a j| * ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j
      ≤ (((j : ℝ) + 1) * (4 + 2 * lam p ^ 2) * (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a) *
          (p : ℝ) ^ ((11 / 20 : ℝ) * j))) * ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j :=
        mul_le_mul_of_nonneg_right h0 (by positivity)
    _ = ((j : ℝ) + 1) * (4 + 2 * lam p ^ 2) * (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a)) *
          ((p : ℝ) ^ ((11 / 20 : ℝ) * j) * ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j) := by ring
    _ = ((j : ℝ) + 1) * (4 + 2 * lam p ^ 2) * (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a)) *
          ((p : ℝ) ^ (-(7 / 60 : ℝ))) ^ j := by rw [hpow]
    _ ≤ ((j : ℝ) + 1) * (6 * (C ^ 2 * p)) * (C ^ 2 * (p : ℝ) ^ a) * ((2 : ℝ) ^ (-(7 / 60 : ℝ))) ^ j := by
        gcongr
    _ = 6 * C ^ 4 * ((p : ℝ) * (p : ℝ) ^ a) * (((j : ℝ) + 1) * ((2 : ℝ) ^ (-(7 / 60 : ℝ))) ^ j) := by ring
    _ ≤ _ := by gcongr

lemma summable_jgeom : Summable fun j : ℕ => ((j : ℝ) + 1) * ((2 : ℝ) ^ (-(7 / 60 : ℝ))) ^ j := by
  have hr : ‖(2 : ℝ) ^ (-(7 / 60 : ℝ))‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h2 := summable_geometric_of_norm_lt_one hr
  exact (h1.add h2).congr fun j => by simp; ring

lemma Gp_bound : ∃ M : ℝ, 1 ≤ M ∧ ∀ (p a : ℕ), p.Prime → 1 ≤ a →
    Summable (fun j : ℕ => |gseq p a j| * ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j) ∧ Gp p a ≤ M * ((p : ℝ) ^ a) ^ 2 := by
  obtain ⟨C, hC1, hC⟩ := lam_bound
  set S : ℝ := ∑' j : ℕ, ((j : ℝ) + 1) * ((2 : ℝ) ^ (-(7 / 60 : ℝ))) ^ j
  refine ⟨max 1 (6 * C ^ 4 * S), le_max_left _ _, fun p a hp ha => ?_⟩
  have hb := Gp_terms_le hC1 hC hp ha
  have hs : Summable (fun j : ℕ => |gseq p a j| * ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hb (summable_jgeom.mul_left _)
  refine ⟨hs, ?_⟩
  have hp1 : (1:ℝ) ≤ (p : ℝ) ^ a := one_le_pow₀ (by exact_mod_cast hp.one_lt.le)
  calc Gp p a ≤ ∑' j : ℕ, 6 * C ^ 4 * ((p : ℝ) ^ a) ^ 2 * (((j : ℝ) + 1) * ((2 : ℝ) ^ (-(7 / 60 : ℝ))) ^ j) :=
        hs.tsum_le_tsum hb (summable_jgeom.mul_left _)
    _ = (6 * C ^ 4 * S) * ((p : ℝ) ^ a) ^ 2 := by rw [tsum_mul_left]; ring
    _ ≤ _ := by gcongr; exact le_max_right _ _

end RamanujanTau.SelbergKeyDiag2
