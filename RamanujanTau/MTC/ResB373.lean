/-
# The residue identity at a `B`-zero

`brB_zero`: if `B_{s₀}(x₀) = Q^{ℓ₀}` and `4ℓ₀ = 3k₁ + s₀ − t₁ − 1`, then the bracket `brB` of `FS_ev_B`
vanishes, provided four monomial identities hold (one for each `r`).

The proof dissects `j(q^{7t₁}x₀; q³)` into four `q⁴⁸`-theta functions, indexed by the residue system
`ρ = c₀ − r` with `c₀ = 7k₁ + 4ℓ₀ − 6` (`dissect_any`, from HM (1.2f) and periodicity in `ρ`). The
`q⁴⁸`-theta function of `Tn(r, s₀)` is that summand after reflection (HM (1.2a)), and the `q^{160}`-theta
function of `Tn(r, s₀)` is `j(A_r)` up to a monomial.
-/
import RamanujanTau.MTC.EvB373

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

lemma Icc03 : Finset.Icc (0 : ℤ) 3 = {0, 1, 2, 3} := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

lemma sum_Icc03 (f : ℤ → L) : ∑ r ∈ Finset.Icc (0 : ℤ) 3, f r = f 0 + f 1 + f 2 + f 3 := by
  rw [Icc03]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

lemma θ_N {N N' : ℕ} (h : N = N') (hN : 1 ≤ N) (hN' : 1 ≤ N') (e : ℤ) (c : ℂ) : θ hN e c = θ hN' e c := by
  subst h; rfl

lemma c2_4 : c2 4 = 6 := by decide

lemma θ_cg {N : ℕ} (hN : 1 ≤ N) {e e' : ℤ} {c c' : ℂ} (he : e = e') (hc : c = c') : θ hN e c = θ hN e' c' := by
  subst he hc; rfl

section Dis
variable {qe : ℕ} (hqe : 1 ≤ qe)

/-- the multiplier of the `ρ`-th summand of the `q³ → q⁴⁸` dissection. -/
noncomputable def dmon (e : ℤ) (c : ℂ) (ρ : ℤ) : L := mono (3 * qe * c2 (-ρ) - e * ρ) ((-1) ^ (-ρ) * c ^ (-ρ))

/-- the `ρ`-th summand. -/
noncomputable def summ (e : ℤ) (c : ℂ) (ρ : ℤ) : L :=
  dmon (qe := qe) e c ρ * θ (h48 hqe) (18 * qe - 12 * qe * ρ + 4 * e) (-c ^ 4)

lemma c2_neg_add4 (ρ : ℤ) : c2 (-(ρ + 4)) = c2 (-ρ) + 4 * ρ + 10 := by
  have h1 := two_c2 (-(ρ + 4)); have h2 := two_c2 (-ρ)
  have : 2 * c2 (-(ρ + 4)) = 2 * (c2 (-ρ) + 4 * ρ + 10) := by rw [h1, mul_add, mul_add, h2]; ring
  omega

lemma summ_period (e : ℤ) {c : ℂ} (hc : c ≠ 0) (ρ : ℤ) : summ hqe e c (ρ + 4) = summ hqe e c ρ := by
  unfold summ dmon
  have hC : -c ^ 4 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ hc)
  rw [show 18 * (qe : ℤ) - 12 * qe * (ρ + 4) + 4 * e = (18 * qe - 12 * qe * ρ + 4 * e) + ((48 * qe : ℕ) : ℤ) * (-1) by
      push_cast; ring,
    θ_qshift (h48 hqe) _ hC (-1), ← mul_assoc]
  congr 1
  rw [mono_mul]
  apply mono_ext
  · rw [c2_neg_add4, show (-1 : ℤ) + 1 = 0 by norm_num, show c2 0 = 0 by decide]
    push_cast; ring
  · have e1 : -(ρ + 4) = -ρ + (-4) := by ring
    rw [e1, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_add₀ hc]
    have h4 : c ^ (-4 : ℤ) * c ^ 4 = 1 := by
      rw [zpow_neg, zpow_ofNat, inv_mul_cancel₀ (pow_ne_zero _ hc)]
    have hm : ((-1 : ℂ)) ^ (-4 : ℤ) = 1 := by norm_num
    have hm1 : ((-1 : ℂ)) ^ (-1 : ℤ) = -1 := by norm_num
    rw [hm, hm1, neg_neg, zpow_one]
    linear_combination ((-1) ^ (-ρ) * c ^ (-ρ)) * h4

/-- HM (1.2f) with `m = 4` in base `q³`. -/
lemma dissect3 (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    θ (h3qe hqe) e c = ∑ r ∈ Finset.Icc (0 : ℤ) 3, summ hqe e c (3 - r) := by
  rw [show ∑ r ∈ Finset.Icc (0 : ℤ) 3, summ hqe e c (3 - r) = ∑ ρ : Fin 4, summ hqe e c ((ρ : ℕ) : ℤ) by
    rw [sum_Icc03, Fin.sum_univ_four]
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    norm_num
    ring]
  rw [θ_dissect (h3qe hqe) 4 (by norm_num) e hc]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  unfold summ dmon
  refine congrArg₂ (· * ·) (mono_ext (by push_cast; ring) rfl) ?_
  rw [θ_N (show 3 * qe * 4 * 4 = 48 * qe by ring) _ (h48 hqe)]
  exact θ_cg (h48 hqe) (by push_cast; rw [c2_4]; ring) (by ring)

/-- the dissection over any four consecutive indices. -/
lemma dissect_any (e : ℤ) {c : ℂ} (hc : c ≠ 0) (c0 : ℤ) :
    θ (h3qe hqe) e c = ∑ r ∈ Finset.Icc (0 : ℤ) 3, summ hqe e c (c0 - r) := by
  have step : ∀ k : ℤ, ∑ r ∈ Finset.Icc (0 : ℤ) 3, summ hqe e c (k + 1 - r) =
      ∑ r ∈ Finset.Icc (0 : ℤ) 3, summ hqe e c (k - r) := by
    intro k
    rw [sum_Icc03, sum_Icc03, show k + 1 - 0 = (k - 3) + 4 by ring, summ_period hqe e hc,
      show k + 1 - 1 = k - 0 by ring, show k + 1 - 2 = k - 1 by ring, show k + 1 - 3 = k - 2 by ring]
    ring
  induction c0 using Int.inductionOn' (b := 3) with
  | zero => exact dissect3 hqe e hc
  | succ k _ ih => rw [step k]; exact ih
  | pred k _ ih =>
      have h := step (k - 1)
      simp only [sub_add_cancel] at h
      rw [← h]; exact ih

end Dis

/-- the algebra of the termwise cancellation. -/
lemma alg4 (S P : L) (d m M T A A' : ℤ → L)
    (hm : ∀ r ∈ Finset.Icc (0 : ℤ) 3, S * d r + m r * M r = 0)
    (hp : ∀ r ∈ Finset.Icc (0 : ℤ) 3, A r * A' r = P) :
    S * (∑ r ∈ Finset.Icc (0 : ℤ) 3, d r * T r) * P +
      ∑ r ∈ Finset.Icc (0 : ℤ) 3, m r * T r * (M r * A r) * A' r = 0 := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun r hr => ?_
  linear_combination (T r * P) * hm r hr + (m r * T r * M r) * hp r hr

section ResB
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)
variable {s0 ℓ0 ex0 t1 k1 : ℤ} {cx0 : ℂ}

lemma c1T_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : c1T cy cx ≠ 0 := by
  unfold c1T; exact neg_ne_zero.mpr (mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy))

/-- the `q⁴⁸`-theta function of `Tn(r, s₀)` is the dissection summand at `ρ = c₀ − r`. -/
lemma θ48_B (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (hlk : 4 * ℓ0 = 3 * k1 + s0 - t1 - 1) (r : ℤ) :
    θ (h48 hqe) (e1T (qe := qe) ey r s0 ex0) (c1T cy cx0) =
      θ (h48 hqe) (18 * qe - 12 * qe * (7 * k1 + 4 * ℓ0 - 6 - r) + 4 * (7 * qe * t1 + ex0)) (-cx0 ^ 4) := by
  rw [← θ_reflect (h48 hqe) _ (c1T_ne cy hcx hcy)]
  congr 1
  · unfold e1T; unfold eBT at hB; push_cast
    first
      | linear_combination hB + 28 * (qe : ℤ) * hlk | linear_combination -hB + 28 * (qe : ℤ) * hlk
      | linear_combination hB - 28 * (qe : ℤ) * hlk | linear_combination -hB - 28 * (qe : ℤ) * hlk
  · unfold c1T; unfold cBT at hc
    have hcy3 : cy ^ (-3 : ℤ) = (cx0 ^ (7 : ℤ))⁻¹ := eq_inv_of_mul_eq_one_right hc
    rw [hcy3]
    simp only [zpow_ofNat]
    field_simp
    try ring

/-- the `q^{160}`-theta function of `Tn(r, s₀)` is `j(A_r)` up to a monomial. -/
lemma θ160_B (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (r : ℤ) :
    θ (h160 hqe) (e2T (qe := qe) ey r s0 ex0) (c2T cy cx0) =
      Msh (160 * qe) (eAT (qe := qe) ey r ex0) ℓ0 (cAT cy cx0) * θ (h160 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0) := by
  have hcc : c2T cy cx0 = cAT cy cx0 := by
    unfold cBT at hc
    unfold c2T cAT
    rw [show cx0 ^ (4 : ℤ) * cy ^ (4 : ℤ) = (cy ^ (7 : ℤ) * cx0 ^ (-3 : ℤ)) * (cx0 ^ (7 : ℤ) * cy ^ (-3 : ℤ)) by
      simp only [zpow_neg, zpow_ofNat]; field_simp; try ring, hc, mul_one]
  rw [hcc]
  exact θ_sh (h160 hqe) (cAT_ne cy hcx hcy) ℓ0 (by
    unfold e2T eAT; unfold eBT at hB; push_cast
    first | linear_combination hB | linear_combination -hB)

lemma Tn_B (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (hlk : 4 * ℓ0 = 3 * k1 + s0 - t1 - 1) (r : ℤ) :
    Tn hqe ey cy r s0 ex0 cx0 = mono (eTn (qe := qe) ey r s0 ex0) (cTn cy r s0 cx0) *
      θ (h48 hqe) (18 * qe - 12 * qe * (7 * k1 + 4 * ℓ0 - 6 - r) + 4 * (7 * qe * t1 + ex0)) (-cx0 ^ 4) *
      (Msh (160 * qe) (eAT (qe := qe) ey r ex0) ℓ0 (cAT cy cx0) * θ (h160 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)) := by
  unfold Tn
  rw [θ48_B hqe ey cy hB hc hcx hcy hlk r, θ160_B hqe ey cy hB hc hcx hcy r]

/-- **the residue identity at a `B`-zero**, modulo four monomial identities. -/
theorem brB_zero (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hcy : cy ≠ 0) (hlk : 4 * ℓ0 = 3 * k1 + s0 - t1 - 1)
    (hm : ∀ r ∈ Finset.Icc (0 : ℤ) 3,
      sig1 (qe := qe) ey cy t1 k1 * mono (-(((160 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) *
          dmon (qe := qe) (7 * qe * t1 + ex0) cx0 (7 * k1 + 4 * ℓ0 - 6 - r) +
        mono (eTn (qe := qe) ey r s0 ex0) (cTn cy r s0 cx0) * Msh (160 * qe) (eAT (qe := qe) ey r ex0) ℓ0 (cAT cy cx0) = 0) :
    brB hqe ey cy t1 k1 ℓ0 s0 ex0 cx0 = 0 := by
  unfold brB
  rw [dissect_any hqe (7 * qe * t1 + ex0) hcx (7 * k1 + 4 * ℓ0 - 6)]
  simp only [Tn_B hqe ey cy hB hc hcx hcy hlk, summ]
  exact alg4 (sig1 (qe := qe) ey cy t1 k1 * mono (-(((160 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)))
    ((idx4.map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod)
    (fun r => dmon (qe := qe) (7 * qe * t1 + ex0) cx0 (7 * k1 + 4 * ℓ0 - 6 - r))
    (fun r => mono (eTn (qe := qe) ey r s0 ex0) (cTn cy r s0 cx0))
    (fun r => Msh (160 * qe) (eAT (qe := qe) ey r ex0) ℓ0 (cAT cy cx0))
    (fun r => θ (h48 hqe) (18 * qe - 12 * qe * (7 * k1 + 4 * ℓ0 - 6 - r) + 4 * (7 * qe * t1 + ex0)) (-cx0 ^ 4))
    (fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0))
    (fun r => ((idx4.erase r).map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod)
    hm (fun r hr => List.prod_map_erase (fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)) (mem_idx4 hr))

end ResB

end MTC
