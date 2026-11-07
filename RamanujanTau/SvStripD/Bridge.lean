/-
# `SvStripD` step 4: bridge to `SvStripC` and the Euler-mass bound for `Γz` (`[DeligneBound]`)

* `γz_bridge`: `SvStripC.γz z p e i j = SvStripD.γz p z e i j` (the generic instance of `Local.lean`).
* `MassZ z y d = Σ_{u₁,u₂≤y} ‖Γz z d u₁ u₂‖`; `MassZ_le_prod`: `MassZ ≤ Π_{p∈primes(y!)∪primes(d)} T^z_p`.
* **`s4_mass`**: there is an absolute `A` with, for `−1/4 ≤ Im z ≤ 0` and `y ≥ 2`,

      Σ_{d≤y²} ‖W^{[1−iz]}(d)‖ · MassZ(z,y,d)² ≤ A · y^{4|Im z|} · log y.
-/
import RamanujanTau.SvStripD.Euler
import RamanujanTau.SvStripC.Prod

set_option autoImplicit false

namespace RamanujanTau.SvStripD

open Complex Finset
open RamanujanTau.SvStripA (xs LcC WcK WdC sum_divisors_prod_localR')
open RamanujanTau.HafnerBridge (lam)
open RamanujanTau.QFProof3 (Fi gRm Xp)
open RamanujanTau.SelbergDelange3 (recF)

lemma tw_neg_eq (p : ℕ) (z : ℂ) : RamanujanTau.SvStripC.tw (-z) p = ωz p z := by
  unfold RamanujanTau.SvStripC.tw ωz; congr 1; ring

lemma xz_eq_tw {p : ℕ} (hp : p.Prime) (z : ℂ) :
    xz p z = RamanujanTau.SvStripC.tw z p * (p : ℂ)⁻¹ := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [xz, xs, RamanujanTau.SvStripC.tw, show -(1 - z * I) = I * z + (-1) by ring, cpow_add _ _ hp0,
    cpow_neg_one]

lemma Fi_tw {p : ℕ} (hp : p.Prime) (z : ℂ) (k : ℕ) :
    (Fi (p ^ k) : ℂ) * RamanujanTau.SvStripC.tw z p ^ k = F1z p z k := by
  rw [F1z, xz_eq_tw hp, mul_pow, RamanujanTau.QFProof4.Fi_apply]
  push_cast
  rw [div_eq_mul_inv, inv_pow]; ring

/-- **`SvStripC.γz` is the generic local factor with the twisted data.** -/
theorem γz_bridge {p : ℕ} (hp : p.Prime) (z : ℂ) (e i j : ℕ) :
    RamanujanTau.SvStripC.γz z p e i j = γz p z e i j := by
  unfold RamanujanTau.SvStripC.γz γz γC
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [tw_neg_eq, Fi_tw hp]
  simp only [A1z, A2z, Lz, F2z]
  push_cast; ring

/-- `M^z_d(y) = Σ_{u₁,u₂≤y} ‖Γ^z_d(u₁,u₂)‖`. -/
noncomputable def MassZ (z : ℂ) (y d : ℕ) : ℝ :=
  ∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y, ‖RamanujanTau.SvStripC.Γz z d u₁ u₂‖

lemma MassZ_nonneg (z : ℂ) (y d : ℕ) : 0 ≤ MassZ z y d :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _

/-- **`M^z_d(y) ≤ Π_{p∈primes(y!)∪primes(d)} T^z_p(v_p d, v_p y!)`.** -/
theorem MassZ_le_prod (z : ℂ) {y d : ℕ} (hd : d ≠ 0) :
    MassZ z y d ≤ ∏ p ∈ (y.factorial).primeFactors ∪ d.primeFactors,
      Tz p z (d.factorization p) ((y.factorial).factorization p) := by
  set S := (y.factorial).primeFactors ∪ d.primeFactors with hS
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => by
    rcases mem_union.1 hp with h | h <;> exact Nat.prime_of_mem_primeFactors h
  have hf0 : y.factorial ≠ 0 := Nat.factorial_ne_zero y
  have hsub : Ioc 0 y ⊆ (y.factorial).divisors := fun u hu => by
    have := mem_Ioc.1 hu
    exact Nat.mem_divisors.2 ⟨Nat.dvd_factorial this.1 this.2, hf0⟩
  unfold MassZ
  calc ∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y, ‖RamanujanTau.SvStripC.Γz z d u₁ u₂‖
      ≤ ∑ u₁ ∈ (y.factorial).divisors, ∑ u₂ ∈ (y.factorial).divisors,
          ‖RamanujanTau.SvStripC.Γz z d u₁ u₂‖ := by
        refine (sum_le_sum fun u₁ _ => sum_le_sum_of_subset_of_nonneg hsub
          fun _ _ _ => norm_nonneg _).trans ?_
        exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sum_nonneg fun _ _ => norm_nonneg _
    _ = ∑ u₁ ∈ (y.factorial).divisors, ∑ u₂ ∈ (y.factorial).divisors,
          ∏ p ∈ S, ‖γz p z (d.factorization p) (u₁.factorization p) (u₂.factorization p)‖ := by
        refine sum_congr rfl fun u₁ hu₁ => sum_congr rfl fun u₂ hu₂ => ?_
        have d₁ := Nat.dvd_of_mem_divisors hu₁
        have d₂ := Nat.dvd_of_mem_divisors hu₂
        rw [RamanujanTau.SvStripC.Γz_eq_prod z hd (Nat.ne_of_gt (Nat.pos_of_mem_divisors hu₁))
          (Nat.ne_of_gt (Nat.pos_of_mem_divisors hu₂))
          ((Nat.primeFactors_mono d₁ hf0).trans subset_union_left)
          ((Nat.primeFactors_mono d₂ hf0).trans subset_union_left) subset_union_right, norm_prod]
        exact prod_congr rfl fun p hp => by rw [γz_bridge (hSp p hp)]
    _ = ∏ p ∈ S, Tz p z (d.factorization p) ((y.factorial).factorization p) := by
        rw [sum_congr rfl fun (u₁ : ℕ) _ => sum_divisors_prod_localR' hf0 subset_union_left
          (fun p j => ‖γz p z (d.factorization p) (u₁.factorization p) j‖)]
        rw [sum_divisors_prod_localR' hf0 subset_union_left (fun p i => ∑ j ∈ Icc 0 ((y.factorial).factorization p),
          ‖γz p z (d.factorization p) i j‖)]
        rfl

lemma normX_eq_Xt {p : ℕ} (hp : p.Prime) (z : ℂ) : ‖xz p z‖ = Xt (-z.im) p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [normX_eq hp, Real.rpow_def_of_pos hp0, Xt]; ring_nf

section Deligne

variable [DeligneBound]

/-- **The twisted Euler-mass bound (S4).** -/
theorem s4_mass : ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℂ, -1 / 4 ≤ z.im → z.im ≤ 0 → ∀ y : ℕ, 2 ≤ y →
    ∑ d ∈ Icc 1 (y ^ 2), ‖WdC (1 - z * I) d‖ * MassZ z y d ^ 2 ≤
      A * Real.exp (4 * |z.im| * Real.log y) * Real.log y := by
  obtain ⟨A, hA0, hA⟩ := euler_strip
  refine ⟨A, hA0, fun z h1 h2 y hy => ?_⟩
  set t := -z.im with htd
  have hab : |z.im| = t := by rw [abs_of_nonpos h2]
  rw [hab]
  set T : ℕ → ℕ → ℝ := fun p e => Tz p z e ((y.factorial).factorization p) with hT
  set W : ℕ → ℕ → ℝ := fun p e => ‖WcK (lam p : ℂ) (xz p z) e‖ with hW
  have hX : ∀ p, p.Prime → ‖xz p z‖ = Xt t p := fun p hp => normX_eq_Xt hp z
  have key := hA t (by linarith) (by linarith) y hy T W (fun _ _ => Tz_nonneg _ _ _ _)
    (fun _ _ => norm_nonneg _)
    (fun p hp => by rw [← hX p hp]; exact Tz_zero_le hp h1 h2 _)
    (fun p hp => by rw [← hX p hp]; exact Tz_one_le hp h1 h2 _)
    (fun p e hp => Tz_le hp h1 h2 e _)
    (fun p hp => by rw [← hX p hp]; exact norm_W1_le hp h1 (RamanujanTau.QFProof5.lam_sq_le hp))
    (fun p e hp => by rw [← hX p hp]; exact norm_We_le hp h1 (RamanujanTau.QFProof5.lam_sq_le hp) e)
  refine le_trans (sum_le_sum fun d hd => ?_) key
  have hd0 : d ≠ 0 := by have := (mem_Icc.1 hd).1; omega
  have hWd : ‖WdC (1 - z * I) d‖ = ∏ p ∈ d.primeFactors, W p (d.factorization p) := by
    rw [WdC, norm_prod]
  rw [hWd]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (MassZ_nonneg _ _ _) (MassZ_le_prod z hd0) 2)
    (prod_nonneg fun _ _ => norm_nonneg _)

end Deligne

end RamanujanTau.SvStripD
