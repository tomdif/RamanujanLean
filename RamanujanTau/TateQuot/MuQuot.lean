/-
# Vélu's quotient of `Tate(q)` by `μ_p` is `Tate(q^p)` with `ω/p`

Short model of `Tate(q)`: `y² = x³ + A x + B`, `A = −c₄/48 = a₄ − 1/48`, `B = −c₆/864 = 1/864 − a₄/12 + a₆`,
with `x_short = x_Tate + 1/12`, `y_short = (2y + x)/2 = θx/2`. The nonzero points of `μ_p` are
`P_k = (X_k, Y_k)`, `X_k = x(ζ^k) + 1/12`, `Y_k = θx(ζ^k)/2` (`1 ≤ k < p`); `S = {1, …, (p−1)/2}`
represents `(μ_p ∖ 0)/±`. Vélu's
`A' = A − 5 Σ_{k∈S} (6X_k² + 2A)`, `B' = B − 7 Σ_{k∈S} (4Y_k² + X_k(6X_k² + 2A))` satisfy
(`velu_mu_A`, `velu_mu_B`)
  `−48 A' = p⁴ E₄(q^p)`, `864 B' = p⁶ E₆(q^p)`,
i.e. `c₄, c₆` of `y² = x³ + A'x + B'` are those of `Tate(q^p)` with the differential `ω_can/p`.
-/
import RamanujanTau.TateQuot.MuSum
import RamanujanTau.ModP.Formal

set_option autoImplicit false

noncomputable section

namespace TateQuot

open PowerSeries Finset

/-! ### Vélu's formulas from the `x`- and `y`-values of a set of representatives -/

section Velu
variable {L : Type*} [CommRing L] {ι : Type*}

/-- Vélu's `A' = A − 5 Σ_{Q∈S} (6x_Q² + 2A)`. -/
def veluA (A : L) (S : Finset ι) (x : ι → L) : L := A - 5 * ∑ i ∈ S, (6 * x i ^ 2 + 2 * A)

/-- Vélu's `B' = B − 7 Σ_{Q∈S} (4y_Q² + x_Q(6x_Q² + 2A))`. -/
def veluB (A B : L) (S : Finset ι) (x y : ι → L) : L :=
  B - 7 * ∑ i ∈ S, (4 * y i ^ 2 + x i * (6 * x i ^ 2 + 2 * A))

end Velu

variable {K : Type*} [Field K] [CharZero K] {p : ℕ} [hp : Fact p.Prime] {ζ : K}

/-- Short-model `A` of `Tate(q)` over `K`. -/
def Ash (K : Type*) [Field K] : PowerSeries K := a4K - C (1 / 48)
/-- Short-model `B` of `Tate(q)` over `K`. -/
def Bsh (K : Type*) [Field K] : PowerSeries K := C (1 / 864) - C (1 / 12) * a4K + a6K

/-- `X_k = x(ζ^k) + 1/12`. -/
def Xmu (ζ : K) (k : ℕ) : PowerSeries K := tx 0 (ζ ^ k) + C (1 / 12)
/-- `Y_k = θx(ζ^k)/2`. -/
def Ymu (ζ : K) (k : ℕ) : PowerSeries K := C (1 / 2) * tx 1 (ζ ^ k)

/-! ### Computing in the field `K((q))` -/

/-- `K⟦q⟧ ↪ K((q))`. -/
abbrev ιL (K : Type*) [Field K] : PowerSeries K →+* LaurentSeries K := HahnSeries.ofPowerSeries ℤ K

omit [CharZero K] in
lemma ιL_inj : Function.Injective (ιL K) := HahnSeries.ofPowerSeries_injective

omit [CharZero K] in
lemma ιL_C (c : K) : ιL K (C c) = HahnSeries.C c := HahnSeries.ofPowerSeries_C c

instance : CharZero (LaurentSeries K) :=
  charZero_of_injective_algebraMap (algebraMap K (LaurentSeries K)).injective

/-- **The `μ_p`-points lie on the short Tate curve**: `Y_k² = X_k³ + A X_k + B`. -/
theorem mu_on_curve (hζ : IsPrimitiveRoot ζ p) {k : ℕ} (hk : k ∈ Ico 1 p) :
    Ymu ζ k ^ 2 = Xmu ζ k ^ 3 + Ash K * Xmu ζ k + Bsh K := by
  have h := congrArg (ιL K) (tx_weier (zeta_pow_ne_zero hζ k) (pow_ne_one_Ico hζ hk))
  apply ιL_inj
  simp only [Ymu, Xmu, Ash, Bsh, map_add, map_mul, map_pow, map_sub, map_ofNat, ιL_C, map_div₀,
    map_one] at h ⊢
  linear_combination (1 / 4 : LaurentSeries K) * h

/-! ### Symmetry `k ↦ p − k` and the half sum over `S = {1, …, (p−1)/2}` -/

omit [CharZero K] in
lemma zeta_pow_sub (hζ : IsPrimitiveRoot ζ p) {k : ℕ} (hk : k ≤ p) : ζ ^ (p - k) = (ζ ^ k)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_add, Nat.sub_add_cancel hk, hζ.pow_eq_one]

omit [CharZero K] in
lemma tx0_inv {w : K} (hw : w ≠ 0) (hw1 : w ≠ 1) : tx 0 w⁻¹ = tx 0 w := by
  have hw1' : w⁻¹ ≠ 1 := by rwa [Ne, inv_eq_one]
  rw [tx_eq (inv_ne_zero hw) hw1', tx_eq hw hw1]
  congr 2
  · simp only [cK, cpoly, Polynomial.eval₂_X]
    have h1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
    have h2 : w⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr hw1'
    rw [div_eq_div_iff (pow_ne_zero 2 h2) (pow_ne_zero 2 h1)]
    field_simp
    ring
  · funext N
    simp only [txc]
    refine sum_congr rfl fun d _ => ?_
    rw [inv_inv]; ring

lemma Xmu_sym (hζ : IsPrimitiveRoot ζ p) {k : ℕ} (hk : k ∈ Ico 1 p) : Xmu ζ (p - k) = Xmu ζ k := by
  rw [Xmu, Xmu, zeta_pow_sub hζ (mem_Ico.mp hk).2.le,
    tx0_inv (zeta_pow_ne_zero hζ k) (pow_ne_one_Ico hζ hk)]

omit [CharZero K] in
lemma half_sum {M : Type*} [AddCommMonoid M] (hp2 : p ≠ 2) (g : ℕ → M)
    (hg : ∀ k ∈ Ico 1 p, g (p - k) = g k) :
    ∑ k ∈ Ico 1 p, g k = ∑ k ∈ Icc 1 (p / 2), g k + ∑ k ∈ Icc 1 (p / 2), g k := by
  have hodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left hp2
  have hpp : p = 2 * (p / 2) + 1 := by omega
  have hh : 1 ≤ p / 2 := by have := hp.out.two_le; omega
  have e : Icc 1 (p / 2) = Ico 1 (p / 2 + 1) := by ext; simp only [mem_Icc, mem_Ico]; omega
  rw [e, ← sum_Ico_consecutive _ (by omega : 1 ≤ p / 2 + 1)
    (by omega : p / 2 + 1 ≤ p)]
  congr 1
  refine sum_nbij' (fun k => p - k) (fun k => p - k) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [mem_coe, mem_Ico] at hk ⊢; omega
  · intro k hk; simp only [mem_coe, mem_Ico] at hk ⊢; omega
  · intro k hk; simp only [mem_coe, mem_Ico] at hk; dsimp only; omega
  · intro k hk; simp only [mem_coe, mem_Ico] at hk; dsimp only; omega
  · intro k hk
    simp only [mem_Ico] at hk
    rw [← hg k (by simp only [mem_Ico]; omega)]

/-! ### Power sums of the `X_k` through the differential equations -/

/-- `Σ_{k=1}^{p−1} x(ζ^k)²`. -/
def T2 (ζ : K) (p : ℕ) : PowerSeries K := ∑ k ∈ Ico 1 p, tx 0 (ζ ^ k) ^ 2
/-- `Σ_{k=1}^{p−1} x(ζ^k)³`. -/
def T3 (ζ : K) (p : ℕ) : PowerSeries K := ∑ k ∈ Ico 1 p, tx 0 (ζ ^ k) ^ 3

lemma hsum2 (hζ : IsPrimitiveRoot ζ p) :
    Ssum K ζ p 2 = 6 * T2 ζ p + Ssum K ζ p 0 + ((p - 1 : ℕ) : PowerSeries K) * (2 * a4K) := by
  rw [Ssum, sum_congr rfl fun k hk => tx_two (zeta_pow_ne_zero hζ k) (pow_ne_one_Ico hζ hk)]
  simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ico, nsmul_eq_mul, T2, Ssum]
  ring

lemma hsum4 (hζ : IsPrimitiveRoot ζ p) :
    Ssum K ζ p 4 = 120 * T3 ζ p + 30 * T2 ζ p + (72 * a4K + 1) * Ssum K ζ p 0 +
      ((p - 1 : ℕ) : PowerSeries K) * (48 * a6K + 2 * a4K) := by
  rw [Ssum, sum_congr rfl fun k hk => tx_four (zeta_pow_ne_zero hζ k) (pow_ne_one_Ico hζ hk)]
  simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ico, nsmul_eq_mul, T2, T3, Ssum]
  ring

lemma sumIco_A (A : PowerSeries K) :
    ∑ k ∈ Ico 1 p, (6 * Xmu ζ k ^ 2 + 2 * A) = 6 * T2 ζ p + 12 * C (1 / 12) * Ssum K ζ p 0 +
      ((p - 1 : ℕ) : PowerSeries K) * (6 * C (1 / 12) ^ 2 + 2 * A) := by
  have e : ∀ k, 6 * Xmu ζ k ^ 2 + 2 * A = 6 * tx 0 (ζ ^ k) ^ 2 + 12 * C (1 / 12) * tx 0 (ζ ^ k) +
      (6 * C (1 / 12) ^ 2 + 2 * A) := fun k => by rw [Xmu]; ring
  simp only [e, sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ico, nsmul_eq_mul, T2, Ssum]
  ring

lemma sumIco_B (A B : PowerSeries K) :
    ∑ k ∈ Ico 1 p, (10 * Xmu ζ k ^ 3 + 6 * A * Xmu ζ k + 4 * B) =
      10 * T3 ζ p + 30 * C (1 / 12) * T2 ζ p + (30 * C (1 / 12) ^ 2 + 6 * A) * Ssum K ζ p 0 +
      ((p - 1 : ℕ) : PowerSeries K) * (10 * C (1 / 12) ^ 3 + 6 * A * C (1 / 12) + 4 * B) := by
  have e : ∀ k, 10 * Xmu ζ k ^ 3 + 6 * A * Xmu ζ k + 4 * B = 10 * tx 0 (ζ ^ k) ^ 3 +
      30 * C (1 / 12) * tx 0 (ζ ^ k) ^ 2 + (30 * C (1 / 12) ^ 2 + 6 * A) * tx 0 (ζ ^ k) +
      (10 * C (1 / 12) ^ 3 + 6 * A * C (1 / 12) + 4 * B) := fun k => by rw [Xmu]; ring
  simp only [e, sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ico, nsmul_eq_mul, T2, T3, Ssum]
  ring

/-! ### The Eisenstein series -/

omit [CharZero K] in
lemma E4_eq : ModP.E4 K = 1 + 240 * sigK K 3 := by
  rw [ModP.E4, RamanujanTau.Mod691.p4, sigK, ← TateCurve.s3_eq, map_add, map_one, map_mul,
    map_ofNat]

omit [CharZero K] in
lemma E6_eq : ModP.E6 K = 1 - 504 * sigK K 5 := by
  rw [ModP.E6, RamanujanTau.Mod691.p6, sigK, ← TateCurve.s5_eq, map_sub, map_one, map_mul,
    map_ofNat]

omit [CharZero K] in
lemma a4K_eq : a4K = -5 * sigK K 3 := by
  rw [a4K, TateCurve.a4, sigK, map_mul, map_neg, map_ofNat]

omit [CharZero K] in
lemma a6K_eq : 12 * a6K = -(5 * sigK K 3 + 7 * sigK K 5) := by
  have h := congrArg (PowerSeries.map (Int.castRingHom K)) TateCurve.twelve_mul_a6
  simp only [map_mul, map_neg, map_add, map_ofNat] at h
  exact h

/-! ### The main identities -/

/-- **Vélu's `A'` for `μ_p`**: `−48 A' = p⁴ E₄(q^p)`. -/
theorem velu_mu_A (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) :
    -48 * veluA (Ash K) (Icc 1 (p / 2)) (Xmu ζ) =
      C ((p : K) ^ 4) * expand p hp.out.ne_zero (ModP.E4 K) := by
  have hh := half_sum hp2 (fun k => 6 * Xmu ζ k ^ 2 + 2 * Ash K)
    (fun k hk => by simp only [Xmu_sym hζ hk])
  simp only [] at hh
  set J := ∑ k ∈ Icc 1 (p / 2), (6 * Xmu ζ k ^ 2 + 2 * Ash K) with hJ
  have hv : veluA (Ash K) (Icc 1 (p / 2)) (Xmu ζ) = Ash K - 5 * J := rfl
  rw [hv]
  have hI := sumIco_A (ζ := ζ) (p := p) (Ash K)
  have h2 := hsum2 hζ
  have hS2 := S2_eq hζ
  have ha4 := a4K_eq (K := K)
  have hp1 : ((p - 1 : ℕ) : PowerSeries K) = (p : PowerSeries K) - 1 := by
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  rw [hp1] at hI h2
  rw [hI] at hh
  apply ιL_inj
  have hh' := congrArg (ιL K) hh
  have h2' := congrArg (ιL K) h2
  have hS2' := congrArg (ιL K) hS2
  have ha4' := congrArg (ιL K) ha4
  simp only [Ash, E4_eq, map_add, map_mul, map_pow, map_sub, map_neg, map_ofNat, map_one,
    map_natCast, ιL_C, map_div₀] at hh' h2' hS2' ha4' ⊢
  linear_combination -120 * hh' - 120 * h2' + 120 * hS2' - 48 * ha4'

/-- **Vélu's `B'` for `μ_p`**: `864 B' = p⁶ E₆(q^p)`. -/
theorem velu_mu_B (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) :
    864 * veluB (Ash K) (Bsh K) (Icc 1 (p / 2)) (Xmu ζ) (Ymu ζ) =
      C ((p : K) ^ 6) * expand p hp.out.ne_zero (ModP.E6 K) := by
  have hsub : ∀ k ∈ Icc 1 (p / 2), k ∈ Ico 1 p := fun k hk => by
    have := hp.out.two_le
    simp only [mem_Icc, mem_Ico] at hk ⊢; omega
  have hcurve : ∑ k ∈ Icc 1 (p / 2), (4 * Ymu ζ k ^ 2 + Xmu ζ k * (6 * Xmu ζ k ^ 2 + 2 * Ash K)) =
      ∑ k ∈ Icc 1 (p / 2), (10 * Xmu ζ k ^ 3 + 6 * Ash K * Xmu ζ k + 4 * Bsh K) :=
    sum_congr rfl fun k hk => by rw [mu_on_curve hζ (hsub k hk)]; ring
  have hv : veluB (Ash K) (Bsh K) (Icc 1 (p / 2)) (Xmu ζ) (Ymu ζ) =
      Bsh K - 7 * ∑ k ∈ Icc 1 (p / 2), (10 * Xmu ζ k ^ 3 + 6 * Ash K * Xmu ζ k + 4 * Bsh K) := by
    rw [veluB, hcurve]
  rw [hv]
  have hh := half_sum hp2 (fun k => 10 * Xmu ζ k ^ 3 + 6 * Ash K * Xmu ζ k + 4 * Bsh K)
    (fun k hk => by simp only [Xmu_sym hζ hk])
  simp only [] at hh
  set J := ∑ k ∈ Icc 1 (p / 2), (10 * Xmu ζ k ^ 3 + 6 * Ash K * Xmu ζ k + 4 * Bsh K) with hJ
  have hI := sumIco_B (ζ := ζ) (p := p) (Ash K) (Bsh K)
  have h4 := hsum4 hζ
  have hS4 := S4_eq hζ
  have ha4 := a4K_eq (K := K)
  have ha6 := a6K_eq (K := K)
  have hp1 : ((p - 1 : ℕ) : PowerSeries K) = (p : PowerSeries K) - 1 := by
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  rw [hp1] at hI h4
  rw [hI] at hh
  apply ιL_inj
  have hh' := congrArg (ιL K) hh
  have h4' := congrArg (ιL K) h4
  have hS4' := congrArg (ιL K) hS4
  have ha4' := congrArg (ιL K) ha4
  have ha6' := congrArg (ιL K) ha6
  simp only [Ash, Bsh, E6_eq, map_add, map_mul, map_pow, map_sub, map_neg, map_ofNat, map_one,
    map_natCast, ιL_C, map_div₀] at hh' h4' hS4' ha4' ha6' ⊢
  linear_combination 3024 * hh' + 252 * h4' - 252 * hS4' + 72 * ha6' - 72 * ha4'

end TateQuot
