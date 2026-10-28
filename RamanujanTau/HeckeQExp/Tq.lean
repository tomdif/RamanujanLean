/-
# The q-expansion Hecke operator `T_p`, its Eisenstein eigenvalues, and the Tate-curve sum

For a prime `p`, a ring `R` and a multiplier `c ∈ R` (in weight `k`, `c = p^{k−1}`):

  `Tq p c F = Σ_n (a_{pn} + c·[p ∣ n]·a_{n/p}) qⁿ = U_p F + c · F(q^p)`     (`Tq_eq`).

* `TqL` — `Tq p c` as an `R`-linear map; `map_Tq` — compatibility with ring maps.
* `sigma_hecke` — `σ_k(pn) + p^k [p ∣ n] σ_k(n/p) = σ_k(p) σ_k(n)`.
* `Tq_Eis` — the formal Eisenstein series is an eigenvector: `Tq p p^{k−1} E_k = (1 + p^{k−1}) E_k`.
* **`tate_geom_sum`** — the Tate-curve side of the geometric Hecke operator, with its normalization.
  Let `Tate(q)` carry the canonical differential `ω` and let `f` have weight `k ≥ 1` and q-expansion
  `F`. For each of the `p + 1` order-`p` subgroups `C` take the quotient `π : Tate(q) → Tate(q)/C` with
  the differential `ω_C` normalized by `π^*ω_C = ω` (this is Vélu's normalization). Then:
  * `C = μ_p`: `Tate(q)/μ_p = Tate(q^p)` via `u ↦ u^p`, so `ω_C = ω_can/p` and
    `f(Tate(q^p), ω_can/p) = p^k F(q^p)`;
  * `C = ⟨ζ^j q^{1/p}⟩`: the quotient is `Tate(ζ^j t)`, `t = q^{1/p}`, via `u ↦ u`, so `ω_C = ω_can`
    and the value is `F(ζ^j t)`.
  In the variable `t` (so `q = t^p`):
    `p^k F(t^{p²}) + Σ_{j<p} F(ζ^j t) = (p · T_p F)(t^p)`,
  i.e. `Σ_C f(Tate/C, ω_C) = p · (T_p f)(Tate, ω)`, with `T_p` the classical Hecke operator
  `Σ a_{pn} qⁿ + p^{k−1} Σ a_n q^{pn}`. Equivalently `T_p f(E,ω) = p^{k−1} Σ_C f(E/C, π̌^*ω)`
  (`π̌^*ω = p·ω_C`).
-/
import RamanujanTau.TateCurve.Hasse
import RamanujanTau.UpContraction.TateU

set_option autoImplicit false

namespace HeckeQExp
open PowerSeries Finset
open scoped ArithmeticFunction.sigma

section Ring
variable {R : Type*} [CommRing R]

/-- **The q-expansion Hecke operator** with multiplier `c` (`c = p^{k−1}` in weight `k`). -/
noncomputable def Tq (p : ℕ) (c : R) (F : PowerSeries R) : PowerSeries R :=
  mk fun n => coeff (p * n) F + c * if p ∣ n then coeff (n / p) F else 0

lemma coeff_Tq (p : ℕ) (c : R) (F : PowerSeries R) (n : ℕ) :
    coeff n (Tq p c F) = coeff (p * n) F + c * if p ∣ n then coeff (n / p) F else 0 :=
  coeff_mk _ _

/-- `T_p = U_p + c · V_p`. -/
lemma Tq_eq (p : ℕ) (hp : p ≠ 0) (c : R) (F : PowerSeries R) :
    Tq p c F = UpContraction.Up p F + C c * expand p hp F := by
  ext n
  rw [coeff_Tq, map_add, UpContraction.Up, coeff_mk, coeff_C_mul, coeff_expand]

/-- `T_p` as an `R`-linear map. -/
noncomputable def TqL (p : ℕ) (c : R) : PowerSeries R →ₗ[R] PowerSeries R where
  toFun := Tq p c
  map_add' F G := by
    ext n; simp only [coeff_Tq, map_add]; split_ifs <;> ring
  map_smul' a F := by
    ext n; simp only [coeff_Tq, coeff_smul, RingHom.id_apply, smul_eq_mul]; split_ifs <;> ring

lemma TqL_apply (p : ℕ) (c : R) (F : PowerSeries R) : TqL p c F = Tq p c F := rfl

lemma map_Tq {S : Type*} [CommRing S] (φ : R →+* S) (p : ℕ) (c : R) (F : PowerSeries R) :
    map φ (Tq p c F) = Tq p (φ c) (map φ F) := by
  ext n
  simp only [coeff_map, coeff_Tq, map_add, map_mul]
  split_ifs <;> simp

end Ring

/-! ### The Eisenstein eigenvalue -/

/-- `Σ_{j<b+3} x^j + x Σ_{j<b+1} x^j = (1 + x) Σ_{j<b+2} x^j`. -/
lemma geom_aux (x : ℕ) (b : ℕ) :
    ∑ j ∈ range (b + 1 + 1 + 1), x ^ j + x * ∑ j ∈ range (b + 1), x ^ j =
      (1 + x) * ∑ j ∈ range (b + 1 + 1), x ^ j := by
  rw [sum_range_succ _ (b + 1 + 1), sum_range_succ _ (b + 1)]
  ring

/-- **Hecke relation for `σ_k`**: `σ_k(pn) + p^k [p ∣ n] σ_k(n/p) = σ_k(p) σ_k(n)`. -/
theorem sigma_hecke {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    σ k (p * n) + (if p ∣ n then p ^ k * σ k (n / p) else 0) = σ k p * σ k n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.one_lt.ne'
  have hcop : ∀ i, Nat.Coprime (p ^ i) m := fun i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  have hσ : ∀ i, σ k (p ^ i * m) = σ k (p ^ i) * σ k m := fun i =>
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop i)
  have hpp : ∀ i, σ k (p ^ i) = ∑ j ∈ range (i + 1), (p ^ k) ^ j := fun i => by
    rw [ArithmeticFunction.sigma_apply_prime_pow hp]
    exact sum_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have hp1 : σ k p = 1 + p ^ k := by
    have := hpp 1
    rw [pow_one] at this
    simp [this, sum_range_succ]
  rw [← mul_assoc, ← pow_succ', hσ, hσ, hp1]
  rcases e with _ | b
  · have : ¬ p ∣ p ^ 0 * m := by simpa using hm
    rw [if_neg this, hpp, hpp]; simp [sum_range_succ]
  · have hd : p ∣ p ^ (b + 1) * m := Dvd.dvd.mul_right (dvd_pow_self p (Nat.succ_ne_zero b)) m
    rw [if_pos hd]
    have hdiv : p ^ (b + 1) * m / p = p ^ b * m := by
      rw [pow_succ, mul_comm (p ^ b) p, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    rw [hdiv, hσ, hpp, hpp, hpp]
    have := geom_aux (p ^ k) b
    calc (∑ j ∈ range (b + 1 + 1 + 1), (p ^ k) ^ j) * σ k m +
          p ^ k * ((∑ j ∈ range (b + 1), (p ^ k) ^ j) * σ k m)
        = (∑ j ∈ range (b + 1 + 1 + 1), (p ^ k) ^ j + p ^ k * ∑ j ∈ range (b + 1), (p ^ k) ^ j) *
            σ k m := by ring
      _ = _ := by rw [this]; ring

/-- **The formal Eisenstein series is a Hecke eigenvector**:
`T_p E_k = (1 + p^{k−1}) E_k` (eigenvalue `σ_{k−1}(p)`). -/
theorem Tq_Eis {p : ℕ} (hp : p.Prime) {k : ℕ} :
    Tq p ((p : ℚ) ^ (k - 1)) (TateCurve.Eis k) = C (1 + (p : ℚ) ^ (k - 1)) * TateCurve.Eis k := by
  ext n
  rw [coeff_Tq, coeff_C_mul]
  simp only [TateCurve.coeff_Eis]
  have hs := sigma_hecke hp (k - 1) n
  have hsQ : ((σ (k - 1) (p * n) : ℕ) : ℚ) +
      (if p ∣ n then (p : ℚ) ^ (k - 1) * (σ (k - 1) (n / p) : ℚ) else 0) =
      (1 + (p : ℚ) ^ (k - 1)) * (σ (k - 1) n : ℚ) := by
    have hp1 : σ (k - 1) p = 1 + p ^ (k - 1) := by
      have h1 := ArithmeticFunction.sigma_apply_prime_pow (k := k - 1) (i := 1) hp
      rw [pow_one] at h1
      simp [h1, sum_range_succ]
    rw [hp1] at hs
    have := congrArg (fun x : ℕ => (x : ℚ)) hs
    push_cast at this
    split_ifs at this ⊢ with h
    · linarith
    · simpa using this
  have hpn : (p * n = 0) ↔ n = 0 := by simp [hp.ne_zero]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg ((not_congr hpn).mpr hn), if_neg hn]
    by_cases h : p ∣ n
    · have hnp : n / p ≠ 0 := by
        obtain ⟨m, rfl⟩ := h
        rw [Nat.mul_div_cancel_left _ hp.pos]; rintro rfl; simp at hn
      rw [if_pos h, if_neg hnp]
      rw [if_pos h] at hsQ
      linear_combination (TateCurve.kappa k) * hsQ
    · rw [if_neg h]
      rw [if_neg h] at hsQ
      linear_combination (TateCurve.kappa k) * hsQ

/-! ### The Tate-curve side: the sum over all `p + 1` subgroups -/

section Tate
variable {R : Type*} [CommRing R] [IsDomain R]

/-- **The geometric Hecke sum on the Tate curve** (normalization `π^*ω_C = ω`, see the module doc).
In the variable `t = q^{1/p}`:

  `p^k F(t^{p²}) + Σ_{j<p} F(ζ^j t) = (p · T_p F)(t^p)`,  `T_p = Tq p p^{k−1}`.

The first term is the canonical subgroup `μ_p` (quotient `Tate(q^p)`, `ω_C = ω_can/p`), the others the
`p` subgroups `⟨ζ^j t⟩` (quotients `Tate(ζ^j t)`, `ω_C = ω_can`). -/
theorem tate_geom_sum {p : ℕ} (hp : p.Prime) {ζ : R} (hζ : IsPrimitiveRoot ζ p) {k : ℕ}
    (hk : 1 ≤ k) (F : PowerSeries R) :
    expand p hp.ne_zero (C ((p : R) ^ k) * expand p hp.ne_zero F) +
        ∑ j ∈ range p, rescale (ζ ^ j) F =
      expand p hp.ne_zero (C (p : R) * Tq p ((p : R) ^ (k - 1)) F) := by
  ext m
  rw [map_add, UpContraction.sum_rescale_coeff hp hζ F m, coeff_expand, coeff_expand]
  split_ifs with h
  · obtain ⟨n, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ hp.pos, coeff_C_mul, coeff_C_mul, coeff_Tq, coeff_expand]
    have hk' : (p : R) ^ k = p * p ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hk']
    split_ifs <;> ring
  · simp

/-- `tate_geom_sum` with a general multiplier `c` satisfying `p^k = p·c` (e.g. `c = p⁻¹` in weight `0`
over a field). -/
theorem tate_geom_sum' {p : ℕ} (hp : p.Prime) {ζ : R} (hζ : IsPrimitiveRoot ζ p) {k : ℕ} {c : R}
    (hc : (p : R) ^ k = p * c) (F : PowerSeries R) :
    expand p hp.ne_zero (C ((p : R) ^ k) * expand p hp.ne_zero F) +
        ∑ j ∈ range p, rescale (ζ ^ j) F =
      expand p hp.ne_zero (C (p : R) * Tq p c F) := by
  ext m
  rw [map_add, UpContraction.sum_rescale_coeff hp hζ F m, coeff_expand, coeff_expand]
  split_ifs with h
  · obtain ⟨n, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ hp.pos, coeff_C_mul, coeff_C_mul, coeff_Tq, coeff_expand, hc]
    split_ifs <;> ring
  · simp

/-- The non-canonical part alone (`TateU`): `Σ_{j<p} F(ζ^j t) = (p · U_p F)(t^p)`. -/
theorem tate_noncanonical_sum {p : ℕ} (hp : p.Prime) {ζ : R} (hζ : IsPrimitiveRoot ζ p)
    (F : PowerSeries R) :
    ∑ j ∈ range p, rescale (ζ ^ j) F = expand p hp.ne_zero (C (p : R) * UpContraction.Up p F) := by
  ext m
  rw [UpContraction.sum_rescale_coeff hp hζ F m, coeff_expand]
  split_ifs with h
  · obtain ⟨n, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ hp.pos, coeff_C_mul, UpContraction.Up, coeff_mk]
  · rfl

end Tate

end HeckeQExp
