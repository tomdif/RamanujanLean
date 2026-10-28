import RamanujanTau.BoylanWebb.Forms
import RamanujanTau.TauCongruences
import RamanujanTau.MockTheta5PartitionCount
import RamanujanTau.AtkinOBrien.Induction

/-!
# The Boylan–Webb sequence `L_ℓ(b)` and its structure mod `ℓ`

`Φ = η(ℓ²z)/η(z) = q^δ (q^{ℓ²};q^{ℓ²})_∞/(q;q)_∞` with `δ = (ℓ²−1)/24`, and
`L(0) = 1`, `L(2b+1) = U(Φ·L(2b))`, `L(2b+2) = U(L(2b+1))`.

* `Ψ_Φ` (Frobenius): `Φ ≡ Δ^δ (mod ℓ)`.
* **`L_eq_partition`**: `L(b) = E·Σ_m p(ℓ^b m − e_b) qᵐ` with `E = (q;q)_∞` (`b` even) or
  `(q^ℓ;q^ℓ)_∞` (`b` odd), `24 e_b = ℓ^{2⌈b/2⌉} − 1`, and `p(negative) = 0`.
* **`L_mod`**: if mod `ℓ` one has `U(Δ^δ) = c f`, `U f = λ f`, `U(Δ^δ f) = μ f` for a series `f`, then
  `L(2b+1) ≡ c(λμ)^b f` and `L(2b+2) ≡ cλ(λμ)^b f`. Hence `L(b+2) ≡ λμ·L(b)` for `b ≥ 1`
  (`L_two_step`) and `L(b) ≢ 0` (`L_ne_zero`).
-/

set_option autoImplicit false

namespace BoylanWebb
open PowerSeries Finset MockTheta5.JTP
open RankProof (Ea coeff_Ea)

section U
variable {R : Type*} [CommRing R] (ℓ : ℕ)

lemma U_add (f g : PowerSeries R) : U ℓ (f + g) = U ℓ f + U ℓ g := by ext n; simp [coeff_U]
lemma U_sub (f g : PowerSeries R) : U ℓ (f - g) = U ℓ f - U ℓ g := by ext n; simp [coeff_U]
lemma U_C_mul (c : R) (f : PowerSeries R) : U ℓ (C c * f) = C c * U ℓ f := by
  ext n; simp [coeff_U, coeff_C_mul]

lemma map_U {S : Type*} [CommRing S] (φ : R →+* S) (f : PowerSeries R) :
    PowerSeries.map φ (U ℓ f) = U ℓ (PowerSeries.map φ f) := by
  ext n; simp [coeff_U]

end U

/-- **`U(g(q^ℓ)·f) = g·U(f)`**. -/
lemma U_Ea_mul (ℓ : ℕ) (hℓ : ℓ ≠ 0) (g f : PowerSeries ℤ) : U ℓ (Ea ℓ hℓ g * f) = g * U ℓ f := by
  have hpos : 0 < ℓ := Nat.pos_of_ne_zero hℓ
  ext n
  rw [coeff_U, coeff_mul, coeff_mul]
  rw [← sum_subset (s₁ := (antidiagonal n).map ⟨fun p => (ℓ * p.1, ℓ * p.2), fun p q h => by
      simp only [Prod.mk.injEq] at h
      ext
      · exact Nat.eq_of_mul_eq_mul_left hpos h.1
      · exact Nat.eq_of_mul_eq_mul_left hpos h.2⟩) ?_ ?_]
  · rw [sum_map]
    refine sum_congr rfl fun p _ => ?_
    simp only [Function.Embedding.coeFn_mk, coeff_Ea, coeff_U]
    rw [if_pos (dvd_mul_right ℓ _), Nat.mul_div_cancel_left _ hpos]
  · intro p hp
    simp only [mem_map, mem_antidiagonal, Function.Embedding.coeFn_mk] at hp ⊢
    obtain ⟨q, hq, rfl⟩ := hp
    rw [← mul_add, hq]
  · intro p hp hp'
    simp only [mem_antidiagonal] at hp
    rw [coeff_Ea]
    split_ifs with h
    · exfalso; apply hp'
      obtain ⟨c, hc⟩ := h
      have h2 : ℓ ∣ p.2 := by
        have : p.2 = ℓ * n - p.1 := by omega
        rw [this, hc, ← Nat.mul_sub]; exact dvd_mul_right _ _
      obtain ⟨d, hd⟩ := h2
      simp only [mem_map, mem_antidiagonal, Function.Embedding.coeFn_mk]
      refine ⟨(c, d), ?_, ?_⟩
      · apply Nat.eq_of_mul_eq_mul_left hpos
        rw [mul_add, ← hc, ← hd, hp]
      · ext <;> simp [hc, hd]
    · rw [zero_mul]

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- `δ = (ℓ² − 1)/24`. -/
def δ : ℕ := (ℓ ^ 2 - 1) / 24

lemma hℓ0 : ℓ ≠ 0 := hℓ.out.ne_zero

/-- `Φ = q^δ (q^{ℓ²};q^{ℓ²})_∞ / (q;q)_∞`. -/
noncomputable def Φ : PowerSeries ℤ :=
  X ^ δ ℓ * Ea (ℓ ^ 2) (TauCong.ppow_ne ℓ 2) qfacInf * partitionGF

/-- the alternating operators: `U(Φ·)` at even steps, `U` at odd steps. -/
noncomputable def T (b : ℕ) (f : PowerSeries ℤ) : PowerSeries ℤ :=
  if Even b then U ℓ (Φ ℓ * f) else U ℓ f

/-- Boylan–Webb's `L_ℓ(b)`. -/
noncomputable def L : ℕ → PowerSeries ℤ
  | 0 => 1
  | b + 1 => T ℓ b (L b)

/-- `Δ = q(q;q)²⁴_∞ ∈ ℤ⟦q⟧`. -/
noncomputable abbrev Dz : PowerSeries ℤ := X * qfacInf ^ 24

lemma qfac_mul_pgf : qfacInf * partitionGF = 1 := Ring.mul_inverse_cancel _ isUnit_qfacInf

/-- **Frobenius**: `Φ ≡ Δ^δ (mod ℓ)` when `24δ = ℓ² − 1`. -/
theorem Ψ_Φ (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) : Ψ ℓ (Φ ℓ) = Ψ ℓ (Dz ^ δ ℓ) := by
  have hF := TauCong.frob_qfacInf ℓ 2
  change (Ψ ℓ qfacInf) ^ (ℓ ^ 2) = Ψ ℓ (Ea (ℓ ^ 2) _ qfacInf) at hF
  have h1 : Ψ ℓ qfacInf * Ψ ℓ partitionGF = 1 := by rw [← map_mul, qfac_mul_pgf, map_one]
  rw [Φ, map_mul, map_mul, ← hF, ← h24, map_pow, map_pow, map_mul, mul_pow, pow_succ, map_pow,
    ← pow_mul, mul_comm 24 (δ ℓ)]
  linear_combination (Ψ ℓ X) ^ δ ℓ * (Ψ ℓ qfacInf) ^ (δ ℓ * 24) * h1

section ModEll
variable (fb : PowerSeries (ZMod ℓ)) (c lam mu : ZMod ℓ)

lemma Ψ_T_even (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (b : ℕ) (hb : Even b) (f : PowerSeries ℤ) :
    Ψ ℓ (T ℓ b f) = U ℓ (Ψ ℓ (Dz ^ δ ℓ) * Ψ ℓ f) := by
  rw [T, if_pos hb, map_U, map_mul, Ψ_Φ ℓ h24]

lemma Ψ_T_odd (b : ℕ) (hb : ¬ Even b) (f : PowerSeries ℤ) : Ψ ℓ (T ℓ b f) = U ℓ (Ψ ℓ f) := by
  rw [T, if_neg hb, map_U]

lemma L_succ (n : ℕ) : L ℓ (n + 1) = T ℓ n (L ℓ n) := rfl

lemma even_2b (b : ℕ) : Even (2 * b) := even_two_mul b
lemma not_even_2b1 (b : ℕ) : ¬ Even (2 * b + 1) := by
  rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one b

/-- **The mod-`ℓ` structure of `L(b)`.** -/
theorem L_mod (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)
    (h0 : U ℓ (Ψ ℓ (Dz ^ δ ℓ)) = C c * fb) (h1 : U ℓ fb = C lam * fb)
    (h2 : U ℓ (Ψ ℓ (Dz ^ δ ℓ) * fb) = C mu * fb) (b : ℕ) :
    Ψ ℓ (L ℓ (2 * b + 1)) = C (c * (lam * mu) ^ b) * fb ∧
      Ψ ℓ (L ℓ (2 * b + 2)) = C (c * lam * (lam * mu) ^ b) * fb := by
  have hstep : ∀ x : ZMod ℓ, Ψ ℓ (L ℓ (2 * b + 1)) = C x * fb →
      Ψ ℓ (L ℓ (2 * b + 2)) = C (x * lam) * fb := by
    intro x hx
    rw [L_succ, Ψ_T_odd ℓ _ (not_even_2b1 b), hx, U_C_mul, h1, map_mul, mul_assoc]
  induction b with
  | zero =>
    have e1 : Ψ ℓ (L ℓ (2 * 0 + 1)) = C (c * (lam * mu) ^ 0) * fb := by
      rw [L_succ, Ψ_T_even ℓ h24 _ (even_2b 0), show L ℓ (2 * 0) = 1 from rfl, map_one, mul_one, h0,
        pow_zero, mul_one]
    refine ⟨e1, ?_⟩
    rw [hstep _ e1]; ring_nf
  | succ b ih =>
    obtain ⟨_, ih2⟩ := ih (fun x hx => by
      rw [L_succ, Ψ_T_odd ℓ _ (not_even_2b1 b), hx, U_C_mul, h1, map_mul, mul_assoc])
    have e1 : Ψ ℓ (L ℓ (2 * (b + 1) + 1)) = C (c * (lam * mu) ^ (b + 1)) * fb := by
      rw [show 2 * (b + 1) = 2 * b + 2 by ring, L_succ, Ψ_T_even ℓ h24 _ (by
        rw [show 2 * b + 2 = 2 * (b + 1) by ring]; exact even_2b _), ih2, mul_left_comm, U_C_mul, h2,
        ← mul_assoc, ← map_mul]
      ring_nf
    refine ⟨e1, ?_⟩
    rw [show 2 * (b + 1) + 2 = (2 * (b + 1) + 1) + 1 by ring, L_succ, Ψ_T_odd ℓ _ (not_even_2b1 _), e1,
      U_C_mul, h1, ← mul_assoc, ← map_mul]
    ring_nf

/-- `L(b+2) ≡ λμ·L(b) (mod ℓ)` for every `b ≥ 1`. -/
theorem L_two_step (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)
    (h0 : U ℓ (Ψ ℓ (Dz ^ δ ℓ)) = C c * fb) (h1 : U ℓ fb = C lam * fb)
    (h2 : U ℓ (Ψ ℓ (Dz ^ δ ℓ) * fb) = C mu * fb) (b : ℕ) (hb : 1 ≤ b) :
    Ψ ℓ (L ℓ (b + 2)) = C (lam * mu) * Ψ ℓ (L ℓ b) := by
  have H := L_mod ℓ fb c lam mu h24 h0 h1 h2
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' b
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1) + 2 = 2 * (j + 1) + 2 from rfl, (H (j + 1)).2,
      show 2 * (j + 1) = 2 * j + 2 by ring, (H j).2, ← mul_assoc, ← map_mul]
    ring_nf
  · rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring, (H (k + 1)).1, (H k).1, ← mul_assoc, ← map_mul]
    ring_nf

/-- `L(b) ≢ 0 (mod ℓ)` for every `b ≥ 1`. -/
theorem L_ne_zero (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)
    (h0 : U ℓ (Ψ ℓ (Dz ^ δ ℓ)) = C c * fb) (h1 : U ℓ fb = C lam * fb)
    (h2 : U ℓ (Ψ ℓ (Dz ^ δ ℓ) * fb) = C mu * fb) (hc : c ≠ 0) (hl : lam ≠ 0) (hm : mu ≠ 0)
    (hf : fb ≠ 0) (b : ℕ) (hb : 1 ≤ b) : Ψ ℓ (L ℓ b) ≠ 0 := by
  have H := L_mod ℓ fb c lam mu h24 h0 h1 h2
  have hC : ∀ x : ZMod ℓ, x ≠ 0 → C x * fb ≠ 0 := fun x hx =>
    mul_ne_zero (fun h => hx (by simpa using congrArg PowerSeries.constantCoeff h)) hf
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' b
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, (H j).2]
    exact hC _ (mul_ne_zero (mul_ne_zero hc hl) (pow_ne_zero _ (mul_ne_zero hl hm)))
  · rw [(H k).1]
    exact hC _ (mul_ne_zero hc (pow_ne_zero _ (mul_ne_zero hl hm)))

end ModEll

/-- `x ≡ 0 (mod ℓ)` coefficientwise iff `x = ℓ • y` in `ℤ⟦q⟧`. -/
theorem Ψ_eq_zero_iff (x : PowerSeries ℤ) : Ψ ℓ x = 0 ↔ AtkinOBrien.Dvd (ℓ : ℤ) 1 x := by
  constructor
  · intro h
    refine ⟨PowerSeries.mk fun n => coeff n x / ℓ, ?_⟩
    ext n
    have hn : ((coeff n x : ℤ) : ZMod ℓ) = 0 := by
      have := congrArg (coeff n) h
      rwa [PowerSeries.coeff_map, map_zero] at this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hn
    rw [pow_one, zsmul_eq_mul, ← map_intCast (PowerSeries.C (R := ℤ)), PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mk, Int.cast_id, Int.mul_ediv_cancel' hn]
  · rintro ⟨y, rfl⟩
    ext n
    rw [pow_one, PowerSeries.coeff_map, zsmul_eq_mul, ← map_intCast (PowerSeries.C (R := ℤ)),
      PowerSeries.coeff_C_mul, map_zero]
    simp

/-! ## `L(b)` and the partition function -/

/-- `p(n)` for `n ∈ ℤ`, with `p(n) = 0` for `n < 0`. -/
noncomputable def pZ (n : ℤ) : ℤ := if n < 0 then 0 else coeff n.toNat partitionGF

/-- `e_k = (ℓ^{2k} − 1)/24`. -/
def ek (k : ℕ) : ℤ := ((ℓ : ℤ) ^ (2 * k) - 1) / 24

/-- `e_b = (ℓ^{2⌈b/2⌉} − 1)/24`, so that `(ℓ^b n + 1)/24 = ℓ^b m − e_b` for the relevant `n`. -/
def eB (b : ℕ) : ℤ := ek ℓ ((b + 1) / 2)

/-- `P(b) = Σ_m p(ℓ^b m − e_b) qᵐ`. -/
noncomputable def Pser (b : ℕ) : PowerSeries ℤ := PowerSeries.mk fun m => pZ ((ℓ : ℤ) ^ b * m - eB ℓ b)

lemma Ea_sq (f : PowerSeries ℤ) : Ea (ℓ ^ 2) (TauCong.ppow_ne ℓ 2) f = Ea ℓ (hℓ0 ℓ) (Ea ℓ (hℓ0 ℓ) f) := by
  have hpos : 0 < ℓ := Nat.pos_of_ne_zero (hℓ0 ℓ)
  ext n
  rw [coeff_Ea, coeff_Ea]
  by_cases h1 : ℓ ∣ n
  · rw [if_pos h1, coeff_Ea]
    obtain ⟨a, rfl⟩ := h1
    rw [Nat.mul_div_cancel_left _ hpos]
    by_cases h2 : ℓ ∣ a
    · obtain ⟨b, rfl⟩ := h2
      rw [if_pos (dvd_mul_right _ _), show ℓ * (ℓ * b) = ℓ ^ 2 * b by ring,
        if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (pow_pos hpos 2),
        Nat.mul_div_cancel_left _ hpos]
    · rw [if_neg h2, if_neg]
      intro h; apply h2; rw [sq] at h; exact (Nat.mul_dvd_mul_iff_left hpos).mp h
  · rw [if_neg h1, if_neg (fun h => h1 (dvd_trans (dvd_pow_self ℓ two_ne_zero) h))]

lemma ek_mul (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (k : ℕ) : 24 * ek ℓ k = (ℓ : ℤ) ^ (2 * k) - 1 := by
  have hd : (24 : ℤ) ∣ (ℓ : ℤ) ^ (2 * k) - 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h24' : ((ℓ : ℤ) ^ 2 - 1) = 24 * (δ ℓ : ℤ) := by
        have : ((24 * δ ℓ + 1 : ℕ) : ℤ) = ((ℓ ^ 2 : ℕ) : ℤ) := by rw [h24]
        push_cast at this; linarith
      obtain ⟨t, ht⟩ := ih
      refine ⟨(ℓ : ℤ) ^ 2 * t + δ ℓ, ?_⟩
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
      linear_combination (ℓ : ℤ) ^ 2 * ht + h24'
  rw [ek, Int.mul_ediv_cancel' hd]

lemma ek_nonneg (k : ℕ) : 0 ≤ ek ℓ k := by
  rw [ek]
  apply Int.ediv_nonneg _ (by norm_num)
  have : (1 : ℤ) ≤ (ℓ : ℤ) ^ (2 * k) := one_le_pow₀ (by exact_mod_cast (Nat.pos_of_ne_zero (hℓ0 ℓ)))
  linarith

lemma ek_succ (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (k : ℕ) :
    ek ℓ (k + 1) = (ℓ : ℤ) ^ (2 * k) * δ ℓ + ek ℓ k := by
  have h1 := ek_mul ℓ h24 (k + 1)
  have h2 := ek_mul ℓ h24 k
  have h24' : ((ℓ : ℤ) ^ 2 - 1) = 24 * (δ ℓ : ℤ) := by
    have : ((24 * δ ℓ + 1 : ℕ) : ℤ) = ((ℓ ^ 2 : ℕ) : ℤ) := by rw [h24]
    push_cast at this; linarith
  rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add] at h1
  have : (24 : ℤ) * ek ℓ (k + 1) = 24 * ((ℓ : ℤ) ^ (2 * k) * δ ℓ + ek ℓ k) := by
    rw [h1, mul_add, h2]; linear_combination (ℓ : ℤ) ^ (2 * k) * h24'
  exact mul_left_cancel₀ (by norm_num) this

lemma pZ_neg {n : ℤ} (h : n < 0) : pZ n = 0 := by rw [pZ, if_pos h]

/-- **`L(b)` in terms of the partition function.** -/
theorem L_eq_partition (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (b : ℕ) :
    L ℓ (2 * b) = qfacInf * Pser ℓ (2 * b) ∧
      L ℓ (2 * b + 1) = Ea ℓ (hℓ0 ℓ) qfacInf * Pser ℓ (2 * b + 1) := by
  have heB0 : ∀ k, eB ℓ (2 * k) = ek ℓ k := fun k => by rw [eB]; congr 1; omega
  have heB1 : ∀ k, eB ℓ (2 * k + 1) = ek ℓ (k + 1) := fun k => by rw [eB]; congr 1; omega
  have hodd : ∀ k, L ℓ (2 * k) = qfacInf * Pser ℓ (2 * k) →
      L ℓ (2 * k + 1) = Ea ℓ (hℓ0 ℓ) qfacInf * Pser ℓ (2 * k + 1) := by
    intro k hk
    rw [L_succ, T, if_pos (even_2b k), hk, Φ, Ea_sq,
      show X ^ δ ℓ * Ea ℓ (hℓ0 ℓ) (Ea ℓ (hℓ0 ℓ) qfacInf) * partitionGF * (qfacInf * Pser ℓ (2 * k)) =
        Ea ℓ (hℓ0 ℓ) (Ea ℓ (hℓ0 ℓ) qfacInf) * (X ^ δ ℓ * Pser ℓ (2 * k)) * (qfacInf * partitionGF) by ring,
      qfac_mul_pgf, mul_one, U_Ea_mul]
    congr 1
    ext m
    rw [coeff_U, coeff_X_pow_mul', Pser, Pser, coeff_mk, heB1, ek_succ ℓ h24]
    split_ifs with hm
    · rw [coeff_mk, heB0, Nat.cast_sub hm]; push_cast; congr 1; ring
    · rw [coeff_mk, pZ_neg]
      have h1 : (ℓ : ℤ) * m < δ ℓ := by exact_mod_cast (not_le.mp hm)
      have h2 : (0 : ℤ) < (ℓ : ℤ) ^ (2 * k) := pow_pos (by exact_mod_cast (Nat.pos_of_ne_zero (hℓ0 ℓ))) _
      have h3 := ek_nonneg ℓ k
      have : (ℓ : ℤ) ^ (2 * k + 1) * m = (ℓ : ℤ) ^ (2 * k) * (ℓ * m) := by ring
      rw [this]
      nlinarith
  induction b with
  | zero =>
    have h0 : L ℓ (2 * 0) = qfacInf * Pser ℓ (2 * 0) := by
      rw [show L ℓ (2 * 0) = 1 from rfl, ← qfac_mul_pgf]
      congr 1
      ext m
      rw [Pser, coeff_mk, heB0, ek, pZ]
      simp
    exact ⟨h0, hodd 0 h0⟩
  | succ b ih =>
    have h0 : L ℓ (2 * (b + 1)) = qfacInf * Pser ℓ (2 * (b + 1)) := by
      rw [show 2 * (b + 1) = 2 * b + 1 + 1 by ring, L_succ, T, if_neg (not_even_2b1 b), ih.2, U_Ea_mul]
      congr 1
      ext m
      rw [coeff_U, Pser, Pser, coeff_mk, coeff_mk, heB1,
        show 2 * b + 1 + 1 = 2 * (b + 1) by ring, heB0]
      push_cast; congr 1; ring
    exact ⟨h0, hodd (b + 1) h0⟩

end BoylanWebb
