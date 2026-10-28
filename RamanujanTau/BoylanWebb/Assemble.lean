import RamanujanTau.BoylanWebb.Compute

/-!
# Assembly: from finite list certificates to the mod-`ℓ` Boylan–Webb structure

`assemble`: for a prime `13 ≤ ℓ ≤ 23` and an integral cusp form `f` of weight `ℓ − 1`, three finite
checks on truncated lists (`chk0`, `chk1`, `chk2`, up to the Sturm bounds `δ`, `1`, `δ + 1`) give the
three q-series congruences
  `U(Δ^δ) ≡ c f`,   `U f ≡ λ f`,   `U(Δ^δ f) ≡ μ f   (mod ℓ)`.
They hold for all coefficients, by Sturm's bound (`U_eq_of_sturm`); `Δ^δ`, `f` and `Δ^δ f` are
compared with `c f A^{(ℓ−1)/2}`, `λ f` and `μ f A^{(ℓ+1)/2}`, where `A ≡ 1` is the Hasse lift.

`boylan_webb_mod`: the consequences for `L_ℓ(b)`, `b ≥ 1`:
* `L(b) ≡ x_b f (mod ℓ)` with `x_b ≠ 0` (rank one mod `ℓ`);
* `L(b+2) ≡ κ L(b) (mod ℓ)` with `κ = λμ`, as `AtkinOBrien.Dvd`;
* `L(b) ≢ 0 (mod ℓ)`;
* `p(ℓ^{b+2} m − e_{b+2}) ≡ κ p(ℓ^b m − e_b) (mod ℓ)` for all `m`.
-/

set_option autoImplicit false

namespace BoylanWebb
open PowerSeries RamanujanTau MockTheta5.JTP
open RankProof (Ea)

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

lemma coeff_of_chk {d : ℕ} {F G : PowerSeries ℤ} {L1 L2 : List ℤ} (h1 : Cg ℓ d F (toPS L1))
    (h2 : Cg ℓ d G (toPS L2)) (c : ℤ) (N : ℕ) (hN : ℓ * N ≤ d)
    (chk : ∀ n, n < N + 1 → (coeffList L1 (ℓ * n) - c * coeffList L2 n) % (ℓ : ℤ) = 0)
    (n : ℕ) (hn : n ≤ N) : coeff (ℓ * n) (Ψ ℓ F) = (c : ZMod ℓ) * coeff n (Ψ ℓ G) := by
  have hl : 0 < ℓ := hℓ.out.pos
  have hℓn : ℓ * n ≤ d := le_trans (Nat.mul_le_mul_left ℓ hn) hN
  have hnd : n ≤ d := le_trans (Nat.le_mul_of_pos_left n hl) hℓn
  rw [Cg_coeff h1 hℓn, Cg_coeff h2 hnd]
  have h := Int.dvd_of_emod_eq_zero (chk n (by omega))
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_mul, sub_eq_zero] at h
  exact h

lemma coeff_zero_Dz_pow {k : ℕ} (hk : 1 ≤ k) (g : PowerSeries ℤ) : coeff 0 (Dz ^ k * g) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ, Dz, mul_comm _ (X * _), mul_assoc, mul_assoc, coeff_zero_eq_constantCoeff, map_mul,
    constantCoeff_X, zero_mul]

theorem assemble (hℓ5 : 5 ≤ ℓ) (hδ1 : 1 ≤ δ ℓ)
    (hk0 : ((12 * δ ℓ - 1 + 1 : ℕ) : ℤ) = ((δ ℓ : ℕ) : ℤ) * 12)
    (hb0 : ((ℓ - 1 : ℕ) : ℤ) + (((ℓ - 1) / 2 : ℕ) : ℤ) * ((ℓ - 1 : ℕ) : ℤ) = ((12 * δ ℓ - 1 + 1 : ℕ) : ℤ))
    (hk1 : ((ℓ - 1 : ℕ) : ℤ) = ((ℓ - 2 + 1 : ℕ) : ℤ))
    (hk2 : ((δ ℓ : ℕ) : ℤ) * 12 + ((ℓ - 1 : ℕ) : ℤ) = ((12 * δ ℓ + (ℓ - 1) - 1 + 1 : ℕ) : ℤ))
    (hb2 : ((ℓ - 1 : ℕ) : ℤ) + (((ℓ + 1) / 2 : ℕ) : ℤ) * ((ℓ - 1 : ℕ) : ℤ) =
      ((12 * δ ℓ + (ℓ - 1) - 1 + 1 : ℕ) : ℤ))
    (hS0 : (12 * δ ℓ - 1 + 1) / 12 = δ ℓ) (hS1 : (ℓ - 2 + 1) / 12 = 1)
    (hS2 : (12 * δ ℓ + (ℓ - 1) - 1 + 1) / 12 = δ ℓ + 1)
    (he0 : 1 ≤ 12 * δ ℓ - 1) (he1 : 1 ≤ ℓ - 2) (he2 : 1 ≤ 12 * δ ℓ + (ℓ - 1) - 1)
    (f : PowerSeries ℤ) (hf : IntForm ((ℓ - 1 : ℕ) : ℤ) f) (hf0 : coeff 0 f = 0)
    (d : ℕ) (hd : ℓ * (δ ℓ + 1) ≤ d) (hd0 : ℓ * δ ℓ ≤ d) (hd1 : ℓ * 1 ≤ d)
    (LD LF LDF : List ℤ) (cgD : Cg ℓ d (Dz ^ δ ℓ) (toPS LD)) (cgF : Cg ℓ d f (toPS LF))
    (cgDF : Cg ℓ d (Dz ^ δ ℓ * f) (toPS LDF)) (c lam mu : ℤ)
    (chk0 : ∀ n, n < δ ℓ + 1 → (coeffList LD (ℓ * n) - c * coeffList LF n) % (ℓ : ℤ) = 0)
    (chk1 : ∀ n, n < 1 + 1 → (coeffList LF (ℓ * n) - lam * coeffList LF n) % (ℓ : ℤ) = 0)
    (chk2 : ∀ n, n < δ ℓ + 1 + 1 → (coeffList LDF (ℓ * n) - mu * coeffList LF n) % (ℓ : ℤ) = 0) :
    U ℓ (Ψ ℓ (Dz ^ δ ℓ)) = C (c : ZMod ℓ) * Ψ ℓ f ∧ U ℓ (Ψ ℓ f) = C (lam : ZMod ℓ) * Ψ ℓ f ∧
      U ℓ (Ψ ℓ (Dz ^ δ ℓ) * Ψ ℓ f) = C (mu : ZMod ℓ) * Ψ ℓ f := by
  obtain ⟨A, hA, hAe⟩ := exists_hasse_lift ℓ hℓ5
  have hΨb : ∀ (x : ℤ) (m : ℕ), Ψ ℓ (PowerSeries.C x * (f * A ^ m)) = PowerSeries.C (x : ZMod ℓ) * Ψ ℓ f := by
    intro x m
    rw [map_mul, map_mul, map_pow, hAe, one_pow, mul_one, PowerSeries.map_C]; rfl
  have hΨl : Ψ ℓ (PowerSeries.C lam * f) = PowerSeries.C (lam : ZMod ℓ) * Ψ ℓ f := by
    rw [map_mul, PowerSeries.map_C]; rfl
  have hDz : IntForm (((δ ℓ : ℕ) : ℤ) * 12) (Dz ^ δ ℓ) := IntForm.disc.pow _
  refine ⟨?_, ?_, ?_⟩
  · -- `U(Δ^δ) ≡ c f`
    have e0 := U_eq_of_sturm ℓ (12 * δ ℓ - 1) he0 (Dz ^ δ ℓ)
      (PowerSeries.C c * (f * A ^ ((ℓ - 1) / 2)))
      (hDz.cast hk0.symm)
      (by simpa using coeff_zero_Dz_pow hδ1 1)
      (((hf.mul (hA.pow _)).C_mul c).cast hb0)
      (fun n hn => by
        rw [hΨb, PowerSeries.coeff_C_mul]
        exact coeff_of_chk ℓ cgD cgF c (δ ℓ) hd0 chk0 n (by rw [hS0] at hn; exact hn))
    rw [e0, hΨb]
  · -- `U f ≡ λ f`
    have e1 := U_eq_of_sturm ℓ (ℓ - 2) he1 f (PowerSeries.C lam * f)
      (hf.cast hk1) hf0 ((hf.C_mul lam).cast hk1)
      (fun n hn => by
        rw [hΨl, PowerSeries.coeff_C_mul]
        exact coeff_of_chk ℓ cgF cgF lam 1 hd1 chk1 n (by rw [hS1] at hn; exact hn))
    rw [e1, hΨl]
  · -- `U(Δ^δ f) ≡ μ f`
    have e2 := U_eq_of_sturm ℓ (12 * δ ℓ + (ℓ - 1) - 1) he2 (Dz ^ δ ℓ * f)
      (PowerSeries.C mu * (f * A ^ ((ℓ + 1) / 2)))
      ((hDz.mul hf).cast hk2)
      (coeff_zero_Dz_pow hδ1 f)
      (((hf.mul (hA.pow _)).C_mul mu).cast hb2)
      (fun n hn => by
        rw [hΨb, PowerSeries.coeff_C_mul]
        exact coeff_of_chk ℓ cgDF cgF mu (δ ℓ + 1) hd chk2 n (by rw [hS2] at hn; exact hn))
    rw [← map_mul, e2, hΨb]

lemma Dvd_adjust (x y : PowerSeries ℤ) (a a' : ℤ) (h : AtkinOBrien.Dvd (ℓ : ℤ) 1 (x - a • y))
    (ha : (ℓ : ℤ) ∣ a - a') : AtkinOBrien.Dvd (ℓ : ℤ) 1 (x - a' • y) := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨t, ht⟩ := ha
  refine ⟨z + t • y, ?_⟩
  rw [pow_one] at hz ⊢
  rw [smul_add, ← hz, smul_smul, ← ht, sub_smul]; abel

/-- the partition-function form of a two-step congruence. -/
theorem partition_of_two_step (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (κ : ZMod ℓ)
    (h : ∀ b, 1 ≤ b → Ψ ℓ (L ℓ (b + 2)) = C κ * Ψ ℓ (L ℓ b)) (b : ℕ) (hb : 1 ≤ b) (m : ℕ) :
    ((pZ ((ℓ : ℤ) ^ (b + 2) * m - eB ℓ (b + 2)) : ℤ) : ZMod ℓ) =
      κ * ((pZ ((ℓ : ℤ) ^ b * m - eB ℓ b) : ℤ) : ZMod ℓ) := by
  have key : ∀ E : PowerSeries ℤ, IsUnit E → L ℓ (b + 2) = E * Pser ℓ (b + 2) → L ℓ b = E * Pser ℓ b →
      ((pZ ((ℓ : ℤ) ^ (b + 2) * m - eB ℓ (b + 2)) : ℤ) : ZMod ℓ) =
        κ * ((pZ ((ℓ : ℤ) ^ b * m - eB ℓ b) : ℤ) : ZMod ℓ) := by
    intro E hE h1 h2
    have hb2 := h b hb
    rw [h1, h2, map_mul, map_mul, mul_left_comm] at hb2
    have := congrArg (coeff m) ((hE.map (Ψ ℓ)).mul_left_cancel hb2)
    rwa [coeff_C_mul, coeff_map, coeff_map, Pser, Pser, coeff_mk, coeff_mk] at this
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' b
  · refine key qfacInf isUnit_qfacInf ?_ (L_eq_partition ℓ h24 k).1
    rw [show 2 * k + 2 = 2 * (k + 1) by ring]; exact (L_eq_partition ℓ h24 (k + 1)).1
  · refine key _ (isUnit_qfacInf.map (Ea ℓ (hℓ0 ℓ))) ?_ (L_eq_partition ℓ h24 k).2
    rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring]; exact (L_eq_partition ℓ h24 (k + 1)).2

/-- **The mod-`ℓ` Boylan–Webb structure, from three eigen-congruences.** -/
theorem boylan_webb_mod (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (f : PowerSeries ℤ) (c lam mu : ℤ)
    (h0 : U ℓ (Ψ ℓ (Dz ^ δ ℓ)) = C (c : ZMod ℓ) * Ψ ℓ f) (h1 : U ℓ (Ψ ℓ f) = C (lam : ZMod ℓ) * Ψ ℓ f)
    (h2 : U ℓ (Ψ ℓ (Dz ^ δ ℓ) * Ψ ℓ f) = C (mu : ZMod ℓ) * Ψ ℓ f)
    (hc : (c : ZMod ℓ) ≠ 0) (hl : (lam : ZMod ℓ) ≠ 0) (hm : (mu : ZMod ℓ) ≠ 0) (hf : Ψ ℓ f ≠ 0) :
    (∀ b, 1 ≤ b → ∃ x : ZMod ℓ, x ≠ 0 ∧ Ψ ℓ (L ℓ b) = C x * Ψ ℓ f) ∧
    (∀ b, 1 ≤ b → AtkinOBrien.Dvd (ℓ : ℤ) 1 (L ℓ (b + 2) - (lam * mu) • L ℓ b)) ∧
    (∀ b, 1 ≤ b → ¬ AtkinOBrien.Dvd (ℓ : ℤ) 1 (L ℓ b)) ∧
    (∀ b, 1 ≤ b → ∀ m : ℕ, ((pZ ((ℓ : ℤ) ^ (b + 2) * m - eB ℓ (b + 2)) : ℤ) : ZMod ℓ) =
      ((lam * mu : ℤ) : ZMod ℓ) * ((pZ ((ℓ : ℤ) ^ b * m - eB ℓ b) : ℤ) : ZMod ℓ)) := by
  have H := L_mod ℓ (Ψ ℓ f) _ _ _ h24 h0 h1 h2
  have h2s := L_two_step ℓ (Ψ ℓ f) _ _ _ h24 h0 h1 h2
  have hnz := L_ne_zero ℓ (Ψ ℓ f) _ _ _ h24 h0 h1 h2 hc hl hm hf
  have hlm : ((lam * mu : ℤ) : ZMod ℓ) = (lam : ZMod ℓ) * (mu : ZMod ℓ) := by push_cast; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' b
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      refine ⟨_, ?_, by rw [show 2 * (j + 1) = 2 * j + 2 by ring]; exact (H j).2⟩
      exact mul_ne_zero (mul_ne_zero hc hl) (pow_ne_zero _ (mul_ne_zero hl hm))
    · exact ⟨_, mul_ne_zero hc (pow_ne_zero _ (mul_ne_zero hl hm)), (H k).1⟩
  · intro b hb
    rw [← Ψ_eq_zero_iff, map_sub, map_zsmul, h2s b hb, zsmul_eq_mul,
      ← map_intCast (PowerSeries.C (R := ZMod ℓ)) (lam * mu), hlm, sub_self]
  · intro b hb h
    exact hnz b hb ((Ψ_eq_zero_iff ℓ _).mpr h)
  · intro b hb m
    refine partition_of_two_step ℓ h24 _ (fun b hb => ?_) b hb m
    rw [h2s b hb, hlm]

end BoylanWebb

namespace BoylanWebb
open PowerSeries

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- **Classical form.** From the `pZ(ℓ^b m − e_b)` form: for every `n` with `24 ∣ ℓ^b n + 1`,
`p((ℓ^{b+2}n + 1)/24) ≡ κ · p((ℓ^b n + 1)/24) (mod ℓ)`. -/
theorem classical_of (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (κ : ZMod ℓ)
    (hP : ∀ b, 1 ≤ b → ∀ m : ℕ, ((pZ ((ℓ : ℤ) ^ (b + 2) * m - eB ℓ (b + 2)) : ℤ) : ZMod ℓ) =
      κ * ((pZ ((ℓ : ℤ) ^ b * m - eB ℓ b) : ℤ) : ZMod ℓ))
    (b : ℕ) (hb : 1 ≤ b) (n : ℕ) (hn : (24 : ℤ) ∣ (ℓ : ℤ) ^ b * n + 1) :
    ((pZ (((ℓ : ℤ) ^ (b + 2) * n + 1) / 24) : ℤ) : ZMod ℓ) =
      κ * ((pZ (((ℓ : ℤ) ^ b * n + 1) / 24) : ℤ) : ZMod ℓ) := by
  set k := (b + 1) / 2 with hk
  have hkb : b ≤ 2 * k := by omega
  set r : ℤ := (ℓ : ℤ) ^ (2 * k - b) with hr
  have hlr : (ℓ : ℤ) ^ b * r = (ℓ : ℤ) ^ (2 * k) := by rw [hr, ← pow_add]; congr 1; omega
  have hr0 : 0 ≤ r := by positivity
  have he := ek_mul ℓ h24 k
  have he' := ek_mul ℓ h24 (k + 1)
  -- `24 ∣ n + r`
  have hdiv : (24 : ℤ) ∣ n + r := by
    obtain ⟨u, hu⟩ := hn
    refine ⟨r * u - ek ℓ k * n, ?_⟩
    linear_combination r * hu + (n : ℤ) * he - (n : ℤ) * hlr
  obtain ⟨t, ht⟩ := hdiv
  have ht0 : 0 ≤ t := by
    have : (0 : ℤ) ≤ n + r := by positivity
    omega
  lift t to ℕ using ht0
  have h1 : ((ℓ : ℤ) ^ b * n + 1) / 24 = (ℓ : ℤ) ^ b * t - eB ℓ b := by
    rw [eB, ← hk]
    have : (ℓ : ℤ) ^ b * n + 1 = 24 * ((ℓ : ℤ) ^ b * t - ek ℓ k) := by
      linear_combination (ℓ : ℤ) ^ b * ht + he - hlr
    rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
  have h2 : ((ℓ : ℤ) ^ (b + 2) * n + 1) / 24 = (ℓ : ℤ) ^ (b + 2) * t - eB ℓ (b + 2) := by
    rw [eB, show (b + 2 + 1) / 2 = k + 1 by omega]
    have hlr' : (ℓ : ℤ) ^ (b + 2) * r = (ℓ : ℤ) ^ (2 * (k + 1)) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, pow_add, ← hlr]; ring
    have : (ℓ : ℤ) ^ (b + 2) * n + 1 = 24 * ((ℓ : ℤ) ^ (b + 2) * t - ek ℓ (k + 1)) := by
      linear_combination (ℓ : ℤ) ^ (b + 2) * ht + he' - hlr'
    rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
  rw [h1, h2]
  exact hP b hb t

lemma pZ_natCast (N : ℕ) : pZ (N : ℤ) = (Fintype.card (Nat.Partition N) : ℤ) := by
  rw [pZ, if_neg (by omega), Int.toNat_natCast, MockTheta5.JTP.coeff_partitionGF_eq_card]

/-- **Partition-count form**: for `24 ∣ ℓ^b n + 1`,
`#Partitions((ℓ^{b+2}n+1)/24) ≡ κ · #Partitions((ℓ^b n+1)/24) (mod ℓ)`. -/
theorem count_of (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (κ : ZMod ℓ)
    (hP : ∀ b, 1 ≤ b → ∀ m : ℕ, ((pZ ((ℓ : ℤ) ^ (b + 2) * m - eB ℓ (b + 2)) : ℤ) : ZMod ℓ) =
      κ * ((pZ ((ℓ : ℤ) ^ b * m - eB ℓ b) : ℤ) : ZMod ℓ))
    (b : ℕ) (hb : 1 ≤ b) (n : ℕ) (hn : 24 ∣ ℓ ^ b * n + 1) :
    (Fintype.card (Nat.Partition ((ℓ ^ (b + 2) * n + 1) / 24)) : ZMod ℓ) =
      κ * (Fintype.card (Nat.Partition ((ℓ ^ b * n + 1) / 24)) : ZMod ℓ) := by
  have h := classical_of ℓ h24 κ hP b hb n (by exact_mod_cast hn)
  have e1 : ((ℓ : ℤ) ^ (b + 2) * n + 1) / 24 = (((ℓ ^ (b + 2) * n + 1) / 24 : ℕ) : ℤ) := by push_cast; rfl
  have e2 : ((ℓ : ℤ) ^ b * n + 1) / 24 = (((ℓ ^ b * n + 1) / 24 : ℕ) : ℤ) := by push_cast; rfl
  rw [e1, e2, pZ_natCast, pZ_natCast] at h
  exact_mod_cast h

end BoylanWebb
