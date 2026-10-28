import RamanujanTau.AtkinOBrienFinal.Transfer
import RamanujanTau.AtkinOBrienFinal.Lead
import RamanujanTau.BoylanWebb.InductionSeq
import RamanujanTau.BoylanWebb.Main

/-!
# `b_ℓ(m) = m` for `ℓ ∈ {13, 17, 19, 23}`, from the matrix bounds (UB), (DB)

The module is `M = ℤ_ℓ⟦q⟧`, with
* `T b = D = U∘(Φ·)` for `b` even and `T b = U` for `b` odd (`Tl`),
* `L b` = Boylan–Webb's `L_ℓ(b)` in `ℤ_ℓ⟦q⟧` (`Ll`),
* `A_c b` = the cuspidal envelope `A_c(γ_b)` (`γ_b = α` for even `b`, `β` for odd `b`) of Katz expansions
  with respect to `E_{ℓ−1}` and the monomial complement `Igusa.S` (`Katz.lean`).

`BoylanWebb.induction_padic`'s hypotheses are discharged as follows:
* `hreg`, `hTper`, `hLT`, `hA₁per`: direct;
* `hL`: induction from `L 0 = 1` with `U_env`/`D_env` at offset 1, and `BoylanWebb.L_cuspidal`;
* `hT`: `U_env`/`D_env` at offset 2, i.e. (UB)/(DB) + `AtkinOBrien.U_step`/`D_step`;
* `hdiv`: `env_div` (Katz uniqueness mod `ℓ`, `Igusa.katz_independent_S`);
* `hlead`: `lead` (Sturm, `dim S_{ℓ−1} = 1`) + `CertX.rank_one` + `AtkinOBrien.envelopes_ge_two`;
* `hbase`: `CertX.two_step` (Boylan–Webb `b_ℓ(1) = 1`).

The resulting `ℓ^b ∣ L(b+2) − κ L(b)` is turned into partition numbers via `BoylanWebb.L_eq_partition`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AtkinOBrienFinal
open PowerSeries AtkinOBrien BoylanWebb

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- the alternating operators on `ℤ_ℓ⟦q⟧`. -/
noncomputable def Tl (ℓ : ℕ) [Fact ℓ.Prime] (b : ℕ) : PS ℓ →ₗ[ℤ_[ℓ]] PS ℓ :=
  if Even b then Dlin ℓ else Ulin ℓ

/-- `L_ℓ(b) ∈ ℤ_ℓ⟦q⟧`. -/
noncomputable def Ll (ℓ : ℕ) [Fact ℓ.Prime] (b : ℕ) : PS ℓ :=
  PowerSeries.map (Int.castRingHom ℤ_[ℓ]) (BoylanWebb.L ℓ b)

/-- envelope exponents: `α` at even, `β` at odd steps. -/
noncomputable def γ (ℓ : ℕ) (b : ℕ) : ℕ → ℤ := if Even b then α ℓ else β ℓ

lemma Tl_add_two (b : ℕ) : Tl ℓ (b + 2) = Tl ℓ b := by
  unfold Tl
  rcases Nat.even_or_odd b with h | h
  · rw [if_pos h, if_pos (h.add even_two)]
  · rw [if_neg (Nat.not_even_iff_odd.mpr h), if_neg (Nat.not_even_iff_odd.mpr (h.add_even even_two))]

lemma γ_add_two (b : ℕ) : γ ℓ (b + 2) = γ ℓ b := by
  unfold γ
  rcases Nat.even_or_odd b with h | h
  · rw [if_pos h, if_pos (h.add even_two)]
  · rw [if_neg (Nat.not_even_iff_odd.mpr h), if_neg (Nat.not_even_iff_odd.mpr (h.add_even even_two))]

lemma Ll_succ (b : ℕ) : Ll ℓ (b + 1) = Tl ℓ b (Ll ℓ b) := by
  unfold Ll Tl
  rw [L_succ, BoylanWebb.T]
  split_ifs
  · rw [Dlin_apply, map_U, map_mul]; rfl
  · rw [Ulin_apply, map_U]

lemma coeff_zero_Tl (b : ℕ) (f : PS ℓ) (hf : coeff 0 f = 0) : coeff 0 (Tl ℓ b f) = 0 := by
  unfold Tl
  split_ifs
  · rw [Dlin_apply, coeff_U, mul_zero, coeff_zero_eq_constantCoeff_apply, map_mul,
      ← coeff_zero_eq_constantCoeff_apply f, hf, mul_zero]
  · rw [Ulin_apply, coeff_U, mul_zero, hf]

lemma α_zero_le (hℓ : 5 ≤ ℓ) : α ℓ 0 ≤ 1 := by
  unfold α
  rw [Int.ceil_le]
  have : (0 : ℚ) < (ℓ : ℚ) + 1 := by positivity
  rw [div_le_iff₀ this]
  push_cast; linarith

lemma one_mem_S (hℓ : 5 ≤ ℓ) : (0 : Fin 2 →₀ ℕ) ∈ Igusa.S ℓ hℓ (0 * (ℓ - 1)) := by
  refine ⟨by simp, fun h => ?_⟩
  have := Igusa.dA_eA (p := ℓ) hℓ
  simp only [Finsupp.coe_zero, Pi.zero_apply, nonpos_iff_eq_zero] at h
  omega

/-- `1 ∈ A₁(α)` (without cusp condition): `1 = 1/E⁰`. -/
lemma env_one (hℓ : 5 ≤ ℓ) : Env ℓ hℓ 1 (α ℓ) 1 := by
  intro N
  refine ⟨1, fun i => if i = 0 then 1 else 0, fun i => ?_, ⟨0, ?_⟩, fun i => ?_⟩
  · dsimp only
    split_ifs with h
    · subst h
      rw [mem_Kpiece, MvPolynomial.support_one]
      intro s hs
      rw [Finset.coe_singleton, Set.mem_singleton_iff] at hs
      subst hs; exact one_mem_S hℓ
    · exact Submodule.zero_mem _
  · simp
  · dsimp only
    split_ifs with h
    · subst h
      have : (max 0 (α ℓ 0 - 1)).toNat = 0 := by have := α_zero_le hℓ; omega
      rw [this]; exact ⟨1, by rw [pow_zero, one_smul]⟩
    · exact Dvd_zero _

/-- one step of the envelope recursion, offset `c ≤ 2` to offset `1`. -/
lemma env_step (hℓ : 5 ≤ ℓ) (hℓ13 : 13 ≤ ℓ) (hUB : UB ℓ hℓ) (hDB : DB ℓ hℓ) (c : ℤ) (hc : c ≤ 2)
    (b : ℕ) (f : PS ℓ) (hf : Env ℓ hℓ c (γ ℓ b) f) : Env ℓ hℓ 1 (γ ℓ (b + 1)) (Tl ℓ b f) := by
  unfold γ Tl at *
  by_cases h : Even b
  · rw [if_pos h] at hf ⊢
    rw [if_neg (by rw [Nat.not_even_iff_odd]; exact h.add_one)]
    exact D_env hℓ hℓ13 hDB c hc f hf
  · rw [if_neg h] at hf ⊢
    rw [if_pos (by rw [Nat.not_even_iff_odd] at h; exact h.add_one)]
    exact U_env hℓ hℓ13 hUB c hc f hf

lemma map_zsmul_int (k : ℤ) (x : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom ℤ_[ℓ]) (k • x) = (k : ℤ_[ℓ]) • PowerSeries.map (Int.castRingHom ℤ_[ℓ]) x := by
  ext n
  rw [coeff_map, coeff_smul, coeff_map, map_zsmul, smul_eq_mul, eq_intCast, eq_intCast, smul_eq_mul,
    Int.cast_mul]

lemma map_dvd_int {m : ℕ} {x : PowerSeries ℤ} (h : AtkinOBrien.Dvd (ℓ : ℤ) m x) :
    AtkinOBrien.Dvd (ℓ : ℤ_[ℓ]) m (PowerSeries.map (Int.castRingHom ℤ_[ℓ]) x) := by
  obtain ⟨y, rfl⟩ := h
  refine ⟨PowerSeries.map (Int.castRingHom ℤ_[ℓ]) y, ?_⟩
  rw [map_zsmul_int]; push_cast; rfl

/-- **Step 3 on `ℤ_ℓ⟦q⟧`**: from (UB), (DB) and the Boylan–Webb inputs, `ℓ^b ∣ L(b+2) − κ L(b)`. -/
theorem L_padic (hℓ : 5 ≤ ℓ) (hℓ13 : 13 ≤ ℓ) (hℓ24 : ℓ ≤ 24) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (κ₀ : ℤ)
    (f : PowerSeries ℤ) (hf : IntForm ((ℓ - 1 : ℕ) : ℤ) f) (hf0 : coeff 0 f = 0)
    (hf1 : coeff 1 (Ψ ℓ f) ≠ 0)
    (hrank : ∀ b, 1 ≤ b → ∃ x : ZMod ℓ, x ≠ 0 ∧ Ψ ℓ (L ℓ b) = C x * Ψ ℓ f)
    (htwo : ∀ b, 1 ≤ b → AtkinOBrien.Dvd (ℓ : ℤ) 1 (L ℓ (b + 2) - κ₀ • L ℓ b))
    (hUB : UB ℓ hℓ) (hDB : DB ℓ hℓ) :
    ∃ κ : ℤ_[ℓ], (∃ d : ℤ_[ℓ], κ = (κ₀ : ℤ_[ℓ]) + ℓ * d) ∧
      ∀ b, 1 ≤ b → AtkinOBrien.Dvd (ℓ : ℤ_[ℓ]) b (Ll ℓ (b + 2) - κ • Ll ℓ b) := by
  have hLenv : ∀ b, Env ℓ hℓ 1 (γ ℓ b) (Ll ℓ b) := by
    intro b
    induction b with
    | zero =>
      have : γ ℓ 0 = α ℓ := by simp [γ]
      rw [this, show Ll ℓ 0 = 1 by simp [Ll, BoylanWebb.L]]
      exact env_one hℓ
    | succ b ih => rw [Ll_succ]; exact env_step hℓ hℓ13 hUB hDB 1 (by norm_num) b _ ih
  have hcusp : ∀ b, 1 ≤ b → coeff 0 (Ll ℓ b) = 0 := by
    intro b hb
    rw [Ll, coeff_map, L_cuspidal ℓ h24 hℓ b hb, map_zero]
  refine induction_padic ℓ (κ₀ : ℤ_[ℓ]) (Tl ℓ) (Ll ℓ) (fun b => envSub hℓ 1 (γ ℓ b))
    (fun b => envSub hℓ 2 (γ ℓ b)) PS_reg Tl_add_two Ll_succ
    (fun b => by simp only [γ_add_two]) (fun b hb => ⟨hcusp b hb, hLenv b⟩) ?hT ?hlead ?hdiv ?hbase
  case hT =>
    rintro b - x ⟨hx0, hx⟩
    exact ⟨coeff_zero_Tl b x hx0, env_step hℓ hℓ13 hUB hDB 2 le_rfl b x hx⟩
  case hlead =>
    intro b hb x hx
    obtain ⟨xb, hxb, hLb⟩ := hrank b hb
    refine lead hℓ hℓ13 hℓ24 f hf hf0 hf1 (Ll ℓ b) xb hxb (by rw [Ll, map_map_int, hLb]) (γ ℓ b)
      (fun i hi => ?_) x hx
    have := envelopes_ge_two hℓ13 i hi
    unfold γ; split_ifs
    · exact this.1
    · exact this.2
  case hdiv =>
    rintro b - x ⟨hx0, hx⟩ y rfl
    refine ⟨?_, by simpa using env_div hℓ 1 (γ ℓ b) hx rfl⟩
    rw [coeff_smul, smul_eq_mul] at hx0
    exact (mul_eq_zero.mp hx0).resolve_left ell_ne_zero
  case hbase =>
    intro β hβ
    have := map_dvd_int (ℓ := ℓ) (htwo β hβ)
    convert this using 1
    rw [map_sub, Ll, Ll, map_zsmul_int]

/-! ### From `L`-series to partition numbers -/

lemma L_factor (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (b : ℕ) :
    ∃ Q : PowerSeries ℤ, IsUnit Q ∧ L ℓ b = Q * Pser ℓ b ∧ L ℓ (b + 2) = Q * Pser ℓ (b + 2) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' b
  · refine ⟨_, MockTheta5.JTP.isUnit_qfacInf, (L_eq_partition ℓ h24 k).1, ?_⟩
    rw [show 2 * k + 2 = 2 * (k + 1) by ring]; exact (L_eq_partition ℓ h24 (k + 1)).1
  · refine ⟨_, MockTheta5.JTP.isUnit_qfacInf.map (RankProof.Ea ℓ (hℓ0 ℓ)), (L_eq_partition ℓ h24 k).2, ?_⟩
    rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring]; exact (L_eq_partition ℓ h24 (k + 1)).2

/-- `ℓ^b ∣ p(ℓ^{b+2}m − e_{b+2}) − κ p(ℓ^b m − e_b)` from the `L`-series congruence. -/
theorem pser_dvd (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (κ : ℤ_[ℓ]) (b : ℕ)
    (h : AtkinOBrien.Dvd (ℓ : ℤ_[ℓ]) b (Ll ℓ (b + 2) - κ • Ll ℓ b)) (m : ℕ) :
    (ℓ : ℤ_[ℓ]) ^ b ∣ ((pZ ((ℓ : ℤ) ^ (b + 2) * m - eB ℓ (b + 2)) : ℤ) : ℤ_[ℓ]) -
      κ * ((pZ ((ℓ : ℤ) ^ b * m - eB ℓ b) : ℤ) : ℤ_[ℓ]) := by
  obtain ⟨Q, hQ, h1, h2⟩ := L_factor h24 b
  obtain ⟨y, hy⟩ := h
  set φ := PowerSeries.map (Int.castRingHom ℤ_[ℓ])
  obtain ⟨u, hu⟩ := hQ.map φ
  have hL : ∀ c, Ll ℓ c = φ (L ℓ c) := fun c => rfl
  rw [hL, hL, h1, h2, map_mul, map_mul, ← hu] at hy
  have hy' : (u : PS ℓ) * (φ (Pser ℓ (b + 2)) - κ • φ (Pser ℓ b)) = (ℓ : ℤ_[ℓ]) ^ b • y := by
    rw [mul_sub, mul_smul_comm]; exact hy
  have hd : φ (Pser ℓ (b + 2)) - κ • φ (Pser ℓ b) = (ℓ : ℤ_[ℓ]) ^ b • (↑u⁻¹ * y) := by
    rw [← mul_smul_comm, ← hy', ← mul_assoc, Units.inv_mul, one_mul]
  have := congrArg (coeff m) hd
  rw [map_sub, coeff_smul, coeff_smul, coeff_map, coeff_map, Pser, Pser, coeff_mk, coeff_mk,
    smul_eq_mul, smul_eq_mul] at this
  exact ⟨_, by rw [eq_intCast, eq_intCast] at this; exact this⟩

/-- the index shift of `BoylanWebb.classical_of`. -/
lemma index_shift (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (b : ℕ) (n : ℕ) (hn : (24 : ℤ) ∣ (ℓ : ℤ) ^ b * n + 1) :
    ∃ t : ℕ, ((ℓ : ℤ) ^ b * n + 1) / 24 = (ℓ : ℤ) ^ b * t - eB ℓ b ∧
      ((ℓ : ℤ) ^ (b + 2) * n + 1) / 24 = (ℓ : ℤ) ^ (b + 2) * t - eB ℓ (b + 2) := by
  set k := (b + 1) / 2 with hk
  have hkb : b ≤ 2 * k := by omega
  set r : ℤ := (ℓ : ℤ) ^ (2 * k - b) with hr
  have hlr : (ℓ : ℤ) ^ b * r = (ℓ : ℤ) ^ (2 * k) := by rw [hr, ← pow_add]; congr 1; omega
  have hr0 : 0 ≤ r := by positivity
  have he := ek_mul ℓ h24 k
  have he' := ek_mul ℓ h24 (k + 1)
  have hdiv : (24 : ℤ) ∣ n + r := by
    obtain ⟨u, hu⟩ := hn
    refine ⟨r * u - ek ℓ k * n, ?_⟩
    linear_combination r * hu + (n : ℤ) * he - (n : ℤ) * hlr
  obtain ⟨t, ht⟩ := hdiv
  have ht0 : 0 ≤ t := by
    have : (0 : ℤ) ≤ n + r := by positivity
    omega
  lift t to ℕ using ht0
  refine ⟨t, ?_, ?_⟩
  · rw [eB, ← hk]
    have : (ℓ : ℤ) ^ b * n + 1 = 24 * ((ℓ : ℤ) ^ b * t - ek ℓ k) := by
      linear_combination (ℓ : ℤ) ^ b * ht + he - hlr
    rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
  · rw [eB, show (b + 2 + 1) / 2 = k + 1 by omega]
    have hlr' : (ℓ : ℤ) ^ (b + 2) * r = (ℓ : ℤ) ^ (2 * (k + 1)) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, pow_add, ← hlr]; ring
    have : (ℓ : ℤ) ^ (b + 2) * n + 1 = 24 * ((ℓ : ℤ) ^ (b + 2) * t - ek ℓ (k + 1)) := by
      linear_combination (ℓ : ℤ) ^ (b + 2) * ht + he' - hlr'
    rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]

/-- **Generic assembly.** For a prime `13 ≤ ℓ ≤ 24` with `24 ∣ ℓ² − 1`, the Boylan–Webb inputs mod `ℓ`
(`hrank`, `htwo`, and a normalized weight-`(ℓ−1)` cusp form `f`) together with (UB), (DB) give
`κ ∈ ℤ_ℓ`, `κ ≡ κ₀ (mod ℓ)`, with `p((ℓ^{m+2}n+1)/24) ≡ κ·p((ℓ^m n+1)/24) (mod ℓ^m)`. -/
theorem atkin_obrien_generic (hℓ : 5 ≤ ℓ) (hℓ13 : 13 ≤ ℓ) (hℓ24 : ℓ ≤ 24) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)
    (κ₀ : ℤ) (f : PowerSeries ℤ) (hf : IntForm ((ℓ - 1 : ℕ) : ℤ) f) (hf0 : coeff 0 f = 0)
    (hf1 : coeff 1 (Ψ ℓ f) ≠ 0)
    (hrank : ∀ b, 1 ≤ b → ∃ x : ZMod ℓ, x ≠ 0 ∧ Ψ ℓ (L ℓ b) = C x * Ψ ℓ f)
    (htwo : ∀ b, 1 ≤ b → AtkinOBrien.Dvd (ℓ : ℤ) 1 (L ℓ (b + 2) - κ₀ • L ℓ b))
    (hUB : UB ℓ hℓ) (hDB : DB ℓ hℓ) :
    ∃ κ : ℤ_[ℓ], (∃ d : ℤ_[ℓ], κ = (κ₀ : ℤ_[ℓ]) + ℓ * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ ℓ ^ m * n + 1 →
        (ℓ : ℤ_[ℓ]) ^ m ∣ (Fintype.card (Nat.Partition ((ℓ ^ (m + 2) * n + 1) / 24)) : ℤ_[ℓ]) -
          κ * (Fintype.card (Nat.Partition ((ℓ ^ m * n + 1) / 24)) : ℤ_[ℓ]) := by
  obtain ⟨κ, hκ, hL⟩ := L_padic hℓ hℓ13 hℓ24 h24 κ₀ f hf hf0 hf1 hrank htwo hUB hDB
  refine ⟨κ, hκ, fun m hm n hn => ?_⟩
  obtain ⟨t, h1, h2⟩ := index_shift h24 m n (by exact_mod_cast hn)
  have h := pser_dvd h24 κ m (hL m hm) t
  rw [← h1, ← h2] at h
  have e1 : ((ℓ : ℤ) ^ (m + 2) * n + 1) / 24 = (((ℓ ^ (m + 2) * n + 1) / 24 : ℕ) : ℤ) := by push_cast; rfl
  have e2 : ((ℓ : ℤ) ^ m * n + 1) / 24 = (((ℓ ^ m * n + 1) / 24 : ℕ) : ℤ) := by push_cast; rfl
  rw [e1, e2, pZ_natCast, pZ_natCast] at h
  exact_mod_cast h

/-! ### The four primes -/

lemma coeff_one_13 : coeff 1 (Ψ 13 Cert13.f) ≠ 0 := fun h => by
  have h1 := Cg_coeff Cert13.cg_f (n := 1) (by decide); rw [h] at h1; exact absurd h1 (by decide)
lemma coeff_one_17 : coeff 1 (Ψ 17 Cert17.f) ≠ 0 := fun h => by
  have h1 := Cg_coeff Cert17.cg_f (n := 1) (by decide); rw [h] at h1; exact absurd h1 (by decide)
lemma coeff_one_19 : coeff 1 (Ψ 19 Cert19.f) ≠ 0 := fun h => by
  have h1 := Cg_coeff Cert19.cg_f (n := 1) (by decide); rw [h] at h1; exact absurd h1 (by decide)
lemma coeff_one_23 : coeff 1 (Ψ 23 Cert23.f) ≠ 0 := fun h => by
  have h1 := Cg_coeff Cert23.cg_f (n := 1) (by decide); rw [h] at h1; exact absurd h1 (by decide)

/-- **`b_13(m) = m`** (Atkin–O'Brien), conditional on (UB), (DB) at `ℓ = 13`. -/
theorem atkin_obrien_13 (hUB : UB 13 (by norm_num)) (hDB : DB 13 (by norm_num)) :
    ∃ κ : ℤ_[13], (∃ d : ℤ_[13], κ = 6 + 13 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 13 ^ m * n + 1 →
        (13 : ℤ_[13]) ^ m ∣ (Fintype.card (Nat.Partition ((13 ^ (m + 2) * n + 1) / 24)) : ℤ_[13]) -
          κ * (Fintype.card (Nat.Partition ((13 ^ m * n + 1) / 24)) : ℤ_[13]) := by
  obtain ⟨κ, hκ, h⟩ := atkin_obrien_generic (ℓ := 13) (by norm_num) le_rfl (by norm_num) Cert13.h24 6
    Cert13.f Cert13.form_f Cert13.coeff_zero_f coeff_one_13 Cert13.rank_one Cert13.two_step hUB hDB
  exact ⟨κ, by simpa using hκ, by exact_mod_cast h⟩

/-- **`b_17(m) = m`**, conditional on (UB), (DB) at `ℓ = 17`. -/
theorem atkin_obrien_17 (hUB : UB 17 (by norm_num)) (hDB : DB 17 (by norm_num)) :
    ∃ κ : ℤ_[17], (∃ d : ℤ_[17], κ = 6 + 17 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 17 ^ m * n + 1 →
        (17 : ℤ_[17]) ^ m ∣ (Fintype.card (Nat.Partition ((17 ^ (m + 2) * n + 1) / 24)) : ℤ_[17]) -
          κ * (Fintype.card (Nat.Partition ((17 ^ m * n + 1) / 24)) : ℤ_[17]) := by
  obtain ⟨κ, hκ, h⟩ := atkin_obrien_generic (ℓ := 17) (by norm_num) (by norm_num) (by norm_num)
    Cert17.h24 6 Cert17.f Cert17.form_f Cert17.coeff_zero_f coeff_one_17 Cert17.rank_one Cert17.two_step
    hUB hDB
  exact ⟨κ, by simpa using hκ, by exact_mod_cast h⟩

/-- **`b_19(m) = m`**, conditional on (UB), (DB) at `ℓ = 19`. -/
theorem atkin_obrien_19 (hUB : UB 19 (by norm_num)) (hDB : DB 19 (by norm_num)) :
    ∃ κ : ℤ_[19], (∃ d : ℤ_[19], κ = 10 + 19 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 19 ^ m * n + 1 →
        (19 : ℤ_[19]) ^ m ∣ (Fintype.card (Nat.Partition ((19 ^ (m + 2) * n + 1) / 24)) : ℤ_[19]) -
          κ * (Fintype.card (Nat.Partition ((19 ^ m * n + 1) / 24)) : ℤ_[19]) := by
  obtain ⟨κ, hκ, h⟩ := atkin_obrien_generic (ℓ := 19) (by norm_num) (by norm_num) (by norm_num)
    Cert19.h24 10 Cert19.f Cert19.form_f Cert19.coeff_zero_f coeff_one_19 Cert19.rank_one Cert19.two_step
    hUB hDB
  exact ⟨κ, by simpa using hκ, by exact_mod_cast h⟩

/-- **`b_23(m) = m`**, conditional on (UB), (DB) at `ℓ = 23`. -/
theorem atkin_obrien_23 (hUB : UB 23 (by norm_num)) (hDB : DB 23 (by norm_num)) :
    ∃ κ : ℤ_[23], (∃ d : ℤ_[23], κ = 5 + 23 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 23 ^ m * n + 1 →
        (23 : ℤ_[23]) ^ m ∣ (Fintype.card (Nat.Partition ((23 ^ (m + 2) * n + 1) / 24)) : ℤ_[23]) -
          κ * (Fintype.card (Nat.Partition ((23 ^ m * n + 1) / 24)) : ℤ_[23]) := by
  obtain ⟨κ, hκ, h⟩ := atkin_obrien_generic (ℓ := 23) (by norm_num) (by norm_num) (by norm_num)
    Cert23.h24 5 Cert23.f Cert23.form_f Cert23.coeff_zero_f coeff_one_23 Cert23.rank_one Cert23.two_step
    hUB hDB
  exact ⟨κ, by simpa using hκ, by exact_mod_cast h⟩

end AtkinOBrienFinal
