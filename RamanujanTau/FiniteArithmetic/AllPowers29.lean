import RamanujanTau.FiniteArithmetic.Image29
import RamanujanTau.FiniteArithmetic.OrbitLift
import RamanujanTau.FiniteArithmetic.Partition29
import RamanujanTau.OrdQuot.Prod
import RamanujanTau.QuotE.Combine

/-! A single 29-adic partition recurrence, valid modulo every power of 29.
The odd image lies in the q² line modulo 29. Each full U,D cycle gains
one digit of precision. This module proves the all-power upper bound;
minimality of the starting index is a separate assertion. -/
set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic.AllPowers29
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal

theorem bounds : UB 29 (by norm_num) ∧ DB 29 (by norm_num) := by
  classical
  have hE := QuotE.quotEBound_C_of_ord (ℓ := 29) (by norm_num)
    (OrdQuot.ordEBound_C' (by norm_num))
  have hU := UBSharp.UB_of_E_C (by norm_num : 5 ≤ 29) hE
  have hQ := SharpHQ.HQ_of_conj_C (by norm_num : 5 ≤ 29) (by norm_num)
    (UBSharp.HConj_of_quot_C (by norm_num) (UBSharp.quotBound_of_E_C (by norm_num) hE))
  exact ⟨hU, VLayer.DB_of_UB_HQ (by norm_num) hU hQ⟩

lemma D_coeff_low (F : PS 29) (n : ℕ) (hn : n < 2) : coeff n (Dlin 29 F) = 0 := by
  rw [Dlin_apply, coeff_U, Φl, BoylanWebb.Φ]
  simp only [map_mul, map_pow, PowerSeries.map_X]
  rw [mul_assoc, mul_assoc, coeff_X_pow_mul', if_neg (by change ¬35 ≤ 29 * n; omega)]

noncomputable def B (c : ℤ) : Submodule ℤ_[29] (PS 29) :=
  envSub (by norm_num : 5 ≤ 29) c (β 29) ⊓ (coeff 1).ker

noncomputable def Xop : Module.End ℤ_[29] (PS 29) := (Dlin 29).comp (Ulin 29)

lemma X_mem (F : PS 29) (hF : F ∈ B 2) : Xop F ∈ B 1 := by
  refine ⟨⟨D_coeff_low _ 0 (by decide), ?_⟩, D_coeff_low _ 1 (by decide)⟩
  exact D_env (by norm_num) (by norm_num) bounds.2 1 (by norm_num) _
    (U_env (by norm_num) (by norm_num) bounds.1 2 le_rfl _ hF.1.2)

lemma B_div (F : PS 29) (hF : F ∈ B 1) (G : PS 29) (h : F = (29 : ℤ_[29]) • G) : G ∈ B 2 := by
  refine ⟨⟨?_, by simpa using env_div (by norm_num : 5 ≤ 29) 1 (β 29) hF.1.2 h⟩, ?_⟩
  · have hz := hF.1.1
    rw [h, coeff_smul, smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz : coeff 1 F = 0 := hF.2
    rw [h, coeff_smul, smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

lemma L_env (b : ℕ) : Env 29 (by norm_num) 1 (γ 29 b) (Ll 29 b) := by
  induction b with
  | zero =>
    rw [show γ 29 0 = α 29 by simp [γ], show Ll 29 0 = 1 by simp [Ll, L]]
    exact env_one (by norm_num)
  | succ b ih =>
    rw [Ll_succ]
    exact env_step (by norm_num) (by norm_num) bounds.1 bounds.2 1 (by norm_num) b _ ih

lemma odd_D (n : ℕ) : Ll 29 (2 * n + 1) = Dlin 29 (Ll 29 (2 * n)) := by
  rw [Ll_succ, Tl, if_pos (even_2b n)]

lemma even_U (n : ℕ) : Ll 29 (2 * n + 2) = Ulin 29 (Ll 29 (2 * n + 1)) := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Ll_succ, Tl, if_neg (not_even_2b1 n)]

lemma odd_mem (n : ℕ) : Ll 29 (2 * n + 1) ∈ B 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [odd_D]; exact D_coeff_low _ 0 (by decide)
  · simpa only [γ, if_neg (not_even_2b1 n)] using L_env (2 * n + 1)
  · change coeff 1 (Ll 29 (2 * n + 1)) = 0
    rw [odd_D]; exact D_coeff_low _ 1 (by decide)

lemma odd_succ (n : ℕ) : Ll 29 (2 * (n + 1) + 1) = Xop (Ll 29 (2 * n + 1)) := by
  rw [odd_D, show 2 * (n + 1) = 2 * n + 2 by omega, even_U]
  rfl

lemma odd_reduction (n : ℕ) :
    PowerSeries.map (PadicInt.toZMod (p := 29)) (Ll 29 (2 * n + 1)) =
      C (8 * (3 : ZMod 29) ^ n) * Ψ 29 Cert29.f := by
  rw [Ll, map_map_int]
  exact (partition_cycle_values 29 (Ψ 29 Cert29.f) (Ψ 29 Cert29.g) 8 3 (by decide)
    Cert29.seed Cert29.even_step Cert29.odd_step n).1

lemma leading (n : ℕ) (F : PS 29) (hF : F ∈ B 1) :
    ∃ c : ℤ_[29], ∃ G : PS 29, F = c • Ll 29 (2 * n + 1) + (29 : ℤ_[29]) • G := by
  obtain ⟨a, ha, he⟩ := envelope_reduction (by norm_num : 5 ≤ 29) (β 29)
    (fun i hi => (envelopes_ge_two (by norm_num : 13 ≤ 29) i hi).2) F hF.1.2
  obtain ⟨c, hc⟩ := Image29.double_cusp_line a ha
    (by rw [he, coeff_map, hF.1.1, map_zero])
    (by rw [he, coeff_map, show coeff 1 F = 0 from hF.2, map_zero])
  let x : ZMod 29 := 8 * 3 ^ n
  have hx : x ≠ 0 := mul_ne_zero (by decide) (pow_ne_zero _ (by decide))
  let r : ℤ_[29] := ((c * x⁻¹).val : ℕ)
  have hr : PadicInt.toZMod r = c * x⁻¹ := by rw [map_natCast, ZMod.natCast_zmod_val]
  obtain ⟨G, hG⟩ := PS_dvd_of_map (F - r • Ll 29 (2 * n + 1)) (by
    rw [map_sub, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, hr,
      odd_reduction, ← he, hc]
    change C c * Ψ 29 Cert29.f - C (c * x⁻¹) * (C x * Ψ 29 Cert29.f) = 0
    rw [← mul_assoc, ← map_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one, sub_self])
  norm_num only [Nat.cast_ofNat] at hG
  exact ⟨r, G, by rw [← hG]; abel⟩

/-- One constant works at every precision; one digit is gained per odd cycle. -/
theorem odd_padic : ∃ κ : ℤ_[29], (∃ d : ℤ_[29], κ = 3 + 29 * d) ∧
    ∀ n : ℕ, Dvd (29 : ℤ_[29]) (n + 1)
      (Ll 29 (2 * n + 3) - κ • Ll 29 (2 * n + 1)) := by
  let O : ℕ → PS 29 := fun b => Ll 29 (2 * b - 1)
  have hO (n : ℕ) : O (n + 1) = Ll 29 (2 * n + 1) := by
    dsimp [O]; congr 1
  have hrec (b : ℕ) (hb : 1 ≤ b) : O (b + 1) = Xop (O b) := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [hO, hO, odd_succ]
  have hmem (b : ℕ) (hb : 1 ≤ b) : O b ∈ B 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [hO]; exact odd_mem n
  have hlead (b : ℕ) (hb : 1 ≤ b) (F : PS 29) (hF : F ∈ B 1) :
      ∃ c : ℤ_[29], ∃ G : PS 29, F = c • O b + (29 : ℤ_[29]) • G := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [hO]; exact leading n F hF
  have hbase (b : ℕ) (hb : 1 ≤ b) : Dvd (29 : ℤ_[29]) 1 (O (b + 1) - 3 • O b) := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [hO, hO]
    obtain ⟨G, hG⟩ := PS_dvd_of_map (Ll 29 (2 * (n + 1) + 1) - (3 : ℤ_[29]) • Ll 29 (2 * n + 1)) (by
      rw [map_sub, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C]
      norm_num only [map_ofNat]
      rw [Ll, Ll, map_map_int, map_map_int,
        show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, Partition29.two_step _ (by omega)]
      rw [show C (3 : ZMod 29) = (3 : PowerSeries (ZMod 29)) from map_ofNat _ 3, sub_self])
    exact ⟨G, by simpa only [pow_one] using hG⟩
  obtain ⟨κ, hκ, h⟩ := lift_padic 1 29 3 (fun _ => Xop) O (fun _ => B 1) (fun _ => B 2)
    PS_reg (fun _ => rfl) hrec (fun _ => rfl) hmem (fun _ _ F hF => X_mem F hF)
    hlead (fun _ _ F hF G hFG => B_div F hF G hFG) hbase
  refine ⟨κ, hκ, fun n => ?_⟩
  have hn := h (n + 1) (by omega)
  rw [hO, hO] at hn
  convert hn using 1

/-- The two parity classes share the same 29-adic multiplier. -/
theorem series_padic : ∃ κ : ℤ_[29], (∃ d : ℤ_[29], κ = 3 + 29 * d) ∧
    ∀ b : ℕ, 1 ≤ b → Dvd (29 : ℤ_[29]) ((b + 1) / 2)
      (Ll 29 (b + 2) - κ • Ll 29 b) := by
  obtain ⟨κ, hκ, hodd⟩ := odd_padic
  refine ⟨κ, hκ, fun b hb => ?_⟩
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' b
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨G, hG⟩ := hodd k
    refine ⟨Ulin 29 G, ?_⟩
    rw [show 2 * (k + 1) = 2 * k + 2 by omega,
      show 2 * k + 2 + 2 = 2 * (k + 1) + 2 by omega, even_U, even_U,
      show 2 * (k + 1) + 1 = 2 * k + 3 by omega, ← map_smul, ← map_sub, hG, map_smul]
    congr 2
    omega
  · have h := hodd n
    convert h using 1
    omega

/-- Cancel the common Euler-product unit at any precision. -/
theorem pser_dvd_precision {ℓ : ℕ} [Fact ℓ.Prime] (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (κ : ℤ_[ℓ]) (b r : ℕ)
    (h : AtkinOBrien.Dvd (ℓ : ℤ_[ℓ]) r (Ll ℓ (b + 2) - κ • Ll ℓ b)) (m : ℕ) :
    (ℓ : ℤ_[ℓ]) ^ r ∣ ((pZ ((ℓ : ℤ) ^ (b + 2) * m - eB ℓ (b + 2)) : ℤ) : ℤ_[ℓ]) -
      κ * ((pZ ((ℓ : ℤ) ^ b * m - eB ℓ b) : ℤ) : ℤ_[ℓ]) := by
  obtain ⟨Q, hQ, h1, h2⟩ := L_factor h24 b
  obtain ⟨y, hy⟩ := h
  set φ := PowerSeries.map (Int.castRingHom ℤ_[ℓ])
  obtain ⟨u, hu⟩ := hQ.map φ
  have hL : ∀ c, Ll ℓ c = φ (L ℓ c) := fun c => rfl
  rw [hL, hL, h1, h2, map_mul, map_mul, ← hu] at hy
  have hy' : (u : PS ℓ) * (φ (Pser ℓ (b + 2)) - κ • φ (Pser ℓ b)) = (ℓ : ℤ_[ℓ]) ^ r • y := by
    rw [mul_sub, mul_smul_comm]; exact hy
  have hd : φ (Pser ℓ (b + 2)) - κ • φ (Pser ℓ b) = (ℓ : ℤ_[ℓ]) ^ r • (↑u⁻¹ * y) := by
    rw [← mul_smul_comm, ← hy', ← mul_assoc, Units.inv_mul, one_mul]
  have := congrArg (coeff m) hd
  rw [map_sub, coeff_smul, coeff_smul, coeff_map, coeff_map, Pser, Pser, coeff_mk, coeff_mk,
    smul_eq_mul, smul_eq_mul] at this
  exact ⟨_, by rw [eq_intCast, eq_intCast] at this; exact this⟩


/-- An unconditional congruence for actual partition counts at every power
of 29. The multiplier is independent of the power, starting index and n. -/
theorem partition_padic : ∃ κ : ℤ_[29], (∃ d : ℤ_[29], κ = 3 + 29 * d) ∧
    ∀ m : ℕ, 1 ≤ m → ∀ b : ℕ, 2 * m - 1 ≤ b → ∀ n : ℕ, 24 ∣ 29 ^ b * n + 1 →
      (29 : ℤ_[29]) ^ m ∣
        (Fintype.card (Nat.Partition ((29 ^ (b + 2) * n + 1) / 24)) : ℤ_[29]) -
        κ * (Fintype.card (Nat.Partition ((29 ^ b * n + 1) / 24)) : ℤ_[29]) := by
  obtain ⟨κ, hκ, hL⟩ := series_padic
  refine ⟨κ, hκ, fun m hm b hb n hn => ?_⟩
  have hb1 : 1 ≤ b := by omega
  have hprecision : m ≤ (b + 1) / 2 := by omega
  have hs := Dvd_mono hprecision (hL b hb1)
  obtain ⟨t, h1, h2⟩ := index_shift (ℓ := 29) (by decide) b n (by exact_mod_cast hn)
  have h := pser_dvd_precision (by decide : 24 * δ 29 + 1 = 29 ^ 2) κ b m hs t
  rw [← h1, ← h2] at h
  norm_num only [Nat.cast_ofNat] at h
  have e1 : ((29 : ℤ) ^ (b + 2) * n + 1) / 24 = (((29 ^ (b + 2) * n + 1) / 24 : ℕ) : ℤ) := by
    push_cast; rfl
  have e2 : ((29 : ℤ) ^ b * n + 1) / 24 = (((29 ^ b * n + 1) / 24 : ℕ) : ℤ) := by
    push_cast; rfl
  rw [e1, e2, pZ_natCast, pZ_natCast] at h
  exact_mod_cast h

/-- The same theorem in finite residue rings, directly usable by a recurrence evaluator. -/
theorem partition_residues (m : ℕ) (hm : 1 ≤ m) : ∃ k : ZMod (29 ^ m),
    ∀ b : ℕ, 2 * m - 1 ≤ b → ∀ n : ℕ, 24 ∣ 29 ^ b * n + 1 →
      (Fintype.card (Nat.Partition ((29 ^ (b + 2) * n + 1) / 24)) : ZMod (29 ^ m)) =
        k * (Fintype.card (Nat.Partition ((29 ^ b * n + 1) / 24)) : ZMod (29 ^ m)) := by
  obtain ⟨κ, -, hκ⟩ := partition_padic
  refine ⟨PadicInt.toZModPow m κ, fun b hb n hn => ?_⟩
  have h := (Ideal.mem_span_singleton.mpr (hκ m hm b hb n hn))
  have hker : RingHom.ker (PadicInt.toZModPow (p := 29) m) = Ideal.span {(29 : ℤ_[29]) ^ m} := by
    simpa only [Nat.cast_ofNat] using PadicInt.ker_toZModPow (p := 29) m
  rw [← hker, RingHom.mem_ker, map_sub, map_mul, map_natCast, map_natCast,
    sub_eq_zero] at h
  exact h

/-- Once a precision is fixed, every future iterate is one scalar power. -/
theorem partition_residues_iterate (m : ℕ) (hm : 1 ≤ m) : ∃ k : ZMod (29 ^ m),
    ∀ b : ℕ, 2 * m - 1 ≤ b → ∀ n : ℕ, 24 ∣ 29 ^ b * n + 1 → ∀ t : ℕ,
      (Fintype.card (Nat.Partition ((29 ^ (b + 2 * t) * n + 1) / 24)) : ZMod (29 ^ m)) =
        k ^ t * (Fintype.card (Nat.Partition ((29 ^ b * n + 1) / 24)) : ZMod (29 ^ m)) := by
  obtain ⟨k, hk⟩ := partition_residues m hm
  refine ⟨k, fun b hb n hn t => ?_⟩
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show b + 2 * (t + 1) = (b + 2 * t) + 2 by omega,
      hk _ (by omega) n (Partition29.valid_index b n t hn), ih, pow_succ']
    ring

end RamanujanTau.FiniteArithmetic.AllPowers29
