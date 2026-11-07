/-
# Kloosterman sums to prime-power moduli `p^k`, `k ≥ 2`

Elementary bound `|S(1,b;p^k)| ≤ 4 p^j`, `j = ⌈k/2⌉`, by the averaging trick:
for `t ∈ ZMod p^k` the map `u ↦ u (1 + p^j t)` permutes the units and `(1+p^j t)⁻¹ = 1 - p^j t`
(as `p^{2j} ≡ 0`), so averaging over `t` gives
`S(a,b;p^k) = ∑_{u : p^j (a u - b u⁻¹) = 0} ψ(a u + b u⁻¹)`.
For `a = 1` the condition is `u² ≡ b (mod p^{k-j})`, which has at most `2 p^j` (odd `p`)
resp. `4 p^j` (`p = 2`) unit solutions mod `p^k`.
-/
import RamanujanTau.TauBound.KlBasic

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Complex
open scoped Real

section Averaging

variable {c : ℕ} [NeZero c]

/-- `S(a,b;c) = ∑_{u : X_u = 0} ψ(a u + b u⁻¹)` where `X_u = x (a u - b u⁻¹)`, whenever `x² = 0`. -/
theorem kl_eq_sum_filter (x : ZMod c) (hx : x * x = 0) (a b : ZMod c) :
    kl c a b = ∑ u : (ZMod c)ˣ, if x * (a * u - b * ((u⁻¹ : (ZMod c)ˣ) : ZMod c)) = 0 then
      ZMod.stdAddChar (a * (u : ZMod c) + b * ((u⁻¹ : (ZMod c)ˣ) : ZMod c)) else 0 := by
  classical
  -- the units `1 + x t`
  let ε : ZMod c → (ZMod c)ˣ := fun t =>
    ⟨1 + x * t, 1 - x * t, by linear_combination (-(t * t)) * hx,
      by linear_combination (-(t * t)) * hx⟩
  have hshift : ∀ t : ZMod c, kl c a b = ∑ u : (ZMod c)ˣ,
      ZMod.stdAddChar (a * (u : ZMod c) + b * ((u⁻¹ : (ZMod c)ˣ) : ZMod c)) *
        ZMod.stdAddChar (t * (x * (a * (u : ZMod c) - b * ((u⁻¹ : (ZMod c)ˣ) : ZMod c)))) := by
    intro t
    unfold kl
    refine (Fintype.sum_equiv (Equiv.mulRight (ε t)) _ _ (fun u => ?_)).symm
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [Equiv.coe_mulRight, Units.val_mul, mul_inv_rev, ε, Units.inv_mk]
    have : ((ε t)⁻¹ : (ZMod c)ˣ) = ⟨1 - x * t, 1 + x * t, by linear_combination (-(t * t)) * hx,
      by linear_combination (-(t * t)) * hx⟩ := rfl
    ring
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hsum : (c : ℂ) * kl c a b = ∑ t : ZMod c, kl c a b := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hmain : (c : ℂ) * kl c a b = (c : ℂ) * ∑ u : (ZMod c)ˣ,
      if x * (a * u - b * ((u⁻¹ : (ZMod c)ˣ) : ZMod c)) = 0 then
        ZMod.stdAddChar (a * (u : ZMod c) + b * ((u⁻¹ : (ZMod c)ˣ) : ZMod c)) else 0 := by
    rw [hsum]
    conv_lhs => rw [Finset.sum_congr rfl (fun t _ => hshift t)]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar c)]
    split_ifs <;> simp [ZMod.card, mul_comm]
  exact mul_left_cancel₀ hc hmain

/-- `|S(a,b;c)| ≤ #{u : x (a u - b u⁻¹) = 0}` whenever `x² = 0`. -/
theorem norm_kl_le_card (x : ZMod c) (hx : x * x = 0) (a b : ZMod c) :
    ‖kl c a b‖ ≤ ((Finset.univ.filter (fun u : (ZMod c)ˣ =>
      x * (a * u - b * ((u⁻¹ : (ZMod c)ˣ) : ZMod c)) = 0)).card : ℝ) := by
  classical
  rw [kl_eq_sum_filter x hx a b]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_le_sum (fun u _ => ?_)
  split_ifs <;> simp

end Averaging

/-! ### Square roots modulo prime powers -/

lemma int_sq_root_dvd_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ) (U U0 : ℤ)
    (h0 : ¬ (p : ℤ) ∣ U0) (h : (p : ℤ) ^ m ∣ (U - U0) * (U + U0)) :
    (p : ℤ) ^ m ∣ U - U0 ∨ (p : ℤ) ^ m ∣ U + U0 := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hD : (p : ℤ) ∣ U - U0
  · by_cases hE : (p : ℤ) ∣ U + U0
    · exfalso
      have h2 : (p : ℤ) ∣ 2 * U0 := by
        have := dvd_sub hE hD; ring_nf at this ⊢; simpa [mul_comm] using this
      rcases hpz.dvd_or_dvd h2 with h2 | h2
      · have : (p : ℤ) ∣ 2 := h2
        have : p ∣ 2 := by exact_mod_cast this
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
        exact hp2 this
      · exact h0 h2
    · left
      have hcop : IsCoprime ((p : ℤ) ^ m) (U + U0) :=
        IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpz).mpr hE)
      exact hcop.dvd_of_dvd_mul_right h
  · right
    have hcop : IsCoprime ((p : ℤ) ^ m) (U - U0) :=
      IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpz).mpr hD)
    exact hcop.dvd_of_dvd_mul_left h

lemma int_sq_root_dvd_two (m : ℕ) (U U0 : ℤ) (hU : ¬ (2 : ℤ) ∣ U) (h0 : ¬ (2 : ℤ) ∣ U0)
    (h : (2 : ℤ) ^ m ∣ (U - U0) * (U + U0)) :
    (2 : ℤ) ^ (m - 1) ∣ U - U0 ∨ (2 : ℤ) ^ (m - 1) ∣ U + U0 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  obtain ⟨A, hA⟩ : (2 : ℤ) ∣ U - U0 := by omega
  obtain ⟨B, hB⟩ : (2 : ℤ) ∣ U + U0 := by omega
  have hBA : B - A = U0 := by omega
  have h2 : Prime (2 : ℤ) := Int.prime_two
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h' : (2 : ℤ) ^ m' ∣ 2 * (A * B) := by
    have : (U - U0) * (U + U0) = 2 * (2 * (A * B)) := by rw [hA, hB]; ring
    rw [this, pow_succ, mul_comm _ (2 : ℤ)] at h
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h
  by_cases hAodd : (2 : ℤ) ∣ A
  · -- then B is odd
    have hB' : ¬ (2 : ℤ) ∣ B := by
      intro hb; exact h0 (by rw [← hBA]; exact dvd_sub hb hAodd)
    left
    have hcop : IsCoprime ((2 : ℤ) ^ m') B :=
      IsCoprime.pow_left ((Prime.coprime_iff_not_dvd h2).mpr hB')
    have : (2 : ℤ) ^ m' ∣ (2 * A) * B := by rw [mul_assoc]; exact h'
    rw [hA]; exact hcop.dvd_of_dvd_mul_right this
  · right
    have hcop : IsCoprime ((2 : ℤ) ^ m') A :=
      IsCoprime.pow_left ((Prime.coprime_iff_not_dvd h2).mpr hAodd)
    have : (2 : ℤ) ^ m' ∣ A * (2 * B) := by
      have : A * (2 * B) = 2 * (A * B) := by ring
      rw [this]; exact h'
    rw [hB]; exact hcop.dvd_of_dvd_mul_left this

/-! ### Counting unit square roots modulo `p^k` -/

section Count

variable {p : ℕ} (hp : p.Prime) (k : ℕ)

include hp in
lemma not_dvd_val_unit (hk : 1 ≤ k) [NeZero (p ^ k)] (u : (ZMod (p ^ k))ˣ) :
    ¬ (p : ℤ) ∣ ((u : ZMod (p ^ k)).val : ℤ) := by
  intro h
  have h' : p ∣ (u : ZMod (p ^ k)).val := by exact_mod_cast h
  have hc := ZMod.val_coe_unit_coprime u
  have : p ∣ Nat.gcd (u : ZMod (p ^ k)).val (p ^ k) :=
    Nat.dvd_gcd h' (dvd_pow_self p (by omega))
  rw [hc] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- The "translate" family `{V + p^{m} s : 0 ≤ s < p^{k-m}}` in `ZMod p^k`. -/
noncomputable def transl (m : ℕ) (V : ℤ) : Finset (ZMod (p ^ k)) :=
  (Finset.range (p ^ (k - m))).image (fun s : ℕ => (((V + (p : ℤ) ^ m * s) : ℤ) : ZMod (p ^ k)))

lemma card_transl_le (m : ℕ) (V : ℤ) : (transl k m V (p := p)).card ≤ p ^ (k - m) :=
  Finset.card_image_le.trans (by simp)

lemma mem_transl (hp0 : 0 < p) (m : ℕ) (hm : m ≤ k) (V U : ℤ) (h : (p : ℤ) ^ m ∣ U - V) :
    ((U : ℤ) : ZMod (p ^ k)) ∈ transl k m V (p := p) := by
  obtain ⟨s, hs⟩ := h
  have hpos : (0 : ℤ) < (p : ℤ) ^ (k - m) := by positivity
  set n := (p : ℤ) ^ (k - m)
  refine Finset.mem_image.mpr ⟨(s % n).toNat, ?_, ?_⟩
  · have h1 : 0 ≤ s % n := Int.emod_nonneg _ hpos.ne'
    have h2 : s % n < n := Int.emod_lt_of_pos _ hpos
    rw [Finset.mem_range]
    have : ((s % n).toNat : ℤ) < ((p ^ (k - m) : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h1]; push_cast; exact h2
    exact_mod_cast this
  · rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    have h1 : 0 ≤ s % n := Int.emod_nonneg _ hpos.ne'
    rw [Int.toNat_of_nonneg h1, Int.emod_def]
    have hpk : ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ m * n := by
      push_cast; rw [← pow_add]; congr 1; omega
    rw [hpk]
    exact ⟨s / n, by rw [show U = V + (p : ℤ) ^ m * s by linarith]; ring⟩

include hp in
/-- At most `4 p^j` units `u` mod `p^k` satisfy `p^j (u² - b) = 0`. -/
theorem card_sqrt_le (hk : 1 ≤ k) [NeZero (p ^ k)] (j : ℕ) (hj : j ≤ k) (b : ZMod (p ^ k)) :
    (Finset.univ.filter (fun u : (ZMod (p ^ k))ˣ =>
      (p : ZMod (p ^ k)) ^ j * ((u : ZMod (p ^ k)) ^ 2 - b) = 0)).card ≤ 4 * p ^ j := by
  classical
  set F := Finset.univ.filter (fun u : (ZMod (p ^ k))ˣ =>
      (p : ZMod (p ^ k)) ^ j * ((u : ZMod (p ^ k)) ^ 2 - b) = 0) with hF
  rcases F.eq_empty_or_nonempty with hE | ⟨u0, hu0⟩
  · rw [hE]; simp
  have hp0 : 0 < p := hp.pos
  set e : ℕ := if p = 2 then 1 else 0 with he
  set m' : ℕ := (k - j) - e with hm'
  set U0 : ℤ := ((u0 : ZMod (p ^ k)).val : ℤ)
  have hsub : ∀ u ∈ F, ((u : ZMod (p ^ k))) ∈ transl k m' U0 (p := p) ∪ transl k m' (-U0) := by
    intro u hu
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hu hu0
    set U : ℤ := ((u : ZMod (p ^ k)).val : ℤ)
    have hUc : ((U : ℤ) : ZMod (p ^ k)) = u := by simp [U]
    have hU0c : ((U0 : ℤ) : ZMod (p ^ k)) = u0 := by simp [U0]
    have hz : ((((p : ℤ) ^ j * ((U - U0) * (U + U0)) : ℤ)) : ZMod (p ^ k)) = 0 := by
      push_cast; rw [hUc, hU0c]; linear_combination hu - hu0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    have hdiv : (p : ℤ) ^ (k - j) ∣ (U - U0) * (U + U0) := by
      have hpk : ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ j * (p : ℤ) ^ (k - j) := by
        push_cast; rw [← pow_add]; congr 1; omega
      rw [hpk] at hz
      exact (mul_dvd_mul_iff_left (by positivity)).mp hz
    have hU0nd : ¬ (p : ℤ) ∣ U0 := not_dvd_val_unit hp k hk u0
    have hUnd : ¬ (p : ℤ) ∣ U := not_dvd_val_unit hp k hk u
    clear_value U U0
    have hcases : (p : ℤ) ^ m' ∣ U - U0 ∨ (p : ℤ) ^ m' ∣ U - (-U0) := by
      rw [sub_neg_eq_add]
      by_cases h2 : p = 2
      · have hm2 : m' = (k - j) - 1 := by simp [hm', he, h2]
        rw [hm2]
        subst h2
        have := int_sq_root_dvd_two (k - j) U U0 (by simpa using hUnd)
          (by simpa using hU0nd) (by simpa using hdiv)
        simpa using this
      · have hm2 : m' = k - j := by simp [hm', he, h2]
        rw [hm2]
        exact int_sq_root_dvd_odd hp h2 (k - j) U U0 hU0nd hdiv
    rw [← hUc]
    rcases hcases with h | h
    · exact Finset.mem_union_left _ (mem_transl k hp0 m' (by omega) U0 U h)
    · exact Finset.mem_union_right _ (mem_transl k hp0 m' (by omega) (-U0) U h)
  have hcard : F.card ≤ (transl k m' U0 (p := p) ∪ transl k m' (-U0)).card :=
    Finset.card_le_card_of_injOn (fun u => (u : ZMod (p ^ k))) (fun u hu => hsub u hu)
      (fun a _ b _ hab => Units.ext hab)
  refine hcard.trans ((Finset.card_union_le _ _).trans ?_)
  have h1 := card_transl_le k m' U0 (p := p)
  have h2 := card_transl_le k m' (-U0) (p := p)
  have hexp : p ^ (k - m') ≤ 2 * p ^ j := by
    by_cases h2 : p = 2
    · have : k - m' ≤ j + 1 := by simp [hm', he, h2]; omega
      calc p ^ (k - m') ≤ p ^ (j + 1) := Nat.pow_le_pow_right hp0 this
        _ = 2 * p ^ j := by rw [pow_succ, h2]; ring
    · have : k - m' = j := by simp [hm', he, h2]; omega
      rw [this]; omega
  omega

end Count

/-- **Prime-power Kloosterman bound**: `|S(1,b;p^k)| ≤ 4 p^{⌈k/2⌉}` for `k ≥ 2`. -/
theorem norm_kl_primePow_le {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 2 ≤ k) [NeZero (p ^ k)]
    (b : ZMod (p ^ k)) : ‖kl (p ^ k) 1 b‖ ≤ 4 * (p : ℝ) ^ ((k + 1) / 2) := by
  classical
  set j := (k + 1) / 2 with hj
  set x : ZMod (p ^ k) := (p : ZMod (p ^ k)) ^ j
  have hx : x * x = 0 := by
    have : x * x = ((p ^ (2 * j) : ℕ) : ZMod (p ^ k)) := by
      simp only [x]; push_cast; ring
    rw [this, ZMod.natCast_eq_zero_iff]
    exact Nat.pow_dvd_pow p (by omega)
  refine (norm_kl_le_card x hx 1 b).trans ?_
  have hcongr : Finset.univ.filter (fun u : (ZMod (p ^ k))ˣ =>
      x * (1 * (u : ZMod (p ^ k)) - b * ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) = 0) =
      Finset.univ.filter (fun u : (ZMod (p ^ k))ˣ =>
        (p : ZMod (p ^ k)) ^ j * ((u : ZMod (p ^ k)) ^ 2 - b) = 0) := by
    refine Finset.filter_congr (fun u _ => ?_)
    have hu : ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * u = 1 := by simp
    constructor
    · intro h
      have : x * ((u : ZMod (p ^ k)) ^ 2 - b) =
          x * (1 * (u : ZMod (p ^ k)) - b * ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) * u := by
        linear_combination (x * b) * hu
      rw [this, h, zero_mul]
    · intro h
      have : x * (1 * (u : ZMod (p ^ k)) - b * ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) =
          x * ((u : ZMod (p ^ k)) ^ 2 - b) * ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) := by
        linear_combination (-(x * (u : ZMod (p ^ k)))) * hu
      simp only [x] at this ⊢
      rw [this, h, zero_mul]
  rw [hcongr]
  have := card_sqrt_le hp k (by omega) j (by omega) b
  exact_mod_cast this


end RamanujanTau.TauBound
