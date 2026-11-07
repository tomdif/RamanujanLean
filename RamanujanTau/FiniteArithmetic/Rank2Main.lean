import RamanujanTau.FiniteArithmetic.Rank2Error
import RamanujanTau.BLBound.Threshold2

/-!
# Rank two: `b_ℓ(m) = 2m − 1` from finite data

`Rank2.Data2.bEll_eq`: for a prime `ℓ ≥ 29` with rank-two data (`Data2`), a Cayley–Hamilton
relation `o₂ = k₁ o₁ + k₀ o₀` for the odd coordinates, `k₀ ≠ 0`, a nonzero initial determinant,
`θ ≠ 0` and a nonzero initial observation, Boylan–Webb's invariant is `b_ℓ(m) = 2m − 1`
for every `m ≥ 1`.

The contracting error `Gₙ` of the second-order recurrence satisfies `X Gₙ = ℓ Gₙ₊₁`, and
`obs(U Gₙ) ≡ θⁿ obs(U G₀) (mod ℓ)` (`divided_step`), so it never vanishes. This feeds
`BLBound.not_mem_of_errors2`.
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.Rank2
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

namespace Data2
variable (D : Data2 ℓ) (h29 : 29 ≤ ℓ) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)

lemma ell_ne : (ℓ : ℤ_[ℓ]) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero

lemma map_ell_smul (F : PS ℓ) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) ((ℓ : ℤ_[ℓ]) • F) = 0 := by
  rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, toZMod_prime_zmod, map_zero, zero_mul]

/-- `obs ∘ U` vanishes on the double-cusp plane. -/
lemma obs_U_plane (e : Fin 3 → ZMod ℓ) (h : ∑ i, D.B 0 i * e i = 0) :
    ∑ i, D.ω i * mv D.Umat e i = 0 := by
  simp only [mv, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ j, ∑ i, D.ω i * (D.Umat i j * e j) = D.lam * D.B 0 j * e j := fun j => by
    rw [← D.hkill j, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by simp only [ω]; ring
  simp only [this]
  rw [show ∑ j, D.lam * D.B 0 j * e j = D.lam * ∑ j, D.B 0 j * e j by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, h, mul_zero]

include h29 h24 in
/-- **The observable error is multiplied by `θ` at each cycle.** -/
theorem divided_step (H E : PS ℓ) (hH : H ∈ envSub D.hℓ5 1 (α ℓ))
    (hE : Dlin ℓ H = (ℓ : ℤ_[ℓ]) • E) :
    PadicInt.toZMod (obs D.w (Ulin ℓ E)) = D.θ * PadicInt.toZMod (obs D.w H) := by
  obtain ⟨c, R, hR, he⟩ := D.decompose h29 H hH
  obtain ⟨w', hw⟩ := D.obs_Y h29 h24 H R c hR he
  have hY : Yop H = (ℓ : ℤ_[ℓ]) • Ulin ℓ E := by
    change Ulin ℓ (Dlin ℓ H) = _
    rw [hE, map_smul]
  rw [hY, map_smul, smul_eq_mul] at hw
  have hw' := mul_left_cancel₀ (ell_ne (ℓ := ℓ)) hw
  set cb : Fin 3 → ZMod ℓ := fun i => PadicInt.toZMod (c i)
  have hHbar : PowerSeries.map (PadicInt.toZMod (p := ℓ)) H = D.comb cb := by
    rw [he, map_add, D.map_sum_lift, map_ell_smul, add_zero]
  have hz : D.comb (mv D.Dmat cb) = 0 := by
    have h := congrArg (PowerSeries.map (PadicInt.toZMod (p := ℓ))) hE
    rw [reduce_D h24, hHbar, D.D_comb, map_ell_smul] at h
    exact h
  have hDc := D.comb_zero_iff _ hz
  rw [hw', map_add, map_mul, toZMod_prime_zmod, zero_mul, add_zero, map_sum, obs_reduce, hHbar,
    D.obsBar_comb]
  have hsum : ∑ i, PadicInt.toZMod (c i * (D.z i : ℤ_[ℓ])) =
      ∑ i, cb i * (D.θ * D.ω i + ∑ j, D.μ j * D.Dmat j i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_intCast, D.hθ i]
    rfl
  rw [hsum]
  have hμ : ∑ i, cb i * ∑ j, D.μ j * D.Dmat j i = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h0 : mv D.Dmat cb j = 0 := by rw [hDc]; rfl
    rw [show ∑ i, cb i * (D.μ j * D.Dmat j i) = D.μ j * mv D.Dmat cb j by
      rw [mv, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, h0, mul_zero]
  rw [show (∑ i, cb i * (D.θ * D.ω i + ∑ j, D.μ j * D.Dmat j i)) =
      (∑ i, cb i * (D.θ * D.ω i)) + ∑ i, cb i * ∑ j, D.μ j * D.Dmat j i by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring, hμ, add_zero,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

include h29 in
lemma U_mem (F : PS ℓ) (hF : F ∈ B h29 2) : Ulin ℓ F ∈ envSub D.hℓ5 1 (α ℓ) := by
  refine ⟨?_, U_env D.hℓ5 (by omega) (bounds h29).1 2 le_rfl _ hF.1.2⟩
  change coeff 0 (U ℓ F) = 0
  rw [coeff_U, mul_zero]
  exact hF.1.1

include h29 in
lemma even_mem (n : ℕ) : Ll ℓ (2 * n + 2) ∈ envSub D.hℓ5 1 (α ℓ) := by
  refine ⟨?_, ?_⟩
  · rw [even_U]
    change coeff 0 (U ℓ (Ll ℓ (2 * n + 1))) = 0
    rw [coeff_U, mul_zero]
    exact (odd_mem h29 n).1.1
  · simpa [γ, show Even (2 * n + 2) from ⟨n + 1, by ring⟩] using L_env h29 (2 * n + 2)

lemma even_succ (n : ℕ) : Ll ℓ (2 * n + 4) = Yop (Ll ℓ (2 * n + 2)) := by
  rw [show 2 * n + 4 = 2 * (n + 1) + 2 by omega, even_U, odd_D]
  rfl

include h29 h24 in
/-- `obs(Y L(2n+2)) = ℓ (Σ (U oₙ)ᵢ zᵢ + ℓ w)`. -/
lemma obs_Y_even (n : ℕ) : ∃ c : Fin 3 → ℤ_[ℓ], (fun i => PadicInt.toZMod (c i)) =
    mv D.Umat (D.odd n) ∧ ∃ w' : ℤ_[ℓ],
      obs D.w (Ll ℓ (2 * n + 4)) = (ℓ : ℤ_[ℓ]) * (∑ i, c i * (D.z i : ℤ_[ℓ]) + ℓ * w') := by
  obtain ⟨c, R, hR, he⟩ := D.decompose h29 _ (D.even_mem h29 n)
  refine ⟨c, ?_, ?_⟩
  · apply D.comb_inj
    rw [← D.map_sum_lift, ← D.even_reduction h24 n, he, map_add, map_ell_smul, add_zero]
  · rw [even_succ]; exact D.obs_Y h29 h24 _ R c hR he

end Data2

/-! ### The main theorem -/

variable (D : Data2 ℓ) (h29 : 29 ≤ ℓ) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)

/-- The predicted initial observation `obs(U G₀) mod ℓ`. -/
def Data2.init (D : Data2 ℓ) (k₀ k₁ : ZMod ℓ) (zL2 : ℤ) : ZMod ℓ :=
  ∑ i, mv D.Umat (D.odd 1) i * ((D.z i : ℤ) : ZMod ℓ) -
    k₁ * ∑ i, mv D.Umat (D.odd 0) i * ((D.z i : ℤ) : ZMod ℓ) - k₀ * ((zL2 : ℤ) : ZMod ℓ)

include h29 h24 in
/-- **`b_ℓ(m) = 2m − 1` for every `m ≥ 1`, from rank-two data.** -/
theorem Data2.bEll_eq {k₀ k₁ : ZMod ℓ} (hcay : D.odd 2 = k₁ • D.odd 1 + k₀ • D.odd 0)
    (hk₀ : k₀ ≠ 0) (hdet₀ : D.det 0 ≠ 0) (zL2 : ℤ)
    (hL2 : ∃ t : ℤ_[ℓ], obs D.w (Ll ℓ 2) = (ℓ : ℤ_[ℓ]) * ((zL2 : ℤ_[ℓ]) + ℓ * t))
    (hθ₀ : D.θ ≠ 0) (hinit : D.init k₀ k₁ zL2 ≠ 0) (m : ℕ) (hm : 1 ≤ m) :
    BLBound.bEll ℓ m = 2 * m - 1 := by
  have hdet : ∀ n, D.det n ≠ 0 := fun n => by
    rw [D.det_eq hcay n]; exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hk₀)) hdet₀
  obtain ⟨κ₀, κ₁, hκ₀, hκ₁, h⟩ := odd_padic2 h29 h24 D.toData hcay hdet
  choose G hGm hG using h
  -- `X Gₙ = ℓ Gₙ₊₁`
  have hX : ∀ n, Dlin ℓ (Ulin ℓ (G n)) = (ℓ : ℤ_[ℓ]) • G (n + 1) := by
    intro n
    have hh := congrArg Xop (hG n)
    rw [map_sub, map_sub, map_smul, map_smul, map_smul] at hh
    have hs := hG (n + 1)
    have a1 : Ll ℓ (2 * (n + 1) + 5) = Xop (Ll ℓ (2 * n + 5)) := by
      have := odd_succ (ℓ := ℓ) (n + 2)
      rwa [show 2 * (n + 2 + 1) + 1 = 2 * (n + 1) + 5 by ring, show 2 * (n + 2) + 1 = 2 * n + 5 by ring] at this
    have a2 : Ll ℓ (2 * (n + 1) + 3) = Xop (Ll ℓ (2 * n + 3)) := by
      have := odd_succ (ℓ := ℓ) (n + 1)
      rwa [show 2 * (n + 1 + 1) + 1 = 2 * (n + 1) + 3 by ring, show 2 * (n + 1) + 1 = 2 * n + 3 by ring] at this
    have a3 : Ll ℓ (2 * (n + 1) + 1) = Xop (Ll ℓ (2 * n + 1)) := odd_succ n
    rw [a1, a2, a3, hh, show (ℓ : ℤ_[ℓ]) ^ (n + 1 + 1) = (ℓ : ℤ_[ℓ]) ^ (n + 1) * ℓ from pow_succ _ _,
      mul_smul] at hs
    apply sub_eq_zero.mp
    apply cancel_pow (ℓ : ℤ_[ℓ]) PS_reg (n + 1)
    rw [smul_sub]
    change (ℓ : ℤ_[ℓ]) ^ (n + 1) • Xop (G n) - _ = 0
    rw [hs, sub_self]
  -- the initial observation
  have hinit' : PadicInt.toZMod (obs D.w (Ulin ℓ (G 0))) = D.init k₀ k₁ zL2 := by
    have hU := congrArg (Ulin ℓ) (hG 0)
    have u5 : Ulin ℓ (Ll ℓ 5) = Ll ℓ 6 := by rw [show (6 : ℕ) = 2 * 2 + 2 from rfl, even_U]
    have u3 : Ulin ℓ (Ll ℓ 3) = Ll ℓ 4 := by rw [show (4 : ℕ) = 2 * 1 + 2 from rfl, even_U]
    have u1 : Ulin ℓ (Ll ℓ 1) = Ll ℓ 2 := by rw [show (2 : ℕ) = 2 * 0 + 2 from rfl, even_U]
    rw [map_sub, map_sub, map_smul, map_smul, map_smul] at hU
    simp only [Nat.mul_zero, Nat.zero_add, pow_one] at hU
    rw [u5, u3, u1] at hU
    obtain ⟨c, hc, w₁, hw₁⟩ := D.obs_Y_even h29 h24 0
    obtain ⟨c', hc', w₂, hw₂⟩ := D.obs_Y_even h29 h24 1
    obtain ⟨t, ht⟩ := hL2
    have hO := congrArg (obs D.w) hU
    rw [map_sub, map_sub, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hO
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at hw₁ hw₂
    rw [show 2 * 1 + 4 = 6 from rfl] at hw₂
    rw [hw₁, hw₂, ht] at hO
    have hO' : obs D.w (Ulin ℓ (G 0)) = (∑ i, c' i * (D.z i : ℤ_[ℓ]) + ℓ * w₂) -
        κ₁ * (∑ i, c i * (D.z i : ℤ_[ℓ]) + ℓ * w₁) - κ₀ * ((zL2 : ℤ_[ℓ]) + ℓ * t) := by
      apply mul_left_cancel₀ (Data2.ell_ne (ℓ := ℓ))
      linear_combination -hO
    rw [hO', Data2.init]
    simp only [map_sub, map_mul, map_add, map_sum, toZMod_prime_zmod, zero_mul, add_zero,
      map_intCast, hκ₀, hκ₁]
    rw [← hc, ← hc']
  have herr : ∀ n, PadicInt.toZMod (obs D.w (Ulin ℓ (G n))) = D.θ ^ n * D.init k₀ k₁ zL2 := by
    intro n
    induction n with
    | zero => rw [hinit', pow_zero, one_mul]
    | succ n ih =>
      rw [D.divided_step h29 h24 _ _ (D.U_mem h29 _ (hGm n)) (hX n), ih, pow_succ]
      ring
  refine BLBound.bEll_eq_of_not_mem (by omega) m hm fun k hk =>
    BLBound.not_mem_of_errors2 κ₀ κ₁ G (PowerSeries.coeff 2) (PowerSeries.coeff 3) (obs D.w)
      hG (fun n => ?_) (fun n => ?_) (fun n => ?_) m k hk
  · -- separation
    have h1 := D.odd_reduction h24 n
    have h2 := D.odd_reduction h24 (n + 1)
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring] at h2
    simp only [BLBound.det2, map_sub, map_mul]
    have c2 : ∀ e, coeff 2 (D.comb e) = lin D.toData 1 e := fun e => D.coeff_comb e 1
    have c3 : ∀ e, coeff 3 (D.comb e) = lin D.toData 2 e := fun e => D.coeff_comb e 2
    rw [← coeff_map, ← coeff_map, ← coeff_map, ← coeff_map, h1, h2, c2, c2, c3, c3]
    exact hdet n
  · -- `obs ∘ U` kills the odd series
    rw [obs_reduce, reduce_U, D.odd_reduction h24, D.U_comb, D.obsBar_comb]
    exact D.obs_U_plane _ (lin_zero_odd h29 h24 D.toData n)
  · rw [herr]; exact mul_ne_zero (pow_ne_zero _ hθ₀) hinit

end RamanujanTau.FiniteArithmetic.Rank2
