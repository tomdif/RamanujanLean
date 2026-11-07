import RamanujanTau.FiniteArithmetic.RankSMod
import RamanujanTau.FiniteArithmetic.OrbitLift2
import RamanujanTau.FiniteArithmetic.SmallThreshold

/-!
# The ℓ-adic second-order recurrence with `s + 2` forms

`Rank2Lift` with `s` vanishing low coefficients: if `ℓ s < δ`, then `D` kills `a₀, …, a_s`, the
odd envelope is cut out by `a₁ = … = a_s = 0`, and the `(a_{s+1}, a_{s+2})`-determinant separates
consecutive odd vectors. Then `L(2n+5) − κ₁ L(2n+3) − κ₀ L(2n+1) = ℓ^(n+1) Gₙ` (`odd_padic2`).
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.RankS
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal

variable {ℓ s : ℕ} [hℓ : Fact ℓ.Prime]

/-! ### Linear algebra of the coordinates -/

lemma mv_add {m n : ℕ} (M : Fin m → Fin n → ZMod ℓ) (u v : Fin n → ZMod ℓ) :
    mv M (u + v) = mv M u + mv M v := by
  ext j; simp [mv, mul_add, Finset.sum_add_distrib]

lemma mv_smul {m n : ℕ} (M : Fin m → Fin n → ZMod ℓ) (c : ZMod ℓ) (v : Fin n → ZMod ℓ) :
    mv M (c • v) = c • mv M v := by
  ext j; simp [mv, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

/-- The coefficient `a_{k+1}` in coordinates. -/
def lin (D : Data ℓ s) (k : Fin (s + 2)) (v : Fin (s + 2) → ZMod ℓ) : ZMod ℓ := ∑ i, D.B k i * v i

lemma lin_add (D : Data ℓ s) (k : Fin (s + 2)) (u v : Fin (s + 2) → ZMod ℓ) : lin D k (u + v) = lin D k u + lin D k v := by
  simp [lin, mul_add, Finset.sum_add_distrib]

lemma lin_smul (D : Data ℓ s) (k : Fin (s + 2)) (c : ZMod ℓ) (v : Fin (s + 2) → ZMod ℓ) :
    lin D k (c • v) = c * lin D k v := by
  simp [lin, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

/-- The index of `a_{s+1}`. -/
def iS (s : ℕ) : Fin (s + 2) := ⟨s, by omega⟩
/-- The index of `a_{s+2}`. -/
def iT (s : ℕ) : Fin (s + 2) := ⟨s + 1, by omega⟩

namespace Data
variable (D : Data ℓ s)

/-- The `(a_{s+1}, a_{s+2})`-determinant of two consecutive odd vectors. -/
def det (n : ℕ) : ZMod ℓ :=
  lin D (iS s) (D.odd n) * lin D (iT s) (D.odd (n + 1)) -
    lin D (iS s) (D.odd (n + 1)) * lin D (iT s) (D.odd n)

variable {k₀ k₁ : ZMod ℓ} (hcay : D.odd 2 = k₁ • D.odd 1 + k₀ • D.odd 0)
include hcay

lemma odd_rec (n : ℕ) : D.odd (n + 2) = k₁ • D.odd (n + 1) + k₀ • D.odd n := by
  induction n with
  | zero => exact hcay
  | succ n ih =>
    rw [show D.odd (n + 1 + 2) = mv D.Dmat (mv D.Umat (D.odd (n + 2))) from rfl]
    conv_lhs => rw [ih]
    rw [mv_add, mv_add, mv_smul, mv_smul, mv_smul, mv_smul]
    rfl

lemma det_succ (n : ℕ) : D.det (n + 1) = -k₀ * D.det n := by
  simp only [det, D.odd_rec hcay n, lin_add, lin_smul]
  ring

lemma det_eq (n : ℕ) : D.det n = (-k₀) ^ n * D.det 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [D.det_succ hcay, ih, pow_succ]; ring

end Data

/-! ### The odd envelopes -/

section Env
variable (h29 : 29 ≤ ℓ) (hlow : ℓ * s < δ ℓ)

include h29 in
lemma h5 : 5 ≤ ℓ := by omega
include h29 in
lemma h13 : 13 ≤ ℓ := by omega

include hlow in
lemma delta_gt (n : ℕ) (hn : n ≤ s) : ¬ δ ℓ ≤ ℓ * n := by
  intro h
  have : ℓ * n ≤ ℓ * s := Nat.mul_le_mul_left _ hn
  omega

include hlow in
lemma D_coeff_low (F : PS ℓ) (n : ℕ) (hn : n ≤ s) : coeff n (Dlin ℓ F) = 0 := by
  rw [Dlin_apply, coeff_U, Φl, BoylanWebb.Φ]
  simp only [map_mul, map_pow, PowerSeries.map_X]
  rw [mul_assoc, mul_assoc, coeff_X_pow_mul', if_neg (delta_gt hlow n hn)]

/-- `a₁ = … = a_s = 0`. -/
noncomputable def lowKer (ℓ s : ℕ) [Fact ℓ.Prime] : Submodule ℤ_[ℓ] (PS ℓ) :=
  ⨅ t : Fin s, LinearMap.ker (PowerSeries.coeff (R := ℤ_[ℓ]) (t.val + 1))

lemma mem_lowKer {F : PS ℓ} : F ∈ lowKer ℓ s ↔ ∀ t : Fin s, coeff (t.val + 1) F = 0 := by
  simp [lowKer, Submodule.mem_iInf]

/-- The odd envelope with `a₀ = a₁ = … = a_s = 0`. -/
noncomputable def B (h29 : 29 ≤ ℓ) (s : ℕ) (c : ℤ) : Submodule ℤ_[ℓ] (PS ℓ) :=
  envSub (h5 h29) c (β ℓ) ⊓ lowKer ℓ s

noncomputable def Xop : Module.End ℤ_[ℓ] (PS ℓ) := (Dlin ℓ).comp (Ulin ℓ)

include h29 in
lemma bounds : UB ℓ (h5 h29) ∧ DB ℓ (h5 h29) := SmallThreshold.ub_db (h5 h29) (by omega)

include hlow in
lemma X_mem (F : PS ℓ) (hF : F ∈ B h29 s 2) : Xop F ∈ B h29 s 1 := by
  refine ⟨⟨D_coeff_low hlow _ 0 (by omega), ?_⟩,
    mem_lowKer.mpr fun t => D_coeff_low hlow _ _ (by omega)⟩
  exact D_env (h5 h29) (h13 h29) (bounds h29).2 1 (by norm_num) _
    (U_env (h5 h29) (h13 h29) (bounds h29).1 2 le_rfl _ hF.1.2)

include h29 in
lemma B_div (F : PS ℓ) (hF : F ∈ B h29 s 1) (G : PS ℓ) (h : F = (ℓ : ℤ_[ℓ]) • G) :
    G ∈ B h29 s 2 := by
  have hl : (ℓ : ℤ_[ℓ]) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  refine ⟨⟨?_, by simpa using env_div (h5 h29) 1 (β ℓ) hF.1.2 h⟩, ?_⟩
  · have hz := hF.1.1
    rw [h, coeff_smul, smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left hl
  · refine mem_lowKer.mpr fun t => ?_
    have hz : coeff (t.val + 1) F = 0 := mem_lowKer.mp hF.2 t
    rw [h, coeff_smul, smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left hl

include h29 in
lemma B_mono (F : PS ℓ) (hF : F ∈ B h29 s 1) : F ∈ B h29 s 2 := by
  refine ⟨⟨hF.1.1, fun N => ?_⟩, hF.2⟩
  obtain ⟨I, a, ha, hd, he⟩ := hF.1.2 N
  exact ⟨I, a, ha, hd, fun i => Dvd_mono (by omega) (he i)⟩

include h29 in
lemma L_env (b : ℕ) : Env ℓ (h5 h29) 1 (γ ℓ b) (Ll ℓ b) := by
  induction b with
  | zero =>
    rw [show γ ℓ 0 = α ℓ by simp [γ], show Ll ℓ 0 = 1 by simp [Ll, L]]
    exact env_one (h5 h29)
  | succ b ih =>
    rw [Ll_succ]
    exact env_step (h5 h29) (h13 h29) (bounds h29).1 (bounds h29).2 1 (by norm_num) b _ ih

lemma odd_D (n : ℕ) : Ll ℓ (2 * n + 1) = Dlin ℓ (Ll ℓ (2 * n)) := by
  rw [Ll_succ, Tl, if_pos (even_2b n)]

lemma even_U (n : ℕ) : Ll ℓ (2 * n + 2) = Ulin ℓ (Ll ℓ (2 * n + 1)) := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Ll_succ, Tl, if_neg (not_even_2b1 n)]

include hlow in
lemma odd_mem (n : ℕ) : Ll ℓ (2 * n + 1) ∈ B h29 s 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [odd_D]; exact D_coeff_low hlow _ 0 (by omega)
  · simpa only [γ, if_neg (not_even_2b1 n)] using L_env h29 (2 * n + 1)
  · refine mem_lowKer.mpr fun t => ?_
    rw [odd_D]; exact D_coeff_low hlow _ _ (by omega)

lemma odd_succ (n : ℕ) : Ll ℓ (2 * (n + 1) + 1) = Xop (Ll ℓ (2 * n + 1)) := by
  rw [odd_D, show 2 * (n + 1) = 2 * n + 2 by omega, even_U]
  rfl

end Env

/-! ### Leading terms and the recurrence -/

section Lift
variable (h29 : 29 ≤ ℓ) (hlow : ℓ * s < δ ℓ) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (D : Data ℓ s)

lemma toZMod_prime_zmod : PadicInt.toZMod (ℓ : ℤ_[ℓ]) = 0 := by
  rw [map_natCast, ZMod.natCast_self]

lemma lift_val (c : ZMod ℓ) : PadicInt.toZMod (((c.val : ℕ) : ℤ_[ℓ])) = c := by
  rw [map_natCast, ZMod.natCast_zmod_val]

include h29 hlow h24 in
/-- The first `s` coordinates of every odd vector vanish. -/
lemma lin_zero_odd (n : ℕ) (k : Fin (s + 2)) (hk : k.val < s) : lin D k (D.odd n) = 0 := by
  have h := congrArg (coeff (k.val + 1)) (D.odd_reduction h24 n)
  rw [coeff_map, show coeff (k.val + 1) (Ll ℓ (2 * n + 1)) = 0 from
    mem_lowKer.mp (odd_mem h29 hlow n).2 ⟨k.val, hk⟩, map_zero] at h
  rw [h, D.coeff_comb]
  rfl

include h29 hlow h24 in
/-- **Rank-two leading terms.** -/
lemma leading2 (hdet : ∀ n, D.det n ≠ 0) (n : ℕ) (F : PS ℓ) (hF : F ∈ B h29 s 1) :
    ∃ c₀ c₁ : ℤ_[ℓ], ∃ G : PS ℓ,
      F = c₀ • Ll ℓ (2 * n + 1) + c₁ • Ll ℓ (2 * n + 3) + (ℓ : ℤ_[ℓ]) • G := by
  obtain ⟨a, ha, he⟩ := envelope_reduction (h5 h29) (β ℓ)
    (fun i hi => (envelopes_ge_two (h13 h29) i hi).2) F hF.1.2
  have ha0 : coeff 0 (Ψ ℓ a) = 0 := by rw [he, coeff_map, hF.1.1, map_zero]
  have ha1 : ∀ t : Fin s, coeff (t.val + 1) (Ψ ℓ a) = 0 := fun t => by
    rw [he, coeff_map, mem_lowKer.mp hF.2 t, map_zero]
  set e : Fin (s + 2) → ZMod ℓ := fun i => ∑ k : Fin (s + 2), D.Binv i k * coeff (k.val + 1) (Ψ ℓ a)
  have hae : Ψ ℓ a = D.comb e := D.cusp_eq a ha ha0
  set u := D.odd n
  set v := D.odd (n + 1)
  set Δ := D.det n
  have hΔ : Δ ≠ 0 := hdet n
  set α := (lin D (iS s) e * lin D (iT s) v - lin D (iS s) v * lin D (iT s) e) * Δ⁻¹
  set β := (lin D (iS s) u * lin D (iT s) e - lin D (iS s) e * lin D (iT s) u) * Δ⁻¹
  have hcomb : D.comb e = C α * D.comb u + C β * D.comb v := by
    rw [← D.comb_smul, ← D.comb_smul, ← D.comb_add]
    refine D.comb_eq_of_coeff fun k => ?_
    rw [D.coeff_comb, D.coeff_comb]
    change lin D k e = lin D k (α • u + β • v)
    rw [lin_add, lin_smul, lin_smul]
    have hΔ' : Δ = lin D (iS s) u * lin D (iT s) v - lin D (iS s) v * lin D (iT s) u := rfl
    rcases Nat.lt_or_ge k.val s with hk | hk
    · have he0 : lin D k e = 0 := by
        rw [show lin D k e = coeff (k.val + 1) (D.comb e) from (D.coeff_comb e k).symm,
          ← hae]; exact ha1 ⟨k.val, hk⟩
      rw [he0, lin_zero_odd h29 hlow h24 D n k hk, lin_zero_odd h29 hlow h24 D (n + 1) k hk]; ring
    · rcases (show k = iS s ∨ k = iT s by
        rcases Nat.eq_or_lt_of_le hk with h | h
        · exact Or.inl (Fin.ext h.symm)
        · exact Or.inr (Fin.ext (by simp only [iT]; omega))) with rfl | rfl
      · simp only [α, β]
        field_simp
        rw [hΔ']; ring
      · simp only [α, β]
        field_simp
        rw [hΔ']; ring
  set r₀ : ℤ_[ℓ] := ((α.val : ℕ) : ℤ_[ℓ])
  set r₁ : ℤ_[ℓ] := ((β.val : ℕ) : ℤ_[ℓ])
  obtain ⟨G, hG⟩ := PS_dvd_of_map (F - r₀ • Ll ℓ (2 * n + 1) - r₁ • Ll ℓ (2 * n + 3)) (by
    rw [map_sub, map_sub, PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_mul, map_mul,
      PowerSeries.map_C, PowerSeries.map_C, lift_val, lift_val, ← he, hae, hcomb,
      D.odd_reduction h24, show 2 * n + 3 = 2 * (n + 1) + 1 by ring, D.odd_reduction h24]
    ring)
  exact ⟨r₀, r₁, G, by rw [← hG]; abel⟩

variable {k₀ k₁ : ZMod ℓ}

include h29 hlow h24 in
/-- **The ℓ-adic second-order recurrence on the odd chain.** -/
theorem odd_padic2 (hcay : D.odd 2 = k₁ • D.odd 1 + k₀ • D.odd 0) (hdet : ∀ n, D.det n ≠ 0) :
    ∃ κ₀ κ₁ : ℤ_[ℓ], PadicInt.toZMod κ₀ = k₀ ∧ PadicInt.toZMod κ₁ = k₁ ∧
      ∀ n : ℕ, ∃ G ∈ B h29 s 2,
        Ll ℓ (2 * n + 5) - κ₁ • Ll ℓ (2 * n + 3) - κ₀ • Ll ℓ (2 * n + 1) =
          (ℓ : ℤ_[ℓ]) ^ (n + 1) • G := by
  let O : ℕ → PS ℓ := fun b => Ll ℓ (2 * b - 1)
  have hO (n : ℕ) : O (n + 1) = Ll ℓ (2 * n + 1) := by dsimp [O]; congr 1
  have hrec (b : ℕ) (hb : 1 ≤ b) : O (b + 1) = Xop (O b) := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [hO, hO, odd_succ]
  have hmem (b : ℕ) (hb : 1 ≤ b) : O b ∈ B h29 s 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [hO]; exact odd_mem h29 hlow n
  have hlead (b : ℕ) (hb : 1 ≤ b) (F : PS ℓ) (hF : F ∈ B h29 s 1) :
      ∃ c₀ c₁ : ℤ_[ℓ], ∃ G : PS ℓ, F = c₀ • O b + c₁ • O (b + 1) + (ℓ : ℤ_[ℓ]) • G := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [hO, show n + 1 + 1 = (n + 1) + 1 from rfl, hO,
      show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
    exact leading2 h29 hlow h24 D hdet n F hF
  set q₀ : ℤ_[ℓ] := ((k₀.val : ℕ) : ℤ_[ℓ])
  set q₁ : ℤ_[ℓ] := ((k₁.val : ℕ) : ℤ_[ℓ])
  have hbase (b : ℕ) (hb : 1 ≤ b) : Dvd (ℓ : ℤ_[ℓ]) 1 (rec2 1 O q₀ q₁ b) := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    have e1 : O (n + 1 + 2 * 1) = Ll ℓ (2 * (n + 2) + 1) := by
      rw [show n + 1 + 2 * 1 = (n + 2) + 1 by ring, hO]
    have e2 : O (n + 1 + 1) = Ll ℓ (2 * (n + 1) + 1) := hO (n + 1)
    obtain ⟨G, hG⟩ := PS_dvd_of_map (rec2 1 O q₀ q₁ (n + 1)) (by
      rw [rec2, e1, e2, hO, map_sub, map_sub, PowerSeries.smul_eq_C_mul,
        PowerSeries.smul_eq_C_mul, map_mul, map_mul, PowerSeries.map_C, PowerSeries.map_C,
        lift_val, lift_val, D.odd_reduction h24, D.odd_reduction h24, D.odd_reduction h24,
        D.odd_rec hcay n, D.comb_add, D.comb_smul, D.comb_smul]
      ring)
    exact ⟨G, by simpa only [pow_one] using hG⟩
  obtain ⟨κ₀, κ₁, hκ₀, hκ₁, h⟩ := lift_padic_mem2 1 ℓ q₀ q₁ (fun _ => Xop) O (fun _ => B h29 s 1)
    (fun _ => B h29 s 2) PS_reg (fun _ => rfl) hrec (fun _ => rfl) hmem
    (fun _ _ F hF => X_mem h29 hlow F hF) hlead (fun _ _ F hF G hFG => B_div h29 F hF G hFG)
    (fun b hb => B_mono h29 _ (hmem b hb)) (fun b hb => B_mono h29 _ (hmem (b + 1) (by omega)))
    hbase
  refine ⟨κ₀, κ₁, ?_, ?_, fun n => ?_⟩
  · obtain ⟨d, hd⟩ := hκ₀
    rw [hd, map_add, map_mul, toZMod_prime_zmod, zero_mul, add_zero, lift_val]
  · obtain ⟨d, hd⟩ := hκ₁
    rw [hd, map_add, map_mul, toZMod_prime_zmod, zero_mul, add_zero, lift_val]
  · obtain ⟨G, hGm, hG⟩ := h (n + 1) (by omega)
    refine ⟨G, hGm, ?_⟩
    rw [rec2, show n + 1 + 2 * 1 = (n + 2) + 1 by ring, hO, show n + 1 + 1 = (n + 1) + 1 from rfl,
      hO, hO] at hG
    rw [show 2 * n + 5 = 2 * (n + 2) + 1 by ring, show 2 * n + 3 = 2 * (n + 1) + 1 by ring]
    exact hG

end Lift

end RamanujanTau.FiniteArithmetic.RankS
