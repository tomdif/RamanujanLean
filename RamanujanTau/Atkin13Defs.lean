/-
# Atkin–O'Brien 13^k: the objects

* `V : q ↦ q¹³`, `U = U₁₃ : Σ aₙqⁿ ↦ Σ a₁₃ₙqⁿ`, `E_k = (q^k;q^k)_∞`.
* `g = q E₁₃²/E₁²` (the Hauptmodul of `Γ₀(13)`) and `φ = q⁷E₁₆₉/E₁`, so `φ² = g·V(g)`.
* `η_a = (q^a;q¹³)_∞(q^{13−a};q¹³)_∞` and the six components of the 13-dissection
  `c₀ = η₄/η₂`, `c₁ = −η₆/η₃`, `c₂ = −η₂/η₁`, `c₅ = η₅/η₄`, `c₉ = q η₁/η₆`, `c₁₂ = −η₃/η₅`.
-/
import RamanujanTau.Atkin11Defs

set_option autoImplicit false

namespace Atkin13
open PowerSeries Finset RankProof
open Atkin11 (PS ex coeff_ex E1 isUnit_E1 isUnit_ex)

/-- `V : q ↦ q¹³`. -/
noncomputable abbrev V : PS →+* PS := ex 13 (by norm_num)

/-- `U₁₃`. -/
noncomputable def U (f : PS) : PS := mk fun n => coeff (13 * n) f

lemma coeff_U (n : ℕ) (f : PS) : coeff n (U f) = coeff (13 * n) f := by simp [U]

lemma U_add (f g : PS) : U (f + g) = U f + U g := by ext n; simp [coeff_U]
lemma U_sub (f g : PS) : U (f - g) = U f - U g := by ext n; simp [coeff_U]
lemma U_smul (c : ℤ) (f : PS) : U (c • f) = c • U f := by
  ext n
  rw [coeff_U, zsmul_eq_mul, zsmul_eq_mul, ← map_intCast (PowerSeries.C (R := ℤ)) c, coeff_C_mul, coeff_C_mul,
    coeff_U]
lemma U_neg (f : PS) : U (-f) = -U f := by ext n; simp [coeff_U]
lemma U_sum {ι : Type*} (s : Finset ι) (f : ι → PS) : U (∑ i ∈ s, f i) = ∑ i ∈ s, U (f i) := by
  ext n; simp [coeff_U, map_sum]

/-- **`U(V(g)·f) = g·U(f)`**. -/
lemma U_V_mul (g f : PS) : U (V g * f) = g * U f := by
  ext n
  rw [coeff_U, coeff_mul, coeff_mul]
  rw [← sum_subset (s₁ := (antidiagonal n).map ⟨fun p => (13 * p.1, 13 * p.2), fun p q h => by
      simp only [Prod.mk.injEq] at h; ext <;> omega⟩) ?_ ?_]
  · rw [sum_map]
    refine sum_congr rfl fun p _ => ?_
    simp only [Function.Embedding.coeFn_mk, coeff_ex, coeff_U]
    rw [if_pos (dvd_mul_right 13 _), Nat.mul_div_cancel_left _ (by norm_num)]
  · intro p hp
    simp only [mem_map, mem_antidiagonal, Function.Embedding.coeFn_mk] at hp ⊢
    obtain ⟨q, hq, rfl⟩ := hp
    omega
  · intro p hp hp'
    simp only [mem_antidiagonal] at hp
    rw [coeff_ex]
    split_ifs with h
    · exfalso; apply hp'
      obtain ⟨c, hc⟩ := h
      simp only [mem_map, mem_antidiagonal, Function.Embedding.coeFn_mk]
      refine ⟨(c, (p.2) / 13), ?_, ?_⟩ <;> [skip; ext] <;> simp only <;> omega
    · rw [zero_mul]

/-! ### the eta quotients -/

noncomputable def E13 : PS := V E1
noncomputable def E169 : PS := V (V E1)

lemma isUnit_E13 : IsUnit E13 := isUnit_ex _ isUnit_E1
lemma isUnit_E169 : IsUnit E169 := isUnit_ex _ isUnit_E13

/-- `g = q E₁₃²/E₁²`. -/
noncomputable def g : PS := X * E13 ^ 2 * Ring.inverse E1 ^ 2

/-- `φ = q⁷ E₁₆₉/E₁`. -/
noncomputable def φ : PS := X ^ 7 * E169 * Ring.inverse E1

lemma inv_E1_sq : Ring.inverse E1 ^ 2 * E1 ^ 2 = 1 := by
  rw [← mul_pow, Ring.inverse_mul_cancel _ isUnit_E1, one_pow]

/-- `φ² = g · V(g)`. -/
lemma V_X : V X = X ^ 13 := by simp [ex]

lemma V_inv_E1 : V (Ring.inverse E1) * E13 = 1 := by
  rw [E13, ← map_mul, Ring.inverse_mul_cancel _ isUnit_E1, map_one]

lemma φ_sq : φ ^ 2 = g * V g := by
  have h := V_inv_E1
  rw [φ, g, map_mul, map_mul, map_pow, map_pow, V_X, show V E13 = E169 from rfl]
  linear_combination (-(X ^ 14 * E169 ^ 2 * Ring.inverse E1 ^ 2) * (V (Ring.inverse E1) * E13 + 1)) * h

/-- `η_a = (q^a;q¹³)_∞ (q^{13−a};q¹³)_∞`. -/
noncomputable def ηP (a : ℕ) : PS := Pinf a 13 * Pinf (13 - a) 13

lemma isUnit_ηP {a : ℕ} (h0 : 1 ≤ a) (h1 : a < 13) : IsUnit (ηP a) :=
  (isUnit_Pinf a 13 h0 (by norm_num)).mul (isUnit_Pinf (13 - a) 13 (by omega) (by norm_num))

noncomputable def c0 : PS := ηP 4 * Ring.inverse (ηP 2)
noncomputable def c1 : PS := -(ηP 6 * Ring.inverse (ηP 3))
noncomputable def c2 : PS := -(ηP 2 * Ring.inverse (ηP 1))
noncomputable def c5 : PS := ηP 5 * Ring.inverse (ηP 4)
noncomputable def c9 : PS := X * ηP 1 * Ring.inverse (ηP 6)
noncomputable def c12 : PS := -(ηP 3 * Ring.inverse (ηP 5))

end Atkin13
