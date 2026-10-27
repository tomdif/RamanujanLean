/-
# Atkin 11^k: the objects

* `E_k = (q^k;q^k)_∞`, `V : q ↦ q¹¹`, `U = U₁₁ : Σ aₙqⁿ ↦ Σ a₁₁ₙqⁿ`.
* `z = q⁵E₁₁¹²/E₁¹²`, `φ = q⁵E₁₂₁/E₁`.
* Atkin's basis of the integral modular functions on `Γ₀(11)` with poles only at `0` (Paule–Radu, Thm. 3.9):
  `g₂ = U₂(1/f₂) − 1/f₃` with `1/f₂ = q²E₁₁³E₂₂/(E₁E₂³)` and `1/f₃ = q³E₁₁E₂₂³/(E₁³E₂)`. Here `g₂` is defined by
  its theta form `GN(c)/GD(c)` in the eta ratios `c` (`Atkin11CDefs`);
  `g₃` is defined by Atkin's relation (R1) `g₂g₃ = g₂² − g₃ + 11z`; `g₄ = g₂² − g₃`, `g₆ = g₂g₄`.
* `J_{5a+i} = zᵃ·(1, g₂, g₃, g₄, g₆)ᵢ`, and `lc c = Σ_ν c_ν J_ν` for finitely supported `c : ℕ →₀ ℤ`.
-/
import RamanujanTau.Atkin11Bound
import RamanujanTau.Atkin11CDefs
import RamanujanTau.MockTheta5JacobiTriple
import RamanujanTau.MockTheta5Frobenius
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false

namespace Atkin11
open PowerSeries Finset

abbrev PS := PowerSeries ℤ

/-- `q ↦ q^k`. -/
noncomputable def ex (k : ℕ) (hk : k ≠ 0) : PS →+* PS := (PowerSeries.expand k hk).toRingHom

/-- `V : q ↦ q¹¹`. -/
noncomputable abbrev V : PS →+* PS := ex 11 (by norm_num)

lemma coeff_ex (k : ℕ) (hk : k ≠ 0) (n : ℕ) (f : PS) :
    coeff n (ex k hk f) = if k ∣ n then coeff (n / k) f else 0 := by
  simp [ex, PowerSeries.coeff_expand]

/-- `U₁₁`. -/
noncomputable def U (f : PS) : PS := mk fun n => coeff (11 * n) f

/-- `U₂`. -/
noncomputable def U2 (f : PS) : PS := mk fun n => coeff (2 * n) f

lemma coeff_U (n : ℕ) (f : PS) : coeff n (U f) = coeff (11 * n) f := by simp [U]

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
  rw [← sum_subset (s₁ := (antidiagonal n).map ⟨fun p => (11 * p.1, 11 * p.2), fun p q h => by
      simp only [Prod.mk.injEq] at h; ext <;> omega⟩) ?_ ?_]
  · rw [sum_map]
    refine sum_congr rfl fun p _ => ?_
    simp only [Function.Embedding.coeFn_mk, coeff_ex, coeff_U]
    rw [if_pos (dvd_mul_right 11 _), Nat.mul_div_cancel_left _ (by norm_num)]
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
      refine ⟨(c, (p.2) / 11), ?_, ?_⟩ <;> [skip; ext] <;> simp only <;> omega
    · rw [zero_mul]

/-! ### the eta quotients -/

noncomputable def E1 : PS := MockTheta5.JTP.qfacInf
noncomputable def E2 : PS := ex 2 (by norm_num) E1
noncomputable def E11 : PS := V E1
noncomputable def E22 : PS := ex 22 (by norm_num) E1
noncomputable def E121 : PS := V (V E1)

lemma isUnit_E1 : IsUnit E1 := MockTheta5.JTP.isUnit_qfacInf
lemma isUnit_ex {k : ℕ} (hk : k ≠ 0) {f : PS} (hf : IsUnit f) : IsUnit (ex k hk f) := hf.map _
lemma isUnit_E2 : IsUnit E2 := isUnit_ex _ isUnit_E1
lemma isUnit_E11 : IsUnit E11 := isUnit_ex _ isUnit_E1
lemma isUnit_E22 : IsUnit E22 := isUnit_ex _ isUnit_E1
lemma isUnit_E121 : IsUnit E121 := isUnit_ex _ isUnit_E11

/-- `z = q⁵E₁₁¹²/E₁¹²`. -/
noncomputable def z : PS := X ^ 5 * E11 ^ 12 * Ring.inverse E1 ^ 12

/-- `φ = q⁵E₁₂₁/E₁`. -/
noncomputable def φ : PS := X ^ 5 * E121 * Ring.inverse E1

/-- `1/f₂ = q²E₁₁³E₂₂/(E₁E₂³)`. -/
noncomputable def f2i : PS := X ^ 2 * E11 ^ 3 * E22 * Ring.inverse (E1 * E2 ^ 3)

/-- `1/f₃ = q³E₁₁E₂₂³/(E₁³E₂)`. -/
noncomputable def f3i : PS := X ^ 3 * E11 * E22 ^ 3 * Ring.inverse (E1 ^ 3 * E2)

/-- Atkin's `g₂`, in its theta form `g₂ = GN(c)/GD(c)` (`Atkin11CDefs`). It agrees with Atkin's
`U₂(1/f₂) − 1/f₃` (checked numerically); only the theta form is used. -/
noncomputable def g2 : PS := gN * Ring.inverse gD

lemma constantCoeff_g2 : constantCoeff g2 = 0 := by
  rw [g2, map_mul, cc_gN, zero_mul]

lemma isUnit_one_add_g2 : IsUnit (1 + g2) := by
  rw [isUnit_iff_constantCoeff, map_add, constantCoeff_g2]; simp

/-- `g₃`, defined by Atkin's relation `(1 + g₂)g₃ = g₂² + 11z`. -/
noncomputable def g3 : PS := (g2 ^ 2 + 11 * z) * Ring.inverse (1 + g2)

noncomputable def g4 : PS := g2 ^ 2 - g3
noncomputable def g6 : PS := g2 * g4

/-- **(R1)** `g₂g₃ = g₂² − g₃ + 11z`. -/
theorem R1 : g2 * g3 = g2 ^ 2 - g3 + 11 * z := by
  have h : (1 + g2) * g3 = g2 ^ 2 + 11 * z := by
    rw [g3, mul_comm, mul_assoc, Ring.inverse_mul_cancel _ isUnit_one_add_g2, mul_one]
  linear_combination h

/-- `(1, g₂, g₃, g₄, g₆)`. -/
noncomputable def gi : ℕ → PS
  | 0 => 1
  | 1 => g2
  | 2 => g3
  | 3 => g4
  | _ => g6

/-- `J_{5a+i} = zᵃ gᵢ`. -/
noncomputable def J (ν : ℕ) : PS := z ^ (ν / 5) * gi (ν % 5)

lemma J_add_five (ν : ℕ) : J (ν + 5) = z * J ν := by
  rw [J, J, show (ν + 5) / 5 = ν / 5 + 1 by omega, show (ν + 5) % 5 = ν % 5 by omega, pow_succ]; ring

lemma J_mk (a i : ℕ) (hi : i < 5) : J (5 * a + i) = z ^ a * gi i := by
  rw [J, show (5 * a + i) / 5 = a by omega, show (5 * a + i) % 5 = i by omega]

/-- `lc c = Σ_ν c_ν J_ν`. -/
noncomputable abbrev lc : (ℕ →₀ ℤ) →ₗ[ℤ] PS := Finsupp.linearCombination ℤ J

/-- a finitely supported function from a list of pairs. -/
noncomputable def ofList (l : List (ℕ × ℤ)) : ℕ →₀ ℤ := (l.map fun p => Finsupp.single p.1 p.2).sum

lemma lc_ofList (l : List (ℕ × ℤ)) : lc (ofList l) = (l.map fun p => p.2 • J p.1).sum := by
  induction l with
  | nil => simp [ofList]
  | cons p l ih =>
    simp only [ofList, List.map_cons, List.sum_cons, map_add] at ih ⊢
    rw [ih, Finsupp.linearCombination_single]

/-! ### the modular-equation coefficients `e_j` and the seeds -/

noncomputable def eF (j : ℕ) : ℕ →₀ ℤ := ofList (eList j)

/-- the seed row `C^λ_{i,·}` for `λ ≤ 10`, `i ≤ 4`. -/
noncomputable def seedF (lam i : ℕ) : ℕ →₀ ℤ := ofList (seedRows.getD (5 * lam + i) [])

/-- **the inputs** — explicit q-series identities between the objects above, all verified numerically (to
`q^1500`–`q^3000`). All three are proved: `r2` and `modeq` in `Atkin11ModEq` (`r2_proved`, `modeq_proved`),
the seeds in `Atkin11Seed.Seeds` (`seeds_proved`); together `Atkin11.inputs_proved`. -/
structure Inputs : Prop where
  /-- the second Atkin relation (the curve `11a1`). -/
  r2 : g3 ^ 2 = g2 ^ 3 - g2 * g3 - z
  /-- the degree-11 modular equation for `φ` over `ℤ[g₂, g₃, z](q¹¹)`. -/
  modeq : φ ^ 11 = ∑ j ∈ range 11, (-1) ^ j * V (lc (eF (j + 1))) * φ ^ (10 - j)
  /-- the 55 seed relations `U(φ^λ J_i) = Σ_ν C^λ_{i,ν} J_ν`. -/
  seeds : ∀ lam < 11, ∀ i < 5, U (φ ^ lam * J i) = lc (seedF lam i)

end Atkin11
