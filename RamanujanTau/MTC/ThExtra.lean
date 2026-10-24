/-
# Closure properties of the theta spaces `Th NQ m μ`

* `Th.base_mul`: `F(Qx) = μx^{−m}F(x)` iterated `k` times: `F ∈ Th (k·NQ) (k·m) (μ^k Q^{−m C(k,2)})`;
* `Th.subst`: `G ∈ Th (d·N) m μ ⟹ G(x^d) ∈ Th N (d·m) μ`;
* `Th.shift_mem`: `x^a F(x) ∈ Th NQ m (Q^a μ)`;
* `conv_mem`: products of elements of theta spaces;
* `θ_qsh`, `θ_shk`: `j(q^k z) = (−1)^k q^{−C(k,2)} z^{−k} j(z)`.
-/
import RamanujanTau.MTC.ThFactor
import RamanujanTau.ALTheta

set_option autoImplicit false

namespace MTC
open ALz HahnSeries

lemma mono_ext_x {E E' : ℤ} {C C' : ℂ} (hE : E = E') (hC : C = C') : (mono E C : L) = mono E' C' := by
  subst hE hC; rfl

section ThX
variable {NQ : ℕ}

lemma Th.congr_μ {m : ℕ} {μ μ' : L} {F : ℤ → L} (h : μ = μ') (hF : F ∈ Th NQ m μ) : F ∈ Th NQ m μ' := h ▸ hF

lemma Th.iter {m : ℕ} {μ : L} {F : ℤ → L} (hF : F ∈ Th NQ m μ) :
    ∀ (k : ℕ) (j : ℤ), μ ^ k * F (j + k * m) = mono (NQ * (k * j + m * c2 k)) 1 * F j
  | 0, j => by simp [c2, show (mono 0 1 : L) = 1 from rfl]
  | k + 1, j => by
    have h1 := hF (j + k * m)
    have h2 := Th.iter hF k j
    rw [show j + ((k + 1 : ℕ) : ℤ) * m = j + k * m + m by push_cast; ring, pow_succ, mul_comm (μ ^ k) μ, mul_assoc,
      mul_left_comm, h1, mul_left_comm, h2, ← mul_assoc, mono_mul]
    congr 1
    exact mono_ext_x (by push_cast; rw [c2_succ]; ring) (by norm_num)

/-- **iterating the functional equation**. -/
lemma Th.base_mul {m : ℕ} {μ : L} {F : ℤ → L} (hF : F ∈ Th NQ m μ) (k : ℕ) :
    F ∈ Th (k * NQ) (k * m) (μ ^ k * mono (-(NQ * m * c2 k)) 1) := by
  intro j
  have h := Th.iter hF k j
  rw [show j + ((k * m : ℕ) : ℤ) = j + k * m by push_cast; ring, mul_comm (μ ^ k), mul_assoc, h, ← mul_assoc,
    mono_mul]
  congr 1
  exact mono_ext_x (by push_cast; ring) (by norm_num)

/-- **substitution `x ↦ x^d`**. -/
lemma Th.subst {m d N : ℕ} {μ : L} {G : ℤ → L} (hd : 0 < d) (hG : G ∈ Th (d * N) m μ) :
    MTC.subst G d 0 1 ∈ Th N (d * m) μ := by
  intro k
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold MTC.subst
  by_cases hk : (d : ℤ) ∣ k
  · obtain ⟨j, rfl⟩ := hk
    have hk2 : (d : ℤ) ∣ d * j + ((d * m : ℕ) : ℤ) := ⟨j + m, by push_cast; ring⟩
    rw [if_pos hk2, if_pos ⟨j, rfl⟩, show (d * j + ((d * m : ℕ) : ℤ)) / d = j + m by
        rw [show (d * j + ((d * m : ℕ) : ℤ)) = d * (j + m) by push_cast; ring, Int.mul_ediv_cancel_left _ hd'],
      Int.mul_ediv_cancel_left _ hd']
    simp only [zero_mul, one_zpow, show (mono 0 1 : L) = 1 from rfl, mul_one]
    have := hG j
    rw [this]
    congr 1
    exact mono_ext_x (by push_cast; ring) rfl
  · have hk2 : ¬ (d : ℤ) ∣ k + ((d * m : ℕ) : ℤ) := fun h => hk (by
      have : (d : ℤ) ∣ ((d * m : ℕ) : ℤ) := ⟨m, by push_cast; ring⟩
      have := dvd_sub h this; simpa using this)
    rw [if_neg hk2, if_neg hk, mul_zero, mul_zero]

/-- **multiplication by `x^a`**. -/
lemma Th.shift_mem {m : ℕ} {μ : L} {F : ℤ → L} (hF : F ∈ Th NQ m μ) (a : ℤ) :
    shiftS F (-a) ∈ Th NQ m (mono (NQ * a) 1 * μ) := by
  intro k
  simp only [shiftS]
  have h := hF (k + -a)
  rw [show k + m + -a = k + -a + m by ring, mul_assoc, h, ← mul_assoc, mono_mul]
  congr 1
  exact mono_ext_x (by ring) (by norm_num)

variable (hNQ : 1 ≤ NQ)
include hNQ

/-- **products**. -/
lemma conv_mem {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) {e₁ e₂ : ℤ} {c₁ c₂ : ℂ} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    {F G : ℤ → L} (hF : F ∈ Th NQ m₁ (mono e₁ c₁)) (hG : G ∈ Th NQ m₂ (mono e₂ c₂)) :
    MTC.conv F G ∈ Th NQ (m₁ + m₂) (mono (e₁ + e₂) (c₁ * c₂)) := by
  have hFE : Ent F := Th.ent hm₁ hc₁ hNQ hF
  have hGE : Ent G := Th.ent hm₂ hc₂ hNQ hG
  refine mem_Th_of_ev (hFE.conv hGE) 0 _ (setNZ_infinite hNQ) (fun c hc => hc) fun c hc => ?_
  rw [ev_conv hFE hGE _ hc, ev_conv hFE hGE _ hc, Th.ev_shift hm₁ hc₁ hNQ hF 0 hc, Th.ev_shift hm₂ hc₂ hNQ hG 0 hc]
  simp only [zero_mul, neg_zero, Nat.cast_add]
  rw [show (-((m₁ : ℤ) + m₂)) = -(m₁ : ℤ) + -(m₂ : ℤ) by ring, zpow_add₀ (show c ≠ 0 from hc)]
  have h1 : mono 0 (c ^ (-(m₁ : ℤ)) * c ^ (-(m₂ : ℤ))) = (mono 0 (c ^ (-(m₁ : ℤ))) : L) * mono 0 (c ^ (-(m₂ : ℤ))) := by
    rw [mono_mul, add_zero]
  have h2 : (mono (e₁ + e₂) (c₁ * c₂) : L) = mono e₁ c₁ * mono e₂ c₂ := by rw [mono_mul]
  rw [h1, h2]; ring

end ThX

section Qsh
variable {N : ℕ} (hN : 1 ≤ N)

/-- `j(qz) = −z⁻¹ j(z)`. -/
lemma θ_qsh (e : ℤ) {c : ℂ} (hc : c ≠ 0) : θ hN (e + N) c = -mono (-e) c⁻¹ * θ hN e c := by
  have h1 := θ_reflect hN (-e) (inv_ne_zero hc)
  rw [inv_inv, show (N : ℤ) - -e = e + N by ring] at h1
  rw [h1, θ_inv hN e hc]

/-- `j(q^k z) = (−1)^k q^{−C(k,2)} z^{−k} j(z)`. -/
lemma θ_shk (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    ∀ k : ℕ, θ hN (e + N * k) c = mono (-(k * e) - N * c2 k) ((-1) ^ k * c ^ (-(k : ℤ))) * θ hN e c
  | 0 => by simp [c2, show (mono 0 1 : L) = 1 from rfl]
  | k + 1 => by
    rw [show e + (N : ℤ) * ((k + 1 : ℕ) : ℤ) = (e + N * k) + N by push_cast; ring, θ_qsh hN _ hc, θ_shk e hc k]
    have hm : (mono (-(e + N * k)) c⁻¹ : L) * mono (-(k * e) - N * c2 k) ((-1) ^ k * c ^ (-(k : ℤ))) =
        -mono (-(((k + 1 : ℕ) : ℤ) * e) - N * c2 ((k + 1 : ℕ) : ℤ)) ((-1) ^ (k + 1) * c ^ (-((k + 1 : ℕ) : ℤ))) := by
      rw [mono_mul, show -(mono (-(((k + 1 : ℕ) : ℤ) * e) - N * c2 ((k + 1 : ℕ) : ℤ))
          ((-1) ^ (k + 1) * c ^ (-((k + 1 : ℕ) : ℤ))) : L) = mono (-(((k + 1 : ℕ) : ℤ) * e) - N * c2 ((k + 1 : ℕ) : ℤ))
          (-((-1) ^ (k + 1) * c ^ (-((k + 1 : ℕ) : ℤ)))) by simp [mono]]
      refine mono_ext_x (by push_cast; rw [c2_succ]; ring) ?_
      rw [pow_succ, show (-((k + 1 : ℕ) : ℤ)) = -(k : ℤ) + -1 by push_cast; ring, zpow_add₀ hc, zpow_neg_one]
      ring
    linear_combination (-θ hN e c) * hm

end Qsh

end MTC
