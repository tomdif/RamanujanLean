/-
# Theta spaces and the zero count

Fix `Q = t^{NQ}`. For `m : ℕ` and a monomial multiplier `μ = mono eμ cμ`, the theta space
`Th NQ m μ ⊆ (ℤ → L)` consists of the bilateral series `F` with `Q^k F_k = μ F_{k+m}`, i.e.
`F(Qx) = μ x^{−m} F(x)`.

* `Th.closed` — `F (i + m j) = μ^{−j} Q^{ij + m C(j,2)} F i`; elements are entire (`Th.ent`).
* `Th.ev_shift` / `mem_Th_of_ev` — membership is equivalent to the value-level functional equation.
* `thS` — the theta series `j(x/p; Q)` of a point `p`, an element of `Th 1 (−p)`.
-/
import RamanujanTau.MTC.Conv

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

/-! ## Quadratic domination -/

lemma two_c2' (k : ℤ) : 2 * c2 k = k * (k - 1) := two_c2 k

/-- a positive multiple of `C(j,2)` dominates every linear function of `|j|`. -/
lemma quad_dom {a : ℤ} (ha : 1 ≤ a) (B : ℤ) : ∃ C, ∀ j : ℤ, B * |j| ≤ a * c2 j + C := by
  refine ⟨(|B| + 1) ^ 2, fun j => ?_⟩
  have h2 := two_c2' j
  have h0 := c2_nonneg j
  have hc : c2 j ≤ a * c2 j := le_mul_of_one_le_left h0 ha
  have hj : |j| * |j| = j * j := abs_mul_abs_self j
  have hjb : j ≤ |j| := le_abs_self j
  have hB : B ≤ |B| := le_abs_self B
  nlinarith [abs_nonneg j, abs_nonneg B, sq_nonneg (|j| - |B| - 1)]

/-! ## The space -/

section Th
variable (NQ : ℕ)

/-- `F(Qx) = μ x^{−m} F(x)`, coefficientwise `Q^k F_k = μ F_{k+m}`. -/
def Th (m : ℕ) (μ : L) : Submodule L (ℤ → L) where
  carrier := {F | ∀ k, μ * F (k + m) = mono (NQ * k) 1 * F k}
  add_mem' := by
    intro F G hF hG k
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    rw [mul_add, mul_add, hF k, hG k]
  zero_mem' := by intro k; simp
  smul_mem' := by
    intro a F hF k
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    rw [mul_left_comm, hF k]; ring

variable {NQ}

lemma mem_Th {m : ℕ} {μ : L} {F : ℤ → L} :
    F ∈ Th NQ m μ ↔ ∀ k, μ * F (k + m) = mono (NQ * k) 1 * F k := Iff.rfl

/-- closed form along residue classes. -/
lemma Th.closed {m : ℕ} {eμ : ℤ} {cμ : ℂ} (hcμ : cμ ≠ 0) {F : ℤ → L} (hF : F ∈ Th NQ m (mono eμ cμ))
    (i j : ℤ) :
    F (i + m * j) = mono (-(eμ * j) + NQ * (i * j + m * c2 j)) (cμ ^ (-j)) * F i := by
  have hμ : mono eμ cμ * mono (-eμ) cμ⁻¹ = 1 := by
    rw [mono_mul, add_neg_cancel, mul_inv_cancel₀ hcμ]; rfl
  have step : ∀ j : ℤ, F (i + m * (j + 1)) = mono (-eμ + NQ * (i + m * j)) cμ⁻¹ * F (i + m * j) := by
    intro j
    have h := hF (i + m * j)
    rw [show i + m * j + m = i + m * (j + 1) by ring] at h
    calc F (i + m * (j + 1)) = mono (-eμ) cμ⁻¹ * (mono eμ cμ * F (i + m * (j + 1))) := by
          rw [← mul_assoc, mul_comm (mono (-eμ) cμ⁻¹), hμ, one_mul]
      _ = _ := by rw [h, ← mul_assoc, mono_mul, mul_one]
  induction j using Int.induction_on with
  | zero => simp [c2]
  | succ j ih =>
      rw [step, ih, ← mul_assoc, mono_mul]
      congr 2
      · rw [c2_succ]; ring
      · rw [show -((j : ℤ) + 1) = -1 + -(j : ℤ) by ring, zpow_add₀ hcμ, zpow_neg_one]
  | pred j ih =>
      have h := step (-(j : ℤ) - 1)
      rw [show -(j : ℤ) - 1 + 1 = -j by ring, ih] at h
      have hne : mono (-eμ + NQ * (i + m * (-(j : ℤ) - 1))) cμ⁻¹ ≠ 0 := by
        rw [mono, Ne, single_eq_zero_iff]; exact inv_ne_zero hcμ
      have h' : F (i + m * (-(j : ℤ) - 1)) = (mono (-eμ + NQ * (i + m * (-(j : ℤ) - 1))) cμ⁻¹)⁻¹ *
          (mono (-(eμ * -(j : ℤ)) + NQ * (i * -(j : ℤ) + m * c2 (-(j : ℤ)))) (cμ ^ (- -(j : ℤ))) * F i) := by
        rw [eq_inv_mul_iff_mul_eq₀ hne]; exact h.symm
      rw [h', ← mul_assoc, mono, inv_single, single_mul_single]
      congr 2
      · have := c2_succ (-(j : ℤ) - 1)
        rw [show -(j : ℤ) - 1 + 1 = -j by ring] at this
        rw [this]; ring
      · rw [inv_inv, neg_neg, show -(-(j : ℤ) - 1) = j + 1 by ring, zpow_add_one₀ hcμ]; ring

/-- elements of a theta space with `m ≥ 1` are entire. -/
lemma Th.ent {m : ℕ} (hm : 1 ≤ m) {eμ : ℤ} {cμ : ℂ} (hcμ : cμ ≠ 0) (hNQ : 1 ≤ NQ) {F : ℤ → L}
    (hF : F ∈ Th NQ m (mono eμ cμ)) : Ent F := by
  classical
  intro A
  have hn : ∀ i, ∃ n, vge (F i) n := fun i => exists_vge (F i)
  set nb : ℤ → ℤ := fun i => Classical.choose (hn i)
  have hnb : ∀ i, vge (F i) (nb i) := fun i => Classical.choose_spec (hn i)
  set C0 := ∑ i ∈ Finset.range m, |nb i|
  have hC0 : ∀ i : ℤ, 0 ≤ i → i < m → vge (F i) (-C0) := by
    intro i h0 h1
    refine vge_mono (hnb i) ?_
    have hmem : i.toNat ∈ Finset.range m := Finset.mem_range.mpr (by omega)
    have := Finset.single_le_sum (f := fun i : ℕ => |nb i|) (fun _ _ => abs_nonneg _) hmem
    simp only [Int.toNat_of_nonneg h0] at this
    have := neg_abs_le (nb i)
    omega
  have hmq : 1 ≤ (NQ : ℤ) * m := by
    have : (1 : ℤ) ≤ NQ := by exact_mod_cast hNQ
    have : (1 : ℤ) ≤ m := by exact_mod_cast hm
    nlinarith
  obtain ⟨C1, hC1⟩ := quad_dom hmq (|A| * m + |eμ| + NQ * m)
  refine ⟨C1 + C0 + |A| * m, fun k => ?_⟩
  have hm0 : (0 : ℤ) < m := by exact_mod_cast hm
  set i := k % m
  set j := k / m
  have hk : k = i + m * j := (Int.emod_add_ediv k m).symm
  have hi0 : 0 ≤ i := Int.emod_nonneg _ (by omega)
  have hi1 : i < m := Int.emod_lt_of_pos _ hm0
  rw [hk, Th.closed hcμ hF i j]
  refine vge_mono (vge_mul (vge_single _ _) (hC0 i hi0 hi1)) ?_
  have hb := hC1 j
  have h1 : |i + m * j| ≤ m + m * |j| := by
    calc |i + m * j| ≤ |i| + |m * j| := abs_add_le _ _
      _ ≤ m + m * |j| := by rw [abs_mul, abs_of_nonneg hi0, abs_of_pos hm0]; linarith
  have h2 : -(|eμ| * |j|) ≤ -(eμ * j) := by
    have := le_abs_self (eμ * j); rw [abs_mul] at this; linarith
  have h3 : -(NQ * m * |j|) ≤ NQ * (i * j) := by
    have hij : -(i * |j|) ≤ i * j := by
      have := neg_abs_le (i * j); rw [abs_mul, abs_of_nonneg hi0] at this; linarith
    have : i * |j| ≤ m * |j| := mul_le_mul_of_nonneg_right hi1.le (abs_nonneg _)
    nlinarith [Int.natCast_nonneg NQ]
  have h4 : A * |i + m * j| ≤ |A| * (m + m * |j|) :=
    (mul_le_mul_of_nonneg_right (le_abs_self A) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg A))
  nlinarith [abs_nonneg A, abs_nonneg j]

/-- value-level functional equation of an element of a theta space. -/
lemma Th.ev_shift {m : ℕ} (hm : 1 ≤ m) {eμ : ℤ} {cμ : ℂ} (hcμ : cμ ≠ 0) (hNQ : 1 ≤ NQ) {F : ℤ → L}
    (hF : F ∈ Th NQ m (mono eμ cμ)) (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    ev F (e + NQ) c = mono eμ cμ * mono (-(e * m)) (c ^ (-(m : ℤ))) * ev F e c := by
  have hE := Th.ent hm hcμ hNQ hF
  have h1 : twist F NQ 1 = fun k => mono eμ cμ * shiftS F m k := by
    funext k; simp only [twist, shiftS, one_zpow]; rw [hF k, mul_comm]
  have := ev_twist hE NQ 1 e c
  rw [mul_one, h1, ev_smul (hE.shift m), MTC.ev_shift hE (m : ℤ) e hc] at this
  rw [← this, mul_assoc]

/-- **membership from values**: an entire series satisfying the value-level functional equation for
infinitely many `c` lies in the theta space. -/
lemma mem_Th_of_ev {m : ℕ} {μ : L} {F : ℤ → L} (hF : Ent F) (e : ℤ) (S : Set ℂ) (hS : S.Infinite)
    (hS0 : ∀ c ∈ S, c ≠ 0)
    (h : ∀ c ∈ S, ev F (e + NQ) c = μ * mono (-(e * m)) (c ^ (-(m : ℤ))) * ev F e c) : F ∈ Th NQ m μ := by
  have hG : Ent (fun k => twist F NQ 1 k - μ * shiftS F m k) := (hF.twist NQ 1).sub ((hF.shift m).smul μ)
  have h0 := eq_zero_of_ev hG e S hS fun c hc => by
    have e1 := ev_sub (hF.twist NQ 1) ((hF.shift m).smul μ) e c
    simp only [Pi.sub_apply] at e1
    rw [show (fun k => twist F NQ 1 k - μ * shiftS F m k) = twist F NQ 1 - fun k => μ * shiftS F m k
      from rfl, e1, ev_twist hF, ev_smul (hF.shift m), MTC.ev_shift hF (m : ℤ) e (hS0 c hc), mul_one, h c hc]
    ring
  intro k
  have := congrFun h0 k
  simp only [twist, shiftS, one_zpow, sub_eq_zero] at this
  rw [← this, mul_comm]

/-! ## The theta series of a point -/

/-- the theta series `j(x/p; Q)` of the point `p = cp t^{ep}`. -/
noncomputable def thS (ep : ℤ) (cp : ℂ) : ℤ → L := fun k => mono (NQ * c2 k - ep * k) ((-1) ^ k * cp ^ (-k))

lemma thS_mem (ep : ℤ) {cp : ℂ} (hcp : cp ≠ 0) : thS (NQ := NQ) ep cp ∈ Th NQ 1 (mono ep (-cp)) := by
  intro k
  simp only [thS, Nat.cast_one, mono_mul, c2_succ, one_mul]
  congr 1
  · ring
  · rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_neg, zpow_neg, zpow_add_one₀ hcp, zpow_one]
    field_simp

lemma thS_ev (hNQ : 1 ≤ NQ) (ep : ℤ) {cp : ℂ} (hcp : cp ≠ 0) (e : ℤ) {c : ℂ} :
    ev (thS (NQ := NQ) ep cp) e c = θ hNQ (e - ep) (c / cp) := by
  have hE : Ent (thS (NQ := NQ) ep cp) := Th.ent le_rfl (neg_ne_zero.mpr hcp) hNQ (thS_mem ep hcp)
  rw [ev_eq hE, θ]
  refine hsum_congr _ _ fun k => ?_
  simp only [evFam_apply, thS, thF, monoFam_apply, thE, thC, mono_mul]
  congr 1
  · ring
  · rw [div_zpow, div_eq_mul_inv, zpow_neg]; ring

end Th

end MTC
