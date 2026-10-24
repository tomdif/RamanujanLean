/-
# `Λ_ℓ(u) = j(u; Q) / (1 − Q^ℓ / u)` as an entire series in `x`, for `u = cb t^{eb} x^d`

With `v = Q^{−ℓ} u`: `Λ_ℓ(u) = (−1)^{ℓ+1} Q^{−C(ℓ,2)} v^{1−ℓ} Λ₀(v)`, `Λ₀(v) = j(v)/(1 − v)` (`lam0S`).

* `lamX_rel` — `(1 − Q^ℓ/u) Λ_ℓ(u) = j(u)` at every monomial point;
* `lamX_spec` — at `u = Q^ℓ` the value is `(−1)^{ℓ+1} Q^{−C(ℓ,2)} Λ₀(1)`.
-/
import RamanujanTau.MTC.Lambda
import RamanujanTau.MTC.EntSum

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

lemma mono_ext_L {E E' : ℤ} {C C' : ℂ} (hE : E = E') (hC : C = C') : mono E C = mono E' C' := by
  subst hE hC; rfl

lemma neg_mono (E : ℤ) (C : ℂ) : -(mono E C : L) = mono E (-C) := by simp [mono]

section LamX
variable {N : ℕ} (hN : 1 ≤ N)

/-- the scalar `(−1)^{ℓ+1} Q^{−C(ℓ,2)} β^{1−ℓ}`, `β = cb t^{eb − Nℓ}`. -/
noncomputable def lamScal (ℓ eb : ℤ) (cb : ℂ) : L :=
  mono (-(N * c2 ℓ) + (eb - N * ℓ) * (1 - ℓ)) ((-1) ^ (ℓ + 1) * cb ^ (1 - ℓ))

/-- the series of `x ↦ Λ_ℓ(cb t^{eb} x^d)`. -/
noncomputable def lamX (ℓ d eb : ℤ) (cb : ℂ) : ℤ → L :=
  fun k => lamScal (N := N) ℓ eb cb * shiftS (subst (lam0S hN) d (eb - N * ℓ) cb) (d * (ℓ - 1)) k

lemma lamX_ent (ℓ : ℤ) {d : ℤ} (hd : d ≠ 0) (eb : ℤ) (cb : ℂ) : Ent (lamX hN ℓ d eb cb) :=
  (((lam0S_ent hN).subst hd _ _).shift _).smul _

lemma lamX_ev (ℓ : ℤ) {d : ℤ} (hd : d ≠ 0) (eb : ℤ) (cb : ℂ) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (lamX hN ℓ d eb cb) ex cx = lamScal (N := N) ℓ eb cb * mono (-(ex * (d * (ℓ - 1)))) (cx ^ (-(d * (ℓ - 1)))) *
      ev (lam0S hN) (eb - N * ℓ + d * ex) (cb * cx ^ d) := by
  unfold lamX
  rw [ev_smul (((lam0S_ent hN).subst hd _ _).shift _), MTC.ev_shift ((lam0S_ent hN).subst hd _ _) _ _ hcx,
    ev_subst (lam0S_ent hN) hd, ← mul_assoc]

/-- `(1 − Q^ℓ/u) Λ_ℓ(u) = j(u)`. -/
theorem lamX_rel (ℓ : ℤ) {d : ℤ} (hd : d ≠ 0) (eb : ℤ) {cb : ℂ} (hcb : cb ≠ 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    (1 - mono (N * ℓ - (eb + d * ex)) (cb * cx ^ d)⁻¹) * ev (lamX hN ℓ d eb cb) ex cx = θ hN (eb + d * ex) (cb * cx ^ d) := by
  have hc : cb * cx ^ d ≠ 0 := mul_ne_zero hcb (zpow_ne_zero _ hcx)
  rw [lamX_ev hN ℓ hd eb cb ex hcx]
  have hrel := lam0S_rel hN (eb - N * ℓ + d * ex) hc
  have hsh := θ_qshift hN (eb - N * ℓ + d * ex) hc ℓ
  rw [show eb - N * ℓ + d * ex + N * ℓ = eb + d * ex by ring] at hsh
  rw [hsh, ← hrel]
  -- `1 − Q^ℓ/u = −(1 − v)/v` and the scalar bookkeeping
  have hv : (1 : L) - mono (N * ℓ - (eb + d * ex)) (cb * cx ^ d)⁻¹ =
      -(mono (-(eb - N * ℓ + d * ex)) (cb * cx ^ d)⁻¹) * (1 - mono (eb - N * ℓ + d * ex) (cb * cx ^ d)) := by
    have h1 : mono (-(eb - N * ℓ + d * ex)) (cb * cx ^ d)⁻¹ * mono (eb - N * ℓ + d * ex) (cb * cx ^ d) = 1 := by
      rw [mono_mul, neg_add_cancel, inv_mul_cancel₀ hc]; rfl
    have h2 : mono (N * ℓ - (eb + d * ex)) (cb * cx ^ d)⁻¹ = mono (-(eb - N * ℓ + d * ex)) (cb * cx ^ d)⁻¹ :=
      mono_ext_L (by ring) rfl
    rw [h2]
    linear_combination (-1 : L) * h1
  rw [hv]
  have hm : -(mono (-(eb - N * ℓ + d * ex)) (cb * cx ^ d)⁻¹) * (lamScal (N := N) ℓ eb cb *
      mono (-(ex * (d * (ℓ - 1)))) (cx ^ (-(d * (ℓ - 1))))) =
      mono (-(N * c2 (ℓ + 1)) - (eb - N * ℓ + d * ex) * ℓ + N * ℓ) ((-1) ^ ℓ * (cb * cx ^ d) ^ (-ℓ)) := by
    unfold lamScal
    simp only [mono_mul, neg_mul, neg_mono]
    apply mono_ext_L
    · rw [c2_succ]; ring
    · have hx' : cx ^ d ≠ 0 := zpow_ne_zero _ hcx
      rw [zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0), show (1 : ℤ) - ℓ = -ℓ + 1 by ring, zpow_add_one₀ hcb,
        show -(d * (ℓ - 1)) = -(d * ℓ) + d by ring, zpow_add₀ hcx, mul_zpow, ← zpow_mul,
        show d * -ℓ = -(d * ℓ) by ring]
      field_simp
      try ring
  linear_combination (1 - mono (eb - N * ℓ + d * ex) (cb * cx ^ d)) * ev (lam0S hN) (eb - N * ℓ + d * ex) (cb * cx ^ d) * hm

/-- the special value at `u = Q^ℓ`. -/
theorem lamX_spec (ℓ : ℤ) {d : ℤ} (hd : d ≠ 0) (eb : ℤ) {cb : ℂ} (hcb : cb ≠ 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0)
    (he : eb + d * ex = N * ℓ) (hc : cb * cx ^ d = 1) :
    ev (lamX hN ℓ d eb cb) ex cx = mono (-(N * c2 ℓ)) ((-1) ^ (ℓ + 1)) * kap hN := by
  rw [lamX_ev hN ℓ hd eb cb ex hcx, show eb - N * ℓ + d * ex = 0 by linarith, hc, kap]
  congr 1
  unfold lamScal
  rw [mono_mul]
  apply mono_ext_L
  · have : eb = N * ℓ - d * ex := by linarith
    rw [this]; ring
  · have hcb' : cb = (cx ^ d)⁻¹ := by field_simp; linear_combination hc
    rw [hcb', inv_zpow', ← zpow_mul, mul_assoc, ← zpow_add₀ hcx,
      show d * -(1 - ℓ) + -(d * (ℓ - 1)) = 0 by ring, zpow_zero, mul_one]

end LamX

end MTC
