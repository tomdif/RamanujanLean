import RamanujanTau.DBound.DB
import RamanujanTau.DBound.Sqrt

/-!
# (HW) `E^s W ∈ B_E(r)` from (I2), (I3) and `G = E/V(E) ∈ B_E(r)`

In `ℤ_ℓ⟦q⟧`, with `P = (q;q)_∞`, `P⁻¹ = Σ p(n)qⁿ`, `V = (q ↦ q^ℓ)` (`PowerSeries.expand ℓ`):

* `Ql = E·V(P)²/P^{2ℓ}` (`Q = E·η(ℓz)²/η(z)^{2ℓ}`), `Gl = E/V(E)`, `W = V²(P)/P^{ℓ²}`.
* **`eta_identity_PS`**: `(E^sW)² = Q^ℓ·V(Q)·G` (the identity `AtkinOBrien.eta_identity`, in `ℤ_ℓ⟦q⟧`).
* **`EsW_cong`**: `E^sW ≡ 1 (mod ℓ)` (Frobenius: `(q;q)^{ℓ²} ≡ (q^{ℓ²};q^{ℓ²}) mod ℓ`, `E ≡ 1`).

Hypotheses (all in sharp Katz-coordinate form, `v_i` = valuation of the `i`-th Katz coordinate):
* **`HQ`** (I2): `v_i(Q) ≥ ⌈ℓi/(ℓ+1)⌉`, i.e. `Q ∈ B_E(r^ℓ)` for every `v(r) < 1/(ℓ+1)`;
* **`HV`** (I3): `V` maps `{v_i ≥ ⌈ℓi/(ℓ+1)⌉}` into `{v_i ≥ ⌈i/(ℓ+1)⌉}`, i.e. `V(B_E(r^ℓ)) ⊆ B_E(r)`;
* **`HG`** (the `G`-half of I1): `v_i(E/V(E)) ≥ ⌈i/(ℓ+1)⌉`, i.e. `G ∈ B_E(r)`.

**`HW_of`**: `HQ → HV → HG → HW`. Proof: `Q^ℓ`, `V(Q)`, `G` all lie in the `⌈i/(ℓ+1)⌉`-class
(`Ap_mul`), so `(E^sW)²` does; `E^sW ≡ 1 (mod ℓ)`, so `sqrt_Ap` (Hensel/binomial square root, `ℓ` odd)
puts `E^sW` in the class; `isKatz_of_Ap` gives the Katz expansion.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace DBound
open MvPolynomial ModP AtkinOBrienFinal AtkinOBrien PowerSeries MockTheta5.JTP

variable (ℓ : ℕ) [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-- `V = (q ↦ q^ℓ)` on `ℤ_ℓ⟦q⟧`. -/
noncomputable def Vl : PS ℓ →ₐ[ℤ_[ℓ]] PS ℓ := PowerSeries.expand ℓ hℓp.out.ne_zero

/-- `(q;q)_∞ ∈ ℤ_ℓ⟦q⟧`. -/
noncomputable def Pl : PS ℓ := PowerSeries.map (Int.castRingHom ℤ_[ℓ]) qfacInf
/-- `1/(q;q)_∞ ∈ ℤ_ℓ⟦q⟧`. -/
noncomputable def Pinv : PS ℓ := PowerSeries.map (Int.castRingHom ℤ_[ℓ]) partitionGF

/-- **`Q = E·η(ℓz)²/η(z)^{2ℓ} = E·V(P)²/P^{2ℓ}`.** -/
noncomputable def Ql : PS ℓ := E ℓ hℓ * Vl ℓ (Pl ℓ) ^ 2 * Pinv ℓ ^ (2 * ℓ)

/-- **`G = E/V(E)`.** -/
noncomputable def Gl : PS ℓ := E ℓ hℓ * Vl ℓ (Einv ℓ hℓ)

variable {ℓ}

lemma Pl_mul_Pinv : Pl ℓ * Pinv ℓ = 1 := by
  rw [Pl, Pinv, ← map_mul, BoylanWebb.qfac_mul_pgf, map_one]

lemma expand_congr {R : Type*} [CommRing R] {a b : ℕ} (h : a = b) (ha : a ≠ 0) (hb : b ≠ 0)
    (φ : PowerSeries R) : PowerSeries.expand a ha φ = PowerSeries.expand b hb φ := by
  subst h; rfl

/-- `W = V(V(P)) · P^{-ℓ²}`. -/
lemma Wl_eq : Wl ℓ = Vl ℓ (Vl ℓ (Pl ℓ)) * Pinv ℓ ^ (ℓ ^ 2) := by
  rw [Wl, Wz, map_mul, map_pow]
  congr 1
  show PowerSeries.map (Int.castRingHom ℤ_[ℓ]) (PowerSeries.expand (ℓ ^ 2) _ qfacInf) = _
  rw [PowerSeries.map_expand, Vl, Pl, ← PowerSeries.expand_mul]
  exact expand_congr (by ring) _ _ _

/-- **Step 1's exact identity in `ℤ_ℓ⟦q⟧`**: `(E^sW)² = Q^ℓ·V(Q)·G`. -/
theorem eta_identity_PS :
    (E ℓ hℓ ^ sN ℓ * Wl ℓ) * (E ℓ hℓ ^ sN ℓ * Wl ℓ) = Ql ℓ hℓ ^ ℓ * Vl ℓ (Ql ℓ hℓ) * Gl ℓ hℓ := by
  have h1 : Vl ℓ (Pl ℓ) * Vl ℓ (Pinv ℓ) = 1 := by rw [← map_mul, Pl_mul_Pinv, map_one]
  have h3 : Vl ℓ (E ℓ hℓ) * Vl ℓ (Einv ℓ hℓ) = 1 := by rw [← map_mul, E_mul_Einv, map_one]
  have hs := two_sN hℓ
  rw [Wl_eq, Ql, Gl, map_mul, map_mul, map_pow, map_pow]
  calc (E ℓ hℓ ^ sN ℓ * (Vl ℓ (Vl ℓ (Pl ℓ)) * Pinv ℓ ^ ℓ ^ 2)) *
        (E ℓ hℓ ^ sN ℓ * (Vl ℓ (Vl ℓ (Pl ℓ)) * Pinv ℓ ^ ℓ ^ 2))
      = E ℓ hℓ ^ (2 * sN ℓ) * Vl ℓ (Vl ℓ (Pl ℓ)) ^ 2 * Pinv ℓ ^ (2 * ℓ ^ 2) := by ring
    _ = E ℓ hℓ ^ (ℓ + 1) * Vl ℓ (Vl ℓ (Pl ℓ)) ^ 2 * Pinv ℓ ^ (2 * ℓ ^ 2) *
          ((Vl ℓ (Pl ℓ) * Vl ℓ (Pinv ℓ)) ^ (2 * ℓ) * (Vl ℓ (E ℓ hℓ) * Vl ℓ (Einv ℓ hℓ))) := by
        rw [h1, h3, hs]; ring
    _ = _ := by ring

/-- **`E^sW ≡ 1 (mod ℓ)`.** -/
theorem EsW_cong : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (E ℓ hℓ ^ sN ℓ * Wl ℓ) = 1 := by
  rw [map_mul, map_pow, map_E, one_pow, one_mul, Wl, ModP.psmap_map,
    show (PadicInt.toZMod (p := ℓ)).comp (Int.castRingHom ℤ_[ℓ]) = Int.castRingHom (ZMod ℓ) from
      RingHom.ext_int _ _]
  change TauCong.Ψ ℓ (Wz ℓ) = 1
  rw [Wz, map_mul, map_pow, ← TauCong.frob_qfacInf ℓ 2, ← mul_pow, ← map_mul,
    BoylanWebb.qfac_mul_pgf, map_one, one_pow]

/-! ### the hypotheses -/

variable (ℓ) in
/-- `v_i ≥ ⌈ℓi/(ℓ+1)⌉`: membership in `B_E(r^ℓ)` for all `v(r) < 1/(ℓ+1)`. -/
def InBp (f : PS ℓ) : Prop :=
  ∃ c : ℕ → Poly ℓ, IsKatz ℓ hℓ c f ∧
    ∀ i : ℕ, AtkinOBrien.Dvd (ℓ : ℤ_[ℓ]) (⌈(ℓ : ℚ) * i / ((ℓ : ℚ) + 1)⌉).toNat (c i)

variable (ℓ) in
/-- `v_i ≥ ⌈i/(ℓ+1)⌉`: membership in `B_E(r)` for all `v(r) < 1/(ℓ+1)`. -/
def InB1 (f : PS ℓ) : Prop :=
  ∃ c : ℕ → Poly ℓ, IsKatz ℓ hℓ c f ∧
    ∀ i : ℕ, AtkinOBrien.Dvd (ℓ : ℤ_[ℓ]) (⌈(i : ℚ) / ((ℓ : ℚ) + 1)⌉).toNat (c i)

variable (ℓ) in
/-- **(I2), sharp Katz form**: `Q ∈ B_E(r^ℓ)`. -/
def HQ : Prop := InBp ℓ hℓ (Ql ℓ hℓ)

variable (ℓ) in
/-- **(I3), Katz form**: `V(B_E(r^ℓ)) ⊆ B_E(r)`. -/
def HV : Prop := ∀ f : PS ℓ, InBp ℓ hℓ f → InB1 ℓ hℓ (Vl ℓ f)

variable (ℓ) in
/-- **(I1, `G`-part)**: `G = E/V(E) ∈ B_E(r)`. -/
def HG : Prop := InB1 ℓ hℓ (Gl ℓ hℓ)

lemma HW_iff : HW ℓ hℓ ↔ InB1 ℓ hℓ (E ℓ hℓ ^ sN ℓ * Wl ℓ) := Iff.rfl

/-! ### assembly -/

lemma B1_mul (k l m : ℕ) (h : m ≤ k + l) : Bq ℓ 0 m ≤ Bq ℓ 0 k + Bq ℓ 0 l := by
  simpa using Bq_mul (ℓ := ℓ) 0 0 k l m h

lemma B1_zero : Bq ℓ 0 0 = 0 := by simp [Bq]

lemma Ap_of_InB1 {f : PS ℓ} (h : InB1 ℓ hℓ f) : Ap hℓ (Bq ℓ 0) f := by
  obtain ⟨c, hc, hcb⟩ := h
  exact Ap_of_isKatz hc fun i => by simpa [Bq] using hcb i

lemma Ap_of_InBp {f : PS ℓ} (h : InBp ℓ hℓ f) : Ap hℓ (Bq ℓ 0) f := by
  obtain ⟨c, hc, hcb⟩ := h
  refine Ap_of_isKatz hc fun i => Dvd_mono ?_ (hcb i)
  simp only [Bq, sub_zero]
  have hpos : (0 : ℚ) < (ℓ : ℚ) + 1 := by positivity
  refine Int.toNat_le_toNat (Int.ceil_mono (div_le_div_of_nonneg_right ?_ hpos.le))
  have : (1 : ℚ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
  have : (0 : ℚ) ≤ i := by positivity
  nlinarith

lemma Ap_pow {B : ℕ → ℕ} (hB : ∀ k l m, m ≤ k + l → B m ≤ B k + B l) (hB0 : B 0 = 0) {f : PS ℓ}
    (hf : Ap hℓ B f) (n : ℕ) : Ap hℓ B (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact Ap_one hB0
  | succ n ih => rw [pow_succ]; exact Ap_mul hB ih hf

/-- **(HW) from (I2), (I3) and `G ∈ B_E(r)`.** -/
theorem HW_of (hQ : HQ ℓ hℓ) (hV : HV ℓ hℓ) (hG : HG ℓ hℓ) : HW ℓ hℓ := by
  have hsq : Ap hℓ (Bq ℓ 0) ((E ℓ hℓ ^ sN ℓ * Wl ℓ) * (E ℓ hℓ ^ sN ℓ * Wl ℓ)) := by
    rw [eta_identity_PS hℓ]
    exact Ap_mul B1_mul (Ap_mul B1_mul (Ap_pow hℓ B1_mul B1_zero (Ap_of_InBp hℓ hQ) ℓ)
      (Ap_of_InB1 hℓ (hV _ hQ))) (Ap_of_InB1 hℓ hG)
  have h1 : Dvd (ℓ : ℤ_[ℓ]) 1 (E ℓ hℓ ^ sN ℓ * Wl ℓ - 1) := by
    obtain ⟨y, hy⟩ := PS_dvd_of_map (E ℓ hℓ ^ sN ℓ * Wl ℓ - 1)
      (by rw [map_sub, EsW_cong hℓ, map_one, sub_self])
    exact ⟨y, by rw [pow_one, hy]⟩
  obtain ⟨c, hc, hcb⟩ := isKatz_of_Ap (sqrt_Ap B1_mul B1_zero h1 hsq)
  exact ⟨c, hc, fun i => by simpa [Bq] using hcb i⟩

/-- **(DB) from (UB), (I2), (I3), and `G ∈ B_E(r)`.** -/
theorem DB_of_UB_I2_I3 (hUB : UB ℓ hℓ) (hQ : HQ ℓ hℓ) (hV : HV ℓ hℓ) (hG : HG ℓ hℓ) : DB ℓ hℓ :=
  DB_of_UB hℓ hUB (HW_of hℓ hQ hV hG)

end DBound
