/-
# R4 (reduction): the off-diagonal clause from a per-quadruple bound

* `lagInt_le_of_inner`: a pointwise bound `E` on the inner `t`-integrals gives `lagInt ≤ h² E`.
* `abs_wc_le`: `|wc(a,b)| ≤ 1` for Selberg's coefficients (`|βSel n| ≤ √n`).
* `QuadOffHyp η B` (named, **provable** — see `docs/SELBERG_KEY.md`, fifth pass): for every
  quadruple `q = (a,b,c,d)` of positive integers, `0 ≤ x ≤ 1`, `|v| ≤ 1`,
  `‖Σ'_{(m,n) off-diagonal} ∫_{T/2}^{3T} Fq‖ ≤ C T^{1−η} (abcd)^B`.
* **`offLag_bound_of_quad`**: `QuadOffHyp η B` with `4θ(1+B) < η` gives the off-diagonal clause
  of `SKSplitHyp'` for the window `φ_T` on `[T/2, 3T]`.
* **`skSplitHyp'_of_diag`**: (diagonal clause for `φ_T`) ∧ `QuadOffHyp η B` ⇒ `SKSplitHyp' θ`.
Level 1 (reductions), level 2 on `QuadOffHyp`.
-/
import RamanujanTau.SelbergKey5.Inner

set_option autoImplicit false

namespace RamanujanTau.SelbergKey5

open Complex MeasureTheory Set Filter Finset RamanujanTau.SelbergKey RamanujanTau.SelbergKey2
  RamanujanTau.SelbergKey4
open scoped Real Interval

/-- A uniform bound on the inner integrals bounds the lag integral. -/
theorem lagInt_le_of_inner {G : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {A B h E : ℝ} (hh : 0 ≤ h)
    (hE : ∀ x ∈ Icc 0 h, ∀ x' ∈ Icc 0 h, |∫ t in A..B, φ t * G (t + x) (x' - x)| ≤ E) :
    lagInt G φ A B h ≤ h ^ 2 * E := by
  unfold lagInt
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hE 0 ⟨le_rfl, hh⟩ 0 ⟨le_rfl, hh⟩)
  refine (le_abs_self _).trans ?_
  rw [← Real.norm_eq_abs]
  have hin : ∀ x ∈ Ι (0:ℝ) h, ‖∫ x' in (0:ℝ)..h, ∫ t in A..B, φ t * G (t + x) (x' - x)‖ ≤ E * h := by
    intro x hx
    rw [uIoc_of_le hh] at hx
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h)
      (f := fun x' => ∫ t in A..B, φ t * G (t + x) (x' - x)) (C := E) fun x' hx' => by
        rw [uIoc_of_le hh] at hx'
        rw [Real.norm_eq_abs]
        exact hE x ⟨hx.1.le, hx.2⟩ x' ⟨hx'.1.le, hx'.2⟩
    rwa [sub_zero, abs_of_nonneg hh] at this
  have := intervalIntegral.norm_integral_le_of_norm_le_const hin
  rw [sub_zero, abs_of_nonneg hh] at this
  calc _ ≤ E * h * h := this
    _ = h ^ 2 * E := by ring

lemma abs_wc_le (y : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |wc (HafnerMV2.βSel y) a b| ≤ 1 := by
  unfold wc
  have har : (0:ℝ) < a := by exact_mod_cast ha
  have hbr : (0:ℝ) < b := by exact_mod_cast hb
  have e : Real.exp (-((Real.log a + Real.log b) / 2)) = (Real.sqrt a * Real.sqrt b)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.rpow_def_of_pos har, Real.rpow_def_of_pos hbr,
      ← Real.exp_add, ← Real.exp_neg]
    congr 1; ring
  rw [e, abs_mul, abs_mul, abs_inv, abs_of_pos (by positivity : 0 < Real.sqrt a * Real.sqrt b)]
  have h1 := HafnerMV2.abs_βSel_le y a
  have h2 := HafnerMV2.abs_βSel_le y b
  have hp : 0 < Real.sqrt a * Real.sqrt b := by positivity
  rw [← div_eq_mul_inv, div_le_one hp]
  exact mul_le_mul h1 h2 (abs_nonneg _) (Real.sqrt_nonneg _)

lemma mem_Q4 {y : ℕ} {q : ℕ × ℕ × ℕ × ℕ} (hq : q ∈ Q4 y) :
    (1 ≤ q.1 ∧ q.1 ≤ y) ∧ (1 ≤ q.2.1 ∧ q.2.1 ≤ y) ∧ (1 ≤ q.2.2.1 ∧ q.2.2.1 ≤ y) ∧
      (1 ≤ q.2.2.2 ∧ q.2.2.2 ≤ y) := by
  unfold Q4 at hq
  simp only [Finset.mem_product, Finset.mem_Icc] at hq
  exact hq

lemma abs_wq_le {y : ℕ} {q : ℕ × ℕ × ℕ × ℕ} (hq : q ∈ Q4 y) : |wq (HafnerMV2.βSel y) q| ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_Q4 hq
  unfold wq
  rw [abs_mul]
  have := abs_wc_le y h1.1 h2.1
  have := abs_wc_le y h3.1 h4.1
  nlinarith [abs_nonneg (wc (HafnerMV2.βSel y) q.1 q.2.1),
    abs_nonneg (wc (HafnerMV2.βSel y) q.2.2.1 q.2.2.2)]

lemma card_Q4 (y : ℕ) : (Q4 y).card = y ^ 4 := by
  unfold Q4; simp [Finset.card_product]; ring

/-- **The per-quadruple off-diagonal bound** (named hypothesis; provable — R2 + R3). -/
def QuadOffHyp (η B : ℝ) : Prop :=
  ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T → ∀ q : ℕ × ℕ × ℕ × ℕ,
    1 ≤ q.1 → 1 ≤ q.2.1 → 1 ≤ q.2.2.1 → 1 ≤ q.2.2.2 → ∀ x v : ℝ, 0 ≤ x → x ≤ 1 → |v| ≤ 1 →
      ‖∑' p : ℕ × ℕ, ∫ t in (T / 2)..(3 * T), Fq T x v q p t‖ ≤
        C * T ^ (1 - η) * ((q.1 * q.2.1 * q.2.2.1 * q.2.2.2 : ℕ) : ℝ) ^ B

/-- The inner integral, bounded by `QuadOffHyp`. -/
theorem abs_inner_le_of_quad {η B θ C T₀ : ℝ} (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hC : 0 ≤ C)
    (H : ∀ T : ℝ, T₀ ≤ T → ∀ q : ℕ × ℕ × ℕ × ℕ,
      1 ≤ q.1 → 1 ≤ q.2.1 → 1 ≤ q.2.2.1 → 1 ≤ q.2.2.2 → ∀ x v : ℝ, 0 ≤ x → x ≤ 1 → |v| ≤ 1 →
        ‖∑' p : ℕ × ℕ, ∫ t in (T / 2)..(3 * T), Fq T x v q p t‖ ≤
          C * T ^ (1 - η) * ((q.1 * q.2.1 * q.2.2.1 * q.2.2.2 : ℕ) : ℝ) ^ B)
    {T : ℝ} (hT : T₀ ≤ T) (hT1 : 1 ≤ T) {x v : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hv : |v| ≤ 1) :
    |∫ t in (T / 2)..(3 * T), phiT T t *
        OffLag (HafnerMV2.βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊ (t + x) v| ≤
      2 * C * T ^ (1 - η + 4 * θ * (1 + B)) := by
  set y := ⌊T ^ θ⌋₊
  have hT0 : 0 < T := by linarith
  have hy : (y : ℝ) ≤ T ^ θ := Nat.floor_le (Real.rpow_nonneg hT0.le _)
  refine (abs_inner_offLag_le _ y hT0.le x v).trans ?_
  have hterm : ∀ q ∈ Q4 y, |wq (HafnerMV2.βSel y) q| *
      ‖∑' p : ℕ × ℕ, ∫ t in (T / 2)..(3 * T), Fq T x v q p t‖ ≤
        C * T ^ (1 - η) * (T ^ θ) ^ (4 * B) := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := mem_Q4 hq
    have hb := H T hT q h1.1 h2.1 h3.1 h4.1 x v hx0 hx1 hv
    have hprod : ((q.1 * q.2.1 * q.2.2.1 * q.2.2.2 : ℕ) : ℝ) ≤ (T ^ θ) ^ 4 := by
      have : ((q.1 * q.2.1 * q.2.2.1 * q.2.2.2 : ℕ) : ℝ) ≤ (y : ℝ) ^ 4 := by
        have : q.1 * q.2.1 * q.2.2.1 * q.2.2.2 ≤ y ^ 4 := by
          calc q.1 * q.2.1 * q.2.2.1 * q.2.2.2 ≤ y * y * y * y := by
                gcongr <;> omega
            _ = y ^ 4 := by ring
        exact_mod_cast this
      exact this.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hy 4)
    have hpow : ((q.1 * q.2.1 * q.2.2.1 * q.2.2.2 : ℕ) : ℝ) ^ B ≤ (T ^ θ) ^ (4 * B) := by
      rw [Real.rpow_mul (Real.rpow_nonneg hT0.le _)]
      have := Real.rpow_le_rpow (Nat.cast_nonneg _) hprod hB
      rwa [← Real.rpow_natCast (T ^ θ) 4] at this
    have hw := abs_wq_le hq
    have hn0 := norm_nonneg (∑' p : ℕ × ℕ, ∫ t in (T / 2)..(3 * T), Fq T x v q p t)
    have hCT : 0 ≤ C * T ^ (1 - η) := mul_nonneg hC (Real.rpow_nonneg hT0.le _)
    calc |wq (HafnerMV2.βSel y) q| * ‖∑' p : ℕ × ℕ, ∫ t in (T / 2)..(3 * T), Fq T x v q p t‖
        ≤ 1 * (C * T ^ (1 - η) * ((q.1 * q.2.1 * q.2.2.1 * q.2.2.2 : ℕ) : ℝ) ^ B) :=
          mul_le_mul hw hb hn0 zero_le_one
      _ ≤ C * T ^ (1 - η) * (T ^ θ) ^ (4 * B) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hpow hCT
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, card_Q4, nsmul_eq_mul] at hsum
  have hy4 : ((y ^ 4 : ℕ) : ℝ) ≤ (T ^ θ) ^ (4 : ℝ) := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    push_cast
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hy 4
  have hfin : ((y ^ 4 : ℕ) : ℝ) * (C * T ^ (1 - η) * (T ^ θ) ^ (4 * B)) ≤
      C * T ^ (1 - η + 4 * θ * (1 + B)) := by
    have hCT : 0 ≤ C * T ^ (1 - η) * (T ^ θ) ^ (4 * B) := by positivity
    calc ((y ^ 4 : ℕ) : ℝ) * (C * T ^ (1 - η) * (T ^ θ) ^ (4 * B))
        ≤ (T ^ θ) ^ (4 : ℝ) * (C * T ^ (1 - η) * (T ^ θ) ^ (4 * B)) :=
          mul_le_mul_of_nonneg_right hy4 hCT
      _ = C * T ^ (1 - η + 4 * θ * (1 + B)) := by
          rw [← Real.rpow_mul hT0.le, ← Real.rpow_mul hT0.le]
          rw [show 1 - η + 4 * θ * (1 + B) = (θ * 4) + ((1 - η) + θ * (4 * B)) by ring,
            Real.rpow_add hT0, Real.rpow_add hT0]
          ring
  push_cast at hsum hfin
  nlinarith [hsum, hfin]

/-- **The off-diagonal clause of `SKSplitHyp'` from `QuadOffHyp`** (window `φ_T` on `[T/2, 3T]`). -/
theorem offLag_bound_of_quad {η B θ : ℝ} (hB : 0 ≤ B) (hθ0 : 0 ≤ θ)
    (hηθ : 4 * θ * (1 + B) < η) (H : QuadOffHyp η B) :
    ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      lagInt (OffLag (HafnerMV2.βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) (phiT T) (T / 2) (3 * T) (K / Real.log T) ≤
        1 / Real.sqrt K * T * (K / Real.log T) ^ 2 := by
  obtain ⟨C, T₁, hC, hH⟩ := H
  intro K hK
  set η' := η - 4 * θ * (1 + B) with hη'
  have hη'0 : 0 < η' := by linarith
  set L : ℝ := 2 * C * Real.sqrt K + 1
  have hL : 1 ≤ L := by have := Real.sqrt_nonneg K; nlinarith
  refine ⟨max (max T₁ (Real.exp K)) (max 1 (L ^ (1 / η'))), fun T hT => ?_⟩
  have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTe : Real.exp K ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT1' : 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTL : L ^ (1 / η') ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT0 : 0 < T := by linarith
  have hlog : K ≤ Real.log T := by
    rw [← Real.log_exp K]; exact Real.log_le_log (Real.exp_pos K) hTe
  have hlogpos : 0 < Real.log T := by linarith
  set h := K / Real.log T
  have hh0 : 0 ≤ h := div_nonneg (by linarith) hlogpos.le
  have hh1 : h ≤ 1 := by rw [div_le_one hlogpos]; exact hlog
  have hE := lagInt_le_of_inner (G := OffLag (HafnerMV2.βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) (φ := phiT T)
    (A := T / 2) (B := 3 * T) (E := 2 * C * T ^ (1 - η + 4 * θ * (1 + B))) hh0
    (fun x hx x' hx' => abs_inner_le_of_quad hB hθ0 hC hH hT1 hT1' hx.1 (hx.2.trans hh1) (by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hx'.1, hx'.2]))
  refine hE.trans ?_
  -- `2C T^{1−η'} ≤ T/√K`
  have hTη : L ≤ T ^ η' := by
    have := Real.rpow_le_rpow (by positivity) hTL hη'0.le
    rwa [← Real.rpow_mul (by linarith), one_div_mul_cancel hη'0.ne', Real.rpow_one] at this
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 (by linarith)
  have hkey : 2 * C * T ^ (1 - η + 4 * θ * (1 + B)) ≤ 1 / Real.sqrt K * T := by
    have e : T ^ (1 - η + 4 * θ * (1 + B)) = T / T ^ η' := by
      rw [show 1 - η + 4 * θ * (1 + B) = 1 - η' by rw [hη']; ring, Real.rpow_sub hT0,
        Real.rpow_one]
    rw [e]
    have hTp : 0 < T ^ η' := Real.rpow_pos_of_pos hT0 _
    rw [mul_div_assoc', div_le_iff₀ hTp, one_div, inv_mul_eq_div, div_mul_eq_mul_div,
      le_div_iff₀ hsK]
    have : 2 * C * Real.sqrt K ≤ T ^ η' := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hT0.le]
  calc h ^ 2 * (2 * C * T ^ (1 - η + 4 * θ * (1 + B))) ≤ h ^ 2 * (1 / Real.sqrt K * T) :=
        mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
    _ = 1 / Real.sqrt K * T * h ^ 2 := by ring

/-- The diagonal clause for the fixed window `φ_T` on `[T/2, 3T]`. -/
def DiagHypT (θ : ℝ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    lagInt (DiagLag (HafnerMV2.βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) (phiT T) (T / 2) (3 * T) (K / Real.log T) ≤
      D / Real.sqrt K * T * (K / Real.log T) ^ 2

/-- **`SKSplitHyp'` from the diagonal clause and `QuadOffHyp`.** -/
theorem skSplitHyp'_of_diag {η B θ : ℝ} (hB : 0 ≤ B) (hθ0 : 0 ≤ θ)
    (hηθ : 4 * θ * (1 + B) < η) (hD : DiagHypT θ) (H : QuadOffHyp η B) : SKSplitHyp' θ := by
  obtain ⟨D, hD0, hDK⟩ := hD
  refine ⟨D, hD0, fun K hK => ?_⟩
  obtain ⟨T₁, h1⟩ := hDK K hK
  obtain ⟨T₂, h2⟩ := offLag_bound_of_quad hB hθ0 hηθ H K hK
  refine ⟨max (max T₁ T₂) 1, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith [le_max_right (max T₁ T₂) 1]
  exact ⟨phiT T, T / 2, 3 * T, admissible_phiT hT0,
    h1 T (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT),
    h2 T (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT)⟩

end RamanujanTau.SelbergKey5
