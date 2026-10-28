/-
# The integral denominator `Dser` is a constant times a unit

For the canonical-subgroup data (`κ.G = Pt(S)`) over `K` algebraically closed with `‖Δ‖ = 1`:
  `Dser = c · U`,  `U ∈ 𝒪⟦z⟧ˣ`,  `‖c‖ = ‖μ‖³`,  `μ = π'(0) = ∏_{h∈S, h≠0} h`    (`Dser_eq`).
Ingredients:
* `wh_pair`: `w(F(z,h)) · w(F(z,-h)) = (ρ_h - z² v(z))³ · unit`, `ρ_h = h² v(h) = 1/x_Q`;
* `Xd_mul_prod`: `Xd · ∏ (1 - x_Q ρ)³ = ∏ (1 - x(T_i+Q) ρ)`, and `‖x(T_i + Q)‖ ≤ 1`
  (`norm_rr_le`), so the right side is a unit of `𝒪⟦z⟧`;
* `map_Dser`: `Dser = Xd · Wst`.
-/
import RamanujanTau.VeluDescent.Sum
import RamanujanTau.VeluDescent.XdFactor

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluDescent
open MvPowerSeries EllipticFormal VeluLubin

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K]

local notation "𝒪" => CanonicalIsogeny.integers K
local notation "jK" => Subring.subtype (CanonicalIsogeny.integers K)

variable {a b : ↥(CanonicalIsogeny.integers K)}

/-- `v(h)`. -/
noncomputable abbrev vpt (a b h : ↥(CanonicalIsogeny.integers K)) : 𝒪 :=
  Lubin.pt (fun _ : Unit => h) (v (shortO a b) : MvPowerSeries Unit 𝒪)

/-- `ρ_h = h² v(h)`. -/
noncomputable abbrev rhoh (a b h : ↥(CanonicalIsogeny.integers K)) : 𝒪 := h ^ 2 * vpt a b h

lemma vpt_neg {h : 𝒪} (h0 : h ≠ 0) (hh : ‖(h : K)‖ < 1) : vpt a b (-h) = vpt a b h := by
  have e := wz_neg a b hh
  rw [wz_eq a b (norm_neg_lt hh), wz_eq a b hh] at e
  have h3 : (-h) ^ 3 ≠ 0 := pow_ne_zero 3 (neg_ne_zero.2 h0)
  apply mul_left_cancel₀ h3
  rw [e]; ring

lemma neg_eq_S_neg (S : Lubin.FinSub (formalGroup (shortO a b))) {h : 𝒪} (hh : h ∈ S.H) :
    S.neg h = -h := by
  have := padd_cancel a b (norm_lt_one_of_tn (S.tn h hh)) (norm_lt_one_of_tn (S.tn _
    (S.neg_mem' hh))) (S.add_neg hh)
  exact this

lemma ev_eq {h : 𝒪} (hh : IsTopologicallyNilpotent h) (g : MvPowerSeries Unit 𝒪) :
    Lubin.ev () h g = C (Lubin.pt (fun _ : Unit => h) g) := by
  have e : Function.update (X : Unit → MvPowerSeries Unit 𝒪) () (C h) = fun _ : Unit => C h := by
    funext u; cases u; rw [Function.update_self]
  rw [Lubin.ev, e]
  exact Lubin.E_const (x := fun _ : Unit => h) (fun _ => hh) g

lemma pt_rho_sub {h z : 𝒪} (hz : IsTopologicallyNilpotent z) :
    Lubin.pt (fun _ : Unit => z) (C (rhoh a b h) - X () ^ 2 * (v (shortO a b) : MvPowerSeries Unit 𝒪)) =
      rhoh a b h - z ^ 2 * vpt a b z := by
  rw [← Lubin.PH_apply (fun _ => hz)]
  simp only [map_sub, map_mul, map_pow, Lubin.PH_apply, Lubin.pt_C, Lubin.pt_X]

/-- `ρ_h - z² v(z) = (z² - h²) · q` with `q` a unit. -/
lemma rho_factor {h : 𝒪} (h0 : h ≠ 0) (hh : ‖(h : K)‖ < 1) :
    ∃ q : MvPowerSeries Unit 𝒪, IsUnit q ∧
      C (rhoh a b h) - X () ^ 2 * (v (shortO a b) : MvPowerSeries Unit 𝒪) =
        (X () ^ 2 - C (h ^ 2)) * q := by
  classical
  have tn := tn_of_norm hh
  have tnn := tn_of_norm (norm_neg_lt hh)
  have hne : h ≠ -h := by
    intro e
    have : (2 : 𝒪) * h = 0 := by linear_combination e
    rcases mul_eq_zero.1 this with h2 | h2
    · exact two_ne_zero_O h2
    · exact h0 h2
  obtain ⟨q, hq⟩ := Lubin.dvd_of_vanish () {h, -h}
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption)
    (C (rhoh a b h) - X () ^ 2 * (v (shortO a b) : MvPowerSeries Unit 𝒪)) (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [ev_eq tn, pt_rho_sub tn, sub_self, map_zero]
      · rw [ev_eq tnn, pt_rho_sub tnn, vpt_neg h0 hh, neg_sq, sub_self, map_zero])
  rw [Finset.prod_pair hne] at hq
  have e2 : (X () - C h) * (X () - C (-h)) = (X () ^ 2 - C (h ^ 2) : MvPowerSeries Unit 𝒪) := by
    rw [map_neg, map_pow]; ring
  rw [e2] at hq
  refine ⟨q, ?_, hq⟩
  rw [isUnit_iff_constantCoeff]
  have hc := congrArg constantCoeff hq
  simp only [map_sub, map_mul, map_pow, constantCoeff_C, constantCoeff_X] at hc
  have hv := isUnit_pt_v (K := K) a b hh
  have : constantCoeff q = -vpt a b h := by
    have h2 : h ^ 2 ≠ 0 := pow_ne_zero 2 h0
    apply mul_left_cancel₀ h2
    linear_combination hc
  rw [this]
  exact hv.neg

/-- **`w(F(z,h)) · w(F(z,-h)) = (ρ_h - z² v(z))³ · unit`**. -/
theorem wh_pair (S : Lubin.FinSub (formalGroup (shortO a b))) {h : 𝒪} (hh : h ∈ S.H) (h0 : h ≠ 0) :
    ∃ U : MvPowerSeries Unit 𝒪, IsUnit U ∧ wh a b h * wh a b (-h) =
      (C (rhoh a b h) - X () ^ 2 * (v (shortO a b) : MvPowerSeries Unit 𝒪)) ^ 3 * U := by
  have nh := norm_lt_one_of_tn (S.tn h hh)
  have hnh := neg_mem_H S hh
  obtain ⟨q1, hq1, e1⟩ := Lubin.tau_factor S hh
  obtain ⟨q2, hq2, e2⟩ := Lubin.tau_factor S hnh
  rw [neg_eq_S_neg S hh] at e1
  rw [neg_eq_S_neg S hnh, neg_neg] at e2
  obtain ⟨q, hq, eq⟩ := rho_factor (a := a) (b := b) h0 nh
  set qi : MvPowerSeries Unit 𝒪 := ((hq.unit⁻¹ : (MvPowerSeries Unit 𝒪)ˣ) : MvPowerSeries Unit 𝒪)
  have hqi : q * qi = 1 := hq.mul_val_inv
  refine ⟨qi ^ 3 * q1 ^ 3 * q2 ^ 3 * vh a b h * vh a b (-h), ?_, ?_⟩
  · refine (((((IsUnit.pow 3 (Units.isUnit _)).mul
      (IsUnit.pow 3 ((isUnit_iff_constantCoeff).2 hq1))).mul
      (IsUnit.pow 3 ((isUnit_iff_constantCoeff).2 hq2))).mul (isUnit_vh nh)).mul
      (isUnit_vh (norm_neg_lt nh)))
  · rw [wh_eq (S.tn h hh), wh_eq (S.tn _ hnh), Fh, Fh, e1, e2, eq]
    have : (X () - C (-h) : MvPowerSeries Unit 𝒪) = X () + C h := by rw [map_neg]; ring
    rw [this]
    have hX : ((X () + C h) * (X () - C h) : MvPowerSeries Unit 𝒪) = X () ^ 2 - C (h ^ 2) := by
      rw [map_pow]; ring
    calc ((X () + C h) * q1) ^ 3 * vh a b h * (((X () - C h) * q2) ^ 3 * vh a b (-h))
        = ((X () + C h) * (X () - C h)) ^ 3 * (q1 ^ 3 * q2 ^ 3 * vh a b h * vh a b (-h)) := by ring
      _ = ((X () ^ 2 - C (h ^ 2)) * q) ^ 3 * qi ^ 3 *
            (q1 ^ 3 * q2 ^ 3 * vh a b h * vh a b (-h)) := by
          rw [hX]
          have : ((X () ^ 2 - C (h ^ 2)) * q) ^ 3 * qi ^ 3 = (X () ^ 2 - C (h ^ 2)) ^ 3 * (q * qi) ^ 3 := by
            ring
          rw [this, hqi, one_pow, mul_one]
      _ = _ := by ring

/-! ### Base change of `v`, and `ρ_h · x_Q = 1` -/

lemma map_v_short : MvPowerSeries.map jK (v (shortO a b) : MvPowerSeries Unit 𝒪) =
    vv (a : K) (b : K) := by
  have h1 := map_w_short (a := a) (b := b)
  rw [show (w (shortO a b) : MvPowerSeries Unit 𝒪) = X () ^ 3 * v (shortO a b) from
    w_eq_X3_mul_v _, map_mul, map_pow, map_X, ww_eq] at h1
  have hX : (X () ^ 3 : MvPowerSeries Unit K) ≠ 0 := pow_ne_zero 3 T_ne_zero
  exact mul_left_cancel₀ hX h1

lemma norm_vpt {h : 𝒪} (hh : ‖(h : K)‖ < 1) : ‖((vpt a b h : 𝒪) : K)‖ = 1 :=
  WeierstrassSupply.norm_eq_one_of_isUnit (isUnit_pt_v (K := K) a b hh)

lemma rhoh_mul_xc {h : 𝒪} (h0 : h ≠ 0) (hh : ‖(h : K)‖ < 1) :
    ((rhoh a b h : 𝒪) : K) * Velu.xc (Pt a b h) = 1 := by
  rw [xc_Pt h0 hh, wz_eq a b hh]
  have hv : ((vpt a b h : 𝒪) : K) ≠ 0 := by
    intro e; have := norm_vpt (a := a) (b := b) hh; rw [e, norm_zero] at this; exact zero_ne_one this
  have hh0 : ((h : 𝒪) : K) ≠ 0 := fun e => h0 (Subtype.ext e)
  push_cast
  field_simp

lemma norm_xc_Pt {h : 𝒪} (h0 : h ≠ 0) (hh : ‖(h : K)‖ < 1) : 1 < ‖Velu.xc (Pt a b h)‖ := by
  have e := rhoh_mul_xc (a := a) (b := b) h0 hh
  have hn : ‖((rhoh a b h : 𝒪) : K)‖ < 1 := by
    simp only [rhoh, Subring.coe_mul, Subring.coe_pow, norm_mul, norm_pow, norm_vpt hh, mul_one]
    exact pow_lt_one₀ (norm_nonneg _) hh (by norm_num)
  have := congrArg norm e
  rw [norm_mul, norm_one] at this
  by_contra hc
  push Not at hc
  have : ‖((rhoh a b h : 𝒪) : K)‖ * ‖Velu.xc (Pt a b h)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hc) hn
  linarith

/-- the roots of `x³ + ax + b` are integral. -/
lemma norm_root_le {e : K} (he : e ^ 3 + (a : K) * e + b = 0) : ‖e‖ ≤ 1 := by
  by_contra hc
  push Not at hc
  have ha : ‖(a : K)‖ ≤ 1 := a.2
  have hb : ‖(b : K)‖ ≤ 1 := b.2
  have e3 : e ^ 3 = -((a : K) * e + b) := by linear_combination he
  have h1 : ‖e ^ 3‖ ≤ max (‖(a : K)‖ * ‖e‖) ‖(b : K)‖ := by
    rw [e3, norm_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [norm_mul])
  rw [norm_pow] at h1
  have hsq : 1 < ‖e‖ ^ 2 := one_lt_pow₀ hc (by norm_num)
  have h2 : ‖(a : K)‖ * ‖e‖ < ‖e‖ ^ 3 := by
    calc ‖(a : K)‖ * ‖e‖ ≤ ‖e‖ := mul_le_of_le_one_left (norm_nonneg _) ha
      _ = ‖e‖ * 1 := (mul_one _).symm
      _ < ‖e‖ * ‖e‖ ^ 2 := mul_lt_mul_of_pos_left hsq (by linarith)
      _ = ‖e‖ ^ 3 := by ring
  have h3 : ‖(b : K)‖ < ‖e‖ ^ 3 := lt_of_le_of_lt hb (one_lt_pow₀ hc (by norm_num))
  exact absurd h1 (not_le.2 (max_lt h2 h3))

/-- `‖x(T + Q)‖ ≤ 1` for `‖x_Q‖ > 1`. -/
lemma norm_rr_aux {e xq x3 : K} (he : ‖e‖ ≤ 1) (hq : 1 < ‖xq‖)
    (h3 : x3 * (xq - e) = e * xq + 2 * e ^ 2 + a) : ‖x3‖ ≤ 1 := by
  have hxe : ‖xq - e‖ = ‖xq‖ := by
    rw [sub_eq_add_neg]
    exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; linarith) |>.trans
      (max_eq_left (by rw [norm_neg]; linarith))
  have hpos : 0 < ‖xq‖ := by linarith
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one K 2
    simpa using this
  have hnum : ‖e * xq + 2 * e ^ 2 + a‖ ≤ ‖xq‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) he
      · rw [norm_mul, norm_pow]
        calc ‖(2 : K)‖ * ‖e‖ ^ 2 ≤ 1 * 1 := by
              gcongr; exact pow_le_one₀ (norm_nonneg _) he
          _ ≤ ‖xq‖ := by linarith
    · exact a.2.trans hq.le
  have := congrArg norm h3
  rw [norm_mul, hxe] at this
  have h4 : ‖x3‖ * ‖xq‖ ≤ 1 * ‖xq‖ := by rw [this, one_mul]; exact hnum
  exact le_of_mul_le_mul_right h4 hpos

/-! ### Assembling: `Dser = c · U` -/

section Assemble
variable (S : Lubin.FinSub (formalGroup (shortO a b))) (κ : Velu.Kernel (a : K) (b : K))
  (hκ : (κ.G : Set (Velu.short (a : K) (b : K)).Point) =
    Pt a b '' (S.H : Set ↥(CanonicalIsogeny.integers K)))

include hκ

lemma prod_H {M : Type*} [CommMonoid M] (f : 𝒪 → M) :
    ∏ h ∈ S.H, f h = f 0 * ∏ Q ∈ κ.S, (f (hQ S Q) * f (-hQ S Q)) := by
  have := sum_H S κ hκ (M := Additive M) (fun h => Additive.ofMul (f h))
  simpa using congrArg Additive.toMul this

lemma prod_H_erase {M : Type*} [CommMonoid M] (f : 𝒪 → M) :
    ∏ h ∈ S.H.erase 0, f h = ∏ Q ∈ κ.S, (f (hQ S Q) * f (-hQ S Q)) := by
  classical
  have h1 := prod_H S κ hκ (fun h => if h = 0 then 1 else f h)
  have hl : ∏ h ∈ S.H, (if h = 0 then 1 else f h) = ∏ h ∈ S.H.erase 0, f h := by
    rw [← Finset.mul_prod_erase _ _ S.zero_mem, if_pos rfl, one_mul]
    exact Finset.prod_congr rfl (fun h hh => if_neg (Finset.ne_of_mem_erase hh))
  rw [← hl, h1, if_pos rfl, one_mul]
  refine Finset.prod_congr rfl fun Q hQ' => ?_
  rw [if_neg (hQ_ne S κ hκ hQ'), if_neg (neg_ne_zero.2 (hQ_ne S κ hκ hQ'))]

lemma Wst_eq : Wst S = ∏ Q ∈ κ.S, (wh a b (hQ S Q) * wh a b (-hQ S Q)) :=
  prod_H_erase S κ hκ _

omit hκ in
/-- `μ = π'(0) = ∏_{h ≠ 0} h`. -/
lemma coeff_pis : coeff (Finsupp.single () 1) (Lubin.pis S) = ∏ h ∈ S.H.erase 0, h := by
  rw [Lubin.pis, Lubin.piE, ← Finset.mul_prod_erase _ _ S.zero_mem]
  show PowerSeries.coeff 1 (Fh a b 0 * ∏ x ∈ S.H.erase 0, Fh a b x) = _
  rw [Fh_zero, show (X () : MvPowerSeries Unit 𝒪) = PowerSeries.X from rfl,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  show constantCoeff (∏ x ∈ S.H.erase 0, Fh a b x) = _
  rw [map_prod]
  exact Finset.prod_congr rfl fun h hh => cc_Fh (S.tn h (Finset.mem_of_mem_erase hh))

lemma norm_coeff_pis : ‖((coeff (Finsupp.single () 1) (Lubin.pis S) : 𝒪) : K)‖ =
    ∏ Q ∈ κ.S, ‖((hQ S Q : 𝒪) : K)‖ ^ 2 := by
  rw [coeff_pis, show ((∏ h ∈ S.H.erase 0, h : 𝒪) : K) = ∏ h ∈ S.H.erase 0, (h : K) from
    map_prod (Subring.subtype _) _ _, norm_prod, prod_H_erase S κ hκ (fun h => ‖((h : 𝒪) : K)‖)]
  refine Finset.prod_congr rfl fun Q _ => ?_
  rw [Subring.coe_neg, norm_neg, sq]

end Assemble

end VeluDescent
