/-
# Points of `E(K)` with non-integral `x` come from the formal group

`W : y² = x³ + ax + b` over `𝒪` (`K` complete ultrametric, char `0`).

* `lift_point`: an affine point `(x, y)` with `‖x‖ > 1` is `Pt(z)` for `z = −x/y` in the disc
  (`w(z) = −1/y` by uniqueness of small solutions of `w = z³ + a z w² + b w³`).
* `nm_p_of_Pt`: if `‖3‖ = 1`, `p ≥ 5` prime and `p • Pt(z) = 0`, then `[p] z = 0` (induction on
  `k • Pt(z) = Pt([k] z)` via the chord law; the doubling uses `[2] z, [3] z ≠ 0`).
-/
import RamanujanTau.OrdQuot.Torsion

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OrdQuot
open MvPowerSeries EllipticFormal EllipticI2 CanonicalIsogeny QuotientHasse VeluLubin

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]
  [DecidableEq K]

local notation "𝒪" => CanonicalIsogeny.integers K

variable (a b : ↥(CanonicalIsogeny.integers K))

lemma norm_add_lt_one {x y : K} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)

lemma norm_mul_lt_one {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ < 1) : ‖x * y‖ < 1 := by
  rw [norm_mul]
  calc ‖x‖ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ < 1 := by rw [one_mul]; exact hy

/-- **uniqueness of small solutions** of `G(z, w) = 0` on the short curve. -/
lemma G_unique_small {z w₁ w₂ : K} (hz : ‖z‖ < 1) (h1 : ‖w₁‖ < 1) (h2 : ‖w₂‖ < 1)
    (hG1 : G (Velu.short (a : K) (b : K) : WeierstrassCurve K) z w₁ = 0)
    (hG2 : G (Velu.short (a : K) (b : K) : WeierstrassCurve K) z w₂ = 0) : w₁ = w₂ := by
  simp only [G, Velu.short_a₁, Velu.short_a₂, Velu.short_a₃, Velu.short_a₄, Velu.short_a₆,
    zero_mul, add_zero] at hG1 hG2
  set c : K := (a : K) * z * (w₁ + w₂) + (b : K) * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)
  have e : (w₁ - w₂) * (1 - c) = 0 := by simp only [c]; linear_combination hG2 - hG1
  have hc : ‖c‖ < 1 := by
    have ha : ‖(a : K)‖ ≤ 1 := a.2
    have hb : ‖(b : K)‖ ≤ 1 := b.2
    refine norm_add_lt_one ?_ ?_
    · rw [mul_assoc]
      exact norm_mul_lt_one ha (norm_mul_lt_one (le_of_lt hz) (norm_add_lt_one h1 h2) |>.trans_le'
        (le_of_eq rfl))
    · refine norm_mul_lt_one hb (norm_add_lt_one (norm_add_lt_one ?_ ?_) ?_)
      · rw [pow_two]; exact norm_mul_lt_one h1.le h1
      · exact norm_mul_lt_one h1.le h2
      · rw [pow_two]; exact norm_mul_lt_one h2.le h2
  have hc1 : 1 - c ≠ 0 := by
    intro h
    have : c = 1 := by linear_combination -h
    rw [this, norm_one] at hc; exact lt_irrefl _ hc
  exact sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_right hc1)

lemma norm_wz_lt {z : ↥(CanonicalIsogeny.integers K)} (hz : ‖(z : K)‖ < 1) :
    ‖((wz a b z : 𝒪) : K)‖ < 1 := by
  rw [wz_eq a b hz, Subring.coe_mul, Subring.coe_pow, norm_mul, norm_pow]
  have h1 : ‖((Lubin.pt (fun _ : Unit => z) (v (shortO a b) : MvPowerSeries Unit 𝒪) : 𝒪) : K)‖ ≤ 1 :=
    (Lubin.pt (fun _ : Unit => z) (v (shortO a b) : MvPowerSeries Unit 𝒪)).2
  calc ‖(z : K)‖ ^ 3 * _ ≤ ‖(z : K)‖ ^ 3 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ < 1 := by
      rw [mul_one]; exact pow_lt_one₀ (norm_nonneg _) hz (by norm_num)

/-- **a point with `‖x‖ > 1` lies in the formal group**: it is `Pt(−x/y)`. -/
theorem lift_point {x y : K} (hxy : (Velu.short (a : K) (b : K)).Nonsingular x y) (hx : 1 < ‖x‖) :
    ∃ z : ↥(CanonicalIsogeny.integers K), z ≠ 0 ∧ ‖(z : K)‖ < 1 ∧
      Pt a b z = WeierstrassCurve.Affine.Point.some x y hxy := by
  have heq : y ^ 2 = x ^ 3 + (a : K) * x + (b : K) :=
    (Velu.short_equation_iff _ _ _ _).1 hxy.1
  have ha : ‖(a : K)‖ ≤ 1 := a.2
  have hb : ‖(b : K)‖ ≤ 1 := b.2
  have hx0 : 0 < ‖x‖ := lt_trans one_pos hx
  have hx3 : ‖x‖ < ‖x‖ ^ 3 := by
    calc ‖x‖ = ‖x‖ ^ 1 := (pow_one _).symm
      _ < ‖x‖ ^ 3 := pow_lt_pow_right₀ hx (by norm_num)
  have hlow : ‖(a : K) * x + (b : K)‖ < ‖x ^ 3‖ := by
    rw [norm_pow]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      calc ‖(a : K)‖ * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ < ‖x‖ ^ 3 := by rw [one_mul]; exact hx3
    · exact lt_of_le_of_lt hb (lt_trans hx hx3)
  have hy2 : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
    rw [← norm_pow, heq, add_assoc,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hlow), max_eq_left hlow.le,
      norm_pow]
  have hy1 : 1 < ‖y‖ := by
    by_contra h
    have h := not_lt.mp h
    have : ‖y‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) h
    have : 1 < ‖x‖ ^ 3 := one_lt_pow₀ hx (by norm_num)
    linarith
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy1; linarith
  have hxne : x ≠ 0 := by
    intro h; rw [h, norm_zero] at hx; linarith
  set z0 : K := -x / y with hz0
  have hz2 : ‖z0‖ ^ 2 * ‖x‖ = 1 := by
    rw [hz0, norm_div, norm_neg, div_pow, hy2]
    field_simp
  have hzl : ‖z0‖ < 1 := by
    have : ‖z0‖ ^ 2 < 1 := by
      by_contra h; have h := not_lt.mp h
      nlinarith
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this
  set zO : ↥(CanonicalIsogeny.integers K) := ⟨z0, hzl.le⟩
  have hzO : ‖(zO : K)‖ < 1 := hzl
  have hzO0 : zO ≠ 0 := by
    intro h
    have : z0 = 0 := congrArg Subtype.val h
    rw [hz0, div_eq_zero_iff, neg_eq_zero] at this
    rcases this with h' | h'
    · exact hxne h'
    · exact hy0 h'
  have hGw : G (Velu.short (a : K) (b : K) : WeierstrassCurve K) z0 (-1 / y) = 0 := by
    have : G (Velu.short (a : K) (b : K) : WeierstrassCurve K) z0 (-1 / y) =
        (y ^ 2 - (x ^ 3 + (a : K) * x + (b : K))) / y ^ 3 := by
      simp only [G, Velu.short_a₁, Velu.short_a₂, Velu.short_a₃, Velu.short_a₄, Velu.short_a₆, hz0]
      field_simp
      ring
    rw [this, heq, sub_self, zero_div]
  have hwl : ‖-1 / y‖ < 1 := by
    rw [norm_div, norm_neg, norm_one]
    exact (div_lt_one (by linarith)).2 hy1
  have hw : ((wz a b zO : 𝒪) : K) = -1 / y :=
    G_unique_small a b hzl (norm_wz_lt a b hzO) hwl (G_wzK a b hzO) hGw
  refine ⟨zO, hzO0, hzO, ?_⟩
  rw [Pt_eq a b hzO0 hzO, pt, WeierstrassCurve.Affine.Point.some.injEq]
  show (z0 / ((wz a b zO : 𝒪) : K) = x) ∧ (-1 / ((wz a b zO : 𝒪) : K) = y)
  rw [hw, hz0]
  constructor <;> field_simp

/-- the doubling step: `Pt([2] z) = 2 • Pt(z)` when `[2] z ≠ 0`, `[3] z ≠ 0`. -/
lemma Pt_double {x : ↥(CanonicalIsogeny.integers K)} (hx0 : x ≠ 0) (nx : ‖(x : K)‖ < 1)
    (h2 : nm a b x 2 ≠ 0) (h3 : nm a b x 3 ≠ 0) : Pt a b (nm a b x 2) = 2 • Pt a b x := by
  set d := Lubin.padd (formalGroup (shortO a b)) x x
  have hd2 : nm a b x 2 = d := nm_two a b x nx
  rw [hd2] at h2 ⊢
  have nd : ‖(d : K)‖ < 1 := norm_padd_lt a b nx nx
  have h3' : Lubin.padd (formalGroup (shortO a b)) x d ≠ 0 := by
    rwa [nm_succ a b x nx, nm_two a b x nx] at h3
  have hdx : Lubin.padd (formalGroup (shortO a b)) d (-x) = x := by
    rw [Lubin.padd_assoc (tn_of_norm nx) (tn_of_norm nx) (tn_of_norm (norm_neg_lt nx)) (tn_of_norm nd)
      (tn_of_norm (by rw [padd_neg a b nx]; simp)), padd_neg a b nx, Lubin.padd_zero (tn_of_norm nx)]
  have hxd : (d : K) / (wz a b d : K) ≠ ((-x : 𝒪) : K) / (wz a b (-x) : K) := by
    intro he
    rcases x_eq a b h2 (neg_ne_zero.2 hx0) nd (norm_neg_lt nx) he with h | h
    · apply h3'
      have hd' : d = -x := h.symm
      rw [hd']; exact padd_neg a b nx
    · have hdx' : d = x := neg_injective h.symm
      apply hx0
      have := hdx
      rw [hdx', padd_neg a b nx] at this
      exact this.symm
  have key := Pt_add a b h2 (neg_ne_zero.2 hx0) nd (norm_neg_lt nx) (by rw [hdx]; exact hx0) hxd
  rw [hdx, Pt_neg] at key
  rw [eq_add_neg_iff_add_eq] at key
  rw [two_nsmul]; exact key.symm

/-- **`p • Pt(z) = 0` forces `[p] z = 0`**. -/
theorem nm_p_of_Pt {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (h3 : ‖(3 : K)‖ = 1)
    {z : ↥(CanonicalIsogeny.integers K)} (hz0 : z ≠ 0) (hz : ‖(z : K)‖ < 1)
    (hpP : p • Pt a b z = 0) : nm a b z p = 0 := by
  set P := Pt a b z with hPdef
  have hP0 : P ≠ 0 := Pt_ne_zero a b hz0 hz
  have ho : addOrderOf P = p := addOrderOf_eq_prime hpP hP0
  have hk0 : ∀ k, k • P = 0 → p ∣ k := fun k h => ho ▸ addOrderOf_dvd_of_nsmul_eq_zero h
  have hd2 : nm a b z 2 ≠ 0 := by
    intro h
    rw [nm_two a b z hz] at h
    have e := padd_cancel a b hz hz h
    have e' : (2 : K) * (z : K) = 0 := by
      have := congrArg (fun t : 𝒪 => (t : K)) e
      simp only [Subring.coe_neg] at this
      linear_combination this
    rcases mul_eq_zero.1 e' with h' | h'
    · exact two_ne_zero h'
    · exact hz0 (Subtype.ext h')
  have hd3 : nm a b z 3 ≠ 0 := by
    intro h
    exact hz0 (tors_unit (formalGroup (shortO a b)) 3 (by simpa using h3) hz h)
  have double := Pt_double a b hz0 hz hd2 hd3
  have key : ∀ k, 1 ≤ k → k ≤ p - 1 → Pt a b (nm a b z k) = k • P := by
    intro k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro _ hk
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · rw [zero_add, nm_one a b z hz, one_nsmul]
      have IH := ih hk1 (by omega)
      set u := nm a b z k
      have nu : ‖(u : K)‖ < 1 := norm_nm a b z hz k
      have hu0 : u ≠ 0 := by
        intro h
        have e : k • P = 0 := by rw [← IH, h, Pt_zero]
        exact absurd (Nat.le_of_dvd hk1 (hk0 k e)) (by omega)
      by_cases hx : (z : K) / (wz a b z : K) = (u : K) / (wz a b u : K)
      · rcases x_eq a b hz0 hu0 hz nu hx with h | h
        · have hk : k = 1 := by
            have e : k • P = P := by rw [← IH, h]
            have e2 : (k - 1) • P = 0 := by
              have e3 : (k - 1) • P + P = 0 + P := by
                rw [← succ_nsmul, Nat.sub_add_cancel hk1, zero_add]; exact e
              exact add_right_cancel e3
            rcases Nat.eq_zero_or_pos (k - 1) with h' | h'
            · omega
            · exact absurd (Nat.le_of_dvd h' (hk0 _ e2)) (by omega)
          subst hk
          exact double
        · exfalso
          have e : k • P = -P := by rw [← IH, h, Pt_neg]
          have e2 : (k + 1) • P = 0 := by rw [succ_nsmul, e, neg_add_cancel]
          exact absurd (Nat.le_of_dvd (by omega) (hk0 _ e2)) (by omega)
      · have hF : Lubin.padd (formalGroup (shortO a b)) z u ≠ 0 := by
          intro h
          apply hx
          have := padd_cancel a b hz nu h
          rw [this, wz_neg a b hz, Subring.coe_neg, Subring.coe_neg, neg_div_neg_eq]
        rw [nm_succ a b z hz, Pt_add a b hz0 hu0 hz nu hF hx, IH, succ_nsmul, add_comm]
  have hp1 : 1 ≤ p - 1 := by omega
  have hm := key (p - 1) hp1 le_rfl
  have hneg : (p - 1) • P = -P := by
    refine eq_neg_of_add_eq_zero_left ?_
    rw [← succ_nsmul, Nat.sub_add_cancel (by omega : 1 ≤ p)]; exact hpP
  rw [hneg, ← Pt_neg] at hm
  have e := VeluDescent.Pt_injOn (norm_nm a b z hz (p - 1)) (norm_neg_lt hz) hm
  rw [show p = (p - 1) + 1 by omega, nm_succ a b z hz, e, padd_neg a b hz]

end OrdQuot
