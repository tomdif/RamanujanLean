/-
# Salié via Stepanov, part 1: the fibre count `M(u,v)`

`M(u,v) = #{(x₁,x₂,x₃) ∈ (𝔽_p^×)³ : x₁+x₂+x₃ = u, x₁⁻¹+x₂⁻¹+x₃⁻¹ = v}`.
Fibring over `x₁ = x` with `s = u - x`, `r = v - x⁻¹`, the pair `(x₂,x₃)` is a root pair of
`z² - s z + s/r`, so `M₂(s,r) = 1 + χ(s² - 4s/r)` for `s, r ≠ 0`, and
`χ(s² - 4s/r) = χ(f_{u,v}(x))` with the **quartic** (genus 1)
`f_{u,v}(x) = A (A - 4x)`, `A = (u - (x : F))(v x - 1)`.
`x = u` is a simple root of `f_{u,v}` when `u ≠ 0`, `uv ≠ 1`, so the Stepanov bound applies:
`|M(u,v) - p| ≤ 4 + 192 √p` for such `(u,v)`, and `|M(u,v) - p| ≤ 3p` always.
Consequently `∑_{u,v} (M(u,v) - p)² ≤ (196² + 18) p³`.
-/
import RamanujanTau.Stepanov.Main
import RamanujanTau.TauBound.KlPrime

set_option autoImplicit false

namespace RamanujanTau.Stepanov

open Polynomial Finset RamanujanTau.TauBound

variable {p : ℕ} [hp : Fact p.Prime]

local notation "F" => ZMod p
local notation "U" => (ZMod p)ˣ
local notation "χ" => quadraticChar (ZMod p)

/-- A simple root rules out `f = const · square`. -/
theorem notConstSq_of_rootMultiplicity_one {f : F[X]} (hf0 : f ≠ 0) (a : F)
    (h : rootMultiplicity a f = 1) : NotConstSq f := by
  intro c u v hc heq
  by_contra hu
  have hl : f * u ^ 2 ≠ 0 := mul_ne_zero hf0 (pow_ne_zero _ hu)
  have hv : v ≠ 0 := by rintro rfl; rw [heq] at hl; simp at hl
  have hr : C c * v ^ 2 ≠ 0 := by rw [← heq]; exact hl
  have h1 := rootMultiplicity_mul (x := a) hl
  have h2 := rootMultiplicity_mul (x := a) hr
  rw [heq] at h1
  rw [h1] at h2
  have hu2 : rootMultiplicity a (u ^ 2) = 2 * rootMultiplicity a u := by
    rw [pow_two, rootMultiplicity_mul (mul_ne_zero hu hu)]; ring
  have hv2 : rootMultiplicity a (v ^ 2) = 2 * rootMultiplicity a v := by
    rw [pow_two, rootMultiplicity_mul (mul_ne_zero hv hv)]; ring
  rw [hu2, hv2, h, rootMultiplicity_C] at h2
  omega

/-- The quartic `f_{u,v}(X) = A(A - 4X)`, `A = (u - X)(vX - 1)`. -/
noncomputable def fUV (u v : F) : F[X] :=
  ((C u - X) * (C v * X - 1)) * ((C u - X) * (C v * X - 1) - C 4 * X)

theorem eval_fUV (u v x : F) : (fUV u v).eval (x : F) =
    ((u - (x : F)) * (v * x - 1)) * ((u - (x : F)) * (v * x - 1) - 4 * x) := by
  simp [fUV]

theorem natDegree_fUV_le (u v : F) : (fUV u v).natDegree ≤ 4 := by
  unfold fUV; compute_degree

theorem notConstSq_fUV (hp2 : p ≠ 2) {u v : F} (hu : u ≠ 0) (huv : u * v ≠ 1) :
    NotConstSq (fUV u v) ∧ fUV u v ≠ 0 := by
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero (Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2))
      (Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2))
  set g : F[X] := -(C v * X - 1) * ((C u - X) * (C v * X - 1) - C 4 * X)
  have hfg : fUV u v = (X - C u) * g := by simp only [fUV, g]; ring
  have hgu : g.eval u ≠ 0 := by
    simp only [g, eval_mul, eval_neg, eval_sub, eval_C, eval_X, eval_one, sub_self, zero_mul,
      zero_sub]
    have : -(v * u - 1) * -(4 * u) = 4 * u * (u * v - 1) := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero h4 hu) (sub_ne_zero.mpr huv)
  have hg0 : g ≠ 0 := by rintro h; rw [h, eval_zero] at hgu; exact hgu rfl
  have hf0 : fUV u v ≠ 0 := by rw [hfg]; exact mul_ne_zero (X_sub_C_ne_zero u) hg0
  refine ⟨notConstSq_of_rootMultiplicity_one hf0 u ?_, hf0⟩
  rw [hfg, rootMultiplicity_mul (hfg ▸ hf0), rootMultiplicity_X_sub_C_self,
    rootMultiplicity_eq_zero hgu]

/-! ### `M₂` -/

/-- `M₂(s,r) = #{(x,y) ∈ (𝔽_p^×)² : x + y = s, x⁻¹ + y⁻¹ = r}`. -/
noncomputable def M2 (s r : F) : ℕ := #(univ.filter (fun w : U × U => sP w = s ∧ tP w = r))

theorem M2_le (s r : F) : M2 s r ≤ p - 1 := by
  unfold M2
  rw [← ZMod.card_units p]
  refine (Finset.card_le_card_of_injOn (fun w : U × U => w.1) (fun _ _ => mem_univ _) ?_).trans
    (le_of_eq (card_univ))
  intro w hw w' hw' h
  simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and, sP] at hw hw'
  simp only at h
  refine Prod.ext h (Units.ext ?_)
  have := hw.1.trans hw'.1.symm
  rw [h] at this
  exact add_left_cancel this

theorem M2_zero_left {r : F} (hr : r ≠ 0) : M2 0 r = 0 := by
  unfold M2
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro ⟨x, y⟩ _ ⟨h1, h2⟩
  simp only [sP, tP] at h1 h2
  have : (y : F) = -x := by linear_combination h1
  rw [this, inv_neg] at h2
  exact hr (by rw [← h2]; ring)

theorem M2_zero_right {s : F} (hs : s ≠ 0) : M2 s 0 = 0 := by
  unfold M2
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro ⟨x, y⟩ _ ⟨h1, h2⟩
  simp only [sP, tP] at h1 h2
  have hx : (x : F) ≠ 0 := x.ne_zero
  have hy : (y : F) ≠ 0 := y.ne_zero
  have : (x : F) + y = 0 := by
    have := congrArg (fun t => t * ((x : F) * y)) h2
    simp only [zero_mul] at this
    field_simp at this
    linear_combination this
  exact hs (h1 ▸ this)

theorem card_sqrts_filter (hp2 : p ≠ 2) (d : F) :
    (#(univ.filter (fun y : F => y ^ 2 = d)) : ℤ) = χ d + 1 := by
  have hF : ringChar F ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  rw [← quadraticChar_card_sqrts hF d]
  congr 2
  ext y; simp

theorem M2_eq (hp2 : p ≠ 2) {s r : F} (hs : s ≠ 0) (hr : r ≠ 0) :
    (M2 s r : ℤ) = χ (s ^ 2 - 4 * (s / r)) + 1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  rw [← card_sqrts_filter hp2]
  congr 1
  unfold M2
  -- step 1: pairs ↔ roots of `z² - s z + s/r`
  have step1 : #(univ.filter (fun w : U × U => sP w = s ∧ tP w = r)) =
      #(univ.filter (fun z : F => z ^ 2 - s * z + s / r = 0)) := by
    apply Finset.card_bij (fun w _ => (w.1 : F))
    · rintro ⟨x, y⟩ hw
      simp only [mem_filter, mem_univ, true_and, sP, tP] at hw ⊢
      have hx : (x : F) ≠ 0 := x.ne_zero
      have hy : (y : F) ≠ 0 := y.ne_zero
      have hy' : (y : F) = s - x := by linear_combination hw.1
      have h := hw.2
      rw [hy'] at h hy
      have key : s / r = x * (s - x) := by
        rw [div_eq_iff hr]
        field_simp at h
        linear_combination h
      rw [key]; ring
    · rintro ⟨x, y⟩ hw ⟨x', y'⟩ hw' h
      simp only [mem_filter, mem_univ, true_and, sP] at hw hw'
      have h' : (x : F) = (x' : F) := by rw [h]
      refine Prod.ext (Units.ext h') (Units.ext ?_)
      have := hw.1.trans hw'.1.symm
      rw [h'] at this; exact add_left_cancel this
    · intro z hz
      simp only [mem_filter, mem_univ, true_and] at hz
      have hz0 : z ≠ 0 := by
        rintro rfl; apply div_ne_zero hs hr; linear_combination hz
      have hsz : s - z ≠ 0 := by
        intro h
        have : z = s := by linear_combination -h
        rw [this] at hz; apply div_ne_zero hs hr; linear_combination hz
      refine ⟨(Units.mk0 z hz0, Units.mk0 (s - z) hsz), ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and, sP, tP, Units.val_mk0]
      refine ⟨by ring, ?_⟩
      have e : s / r = z * (s - z) := by linear_combination hz
      have e2 := (div_eq_iff hr).mp e
      rw [inv_add_inv hz0 hsz, div_eq_iff (mul_ne_zero hz0 hsz)]
      linear_combination e2
  rw [step1]
  -- step 2: complete the square
  apply Finset.card_nbij' (fun z => 2 * z - s) (fun y => (y + s) / 2)
  · intro z hz
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hz ⊢
    field_simp at hz ⊢
    linear_combination 4 * hz
  · intro y hy
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hy ⊢
    field_simp at hy ⊢
    linear_combination hy
  · intro z _; simp only; field_simp; ring
  · intro y _; simp only; field_simp; ring

/-- `χ(s² - 4s/r) = χ(f_{u,v}(x))`. -/
theorem chi_fUV (u v : F) (x : U) (hs : u - (x : F) ≠ 0) (hr : v - (x : F)⁻¹ ≠ 0) :
    χ ((u - (x : F)) ^ 2 - 4 * ((u - (x : F)) / (v - (x : F)⁻¹))) = χ ((fUV u v).eval (x : F)) := by
  have hx : (x : F) ≠ 0 := x.ne_zero
  have hrx : (v - (x : F)⁻¹) * x ≠ 0 := mul_ne_zero hr hx
  have key : (fUV u v).eval (x : F) =
      ((u - (x : F)) ^ 2 - 4 * ((u - (x : F)) / (v - (x : F)⁻¹))) * ((v - (x : F)⁻¹) * x) ^ 2 := by
    have hv : v * (x : F) - 1 = (v - (x : F)⁻¹) * x := by field_simp
    rw [eval_fUV, hv]
    generalize v - (x : F)⁻¹ = r at hr ⊢
    field_simp
  rw [key, map_mul, quadraticChar_sq_one' hrx, mul_one]

theorem fUV_eval_eq_zero (u v : F) (x : U) (h : u - (x : F) = 0 ∨ v - (x : F)⁻¹ = 0) :
    (fUV u v).eval (x : F) = 0 := by
  rw [eval_fUV]
  have hx : (x : F) ≠ 0 := x.ne_zero
  rcases h with h | h
  · rw [h]; ring
  · have : v * x - 1 = 0 := by
      have : v = (x : F)⁻¹ := by linear_combination h
      rw [this, inv_mul_cancel₀ hx, sub_self]
    rw [this]; ring

/-- Per-fibre estimate. -/
theorem M2_fibre (hp2 : p ≠ 2) (u v : F) (x : U) :
    |(M2 (u - (x : F)) (v - (x : F)⁻¹) : ℤ) - (if u - (x : F) ≠ 0 ∧ v - (x : F)⁻¹ ≠ 0 then 1 else 0)
      - χ ((fUV u v).eval (x : F))| ≤
      (p - 1 : ℤ) * (if u - (x : F) = 0 ∧ v - (x : F)⁻¹ = 0 then 1 else 0) := by
  by_cases hs : u - (x : F) = 0
  · rw [fUV_eval_eq_zero u v x (Or.inl hs), hs, MulChar.map_zero, sub_zero]
    by_cases hr : v - (x : F)⁻¹ = 0
    · rw [hr, if_neg (fun h => h.1 rfl), if_pos ⟨rfl, rfl⟩, sub_zero, mul_one]
      have := M2_le (p := p) 0 0
      have h1 := hp.out.one_lt
      rw [abs_of_nonneg (by positivity)]
      omega
    · rw [M2_zero_left hr, if_neg (fun h => h.1 rfl), if_neg (fun h => hr h.2)]
      simp only [Nat.cast_zero, sub_zero, abs_zero, mul_zero, le_refl]
  · by_cases hr : v - (x : F)⁻¹ = 0
    · rw [fUV_eval_eq_zero u v x (Or.inr hr), hr, MulChar.map_zero, sub_zero, M2_zero_right hs,
        if_neg (fun h => h.2 rfl), if_neg (fun h => hs h.1)]
      simp only [Nat.cast_zero, sub_zero, abs_zero, mul_zero, le_refl]
    · rw [M2_eq hp2 hs hr, chi_fUV u v x hs hr, if_pos ⟨hs, hr⟩, if_neg (fun h => hs h.1)]
      simp only [add_sub_cancel_right, sub_self, abs_zero, mul_zero, le_refl]

/-- `∑_{x ∈ 𝔽_p} g x = g 0 + ∑_{x ∈ 𝔽_p^×} g x`. -/
theorem sum_F_eq_units (g : F → ℤ) : ∑ x : F, g x = g 0 + ∑ x : U, g x := by
  rw [← Finset.add_sum_erase univ g (mem_univ 0)]
  congr 1
  symm
  apply Finset.sum_bij (fun (x : U) _ => (x : F))
  · intro x _; simp [x.ne_zero]
  · intro x _ y _ h; exact Units.ext h
  · intro y hy
    have hy0 : y ≠ 0 := (mem_erase.mp hy).1
    exact ⟨Units.mk0 y hy0, mem_univ _, rfl⟩
  · intro _ _; rfl

/-! ### `M₃ = M(u,v)` -/

/-- `M(u,v)` (triples written `(x, (y, z))`). -/
noncomputable def M3 (u v : F) : ℕ :=
  #(univ.filter (fun w : U × (U × U) => (w.1 : F) + sP w.2 = u ∧ (w.1 : F)⁻¹ + tP w.2 = v))

theorem M3_eq_sum (u v : F) : (M3 u v : ℤ) = ∑ x : U, (M2 (u - (x : F)) (v - (x : F)⁻¹) : ℤ) := by
  unfold M3 M2
  rw [Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by rw [← h1]; ring, by rw [← h2]; ring⟩
  · rintro ⟨h1, h2⟩; exact ⟨by rw [h1]; ring, by rw [h2]; ring⟩

theorem card_good_fibres (u v : F) :
    (p : ℤ) - 3 ≤ (#(univ.filter (fun x : U => u - (x : F) ≠ 0 ∧ v - (x : F)⁻¹ ≠ 0)) : ℤ) ∧
    (#(univ.filter (fun x : U => u - (x : F) ≠ 0 ∧ v - (x : F)⁻¹ ≠ 0)) : ℤ) ≤ p - 1 := by
  have hcardU : (Fintype.card U : ℤ) = p - 1 := by
    rw [ZMod.card_units p]; have := hp.out.one_lt; push_cast [Nat.cast_sub this.le]; ring
  have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset U))
    (fun x : U => u - (x : F) ≠ 0 ∧ v - (x : F)⁻¹ ≠ 0)
  rw [card_univ] at h1
  have hbad : #(univ.filter (fun x : U => ¬ (u - (x : F) ≠ 0 ∧ v - (x : F)⁻¹ ≠ 0))) ≤ 2 := by
    have hsub : univ.filter (fun x : U => ¬ (u - (x : F) ≠ 0 ∧ v - (x : F)⁻¹ ≠ 0)) ⊆
        univ.filter (fun x : U => (x : F) = u) ∪ univ.filter (fun x : U => (x : F)⁻¹ = v) := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and, not_and_or, not_not, mem_union] at hx ⊢
      rcases hx with h | h
      · left; linear_combination -h
      · right; linear_combination -h
    have hA : #(univ.filter (fun x : U => (x : F) = u)) ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [mem_filter, mem_univ, true_and] at ha hb
      exact Units.ext (ha.trans hb.symm)
    have hB : #(univ.filter (fun x : U => (x : F)⁻¹ = v)) ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [mem_filter, mem_univ, true_and] at ha hb
      exact Units.ext (inv_injective (ha.trans hb.symm))
    exact (card_le_card hsub).trans ((card_union_le _ _).trans (by omega))
  constructor <;> push_cast <;> omega

theorem card_bad_fibres (u v : F) :
    #(univ.filter (fun x : U => u - (x : F) = 0 ∧ v - (x : F)⁻¹ = 0)) ≤ 1 ∧
    (u * v ≠ 1 → #(univ.filter (fun x : U => u - (x : F) = 0 ∧ v - (x : F)⁻¹ = 0)) = 0) := by
  constructor
  · rw [Finset.card_le_one]
    intro a ha b hb
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact Units.ext (by linear_combination hb.1 - ha.1)
  · intro huv
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro x _ ⟨h1, h2⟩
    apply huv
    have hx : (x : F) ≠ 0 := x.ne_zero
    have e1 : u = x := by linear_combination h1
    have e2 : v = (x : F)⁻¹ := by linear_combination h2
    rw [e1, e2, mul_inv_cancel₀ hx]

/-- `|M(u,v) - p| ≤ 4 + |∑_x χ(f_{u,v}(x))| + (p-1)·#{bad fibres}`. -/
theorem M3_sub_p_le (hp2 : p ≠ 2) (u v : F) :
    |(M3 u v : ℤ) - p| ≤ 4 + |∑ x : F, χ ((fUV u v).eval (x : F))| +
      (p - 1 : ℤ) * #(univ.filter (fun x : U => u - (x : F) = 0 ∧ v - (x : F)⁻¹ = 0)) := by
  set G := #(univ.filter (fun x : U => u - (x : F) ≠ 0 ∧ v - (x : F)⁻¹ ≠ 0))
  set B := #(univ.filter (fun x : U => u - (x : F) = 0 ∧ v - (x : F)⁻¹ = 0))
  have hG := card_good_fibres (p := p) u v
  have hsumF := sum_F_eq_units (p := p) (fun x => χ ((fUV u v).eval (x : F)))
  have h0 : |χ ((fUV u v).eval 0)| ≤ 1 := by
    by_cases h : (fUV u v).eval 0 = 0
    · simp [h]
    · rcases quadraticChar_dichotomy h with h' | h' <;> simp [h']
  have hdecomp : (M3 u v : ℤ) - p = ∑ x : U, ((M2 (u - (x : F)) (v - (x : F)⁻¹) : ℤ) -
      (if u - (x : F) ≠ 0 ∧ v - (x : F)⁻¹ ≠ 0 then 1 else 0) - χ ((fUV u v).eval (x : F))) +
      ((G : ℤ) - p) + ∑ x : U, χ ((fUV u v).eval (x : F)) := by
    rw [M3_eq_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_boole]
    push_cast
    ring
  have hfib : |∑ x : U, ((M2 (u - (x : F)) (v - (x : F)⁻¹) : ℤ) -
      (if u - (x : F) ≠ 0 ∧ v - (x : F)⁻¹ ≠ 0 then 1 else 0) - χ ((fUV u v).eval (x : F)))| ≤
      (p - 1 : ℤ) * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun x _ => M2_fibre hp2 u v x).trans ?_
    rw [← Finset.mul_sum, Finset.sum_boole]
  rw [hdecomp]
  have hU : ∑ x : U, χ ((fUV u v).eval (x : F)) = ∑ x : F, χ ((fUV u v).eval (x : F)) -
      χ ((fUV u v).eval 0) := by rw [hsumF]; ring
  rw [hU]
  have := abs_add_le (∑ x : U, ((M2 (u - (x : F)) (v - (x : F)⁻¹) : ℤ) -
      (if u - (x : F) ≠ 0 ∧ v - (x : F)⁻¹ ≠ 0 then 1 else 0) - χ ((fUV u v).eval (x : F))) +
      ((G : ℤ) - p)) (∑ x : F, χ ((fUV u v).eval (x : F)) - χ ((fUV u v).eval 0))
  have := abs_add_le (∑ x : U, ((M2 (u - (x : F)) (v - (x : F)⁻¹) : ℤ) -
      (if u - (x : F) ≠ 0 ∧ v - (x : F)⁻¹ ≠ 0 then 1 else 0) - χ ((fUV u v).eval (x : F))))
      ((G : ℤ) - p)
  have := abs_sub (∑ x : F, χ ((fUV u v).eval (x : F))) (χ ((fUV u v).eval 0))
  have : |(G : ℤ) - p| ≤ 3 := by rw [abs_le]; constructor <;> linarith [hG.1, hG.2]
  linarith

/-- **Pointwise fibre bound.** For `u ≠ 0`, `uv ≠ 1`: `|M(u,v) - p| ≤ 196 √p`; always `≤ 3p`. -/
theorem M3_sub_p_sq_le (hp2 : p ≠ 2) (u v : F) :
    (((M3 u v : ℤ) - p : ℤ) : ℝ) ^ 2 ≤
      196 ^ 2 * p + (if u = 0 ∨ u * v = 1 then 9 * (p : ℝ) ^ 2 else 0) := by
  have hmain := M3_sub_p_le hp2 u v
  have hB := card_bad_fibres (p := p) u v
  have hp3 : (3 : ℝ) ≤ p := by
    have := hp.out.two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hp3' : 3 ≤ p := by
    have := hp.out.two_le
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hsp : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hs1 : 1 ≤ Real.sqrt p := by rw [Real.one_le_sqrt]; linarith
  -- trivial bound on the character sum
  have htriv : |(∑ x : F, χ ((fUV u v).eval (x : F)) : ℤ)| ≤ p := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ x : F, |χ ((fUV u v).eval (x : F))| ≤ 1 := by
      intro x
      by_cases h0 : (fUV u v).eval (x : F) = 0
      · simp [h0]
      · rcases quadraticChar_dichotomy h0 with h | h <;> simp [h]
    refine (Finset.sum_le_sum fun x _ => this x).trans ?_
    simp
  split_ifs with hbad
  · -- crude: |M - p| ≤ 3p
    have hle : |(M3 u v : ℤ) - p| ≤ 3 * p := by
      have h1 : (#(univ.filter (fun x : U => u - (x : F) = 0 ∧ v - (x : F)⁻¹ = 0)) : ℤ) ≤ 1 := by
        exact_mod_cast hB.1
      have : (p - 1 : ℤ) * #(univ.filter (fun x : U => u - (x : F) = 0 ∧ v - (x : F)⁻¹ = 0))
          ≤ p - 1 := by
        have := hp.out.one_lt
        have : (0 : ℤ) ≤ p - 1 := by omega
        nlinarith [Nat.cast_nonneg (α := ℤ)
          (#(univ.filter (fun x : U => u - (x : F) = 0 ∧ v - (x : F)⁻¹ = 0)))]
      have : (3 : ℤ) ≤ p := by exact_mod_cast hp3' 
      linarith
    have hleR : |(((M3 u v : ℤ) - p : ℤ) : ℝ)| ≤ 3 * p := by exact_mod_cast hle
    have := sq_abs ((((M3 u v : ℤ) - p : ℤ) : ℝ))
    nlinarith [abs_nonneg ((((M3 u v : ℤ) - p : ℤ) : ℝ))]
  · push Not at hbad
    have hB0 := hB.2 hbad.2
    rw [hB0] at hmain
    simp only [Nat.cast_zero, mul_zero, add_zero] at hmain
    obtain ⟨hns, hf0⟩ := notConstSq_fUV hp2 hbad.1 hbad.2
    have hW := hasseWeil_charSum_le_of_notConstSq hp2 (fUV u v) hns hf0
    have hdeg : ((fUV u v).natDegree : ℝ) ≤ 4 := by exact_mod_cast natDegree_fUV_le u v
    have hW' : |(∑ x : F, ((χ ((fUV u v).eval (x : F)) : ℤ) : ℝ))| ≤ 192 * Real.sqrt p := by
      refine hW.trans ?_
      have : ((fUV u v).natDegree : ℝ) ^ 2 ≤ 16 := by
        have := Nat.cast_nonneg (α := ℝ) (fUV u v).natDegree
        nlinarith
      nlinarith [Real.sqrt_nonneg (p : ℝ)]
    have hmainR : |(((M3 u v : ℤ) - p : ℤ) : ℝ)| ≤
        4 + |(∑ x : F, ((χ ((fUV u v).eval (x : F)) : ℤ) : ℝ))| := by exact_mod_cast hmain
    have h196 : |(((M3 u v : ℤ) - p : ℤ) : ℝ)| ≤ 196 * Real.sqrt p := by linarith
    have := sq_abs ((((M3 u v : ℤ) - p : ℤ) : ℝ))
    have h2 : |(((M3 u v : ℤ) - p : ℤ) : ℝ)| ^ 2 ≤ (196 * Real.sqrt p) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h196 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at h2
    linarith

end RamanujanTau.Stepanov
