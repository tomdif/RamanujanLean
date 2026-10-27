/-
# The Farey decomposition of `p(n)`

`f(τ) = F(e^{2πiτ}) e^{−2πinτ}` has the explicit primitive on `ℍ`

  `G(τ) = p(n)τ + Σ_{m≠n} p(m) e^{2πi(m−n)τ}/(2πi(m−n))`,  `G(τ+1) = G(τ) + p(n)`.

For `h/k` let `τ_{h,k}(u) = (h + i/(k+iu))/k`. These are vertical segments `w = k + iu` in `w = 1/z`. For Farey
neighbours `h/k < h₂/k₂` (`kh₂ − hk₂ = 1`): `τ_{h,k}(k₂) = τ_{h₂,k₂}(−k)`, the tangency point of their
Ford circles. Summing `∫_{−k₁}^{k₂} f(τ_{h,k}(u)) τ'_{h,k}(u) du` over `F_N` telescopes to
`G(τ₀ + 1) − G(τ₀) = p(n)`.
-/
import RamanujanTau.Rademacher.Farey
import RamanujanTau.Rademacher.FTransform
import RamanujanTau.HardyRamanujan.Coeff

set_option autoImplicit false

namespace Rademacher
open Complex HardyRamanujan Filter Metric
open scoped Real Topology

noncomputable section

/-- the integrand `f(τ) = F(e^{2πiτ}) e^{−2πinτ}`. -/
def fI (n : ℕ) (τ : ℂ) : ℂ := F (cexp (2 * π * I * τ)) * cexp (-(2 * π * I * n * τ))

/-- the terms of the primitive. -/
def gT (n m : ℕ) (τ : ℂ) : ℂ :=
  if m = n then (p n : ℂ) * τ else (p m : ℂ) * cexp (2 * π * I * ((m : ℂ) - n) * τ) / (2 * π * I * ((m : ℂ) - n))

/-- their derivatives. -/
def gT' (n m : ℕ) (τ : ℂ) : ℂ := (p m : ℂ) * cexp (2 * π * I * ((m : ℂ) - n) * τ)

/-- **the primitive**. -/
def Gp (n : ℕ) (τ : ℂ) : ℂ := ∑' m, gT n m τ

lemma hasDerivAt_gT (n m : ℕ) (τ : ℂ) : HasDerivAt (gT n m) (gT' n m τ) τ := by
  unfold gT gT'
  split_ifs with h
  · subst h; simpa using (hasDerivAt_id τ).const_mul (p m : ℂ)
  · have hm : ((m : ℂ) - n) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    have hc : (2 * π * I * ((m : ℂ) - n)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero) hm
    have h1 := ((hasDerivAt_id τ).const_mul (2 * π * I * ((m : ℂ) - n))).cexp
    have h2 := (h1.const_mul (p m : ℂ)).div_const (2 * π * I * ((m : ℂ) - n))
    convert h2 using 1
    simp only [id, mul_one]
    try field_simp

lemma norm_gT' (n m : ℕ) (τ : ℂ) :
    ‖gT' n m τ‖ = p m * Real.exp (-(2 * π * ((m : ℝ) - n) * τ.im)) := by
  rw [gT', norm_mul, Complex.norm_natCast, norm_exp]
  congr 2
  simp
  try ring

/-- the derivative series is `f`. -/
lemma tsum_gT' (n : ℕ) {τ : ℂ} (hτ : 0 < τ.im) : ∑' m, gT' n m τ = fI n τ := by
  have hq : cexp (2 * π * I * τ) ∈ ball (0 : ℂ) 1 := cexp_mem_ball hτ
  have h := (hasSum_F hq).mul_right (cexp (-(2 * π * I * n * τ)))
  rw [fI, ← h.tsum_eq]
  congr 1; funext m
  rw [gT', ← Complex.exp_nat_mul, mul_assoc (p m : ℂ) (cexp _) (cexp _), ← Complex.exp_add]
  congr 2; ring


lemma summable_boundG (n : ℕ) {y : ℝ} (hy : 0 < y) (Y : ℝ) :
    Summable fun m : ℕ => (p m : ℝ) * Real.exp (-(m * (π * y))) * Real.exp (2 * π * n * Y) :=
  (summable_p_exp (by positivity)).mul_right _

lemma summable_gT (n : ℕ) {τ : ℂ} (hτ : 0 < τ.im) : Summable fun m => gT n m τ := by
  set y := τ.im with hy
  refine Summable.of_norm_bounded_eventually (g := fun m : ℕ =>
    (p m : ℝ) * Real.exp (-(m * (π * y))) * Real.exp (2 * π * n * (2 * y))) (summable_boundG n hτ _) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_gt_atTop (n + 1)] with m hm
  have hne : m ≠ n := by omega
  rw [gT, if_neg hne, norm_div]
  have hmn : (1 : ℝ) ≤ ‖2 * π * I * ((m : ℂ) - n)‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    have : (1 : ℝ) ≤ ‖(m : ℂ) - n‖ := by
      rw [show (m : ℂ) - n = ((m - n : ℤ) : ℂ) by push_cast; ring, Complex.norm_intCast]
      have : (1 : ℤ) ≤ (m : ℤ) - n := by omega
      exact_mod_cast (le_abs.mpr (Or.inl this))
    nlinarith [Real.pi_gt_three]
  have hb : ‖gT' n m τ‖ ≤ (p m : ℝ) * Real.exp (-(m * (π * y))) * Real.exp (2 * π * n * (2 * y)) := by
    rw [norm_gT', mul_assoc ((p m : ℝ)) (Real.exp _) (Real.exp _), ← Real.exp_add]
    gcongr
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [← hy]
    nlinarith [Real.pi_pos, mul_nonneg (mul_nonneg Real.pi_pos.le hn) hτ.le, mul_nonneg (mul_nonneg Real.pi_pos.le hm) hτ.le]
  rw [div_le_iff₀ (by linarith)]
  calc ‖(p m : ℂ) * cexp (2 * π * I * ((m : ℂ) - n) * τ)‖ = ‖gT' n m τ‖ := rfl
    _ ≤ _ := hb
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hmn

/-- **`G' = f`** on `ℍ`. -/
lemma hasDerivAt_Gp (n : ℕ) {τ : ℂ} (hτ : 0 < τ.im) : HasDerivAt (Gp n) (fI n τ) τ := by
  set y := τ.im with hy
  set t : Set ℂ := {z | y / 2 < z.im ∧ z.im < 2 * y} with ht
  have hto : IsOpen t := (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)
  have htc : IsPreconnected t := by
    refine Convex.isPreconnected ?_
    exact (convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)
  have hτt : τ ∈ t := ⟨by linarith, by linarith⟩
  have hb : ∀ m z, z ∈ t → ‖gT' n m z‖ ≤ (p m : ℝ) * Real.exp (-(m * (π * y))) * Real.exp (2 * π * n * (2 * y)) := by
    intro m z hz
    rw [norm_gT', mul_assoc ((p m : ℝ)) (Real.exp _) (Real.exp _), ← Real.exp_add]
    gcongr
    have h1 : (y / 2) < z.im := hz.1
    have h2 : z.im < 2 * y := hz.2
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hπ := Real.pi_pos
    rcases le_total (m : ℝ) n with hmn | hmn
    · have := mul_le_mul_of_nonneg_left h2.le (sub_nonneg.mpr hmn)
      nlinarith [mul_nonneg (mul_nonneg hπ.le hm) hτ.le]
    · have := mul_le_mul_of_nonneg_left h1.le (sub_nonneg.mpr hmn)
      nlinarith [mul_nonneg (mul_nonneg hπ.le hn) hτ.le]
  have hsum0 : Summable fun m => gT n m τ := summable_gT n hτ
  have H := hasDerivAt_tsum_of_isPreconnected (summable_boundG n hτ (2 * y)) hto htc
    (fun m z _ => hasDerivAt_gT n m z) hb hτt hsum0 hτt
  rw [tsum_gT' n hτ] at H
  exact H

/-- **`G(τ+1) = G(τ) + p(n)`**. -/
lemma Gp_add_one (n : ℕ) {τ : ℂ} (hτ : 0 < τ.im) : Gp n (τ + 1) = Gp n τ + p n := by
  have hterm : ∀ m, gT n m (τ + 1) = gT n m τ + if m = n then (p n : ℂ) else 0 := by
    intro m
    unfold gT
    split_ifs with h
    · subst h; ring
    · have e : cexp (2 * π * I * ((m : ℂ) - n) * (τ + 1)) = cexp (2 * π * I * ((m : ℂ) - n) * τ) := by
        rw [show 2 * π * I * ((m : ℂ) - n) * (τ + 1) = 2 * π * I * ((m : ℂ) - n) * τ + ((m - n : ℤ) : ℂ) *
          (2 * π * I) by push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      rw [e, add_zero]
  unfold Gp
  simp only [hterm]
  rw [(summable_gT n hτ).tsum_add (summable_of_ne_finset_zero (s := {n}) (fun m hm => by
    rw [Finset.mem_singleton] at hm; rw [if_neg hm])), tsum_ite_eq]

/-! ### the segments -/

/-- `τ_{h,k}(u) = (h + i/(k+iu))/k`. -/
def τc (h k : ℕ) (u : ℝ) : ℂ := ((h : ℂ) + I / ((k : ℂ) + u * I)) / k

lemma wk_ne {k : ℕ} (hk : 0 < k) (u : ℝ) : (k : ℂ) + u * I ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp at this; omega

lemma τc_im {h k : ℕ} (hk : 0 < k) (u : ℝ) : (τc h k u).im = 1 / ((k : ℝ) ^ 2 + u ^ 2) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [τc, show ((k : ℂ)) = ((k : ℝ) : ℂ) from rfl, div_ofReal_im]
  simp only [add_im, natCast_im, zero_add, div_im, I_re, I_im, add_re, natCast_re, mul_re, ofReal_re, ofReal_im,
    mul_im, zero_mul, sub_zero, one_mul, mul_zero, add_zero, Complex.normSq_apply, zero_sub]
  field_simp
  ring

lemma τc_im_pos {h k : ℕ} (hk : 0 < k) (u : ℝ) : 0 < (τc h k u).im := by
  rw [τc_im hk]; have : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

/-- `τ'(u) = 1/(k(k+iu)²)`. -/
def dτc (k : ℕ) (u : ℝ) : ℂ := 1 / ((k : ℂ) * ((k : ℂ) + u * I) ^ 2)

lemma hasDerivAt_τc {h k : ℕ} (hk : 0 < k) (u : ℝ) : HasDerivAt (τc h k) (dτc k u) u := by
  have hw := wk_ne hk u
  have h1 : HasDerivAt (fun u : ℝ => (k : ℂ) + u * I) I u := by
    simpa using ((hasDerivAt_id u).ofReal_comp.mul_const I).const_add (k : ℂ)
  have h2 := (((hasDerivAt_inv hw).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt u h1).const_mul I
  have h3 := (h2.const_add (h : ℂ)).div_const (k : ℂ)
  convert h3 using 1
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [dτc, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  field_simp
  ring_nf
  rw [I_sq]; ring

/-- the segment integral. -/
def piece (n h k : ℕ) (a b : ℝ) : ℂ := ∫ u in (-a)..b, fI n (τc h k u) * dτc k u

lemma fI_cont (n : ℕ) {h k : ℕ} (hk : 0 < k) : Continuous fun u : ℝ => fI n (τc h k u) := by
  have hτ : Continuous (τc h k) := continuous_iff_continuousAt.mpr fun u => (hasDerivAt_τc hk u).continuousAt
  unfold fI
  refine Continuous.mul ?_ (by fun_prop)
  exact F_diff.continuousOn.comp_continuous (by fun_prop) (fun u => cexp_mem_ball (τc_im_pos hk u))

lemma dτc_cont {k : ℕ} (hk : 0 < k) : Continuous (dτc k) := by
  unfold dτc
  exact continuous_const.div (by fun_prop) fun u => mul_ne_zero (by exact_mod_cast hk.ne') (pow_ne_zero _ (wk_ne hk u))

/-- **FTC on a segment**. -/
lemma piece_eq (n h k : ℕ) (hk : 0 < k) (a b : ℝ) :
    piece n h k a b = Gp n (τc h k b) - Gp n (τc h k (-a)) := by
  unfold piece
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => Gp n (τc h k u)) (fun u _ => ?_) ?_
  · have hG := (hasDerivAt_Gp n (τc_im_pos (h := h) hk u))
    have := (hG.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt u (hasDerivAt_τc hk u)
    simpa [Function.comp, mul_comm] using this
  · exact ((fI_cont n hk).mul (dτc_cont hk)).intervalIntegrable _ _

/-- **the tangency points** of neighbouring Ford circles agree. -/
lemma τc_tangent {h k h₂ k₂ : ℕ} (hk : 0 < k) (hk₂ : 0 < k₂) (hdet : k * h₂ = h * k₂ + 1) :
    τc h k k₂ = τc h₂ k₂ (-k) := by
  have hdet' : (k : ℂ) * h₂ = h * k₂ + 1 := by exact_mod_cast hdet
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk20 : (k₂ : ℂ) ≠ 0 := by exact_mod_cast hk₂.ne'
  have hw1 : (k : ℂ) + (k₂ : ℝ) * I ≠ 0 := wk_ne hk _
  have hw2 : (k₂ : ℂ) + ((-k : ℝ) : ℂ) * I ≠ 0 := wk_ne hk₂ _
  unfold τc
  set w : ℂ := (k : ℂ) + (k₂ : ℝ) * I with hwdef
  have e2 : (k₂ : ℂ) + ((-k : ℝ) : ℂ) * I = -I * w := by
    rw [hwdef]; push_cast; ring_nf; rw [I_sq]; ring
  rw [e2]
  have hI : -I ≠ 0 := neg_ne_zero.mpr I_ne_zero
  rw [div_eq_div_iff hk0 hk20]
  field_simp
  rw [hwdef]
  push_cast
  ring_nf
  linear_combination (-((k₂ : ℂ) * I + k)) * hdet'

/-! ### telescoping along the Farey chain -/

/-- `Σ_j piece(x_j; k_{j−1}, k_{j+1})` (the last element only closes the chain). -/
def pieceSum (n : ℕ) : ℕ → List (ℕ × ℕ) → ℂ
  | _, [] => 0
  | _, [_] => 0
  | kp, x :: y :: rest => piece n x.1 x.2 kp y.2 + pieceSum n x.2 (y :: rest)

/-- the last element and its predecessor's denominator. -/
def lastPrev : ℕ → List (ℕ × ℕ) → (ℕ × ℕ) × ℕ
  | kp, [] => ((0, 1), kp)
  | kp, [x] => (x, kp)
  | _, x :: y :: rest => lastPrev x.2 (y :: rest)

lemma tele (n N : ℕ) : ∀ (rest : List (ℕ × ℕ)) (kp : ℕ) (x : ℕ × ℕ),
    List.IsChain (Farey.Nb N) (x :: rest) → (∀ z ∈ x :: rest, 0 < z.2) →
    pieceSum n kp (x :: rest) = Gp n (τc (lastPrev kp (x :: rest)).1.1 (lastPrev kp (x :: rest)).1.2
      (-((lastPrev kp (x :: rest)).2 : ℝ))) - Gp n (τc x.1 x.2 (-(kp : ℝ))) := by
  intro rest
  induction rest with
  | nil => intro kp x _ _; simp [pieceSum, lastPrev]
  | cons y rest ih =>
    intro kp x hc hpos
    rw [List.isChain_cons_cons] at hc
    have hx : 0 < x.2 := hpos x (by simp)
    have hy : 0 < y.2 := hpos y (by simp)
    have ih' := ih x.2 y hc.2 (fun z hz => hpos z (List.mem_cons_of_mem _ hz))
    rw [pieceSum, ih', lastPrev, piece_eq n x.1 x.2 hx, τc_tangent hx hy hc.1.1]
    ring

lemma lastPrev_append (kp : ℕ) (z : ℕ × ℕ) : ∀ (l : List (ℕ × ℕ)) (hl : l ≠ []),
    lastPrev kp (l ++ [z]) = (z, (l.getLast hl).2) := by
  intro l
  induction l generalizing kp with
  | nil => intro h; exact absurd rfl h
  | cons x l ih =>
    intro _
    rcases l with _ | ⟨y, l⟩
    · simp [lastPrev]
    · simp only [List.cons_append]
      rw [lastPrev]
      have := ih x.2 (List.cons_ne_nil y l)
      simpa using this

/-- the Farey list of order `N`, from `0/1` to `1/1`. -/
def fareyList (N : ℕ) : List (ℕ × ℕ) := (0, 1) :: (Farey.sb N 0 1 1 1 ++ [(1, 1)])

lemma farey_chain (N : ℕ) : List.IsChain (Farey.Nb N) (fareyList N) :=
  Farey.chain N 0 1 1 1 (by norm_num) one_pos one_pos

lemma farey_pos (N : ℕ) : ∀ z ∈ fareyList N, 0 < z.2 := by
  intro z hz
  simp only [fareyList, List.mem_cons, List.mem_append] at hz
  rcases hz with rfl | hz | hz
  · exact one_pos
  · exact (Farey.mem_sb N 0 1 1 1 (by norm_num) z hz).2.2.1
  · rcases hz with rfl | h
    · exact one_pos
    · simp at h

/-- **the Farey decomposition** `p(n) = Σ_{h/k ∈ F_N} ∫_{−k₁}^{k₂} f(τ_{h,k}(u)) τ'(u) du`. -/
theorem farey_decomp (n N : ℕ) (hN : 1 ≤ N) : (p n : ℂ) = pieceSum n N (fareyList N) := by
  have ht := tele n N (Farey.sb N 0 1 1 1 ++ [(1, 1)]) N (0, 1) (farey_chain N) (farey_pos N)
  rw [fareyList, ht]
  rw [show (0, 1) :: (Farey.sb N 0 1 1 1 ++ [(1, 1)]) = ((0, 1) :: Farey.sb N 0 1 1 1) ++ [(1, 1)] by simp,
    lastPrev_append N (1, 1) _ (List.cons_ne_nil _ _)]
  -- the predecessor of `1/1` has denominator `N`
  set y := ((0, 1) :: Farey.sb N 0 1 1 1).getLast (List.cons_ne_nil _ _) with hy
  have hyN : y.2 = N := by
    have hc := farey_chain N
    rw [fareyList, show (0, 1) :: (Farey.sb N 0 1 1 1 ++ [(1, 1)]) = ((0, 1) :: Farey.sb N 0 1 1 1) ++ [(1, 1)] by
      simp, List.isChain_append] at hc
    have hrel := hc.2.2 y (by simp [hy, List.getLast?_eq_some_getLast]) (1, 1) (by simp)
    have hmem : y ∈ (0, 1) :: Farey.sb N 0 1 1 1 := List.getLast_mem _
    have hle : y.2 ≤ N := by
      rcases List.mem_cons.mp hmem with h | h
      · rw [h]; exact hN
      · exact (Farey.mem_sb N 0 1 1 1 (by norm_num) y h).2.2.2.1
    have := hrel.2
    simp only at this hrel
    omega
  simp only [hyN]
  have hτ : τc 1 1 (-(N : ℝ)) = τc 0 1 (-(N : ℝ)) + 1 := by
    simp [τc]; ring
  rw [hτ, Gp_add_one n (τc_im_pos one_pos _)]
  ring

end

end Rademacher
