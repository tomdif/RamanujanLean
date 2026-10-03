/-
# Change of `z` for Appell–Lerch sums, formally

Everything lives in `L = ℂ((t))`, `q = t^N`. Points are monomials `c·tᵉ`.
Part 1: theta terms, products of two thetas as `z`-series (`TT`), their recursion and evaluation.
-/
import RamanujanTau.ALBase

set_option autoImplicit false

namespace ALz
open HahnSeries Finset

lemma mono_zpow (β : ℤ) (c : ℂ) (k : ℤ) : (mono β c) ^ k = mono (k * β) (c ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, mono, single_pow, zpow_natCast, nsmul_eq_mul]
  · rw [zpow_neg, zpow_natCast, mono, single_pow, inv_single, zpow_neg, zpow_natCast, nsmul_eq_mul]
    congr 1; ring

section Terms
variable (N : ℕ)

/-- the `k`-th theta term `(−1)^k q^{C(k,2)} (c tᵉ)^k`. -/
noncomputable def thT (e : ℤ) (c : ℂ) (k : ℤ) : L := mono (thE N e k) (thC c k)

variable {N}

lemma thT_succ (e : ℤ) {c : ℂ} (hc : c ≠ 0) (k : ℤ) :
    thT N e c (k + 1) = mono (N * k + e) (-c) * thT N e c k := by
  rw [thT, thT, mono_mul]
  congr 1
  · unfold thE; rw [c2_succ]; ring
  · unfold thC
    rw [zpow_add₀ (by norm_num), zpow_add₀ hc, zpow_one, zpow_one]; ring

lemma thT_eval (e β : ℤ) (c cp : ℂ) (k : ℤ) :
    thT N e c k * (mono β cp) ^ k = thT N (e + β) (c * cp) k := by
  rw [mono_zpow, thT, thT, mono_mul]
  congr 1
  · unfold thE; ring
  · unfold thC; rw [mul_zpow]; ring

lemma thE_le_bound (hN : 1 ≤ N) (e k n : ℤ) (h : thE N e k ≤ n) : |k| ≤ 2 * |n| + 2 * |e| + 1 := by
  unfold thE at h
  have h2 := two_c2 k
  have h0 := c2_nonneg k
  have : c2 k ≤ (N : ℤ) * c2 k := le_mul_of_one_le_left h0 (by exact_mod_cast hN)
  rcases abs_cases k with ⟨hk, _⟩ | ⟨hk, _⟩ <;> rcases abs_cases e with ⟨he, _⟩ | ⟨he, _⟩ <;>
    rcases abs_cases n with ⟨hn, _⟩ | ⟨hn, _⟩ <;> rw [hk, he, hn] <;> nlinarith

end Terms

/-! ## Products of two thetas as `z`-series -/

section TT
variable {N : ℕ} (hN : 1 ≤ N)
include hN

/-- the `i`-family of `[z^k] θ(w₁z)θ(w₂z)`. -/
noncomputable def ttF (e₁ : ℤ) (c₁ : ℂ) (e₂ : ℤ) (c₂ : ℂ) (k : ℤ) : SummableFamily ℤ ℂ ℤ :=
  monoFam (fun i => thE N e₁ i + thE N e₂ (k - i)) (fun i => thC c₁ i * thC c₂ (k - i))
    (-(e₁ * e₁) - 1 + (-(e₂ * e₂) - 1))
    (fun i => add_le_add (thE_lb hN e₁ i) (thE_lb hN e₂ (k - i)))
    (fun n => (Set.finite_Icc (-(2 * |n + e₂ * e₂ + 1| + 2 * |e₁| + 1))
      (2 * |n + e₂ * e₂ + 1| + 2 * |e₁| + 1)).subset fun i hi => by
        have h1 := thE_lb hN e₂ (k - i)
        have := thE_le_bound hN e₁ i (n + e₂ * e₂ + 1) (by simp only [Set.mem_setOf_eq] at hi; omega)
        rw [abs_le] at this
        exact ⟨this.1, this.2⟩)

lemma ttF_apply (e₁ : ℤ) (c₁ : ℂ) (e₂ : ℤ) (c₂ : ℂ) (k i : ℤ) :
    ttF hN e₁ c₁ e₂ c₂ k i = thT N e₁ c₁ i * thT N e₂ c₂ (k - i) := by
  rw [ttF, monoFam_apply, thT, thT, mono_mul]

/-- `[z^k] θ(w₁z)θ(w₂z)`. -/
noncomputable def TT (e₁ : ℤ) (c₁ : ℂ) (e₂ : ℤ) (c₂ : ℂ) (k : ℤ) : L := hs (ttF hN e₁ c₁ e₂ c₂ k)

/-- the quasi-periodicity `T_{k+2} = q^k w₁ w₂ T_k`. -/
theorem TT_rec (e₁ : ℤ) {c₁ : ℂ} (h₁ : c₁ ≠ 0) (e₂ : ℤ) {c₂ : ℂ} (h₂ : c₂ ≠ 0) (k : ℤ) :
    TT hN e₁ c₁ e₂ c₂ (k + 2) = mono (N * k + (e₁ + e₂)) (c₁ * c₂) * TT hN e₁ c₁ e₂ c₂ k := by
  refine hsum_reindex _ _ (Equiv.addRight 1) _ fun i => ?_
  rw [Equiv.coe_addRight, ttF_apply, ttF_apply, show k + 2 - (i + 1) = (k - i) + 1 by ring,
    thT_succ e₁ h₁, thT_succ e₂ h₂]
  have : mono (N * i + e₁ + (N * (k - i) + e₂)) (-c₁ * -c₂) = mono (N * k + (e₁ + e₂)) (c₁ * c₂) := by
    congr 1 <;> ring
  rw [← this, ← mono_mul]
  ring

end TT


/-! ## Evaluation of `TT` -/

section TTeval
variable {N : ℕ} (hN : 1 ≤ N)
include hN

/-- `(i, j) ↦ (i + j, i)`. -/
def diagEquiv : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (p.1 + p.2, p.1)
  invFun p := (p.2, p.1 - p.2)
  left_inv p := by simp
  right_inv p := by simp

lemma thF_apply (e : ℤ) (c : ℂ) (k : ℤ) : thF hN e c k = thT N e c k := rfl

/-- the evaluated family `k ↦ p^k · [z^k] θ(w₁z)θ(w₂z)`. -/
noncomputable def ttEv (e₁ : ℤ) (c₁ : ℂ) (e₂ : ℤ) (c₂ : ℂ) (β : ℤ) (cp : ℂ) : SummableFamily ℤ ℂ ℤ :=
  rowFam (SummableFamily.Equiv diagEquiv
    (SummableFamily.mul (thF hN (e₁ + β) (c₁ * cp)) (thF hN (e₂ + β) (c₂ * cp))))

theorem ttEv_apply (e₁ : ℤ) (c₁ : ℂ) (e₂ : ℤ) (c₂ : ℂ) (β : ℤ) {cp : ℂ} (hp : cp ≠ 0) (k : ℤ) :
    ttEv hN e₁ c₁ e₂ c₂ β cp k = (mono β cp) ^ k * TT hN e₁ c₁ e₂ c₂ k := by
  refine hsum_reindex _ _ (Equiv.refl ℤ) _ fun i => ?_
  have hm : (mono β cp) ^ k = (mono β cp) ^ i * (mono β cp) ^ (k - i) := by
    rw [← zpow_add₀ (by simp [mono, hp])]; ring_nf
  simp only [Equiv.refl_apply, row_apply, SummableFamily.Equiv_toFun, SummableFamily.mul_toFun]
  rw [ttF_apply, hm, show diagEquiv.symm (k, i) = (i, k - i) from rfl, thF_apply, thF_apply,
    ← thT_eval, ← thT_eval]
  ring

/-- **evaluation**: `Σ_k p^k [z^k] θ(w₁z)θ(w₂z) = θ(w₁p) θ(w₂p)`. -/
theorem ttEv_sum (e₁ : ℤ) (c₁ : ℂ) (e₂ : ℤ) (c₂ : ℂ) (β : ℤ) (cp : ℂ) :
    hs (ttEv hN e₁ c₁ e₂ c₂ β cp) = θ hN (e₁ + β) (c₁ * cp) * θ hN (e₂ + β) (c₂ * cp) := by
  rw [ttEv, hs_rowFam, hs_eq, SummableFamily.hsum_equiv, SummableFamily.hsum_mul]
  rfl

end TTeval


/-! ## The Appell part `𝒜(z) = θ(xz)·A(x,z)` as a `z`-series

`A(x,z) = Σ_r (−1)^r q^{C(r,2)} z^r/(1 − q^{r−1}xz)`, expanded on the cone
`(r ≥ 1, j ≥ 0) ∪ (r ≤ 0, j ≤ −1)` (the geometric expansion valid for `0 < val(xz) < N`).
`[z^k] 𝒜 = Σ_{(r,j) ∈ cone} sgn(r) (−1)^{r+i} q^{C(r,2)+C(i,2)+(r−1)j} x^{k−r}`, `i = k − r − j`. -/

section Appell

/-- the expansion cone. -/
def cone (r j : ℤ) : Prop := (1 ≤ r ∧ 0 ≤ j) ∨ (r ≤ 0 ∧ j ≤ -1)

instance (r j : ℤ) : Decidable (cone r j) := by unfold cone; infer_instance

/-- the sign of the geometric expansion. -/
def sgnC (r : ℤ) : ℂ := if 1 ≤ r then 1 else -1

lemma cone_mul_nonneg {r j : ℤ} (h : cone r j) : 0 ≤ (r - 1) * j := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> nlinarith

variable (N : ℕ)

/-- exponent of the `(r,j)` term of `[z^k] 𝒜`. -/
def aaExp (a k r j : ℤ) : ℤ := N * (c2 r + c2 (k - r - j) + (r - 1) * j) + a * (k - r)

variable {N}

lemma aaExp_lb (hN : 1 ≤ N) (a k r j : ℤ) (h : cone r j) :
    -((|a| + 1) * (|a| + 1)) - |a| * |k| ≤ aaExp N a k r j := by
  unfold aaExp
  have h1 := two_c2 r
  have h0 := c2_nonneg (k - r - j)
  have h3 := cone_mul_nonneg h
  have hr := c2_nonneg r
  have hX : c2 r + c2 (k - r - j) + (r - 1) * j ≤ (N : ℤ) * (c2 r + c2 (k - r - j) + (r - 1) * j) :=
    le_mul_of_one_le_left (by linarith) (by exact_mod_cast hN)
  have ha : -(|a| * (|k| + |r|)) ≤ a * (k - r) := by
    have := abs_mul a (k - r)
    have := neg_abs_le (a * (k - r))
    have := abs_sub k r
    nlinarith [abs_nonneg a]
  rcases abs_cases r with ⟨hr', _⟩ | ⟨hr', _⟩ <;> rw [hr'] at ha <;>
    nlinarith [abs_nonneg a, abs_nonneg k, sq_nonneg (r - |a| - 1), sq_nonneg (r + |a| + 1)]


/-- crude size bounds on the cone from an upper bound on the exponent. -/
lemma aaExp_bound (hN : 1 ≤ N) (a k r j n : ℤ) (h : cone r j) (hn : aaExp N a k r j ≤ n) :
    |r| ≤ 2 * |a| + 1 + 2 * (|n| + |a| * |k|) ∧
    |k - r - j| ≤ 1 + 2 * ((|n| + |a| * |k|) + |a| * (2 * |a| + 1 + 2 * (|n| + |a| * |k|))) := by
  unfold aaExp at hn
  have h1 := two_c2 r
  have h2 := two_c2 (k - r - j)
  have h0 := c2_nonneg (k - r - j)
  have h3 := cone_mul_nonneg h
  have hr := c2_nonneg r
  have hX : c2 r + c2 (k - r - j) + (r - 1) * j ≤ (N : ℤ) * (c2 r + c2 (k - r - j) + (r - 1) * j) :=
    le_mul_of_one_le_left (by linarith) (by exact_mod_cast hN)
  have ha : -(|a| * (|k| + |r|)) ≤ a * (k - r) := by
    have := abs_mul a (k - r)
    have := neg_abs_le (a * (k - r))
    have := abs_sub k r
    nlinarith [abs_nonneg a]
  have hn' : n ≤ |n| := le_abs_self n
  have hA := abs_nonneg a
  have hK := abs_nonneg k
  -- bound on r
  have hR : |r| ≤ 2 * |a| + 1 + 2 * (|n| + |a| * |k|) := by
    have hc : c2 r ≤ |n| + |a| * |k| + |a| * |r| := by nlinarith
    have hsq : r * r ≤ 2 * (|n| + |a| * |k|) + (2 * |a| + 1) * |r| := by
      rcases abs_cases r with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] at hc ⊢ <;> nlinarith
    have hrr : |r| * |r| = r * r := by rw [← abs_mul, abs_mul_self]
    by_contra hc'
    push Not at hc'
    have hpos : 0 < |r| := by nlinarith [abs_nonneg n]
    have hM : 0 ≤ |n| + |a| * |k| := by nlinarith [abs_nonneg n]
    have := mul_lt_mul_of_pos_right hc' hpos
    nlinarith
  refine ⟨hR, ?_⟩
  set i := k - r - j
  have hc : c2 i ≤ |n| + |a| * |k| + |a| * |r| := by nlinarith
  have hc2 : c2 i ≤ (|n| + |a| * |k|) + |a| * (2 * |a| + 1 + 2 * (|n| + |a| * |k|)) := by
    nlinarith [mul_le_mul_of_nonneg_left hR hA]
  have hsq : i * i ≤ 2 * ((|n| + |a| * |k|) + |a| * (2 * |a| + 1 + 2 * (|n| + |a| * |k|))) + |i| := by
    rcases abs_cases i with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> nlinarith
  have hii : |i| * |i| = i * i := by rw [← abs_mul, abs_mul_self]
  by_contra hc'
  push Not at hc'
  have hM : 0 ≤ (|n| + |a| * |k|) + |a| * (2 * |a| + 1 + 2 * (|n| + |a| * |k|)) := by
    nlinarith [abs_nonneg n]
  have hpos : 0 < |i| := by nlinarith
  have := mul_lt_mul_of_pos_right hc' hpos
  nlinarith


variable (N)

/-- exponent, with a harmless dummy off the cone. -/
def aaE (a k : ℤ) (rj : ℤ × ℤ) : ℤ := if cone rj.1 rj.2 then aaExp N a k rj.1 rj.2 else |rj.1| + |rj.2|

/-- coefficient (zero off the cone). -/
noncomputable def aaC (cx : ℂ) (k : ℤ) (rj : ℤ × ℤ) : ℂ :=
  if cone rj.1 rj.2 then sgnC rj.1 * (-1) ^ (rj.1 + (k - rj.1 - rj.2)) * cx ^ (k - rj.1) else 0

variable {N}

/-- the big box containing the fibre of `aaE` over `n`. -/
def aaBox (a k n : ℤ) : ℤ :=
  |n| + |k| + (2 * |a| + 1 + 2 * (|n| + |a| * |k|)) +
    (1 + 2 * ((|n| + |a| * |k|) + |a| * (2 * |a| + 1 + 2 * (|n| + |a| * |k|))))

lemma aaE_fin (hN : 1 ≤ N) (a k n : ℤ) : {rj : ℤ × ℤ | aaE N a k rj = n}.Finite := by
  refine ((Set.finite_Icc (-aaBox a k n) (aaBox a k n)).prod
    (Set.finite_Icc (-aaBox a k n) (aaBox a k n))).subset fun ⟨r, j⟩ h => ?_
  simp only [Set.mem_setOf_eq, aaE] at h
  have hA := abs_nonneg a; have hK := abs_nonneg k; have hn := abs_nonneg n
  have hP : 0 ≤ |n| + |a| * |k| := by positivity
  have hQ : 0 ≤ |a| * (2 * |a| + 1 + 2 * (|n| + |a| * |k|)) := by positivity
  split_ifs at h with hc
  · obtain ⟨h1, h2⟩ := aaExp_bound hN a k r j n hc h.le
    have h3 : |j| ≤ |k| + |r| + |k - r - j| := by
      have := abs_sub (k - r) (k - r - j)
      have := abs_sub k r
      rw [show k - r - (k - r - j) = j by ring] at *
      linarith
    simp only [Set.mem_prod, Set.mem_Icc, aaBox]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> [have := neg_abs_le r; have := le_abs_self r;
      have := neg_abs_le j; have := le_abs_self j] <;> linarith
  · have hr := abs_nonneg r; have hj := abs_nonneg j
    have h1 : |r| ≤ |n| := by rw [← h]; have := le_abs_self (|r| + |j|); linarith
    have h2 : |j| ≤ |n| := by rw [← h]; have := le_abs_self (|r| + |j|); linarith
    simp only [Set.mem_prod, Set.mem_Icc, aaBox]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> [have := neg_abs_le r; have := le_abs_self r;
      have := neg_abs_le j; have := le_abs_self j] <;> nlinarith

lemma aaE_lb (hN : 1 ≤ N) (a k : ℤ) (rj : ℤ × ℤ) :
    -((|a| + 1) * (|a| + 1)) - |a| * |k| ≤ aaE N a k rj := by
  unfold aaE
  split_ifs with hc
  · exact aaExp_lb hN a k _ _ hc
  · have := abs_nonneg rj.1; have := abs_nonneg rj.2; have := abs_nonneg a; have := abs_nonneg k
    nlinarith

/-- the `(r,j)`-family of `[z^k] 𝒜`. -/
noncomputable def aaF (hN : 1 ≤ N) (a : ℤ) (cx : ℂ) (k : ℤ) : SummableFamily ℤ ℂ (ℤ × ℤ) :=
  monoFam (aaE N a k) (aaC cx k) _ (aaE_lb hN a k) (aaE_fin hN a k)

/-- `[z^k] θ(xz) A(x,z)`. -/
noncomputable def AA (hN : 1 ≤ N) (a : ℤ) (cx : ℂ) (k : ℤ) : L := hs (aaF hN a cx k)

lemma aaF_apply (hN : 1 ≤ N) (a : ℤ) (cx : ℂ) (k : ℤ) (rj : ℤ × ℤ) :
    aaF hN a cx k rj = if cone rj.1 rj.2 then
      mono (aaExp N a k rj.1 rj.2) (sgnC rj.1 * (-1) ^ (rj.1 + (k - rj.1 - rj.2)) * cx ^ (k - rj.1))
      else 0 := by
  rw [aaF, monoFam_apply, aaE, aaC]
  split_ifs <;> simp [mono]


lemma cone_succ_iff {r j : ℤ} (hr : r ≠ 0) : cone (r + 1) j ↔ cone r j := by
  unfold cone; constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega

lemma sgnC_succ {r : ℤ} (hr : r ≠ 0) : sgnC (r + 1) = sgnC r := by
  unfold sgnC; split_ifs <;> first | rfl | omega

lemma neg_one_zpow_add_two (m : ℤ) : ((-1 : ℂ)) ^ (m + 2) = (-1) ^ m := by
  rw [zpow_add₀ (by norm_num)]; norm_num

/-- off the boundary slice, the shift `r ↦ r+1` multiplies by `q^k x`. -/
lemma aaF_shift (hN : 1 ≤ N) (a : ℤ) {cx : ℂ} (hx : cx ≠ 0) (k r j : ℤ) (hr : r ≠ 0) :
    aaF hN a cx (k + 2) (r + 1, j) = mono (N * k + a) cx * aaF hN a cx k (r, j) := by
  rw [aaF_apply, aaF_apply]
  simp only [cone_succ_iff hr]
  split_ifs with hc
  · rw [mono_mul]
    congr 1
    · unfold aaExp
      rw [show k + 2 - (r + 1) - j = (k - r - j) + 1 by ring, c2_succ, c2_succ]; ring
    · rw [sgnC_succ hr, show r + 1 + (k + 2 - (r + 1) - j) = (r + (k - r - j)) + 2 by ring,
        neg_one_zpow_add_two, show k + 2 - (r + 1) = (k - r) + 1 by ring, zpow_add₀ hx, zpow_one]
      ring
  · rw [mul_zero]

/-- the boundary term. -/
noncomputable def bdry (a : ℤ) (cx : ℂ) (k j : ℤ) : L :=
  mono (a * (k + 1)) (-cx ^ (k + 1)) * thT N 0 1 (k + 1 - j)

lemma aaF_bdry (hN : 1 ≤ N) (a : ℤ) {cx : ℂ} (hx : cx ≠ 0) (k j : ℤ) :
    aaF hN a cx (k + 2) (0 + 1, j) = mono (N * k + a) cx * aaF hN a cx k (0, j) + bdry (N := N) a cx k j := by
  rw [aaF_apply, aaF_apply, bdry, thT, mono_mul]
  simp only [zero_add]
  by_cases hj : 0 ≤ j
  · have h1 : cone 1 j := Or.inl ⟨le_rfl, hj⟩
    have h0 : ¬ cone 0 j := by unfold cone; omega
    rw [if_pos h1, if_neg h0, mul_zero, zero_add]
    congr 1
    · unfold aaExp thE; rw [show k + 2 - 1 - j = k + 1 - j by ring]; simp [c2]; ring
    · unfold sgnC thC; rw [if_pos le_rfl, show (1 : ℤ) + (k + 2 - 1 - j) = (k + 1 - j) + 1 by ring,
        zpow_add₀ (by norm_num), show k + 2 - 1 = k + 1 by ring]; simp; ring
  · have h1 : ¬ cone 1 j := by unfold cone; omega
    have h0 : cone 0 j := Or.inr ⟨le_rfl, by omega⟩
    rw [if_neg h1, if_pos h0, mono_mul]
    have he : N * k + a + aaExp N a k 0 j = a * (k + 1) + thE N 0 (k + 1 - j) := by
      unfold aaExp thE
      rw [show k + 1 - j = (k - j) + 1 by ring, c2_succ]; simp [c2]; ring
    rw [he, mono, mono, ← single_add]
    have hc : cx * (sgnC 0 * (-1) ^ (k - 0 - j) * cx ^ (k - 0)) + -cx ^ (k + 1) * thC 1 (k + 1 - j) = 0 := by
      unfold sgnC thC
      rw [if_neg (by norm_num), show k + 1 - j = (k - j) + 1 by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
        zpow_add₀ hx]
      simp only [sub_zero, one_zpow, zpow_one, mul_one]
      ring
    rw [hc, map_zero]


/-- `(r, j) ↦ (r − 1, j)`. -/
def shiftR : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (p.1 - 1, p.2)
  invFun p := (p.1 + 1, p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- `j ↦ (0, j)`. -/
def slice0 : ℤ ↪ ℤ × ℤ := ⟨fun j => (0, j), fun _ _ h => (Prod.mk.inj h).2⟩

/-- the boundary family `j ↦ bdry j`. -/
noncomputable def bdryF (hN : 1 ≤ N) (a : ℤ) (cx : ℂ) (k : ℤ) : SummableFamily ℤ ℂ ℤ :=
  (mono (a * (k + 1)) (-cx ^ (k + 1))) • SummableFamily.Equiv (Equiv.subLeft (k + 1)) (thF hN 0 1)

lemma bdryF_apply (hN : 1 ≤ N) (a : ℤ) (cx : ℂ) (k j : ℤ) :
    bdryF hN a cx k j = bdry (N := N) a cx k j := by
  simp only [bdryF, SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul,
    SummableFamily.Equiv_toFun, Equiv.subLeft_symm_apply, bdry]
  rw [show -j + (k + 1) = k + 1 - j by ring]
  rfl

lemma hs_bdryF (hN : 1 ≤ N) (a : ℤ) (cx : ℂ) (k : ℤ) : hs (bdryF hN a cx k) = 0 := by
  rw [bdryF, hs_eq, SummableFamily.hsum_smul, SummableFamily.hsum_equiv]
  have := θ_one hN
  rw [θ, hs_eq] at this
  rw [this, mul_zero]

/-- **quasi-periodicity of the Appell part**: `𝒜_{k+2} = q^k x 𝒜_k`. -/
theorem AA_rec (hN : 1 ≤ N) (a : ℤ) {cx : ℂ} (hx : cx ≠ 0) (k : ℤ) :
    AA hN a cx (k + 2) = mono (N * k + a) cx * AA hN a cx k := by
  have hG : ∀ b : ℤ × ℤ, SummableFamily.Equiv shiftR (aaF hN a cx (k + 2)) b =
      ((mono (N * k + a) cx) • aaF hN a cx k + (bdryF hN a cx k).embDomain slice0) b := by
    rintro ⟨r, j⟩
    simp only [SummableFamily.Equiv_toFun, SummableFamily.add_apply, SummableFamily.smul_apply,
      HahnSeries.of_symm_smul_of_eq_mul]
    show aaF hN a cx (k + 2) (r + 1, j) = _
    by_cases hr : r = 0
    · subst hr
      rw [aaF_bdry hN a hx, show ((0 : ℤ), j) = slice0 j from rfl, SummableFamily.embDomain_image,
        bdryF_apply]
    · rw [aaF_shift hN a hx k r j hr, SummableFamily.embDomain_notin_range, add_zero]
      rintro ⟨j', hj'⟩
      exact hr (congrArg Prod.fst hj').symm
  have := hsum_congr _ _ hG
  rw [hs_eq, hs_eq, SummableFamily.hsum_equiv, SummableFamily.hsum_add, SummableFamily.hsum_smul,
    SummableFamily.hsum_embDomain] at this
  rw [AA, AA, hs_eq, hs_eq, this, ← hs_eq (bdryF hN a cx k), hs_bdryF, add_zero]

end Appell


/-! ## The Appell–Lerch sum `A(x,p)` at a monomial point -/

section Aser
variable (N : ℕ)

/-- exponent of the `(r,j)` term of `A(x,p) = Σ_cone sgn(r)(−1)^r q^{C(r,2)} p^r (q^{r−1}xp)^j`. -/
def asExp (a β r j : ℤ) : ℤ := N * c2 r + β * r + (N * (r - 1) + a + β) * j

variable {N}

lemma cone_lin {a β r j : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) (h : cone r j) :
    |j| ≤ (N * (r - 1) + a + β) * j := by
  have hN0 : (0 : ℤ) ≤ N := by positivity
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h2]
    have : 0 ≤ (N : ℤ) * (r - 1) := mul_nonneg hN0 (by omega)
    have : 0 ≤ (N * (r - 1) + a + β - 1) * j := mul_nonneg (by omega) h2
    nlinarith
  · rw [abs_of_neg (by omega)]
    have : (N : ℤ) * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN0 h1
    have : 0 ≤ (N * (r - 1) + a + β + 1) * j :=
      mul_nonneg_of_nonpos_of_nonpos (by nlinarith) (by omega)
    nlinarith

lemma asExp_ge (hN : 1 ≤ N) {a β r j : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) (h : cone r j) :
    c2 r - |β| * |r| + |j| ≤ asExp N a β r j := by
  unfold asExp
  have := cone_lin hlo hhi h
  have h0 := c2_nonneg r
  have : c2 r ≤ (N : ℤ) * c2 r := le_mul_of_one_le_left h0 (by exact_mod_cast hN)
  have : -(|β| * |r|) ≤ β * r := by rw [← abs_mul]; exact neg_abs_le _
  linarith

lemma c2_sub_bound (b r : ℤ) : -((|b| + 1) * (|b| + 1)) ≤ c2 r - |b| * |r| := by
  have h := two_c2 r
  rcases abs_cases r with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;>
    nlinarith [abs_nonneg b, sq_nonneg (r - |b| - 1), sq_nonneg (r + |b| + 1)]

lemma c2_sub_le (b r n : ℤ) (h : c2 r - |b| * |r| ≤ n) : |r| ≤ 2 * |b| + 1 + 2 * |n| := by
  have h2 := two_c2 r
  have hrr : |r| * |r| = r * r := by rw [← abs_mul, abs_mul_self]
  have hsq : r * r ≤ 2 * |n| + (2 * |b| + 1) * |r| := by
    rcases abs_cases r with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] at h ⊢ <;> nlinarith [le_abs_self n]
  by_contra hc
  push Not at hc
  have hpos : 0 < |r| := by nlinarith [abs_nonneg n, abs_nonneg b]
  have := mul_lt_mul_of_pos_right hc hpos
  nlinarith [abs_nonneg n]

variable (N)

def asE (a β : ℤ) (rj : ℤ × ℤ) : ℤ := if cone rj.1 rj.2 then asExp N a β rj.1 rj.2 else |rj.1| + |rj.2|

noncomputable def asC (cx cp : ℂ) (rj : ℤ × ℤ) : ℂ :=
  if cone rj.1 rj.2 then sgnC rj.1 * (-1) ^ rj.1 * cp ^ rj.1 * (cx * cp) ^ rj.2 else 0

variable {N}

lemma asE_lb (hN : 1 ≤ N) {a β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) (rj : ℤ × ℤ) :
    -((|β| + 1) * (|β| + 1)) ≤ asE N a β rj := by
  unfold asE
  split_ifs with hc
  · have := asExp_ge hN hlo hhi hc; have := c2_sub_bound β rj.1; have := abs_nonneg rj.2; linarith
  · have := abs_nonneg rj.1; have := abs_nonneg rj.2; nlinarith

lemma asE_fin (hN : 1 ≤ N) {a β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) (n : ℤ) :
    {rj : ℤ × ℤ | asE N a β rj = n}.Finite := by
  set B := 2 * |β| + 1 + 2 * |n + (|β| + 1) * (|β| + 1)| + |n| + (|β| + 1) * (|β| + 1) + |n|
  refine ((Set.finite_Icc (-B) B).prod (Set.finite_Icc (-B) B)).subset fun ⟨r, j⟩ h => ?_
  simp only [Set.mem_setOf_eq, asE] at h
  have hb := abs_nonneg β; have hn := abs_nonneg n
  have hP : 0 ≤ (|β| + 1) * (|β| + 1) := by positivity
  split_ifs at h with hc
  · have h1 := asExp_ge hN hlo hhi hc
    have h2 := c2_sub_bound β r
    have hj : |j| ≤ n + (|β| + 1) * (|β| + 1) := by linarith
    have hr : |r| ≤ 2 * |β| + 1 + 2 * |n + (|β| + 1) * (|β| + 1)| :=
      c2_sub_le β r _ (by have := abs_nonneg j; linarith)
    have := abs_nonneg (n + (|β| + 1) * (|β| + 1))
    simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> [have := neg_abs_le r; have := le_abs_self r;
      have := neg_abs_le j; have := le_abs_self j] <;> nlinarith [le_abs_self n]
  · have hr := abs_nonneg r; have hj := abs_nonneg j
    have h1 : |r| ≤ |n| := by rw [← h]; have := le_abs_self (|r| + |j|); linarith
    have h2 : |j| ≤ |n| := by rw [← h]; have := le_abs_self (|r| + |j|); linarith
    have := abs_nonneg (n + (|β| + 1) * (|β| + 1))
    simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> [have := neg_abs_le r; have := le_abs_self r;
      have := neg_abs_le j; have := le_abs_self j] <;> nlinarith

/-- the family of `A(x,p)`. -/
noncomputable def asF (hN : 1 ≤ N) {a β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) (cx cp : ℂ) :
    SummableFamily ℤ ℂ (ℤ × ℤ) :=
  monoFam (asE N a β) (asC cx cp) _ (asE_lb hN hlo hhi) (asE_fin hN hlo hhi)

/-- the Appell–Lerch sum `A(x,p) = Σ_r (−1)^r q^{C(r,2)} p^r / (1 − q^{r−1} x p)`, `x = cx t^a`, `p = cp t^β`. -/
noncomputable def Aser (hN : 1 ≤ N) {a β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) (cx cp : ℂ) : L :=
  hs (asF hN hlo hhi cx cp)

end Aser


section AAeval
variable {N : ℕ} (hN : 1 ≤ N)
include hN

lemma asF_apply {a β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) (cx cp : ℂ) (rj : ℤ × ℤ) :
    asF hN hlo hhi cx cp rj = if cone rj.1 rj.2 then
      mono (asExp N a β rj.1 rj.2) (sgnC rj.1 * (-1) ^ rj.1 * cp ^ rj.1 * (cx * cp) ^ rj.2) else 0 := by
  rw [asF, monoFam_apply, asE, asC]
  split_ifs <;> simp [mono]

lemma aa_eval_pt {a β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) {cx cp : ℂ} (hx : cx ≠ 0)
    (hp : cp ≠ 0) (k r j : ℤ) :
    thT N (a + β) (cx * cp) (k - r - j) * asF hN hlo hhi cx cp (r, j) =
      (mono β cp) ^ k * aaF hN a cx k (r, j) := by
  rw [asF_apply, aaF_apply]
  simp only
  split_ifs with hc
  · rw [thT, mono_mul, mono_zpow, mono_mul]
    congr 1
    · unfold thE asExp aaExp; ring
    · unfold thC
      have e1 : (cx * cp) ^ (k - r - j) * (cx * cp) ^ j = cx ^ (k - r) * cp ^ (k - r) := by
        rw [← zpow_add₀ (mul_ne_zero hx hp), mul_zpow]; ring_nf
      have e2 : cp ^ k = cp ^ r * cp ^ (k - r) := by rw [← zpow_add₀ hp]; ring_nf
      have e3 : ((-1 : ℂ)) ^ (r + (k - r - j)) = (-1) ^ (k - r - j) * (-1) ^ r := by
        rw [zpow_add₀ (by norm_num)]; ring
      rw [e3, e2]
      linear_combination (sgnC r * (-1) ^ r * cp ^ r * (-1) ^ (k - r - j)) * e1
  · rw [mul_zero, mul_zero]

/-- `(i, (r, j)) ↦ (i + r + j, (r, j))`. -/
def e3 : ℤ × (ℤ × ℤ) ≃ ℤ × (ℤ × ℤ) where
  toFun p := (p.1 + p.2.1 + p.2.2, p.2)
  invFun p := (p.1 - p.2.1 - p.2.2, p.2)
  left_inv p := by ext <;> simp; ring
  right_inv p := by ext <;> simp; ring

/-- the evaluated family `k ↦ p^k 𝒜_k`. -/
noncomputable def aaEv {a β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) (cx cp : ℂ) :
    SummableFamily ℤ ℂ ℤ :=
  rowFam (SummableFamily.Equiv e3
    (SummableFamily.mul (thF hN (a + β) (cx * cp)) (asF hN hlo hhi cx cp)))

theorem aaEv_apply {a β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) {cx cp : ℂ} (hx : cx ≠ 0)
    (hp : cp ≠ 0) (k : ℤ) : aaEv hN hlo hhi cx cp k = (mono β cp) ^ k * AA hN a cx k := by
  refine hsum_reindex _ _ (Equiv.refl _) _ fun ⟨r, j⟩ => ?_
  simp only [Equiv.refl_apply, row_apply, SummableFamily.Equiv_toFun, SummableFamily.mul_toFun]
  rw [show e3.symm (k, (r, j)) = (k - r - j, (r, j)) from rfl, thF_apply]
  exact aa_eval_pt hN hlo hhi hx hp k r j

/-- **evaluation**: `Σ_k p^k [z^k] θ(xz)A(x,z) = θ(xp) A(x,p)`. -/
theorem aaEv_sum {a β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) (cx cp : ℂ) :
    hs (aaEv hN hlo hhi cx cp) = θ hN (a + β) (cx * cp) * Aser hN hlo hhi cx cp := by
  rw [aaEv, hs_rowFam, hs_eq, SummableFamily.hsum_equiv, SummableFamily.hsum_mul]
  rfl

end AAeval


/-! ## Uniqueness: the solution space of `F_{k+2} = q^k x F_k` is spanned by `E₀, E₁` -/

section Basis
variable {N : ℕ} (a : ℤ) (cx : ℂ)

/-- the multiplier `q^k x`. -/
noncomputable def mult (N : ℕ) (a : ℤ) (cx : ℂ) (k : ℤ) : L := mono (N * k + a) cx

/-- even basis solution: `E₀(2m) = x^m q^{m(m−1)}`. -/
noncomputable def E0 (N : ℕ) (k : ℤ) : L :=
  if Even k then mono (a * (k / 2) + N * ((k / 2) * (k / 2 - 1))) (cx ^ (k / 2)) else 0

/-- odd basis solution: `E₁(2m+1) = x^m q^{m²}`. -/
noncomputable def E1 (N : ℕ) (k : ℤ) : L :=
  if Odd k then mono (a * ((k - 1) / 2) + N * ((k - 1) / 2) ^ 2) (cx ^ ((k - 1) / 2)) else 0

variable {a cx}

lemma E0_rec (hx : cx ≠ 0) (k : ℤ) : E0 a cx N (k + 2) = mult N a cx k * E0 a cx N k := by
  unfold E0 mult
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [if_pos ⟨m + 1, by ring⟩, if_pos ⟨m, rfl⟩, mono_mul,
      show (m + m + 2) / 2 = m + 1 by omega, show (m + m) / 2 = m by omega, zpow_add₀ hx, zpow_one]
    congr 1 <;> ring
  · rw [if_neg (by rw [Int.not_even_iff_odd]; exact ⟨m + 1, by ring⟩),
      if_neg (by rw [Int.not_even_iff_odd]; exact ⟨m, rfl⟩), mul_zero]

lemma E1_rec (hx : cx ≠ 0) (k : ℤ) : E1 a cx N (k + 2) = mult N a cx k * E1 a cx N k := by
  unfold E1 mult
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [if_neg (by rw [Int.not_odd_iff_even]; exact ⟨m + 1, by ring⟩),
      if_neg (by rw [Int.not_odd_iff_even]; exact ⟨m, rfl⟩), mul_zero]
  · rw [if_pos ⟨m + 1, by ring⟩, if_pos ⟨m, rfl⟩, mono_mul,
      show (2 * m + 1 + 2 - 1) / 2 = m + 1 by omega, show (2 * m + 1 - 1) / 2 = m by omega,
      zpow_add₀ hx, zpow_one]
    congr 1 <;> ring

lemma E0_zero : E0 a cx N 0 = 1 := by simp [E0, mono]
lemma E0_one : E0 a cx N 1 = 0 := by simp [E0]
lemma E1_zero : E1 a cx N 0 = 0 := by simp [E1]
lemma E1_one : E1 a cx N 1 = 1 := by simp [E1, mono]

lemma mult_ne (hx : cx ≠ 0) (k : ℤ) : mult N a cx k ≠ 0 := by
  simp [mult, mono, hx]

/-- a solution vanishing at `0, 1` vanishes. -/
lemma sol_zero (hx : cx ≠ 0) (G : ℤ → L) (hG : ∀ k, G (k + 2) = mult N a cx k * G k)
    (h0 : G 0 = 0) (h1 : G 1 = 0) : ∀ k, G k = 0 := by
  have up : ∀ n : ℕ, G n = 0 ∧ G (n + 1) = 0 := by
    intro n
    induction n with
    | zero => exact ⟨h0, by simpa using h1⟩
    | succ n ih =>
      refine ⟨by exact_mod_cast ih.2, ?_⟩
      have := hG n
      rw [ih.1, mul_zero] at this
      rw [show ((n + 1 : ℕ) : ℤ) + 1 = n + 2 by push_cast; ring, this]
  have down : ∀ n : ℕ, G (-n) = 0 ∧ G (-n + 1) = 0 := by
    intro n
    induction n with
    | zero => exact ⟨by simpa using h0, by simpa using h1⟩
    | succ n ih =>
      refine ⟨?_, by rw [show -((n + 1 : ℕ) : ℤ) + 1 = -n by push_cast; ring]; exact ih.1⟩
      have := hG (-(n + 1 : ℕ))
      rw [show -((n + 1 : ℕ) : ℤ) + 2 = -n + 1 by push_cast; ring, ih.2] at this
      exact (mul_eq_zero.mp this.symm).resolve_left (mult_ne hx _)
  intro k
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · exact (up n).1
  · exact (down n).1

/-- **2-dimensionality**: `F_k = F_0 E₀(k) + F_1 E₁(k)`. -/
theorem sol_basis (hx : cx ≠ 0) (F : ℤ → L) (hF : ∀ k, F (k + 2) = mult N a cx k * F k) (k : ℤ) :
    F k = F 0 * E0 a cx N k + F 1 * E1 a cx N k := by
  have := sol_zero hx (fun k => F k - (F 0 * E0 a cx N k + F 1 * E1 a cx N k))
    (fun k => by simp only; rw [hF, E0_rec hx, E1_rec hx]; ring)
    (by simp [E0_zero, E1_zero]) (by simp [E0_one, E1_one]) k
  exact sub_eq_zero.mp this

end Basis


section BasisEval
variable {N : ℕ} (hN : 1 ≤ N) (a : ℤ) (cx : ℂ)
include hN

lemma two_N : 1 ≤ 2 * N := by omega

/-- `m`-family of `Σ_m x^m q^{m(m−1)} p^{2m}`. -/
noncomputable def e0M (β : ℤ) (cp : ℂ) : SummableFamily ℤ ℂ ℤ :=
  monoFam (thE (2 * N) (2 * β + a)) (fun m => cp ^ (2 * m) * cx ^ m) _
    (thE_lb (two_N hN) _) (thE_fin (two_N hN) _)

/-- `m`-family of `Σ_m x^m q^{m²} p^{2m+1}`. -/
noncomputable def e1M (β : ℤ) (cp : ℂ) : SummableFamily ℤ ℂ ℤ :=
  monoFam (fun m => thE (2 * N) (N + 2 * β + a) m + β) (fun m => cp ^ (2 * m + 1) * cx ^ m)
    (-((N + 2 * β + a) * (N + 2 * β + a)) - 1 + β)
    (fun m => by have := thE_lb (two_N hN) (N + 2 * β + a) m; push_cast at this ⊢; linarith)
    (fun n => (thE_fin (two_N hN) (N + 2 * β + a) (n - β)).subset fun m hm => by
      simp only [Set.mem_setOf_eq] at hm ⊢; omega)

def dbl : ℤ ↪ ℤ := ⟨fun m => 2 * m, fun _ _ h => by simpa using h⟩
def dbl1 : ℤ ↪ ℤ := ⟨fun m => 2 * m + 1, fun _ _ h => by simpa using h⟩

/-- `k ↦ p^k E₀(k)`. -/
noncomputable def e0Fam (β : ℤ) (cp : ℂ) : SummableFamily ℤ ℂ ℤ := (e0M hN a cx β cp).embDomain dbl
/-- `k ↦ p^k E₁(k)`. -/
noncomputable def e1Fam (β : ℤ) (cp : ℂ) : SummableFamily ℤ ℂ ℤ := (e1M hN a cx β cp).embDomain dbl1

variable {cx}

lemma e0Fam_apply (β : ℤ) {cp : ℂ} (hp : cp ≠ 0) (k : ℤ) :
    e0Fam hN a cx β cp k = (mono β cp) ^ k * E0 a cx N k := by
  unfold e0Fam E0
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show m + m = dbl m by simp [dbl]; ring, SummableFamily.embDomain_image, if_pos ⟨m, by simp [dbl]; ring⟩]
    simp only [e0M, monoFam_apply, dbl, Function.Embedding.coeFn_mk]
    rw [mono_zpow, mono_mul, show 2 * m / 2 = m by omega]
    congr 1
    · unfold thE; have := two_c2 m; push_cast; nlinarith
  · rw [SummableFamily.embDomain_notin_range, if_neg (by rw [Int.not_even_iff_odd]; exact ⟨m, rfl⟩),
      mul_zero]
    rintro ⟨m', hm'⟩; simp [dbl] at hm'; omega

lemma e1Fam_apply (β : ℤ) {cp : ℂ} (hp : cp ≠ 0) (k : ℤ) :
    e1Fam hN a cx β cp k = (mono β cp) ^ k * E1 a cx N k := by
  unfold e1Fam E1
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [SummableFamily.embDomain_notin_range, if_neg (by rw [Int.not_odd_iff_even]; exact ⟨m, rfl⟩),
      mul_zero]
    rintro ⟨m', hm'⟩; simp [dbl1] at hm'; omega
  · rw [show 2 * m + 1 = dbl1 m by simp [dbl1], SummableFamily.embDomain_image, if_pos ⟨m, by simp [dbl1]⟩]
    simp only [e1M, monoFam_apply, dbl1, Function.Embedding.coeFn_mk]
    rw [mono_zpow, mono_mul, show (2 * m + 1 - 1) / 2 = m by omega]
    congr 1
    · unfold thE; have := two_c2 m; push_cast; nlinarith

/-- **evaluation of a solution**: `Σ_k p^k F_k = F₀ ev(E₀)(p) + F₁ ev(E₁)(p)`. -/
theorem ev_decomp (hx : cx ≠ 0) (F : ℤ → L) (hF : ∀ k, F (k + 2) = mult N a cx k * F k)
    (β : ℤ) {cp : ℂ} (hp : cp ≠ 0) (S : SummableFamily ℤ ℂ ℤ) (hS : ∀ k, S k = (mono β cp) ^ k * F k) :
    hs S = F 0 * hs (e0Fam hN a cx β cp) + F 1 * hs (e1Fam hN a cx β cp) := by
  have h := hsum_congr S (F 0 • e0Fam hN a cx β cp + F 1 • e1Fam hN a cx β cp) fun k => by
    simp only [SummableFamily.add_apply, SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul]
    rw [hS, e0Fam_apply hN a β hp, e1Fam_apply hN a β hp, sol_basis hx F hF k]
    ring
  rw [h, hs_eq, hs_eq, hs_eq, SummableFamily.hsum_add, SummableFamily.hsum_smul, SummableFamily.hsum_smul]

end BasisEval


/-! ## Leading terms -/

section Leading

lemma coeff_mul_lowest (X Y : L) (n₀ n₁ : ℤ) (hX : ∀ n < n₀, X.coeff n = 0) (hY : ∀ n < n₁, Y.coeff n = 0) :
    (X * Y).coeff (n₀ + n₁) = X.coeff n₀ * Y.coeff n₁ := by
  rw [coeff_mul]
  have key : ∀ ij ∈ addAntidiagonal X.isPWO_support Y.isPWO_support (n₀ + n₁), ij = (n₀, n₁) := by
    intro ij hij
    rw [mem_addAntidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    have a1 : n₀ ≤ ij.1 := by by_contra h; exact h1 (hX _ (lt_of_not_ge h))
    have a2 : n₁ ≤ ij.2 := by by_contra h; exact h2 (hY _ (lt_of_not_ge h))
    ext <;> simp <;> omega
  by_cases hm : (n₀, n₁) ∈ addAntidiagonal X.isPWO_support Y.isPWO_support (n₀ + n₁)
  · rw [Finset.sum_eq_single_of_mem _ hm fun b hb hne => absurd (key b hb) hne]
  · rw [Finset.sum_eq_zero fun b hb => absurd (key b hb ▸ hb) hm]
    rw [mem_addAntidiagonal] at hm
    by_cases h0 : X.coeff n₀ = 0
    · rw [h0, zero_mul]
    · by_cases h1 : Y.coeff n₁ = 0
      · rw [h1, mul_zero]
      · exact absurd ⟨h0, h1, rfl⟩ hm

lemma coeff_mul_below (X Y : L) (n₀ n₁ : ℤ) (hX : ∀ n < n₀, X.coeff n = 0) (hY : ∀ n < n₁, Y.coeff n = 0)
    (n : ℤ) (hn : n < n₀ + n₁) : (X * Y).coeff n = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [mem_addAntidiagonal] at hij
  obtain ⟨h1, h2, h3⟩ := hij
  have a1 : n₀ ≤ ij.1 := by by_contra h; exact h1 (hX _ (lt_of_not_ge h))
  have a2 : n₁ ≤ ij.2 := by by_contra h; exact h2 (hY _ (lt_of_not_ge h))
  omega

variable {ι : Type*}

lemma monoFam_coeff (E : ι → ℤ) (c : ι → ℂ) (D hD hfin) (n : ℤ) :
    (hs (monoFam E c D hD hfin)).coeff n = ∑ᶠ i, if E i = n then c i else 0 := by
  rw [hs, SummableFamily.coeff_hsum]
  refine finsum_congr fun i => ?_
  simp only [monoFam_apply, mono, coeff_single]
  split_ifs <;> simp_all [eq_comm]

lemma monoFam_coeff_zero (E : ι → ℤ) (c : ι → ℂ) (D hD hfin) (n : ℤ) (h : ∀ i, E i ≠ n) :
    (hs (monoFam E c D hD hfin)).coeff n = 0 := by
  rw [monoFam_coeff]; exact finsum_eq_zero_of_forall_eq_zero fun i => if_neg (h i)

lemma monoFam_coeff_single (E : ι → ℤ) (c : ι → ℂ) (D hD hfin) (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → E i ≠ E i₀) : (hs (monoFam E c D hD hfin)).coeff (E i₀) = c i₀ := by
  rw [monoFam_coeff, finsum_eq_single _ i₀ fun i hi => if_neg (h i hi), if_pos rfl]

lemma monoFam_coeff_at (E : ι → ℤ) (c : ι → ℂ) (D hD hfin) (i₀ : ι) (n : ℤ) (h0 : E i₀ = n)
    (h : ∀ i, i ≠ i₀ → E i ≠ n) : (hs (monoFam E c D hD hfin)).coeff n = c i₀ := by
  subst h0; exact monoFam_coeff_single E c D hD hfin i₀ h

end Leading


/-! ## The determinant -/

section Det
variable {N : ℕ} (hN : 1 ≤ N)
include hN

omit hN in
lemma thE2 (e m : ℤ) : thE (2 * N) e m = N * m * (m - 1) + e * m := by
  unfold thE; have := two_c2 m; push_cast; linear_combination (N : ℤ) * this

lemma quad_pos {e : ℤ} (h0 : 0 < e) (h1 : e < 2 * N) {m : ℤ} (hm : m ≠ 0) : 0 < thE (2 * N) e m := by
  rw [thE2]
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  rcases lt_or_gt_of_ne hm with h | h
  · obtain ⟨u, rfl⟩ : ∃ u, m = -u := ⟨-m, by ring⟩
    have hu : 1 ≤ u := by omega
    have h3 : 0 ≤ (N : ℤ) * (u * (u - 1)) := mul_nonneg (by omega) (by nlinarith)
    have h4 : 0 < (2 * N - e) * u := mul_pos (by omega) (by omega)
    nlinarith
  · have h3 : 0 ≤ (N : ℤ) * (m * (m - 1)) := mul_nonneg (by omega) (by nlinarith)
    have h4 : 0 < e * m := mul_pos h0 h
    nlinarith

lemma quad_nonneg {e : ℤ} (h0 : 0 < e) (h1 : e < 2 * N) (m : ℤ) : 0 ≤ thE (2 * N) e m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [thE, c2]
  · exact (quad_pos hN h0 h1 hm).le

lemma F4 {a b : ℤ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b < N) (m : ℤ) :
    1 ≤ thE (2 * N) (N + 2 * b + a) m + b := by
  rw [thE2]
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  rcases le_or_gt 0 m with h | h
  · have h3 : 0 ≤ (N : ℤ) * (m * (m - 1)) :=
      mul_nonneg (by omega) (by rcases le_or_gt m 0 with h' | h' <;> nlinarith)
    have h4 : 0 ≤ (N + 2 * b + a) * m := mul_nonneg (by omega) h
    nlinarith
  · rcases eq_or_lt_of_le (show m ≤ -1 by omega) with h' | h'
    · subst h'; nlinarith
    · obtain ⟨u, rfl⟩ : ∃ u, m = -u := ⟨-m, by ring⟩
      have hu : 2 ≤ u := by omega
      have h4 : 0 ≤ (N * u - 2 * b - a - 1) * u := mul_nonneg (by nlinarith) (by omega)
      nlinarith

lemma F7 {a b : ℤ} (ha : a < N) (hb : b ≤ -1) (hab : 1 ≤ a + b) (hab' : a + b < N) (m : ℤ) :
    b + 1 ≤ thE (2 * N) (2 * b + a) m := by
  rw [thE2]
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  rcases lt_trichotomy m 0 with h | h | h
  · obtain ⟨u, rfl⟩ : ∃ u, m = -u := ⟨-m, by ring⟩
    have hu : 1 ≤ u := by omega
    have h4 : 0 ≤ (N * (u + 1) - 2 * b - a) * u := mul_nonneg (by nlinarith) (by omega)
    nlinarith
  · subst h; simp; omega
  · rcases eq_or_lt_of_le (show 1 ≤ m by omega) with h' | h'
    · subst h'; nlinarith
    · have h5 : (N : ℤ) ≤ N * (m - 1) := by nlinarith
      have h4 : 0 ≤ (N * (m - 1) + 2 * b + a) * m := mul_nonneg (by omega) (by omega)
      nlinarith


omit hN in
lemma thE_zero (M : ℕ) (e : ℤ) : thE M e 0 = 0 := by simp [thE, c2]

/-- lowest coefficient of an even basis evaluation when `0` is the strict minimum. -/
lemma e0M_low {a β : ℤ} (cx cp : ℂ) (h0 : 0 < 2 * β + a) (h1 : 2 * β + a < 2 * N) :
    (hs (e0M hN a cx β cp)).coeff 0 = 1 ∧ ∀ n < 0, (hs (e0M hN a cx β cp)).coeff n = 0 := by
  refine ⟨?_, fun n hn => monoFam_coeff_zero _ _ _ _ _ _ fun m => ?_⟩
  · unfold e0M
    rw [monoFam_coeff_at _ _ _ _ _ 0 0 (thE_zero _ _) fun m hm => (quad_pos hN h0 h1 hm).ne']
    rw [mul_zero, zpow_zero, zpow_zero, one_mul]
  · have := quad_nonneg hN h0 h1 m; omega

lemma e1M_low {a β : ℤ} (cx cp : ℂ) (h0 : 0 < N + 2 * β + a) (h1 : N + 2 * β + a < 2 * N) :
    (hs (e1M hN a cx β cp)).coeff β = cp ∧ ∀ n < β, (hs (e1M hN a cx β cp)).coeff n = 0 := by
  refine ⟨?_, fun n hn => monoFam_coeff_zero _ _ _ _ _ _ fun m => ?_⟩
  · unfold e1M
    rw [monoFam_coeff_at _ _ _ _ _ 0 β (by simp [thE_zero]) fun m hm => by
      have := quad_pos hN h0 h1 hm; omega]
    rw [mul_zero, zero_add, zpow_one, zpow_zero, mul_one]
  · have := quad_nonneg hN h0 h1 m; omega

omit hN in
lemma lowerAll {ι : Type*} (E : ι → ℤ) (c : ι → ℂ) (D hD hfin) (n₀ : ℤ) (h : ∀ i, n₀ ≤ E i) :
    ∀ n < n₀, (hs (monoFam E c D hD hfin)).coeff n = 0 :=
  fun n hn => monoFam_coeff_zero _ _ _ _ _ _ fun i => by have := h i; omega

/-- **the determinant is nonzero** for `0 < a < N`, `0 < a + b₀ < N`, `z₀ ≠ 1`. -/
theorem det_ne {a b₀ : ℤ} (ha0 : 0 < a) (haN : a < N) (hb0 : 0 < a + b₀) (hbN : a + b₀ < N)
    (cx : ℂ) {c₀ : ℂ} (hc0 : c₀ ≠ 0) (h1 : b₀ = 0 → c₀ ≠ 1) :
    hs (e0M hN a cx 0 1) * hs (e1M hN a cx b₀ c₀) - hs (e0M hN a cx b₀ c₀) * hs (e1M hN a cx 0 1) ≠ 0 := by
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  obtain ⟨P0, Pb⟩ := e0M_low hN (β := 0) (a := a) cx 1 (by omega) (by omega)
  obtain ⟨Q0, Qb⟩ := e1M_low hN (β := 0) (a := a) cx 1 (by omega) (by omega)
  rcases lt_trichotomy b₀ 0 with hb | rfl | hb
  · -- `b₀ < 0`: compare coefficients at `b₀`
    obtain ⟨S0, Sb⟩ := e1M_low hN (β := b₀) (a := a) cx c₀ (by omega) (by omega)
    have Rb : ∀ n < b₀ + 1, (hs (e0M hN a cx b₀ c₀)).coeff n = 0 := by
      unfold e0M; exact lowerAll _ _ _ _ _ _ (F7 hN haN (by omega) (by omega) hbN)
    intro hΔ
    have := congrArg (fun f : L => f.coeff b₀) hΔ
    simp only [coeff_sub, coeff_zero] at this
    have e1 := coeff_mul_lowest _ _ 0 b₀ Pb Sb
    rw [zero_add] at e1
    rw [e1, coeff_mul_below _ _ (b₀ + 1) 0 Rb Qb _ (by omega), P0, S0] at this
    simp at this; exact hc0 this
  · -- `b₀ = 0`
    obtain ⟨S0, Sb⟩ := e1M_low hN (β := 0) (a := a) cx c₀ (by omega) (by omega)
    obtain ⟨R0, Rb⟩ := e0M_low hN (β := 0) (a := a) cx c₀ (by omega) (by omega)
    intro hΔ
    have := congrArg (fun f : L => f.coeff (0 + 0)) hΔ
    simp only [coeff_sub, coeff_zero] at this
    rw [coeff_mul_lowest _ _ 0 0 Pb Sb, coeff_mul_lowest _ _ 0 0 Rb Qb, P0, S0, R0, Q0] at this
    exact h1 rfl (by linear_combination this)
  · -- `b₀ > 0`
    obtain ⟨R0, Rb⟩ := e0M_low hN (β := b₀) (a := a) cx c₀ (by omega) (by omega)
    have Sb : ∀ n < 1, (hs (e1M hN a cx b₀ c₀)).coeff n = 0 := by
      unfold e1M; exact lowerAll _ _ _ _ _ _ (F4 hN (by omega) (by omega) hbN)
    intro hΔ
    have := congrArg (fun f : L => f.coeff (0 + 0)) hΔ
    simp only [coeff_sub, coeff_zero] at this
    rw [coeff_mul_below _ _ 0 1 Pb Sb _ (by omega), coeff_mul_lowest _ _ 0 0 Rb Qb, R0, Q0] at this
    norm_num at this

end Det


/-! ## Assembly: the change-of-`z` theorem -/

section Main
variable {N : ℕ} (hN : 1 ≤ N)
include hN

lemma hs_e0Fam (a : ℤ) (cx : ℂ) (β : ℤ) (cp : ℂ) : hs (e0Fam hN a cx β cp) = hs (e0M hN a cx β cp) := by
  rw [e0Fam, hs_eq, hs_eq, SummableFamily.hsum_embDomain]
lemma hs_e1Fam (a : ℤ) (cx : ℂ) (β : ℤ) (cp : ℂ) : hs (e1Fam hN a cx β cp) = hs (e1M hN a cx β cp) := by
  rw [e1Fam, hs_eq, hs_eq, SummableFamily.hsum_embDomain]

/-- **uniqueness**: a solution of `F_{k+2} = q^k x F_k` whose evaluations at `1` and at `z₀` vanish
is identically zero. -/
theorem sol_vanish {a b₀ : ℤ} (ha0 : 0 < a) (haN : a < N) (hb0 : 0 < a + b₀) (hbN : a + b₀ < N)
    {cx c₀ : ℂ} (hx : cx ≠ 0) (hc0 : c₀ ≠ 0) (h1 : b₀ = 0 → c₀ ≠ 1)
    (F : ℤ → L) (hF : ∀ k, F (k + 2) = mult N a cx k * F k)
    (S₁ S₀ : SummableFamily ℤ ℂ ℤ) (hS₁ : ∀ k, S₁ k = (mono 0 1) ^ k * F k)
    (hS₀ : ∀ k, S₀ k = (mono b₀ c₀) ^ k * F k) (e₁ : hs S₁ = 0) (e₀ : hs S₀ = 0) : ∀ k, F k = 0 := by
  have d₁ := ev_decomp hN a hx F hF 0 one_ne_zero S₁ hS₁
  have d₀ := ev_decomp hN a hx F hF b₀ hc0 S₀ hS₀
  rw [e₁, hs_e0Fam, hs_e1Fam] at d₁
  rw [e₀, hs_e0Fam, hs_e1Fam] at d₀
  have hΔ := det_ne hN ha0 haN hb0 hbN cx hc0 h1
  set P := hs (e0M hN a cx 0 1); set Q := hs (e1M hN a cx 0 1)
  set R := hs (e0M hN a cx b₀ c₀); set S := hs (e1M hN a cx b₀ c₀)
  have f0 : F 0 * (P * S - R * Q) = 0 := by linear_combination (-S) * d₁ + Q * d₀
  have f1 : F 1 * (P * S - R * Q) = 0 := by linear_combination R * d₁ - P * d₀
  have z0 := (mul_eq_zero.mp f0).resolve_right hΔ
  have z1 := (mul_eq_zero.mp f1).resolve_right hΔ
  intro k
  rw [sol_basis hx F hF k, z0, z1]; ring


/-- `κ(x) = θ(x)·A(x,1)`. (Classically `κ = −(q;q)_∞³`.) -/
noncomputable def kap {a : ℤ} (ha0 : 0 < a) (haN : a < N) (cx : ℂ) : L :=
  θ hN a cx * Aser hN (a := a) (β := 0) (by omega) (by omega) cx 1

/-- the evaluation family of `F = 𝒜 − m₀ θ(z)θ(xz) + c θ(z/z₀)θ(xz₀z)` at `p = c_p t^β`. -/
noncomputable def Fev {a b₀ β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) (cx c₀ : ℂ) (m₀ cc : L) (cp : ℂ) :
    SummableFamily ℤ ℂ ℤ :=
  aaEv hN hlo hhi cx cp - m₀ • ttEv hN 0 1 a cx β cp + cc • ttEv hN (-b₀) c₀⁻¹ (a + b₀) (cx * c₀) β cp

lemma Fev_apply {a b₀ β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) {cx c₀ : ℂ} (hx : cx ≠ 0)
    (m₀ cc : L) {cp : ℂ} (hp : cp ≠ 0) (k : ℤ) :
    Fev hN (b₀ := b₀) hlo hhi cx c₀ m₀ cc cp k = (mono β cp) ^ k *
      (AA hN a cx k - m₀ * TT hN 0 1 a cx k + cc * TT hN (-b₀) c₀⁻¹ (a + b₀) (cx * c₀) k) := by
  simp only [Fev, SummableFamily.add_apply, SummableFamily.sub_apply, SummableFamily.smul_apply,
    HahnSeries.of_symm_smul_of_eq_mul]
  rw [aaEv_apply hN hlo hhi hx hp, ttEv_apply hN _ _ _ _ _ hp, ttEv_apply hN _ _ _ _ _ hp]
  ring

lemma Fev_sum {a b₀ β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) (cx c₀ : ℂ) (m₀ cc : L) (cp : ℂ) :
    hs (Fev hN (b₀ := b₀) hlo hhi cx c₀ m₀ cc cp) =
      θ hN (a + β) (cx * cp) * Aser hN hlo hhi cx cp - m₀ * (θ hN (0 + β) (1 * cp) * θ hN (a + β) (cx * cp))
      + cc * (θ hN (-b₀ + β) (c₀⁻¹ * cp) * θ hN (a + b₀ + β) (cx * c₀ * cp)) := by
  rw [Fev, hs_eq, SummableFamily.hsum_add, SummableFamily.hsum_sub, SummableFamily.hsum_smul,
    SummableFamily.hsum_smul, ← hs_eq, ← hs_eq, ← hs_eq, aaEv_sum, ttEv_sum, ttEv_sum]

/-- **Change of `z`** (Hickerson–Mortenson, Theorem 3.3), multiplied out. With `x = c_x t^a`,
`zᵢ = cᵢ t^{bᵢ}`, `q = t^N`, `A(x,z) = θ(z) m(x,q,z)` and `κ = θ(x)A(x,1)`:
`θ(z₀)θ(xz₀)θ(xz₁)A(x,z₁) − A(x,z₀)θ(xz₀)θ(z₁)θ(xz₁) + z₀ κ θ(z₁/z₀) θ(xz₀z₁) = 0`,
i.e. `m(x,q,z₁) − m(x,q,z₀) = −z₀ κ θ(z₁/z₀)θ(xz₀z₁)/(θ(z₀)θ(z₁)θ(xz₀)θ(xz₁))`. -/
theorem change_of_z {a b₀ b₁ : ℤ} (ha0 : 0 < a) (haN : a < N) (hb0 : 0 < a + b₀) (hbN : a + b₀ < N)
    (hc0' : 0 < a + b₁) (hcN : a + b₁ < N) {cx c₀ c₁ : ℂ} (hx : cx ≠ 0) (hc0 : c₀ ≠ 0) (hc1 : c₁ ≠ 0)
    (h1 : b₀ = 0 → c₀ ≠ 1) (hθ₀ : θ hN b₀ c₀ ≠ 0) (hθx₀ : θ hN (a + b₀) (cx * c₀) ≠ 0) :
    θ hN b₀ c₀ * θ hN (a + b₀) (cx * c₀) * θ hN (a + b₁) (cx * c₁) * Aser hN hc0' hcN cx c₁
      - Aser hN hb0 hbN cx c₀ * θ hN (a + b₀) (cx * c₀) * θ hN b₁ c₁ * θ hN (a + b₁) (cx * c₁)
      + mono b₀ c₀ * kap hN ha0 haN cx * θ hN (-b₀ + b₁) (c₀⁻¹ * c₁) * θ hN (a + b₀ + b₁) (cx * c₀ * c₁)
      = 0 := by
  set m₀ := Aser hN hb0 hbN cx c₀ / θ hN b₀ c₀ with hm₀
  set cc := mono b₀ c₀ * kap hN ha0 haN cx / (θ hN b₀ c₀ * θ hN (a + b₀) (cx * c₀)) with hcc
  set F : ℤ → L := fun k => AA hN a cx k - m₀ * TT hN 0 1 a cx k + cc * TT hN (-b₀) c₀⁻¹ (a + b₀) (cx * c₀) k
  have hF : ∀ k, F (k + 2) = mult N a cx k * F k := by
    intro k
    simp only [F]
    rw [AA_rec hN a hx, TT_rec hN 0 one_ne_zero a hx, TT_rec hN (-b₀) (inv_ne_zero hc0) (a + b₀)
      (mul_ne_zero hx hc0)]
    have e1 : mono (N * k + (0 + a)) (1 * cx) = mult N a cx k := by simp [mult]
    have e2 : mono (N * k + (-b₀ + (a + b₀))) (c₀⁻¹ * (cx * c₀)) = mult N a cx k := by
      unfold mult; congr 1
      · ring
      · field_simp
    rw [e1, e2, show mono (N * k + a) cx = mult N a cx k from rfl]
    ring
  have hone : (mono 0 (1 : ℂ)) = 1 := rfl
  -- evaluation at `1`
  have E₁ := Fev_sum hN (a := a) (b₀ := b₀) (β := 0) (by omega) (by omega) cx c₀ m₀ cc 1
  -- evaluation at `z₀`
  have E₀ := Fev_sum hN (b₀ := b₀) hb0 hbN cx c₀ m₀ cc c₀
  -- evaluation at `z₁`
  have E₂ := Fev_sum hN (b₀ := b₀) hc0' hcN cx c₀ m₀ cc c₁
  have z₁ : hs (Fev hN (a := a) (b₀ := b₀) (β := 0) (by omega) (by omega) cx c₀ m₀ cc 1) = 0 := by
    rw [E₁]
    simp only [add_zero, mul_one]
    rw [θ_one hN, θ_inv hN b₀ hc0]
    have hmm : mono b₀ c₀ * mono (-b₀) c₀⁻¹ = 1 := by rw [mono_mul]; simp [hc0, mono]
    have key : cc * (θ hN b₀ c₀ * θ hN (a + b₀) (cx * c₀)) = mono b₀ c₀ * kap hN ha0 haN cx := by
      rw [hcc]; field_simp
    have hk : θ hN a cx * Aser hN (a := a) (β := 0) (by omega) (by omega) cx 1 = kap hN ha0 haN cx := rfl
    rw [hk]
    linear_combination (-mono (-b₀) c₀⁻¹) * key - kap hN ha0 haN cx * hmm
  have hm0' : m₀ * θ hN b₀ c₀ = Aser hN hb0 hbN cx c₀ := by rw [hm₀]; field_simp
  have key : cc * (θ hN b₀ c₀ * θ hN (a + b₀) (cx * c₀)) = mono b₀ c₀ * kap hN ha0 haN cx := by
    rw [hcc]; field_simp
  have z₀ : hs (Fev hN (b₀ := b₀) hb0 hbN cx c₀ m₀ cc c₀) = 0 := by
    rw [E₀]
    simp only [zero_add, one_mul]
    rw [show -b₀ + b₀ = 0 by ring, inv_mul_cancel₀ hc0, θ_one hN]
    linear_combination (-θ hN (a + b₀) (cx * c₀)) * hm0'
  have hall := sol_vanish hN ha0 haN hb0 hbN hx hc0 h1 F hF _ _
    (fun k => Fev_apply hN (b₀ := b₀) (β := 0) (by omega) (by omega) hx m₀ cc one_ne_zero k)
    (fun k => Fev_apply hN (b₀ := b₀) hb0 hbN hx m₀ cc hc0 k) z₁ z₀
  have z₂ := ev_decomp hN a hx F hF b₁ hc1 _ (fun k => Fev_apply hN (b₀ := b₀) hc0' hcN hx m₀ cc hc1 k)
  rw [hall 0, hall 1, zero_mul, zero_mul, add_zero, E₂] at z₂
  simp only [zero_add, one_mul] at z₂
  linear_combination (θ hN b₀ c₀ * θ hN (a + b₀) (cx * c₀)) * z₂
    + (θ hN (a + b₀) (cx * c₀) * θ hN b₁ c₁ * θ hN (a + b₁) (cx * c₁)) * hm0'
    - (θ hN (-b₀ + b₁) (c₀⁻¹ * c₁) * θ hN (a + b₀ + b₁) (cx * c₀ * c₁)) * key

end Main

end ALz
