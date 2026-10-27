/-
# Dedekind sums and Dedekind's reciprocity law

`s(h,k) = Σ_{r mod k} ((r/k)) ((hr/k))`, with the sawtooth `((x)) = x − ⌊x⌋ − 1/2` for `x ∉ ℤ`, `((x)) = 0`
for `x ∈ ℤ`. For coprime `h, k ≥ 1`:

* `s(h,k)` depends only on `h mod k`, and `s(H,h) = −s(k,h)` when `H ≡ −k (mod h)`;
* **reciprocity**: `s(h,k) + s(k,h) = (h/k + k/h + 1/(hk))/12 − 1/4`.

The proof is the elementary one: with `ρ_r = hr mod k`, `q_r = ⌊hr/k⌋`, the map `r ↦ ρ_r` permutes
`{0, …, k−1}`, so `Σ ρ_r² = Σ r²`; and `Σ q_r²` is computed by counting lattice points, which brings in
`Σ_m m ⌊mk/h⌋`, the corresponding quantity for `s(k,h)`.
-/
import Mathlib

set_option autoImplicit false

namespace Rademacher

open Finset

noncomputable section

/-- the sawtooth `((x))`. -/
def saw (x : ℝ) : ℝ := if Int.fract x = 0 then 0 else Int.fract x - 1 / 2

/-- **the Dedekind sum** `s(h,k) = Σ_{r mod k} ((r/k)) ((hr/k))`. -/
def dsum (h k : ℕ) : ℝ := ∑ r ∈ range k, saw ((r : ℝ) / k) * saw ((h : ℝ) * r / k)

/-- `((n/k)) = g_k(n mod k)` with `g_k(0) = 0`, `g_k(m) = m/k − 1/2`. -/
def gk (k n : ℕ) : ℝ := if n = 0 then 0 else (n : ℝ) / k - 1 / 2

lemma saw_natCast_div {k : ℕ} (hk : 0 < k) (n : ℕ) : saw ((n : ℝ) / k) = gk k (n % k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [saw, Int.fract_div_natCast_eq_div_natCast_mod, gk]
  by_cases h0 : n % k = 0
  · simp [h0]
  · have : ((n % k : ℕ) : ℝ) / k ≠ 0 := div_ne_zero (by exact_mod_cast h0) hk0
    simp only [this, h0, if_false]

lemma dsum_eq_gk {h k : ℕ} (hk : 0 < k) :
    dsum h k = ∑ r ∈ range k, gk k r * gk k (h * r % k) := by
  refine sum_congr rfl fun r hr => ?_
  rw [saw_natCast_div hk, show (h : ℝ) * r = ((h * r : ℕ) : ℝ) by push_cast; ring, saw_natCast_div hk,
    Nat.mod_eq_of_lt (mem_range.mp hr)]

/-- `s(h,k)` depends only on `h mod k`. -/
lemma dsum_mod {h k : ℕ} (hk : 0 < k) : dsum h k = dsum (h % k) k := by
  rw [dsum_eq_gk hk, dsum_eq_gk hk]
  refine sum_congr rfl fun r _ => ?_
  rw [Nat.mod_mul_mod]

lemma dsum_zero_one : dsum 0 1 = 0 := by simp [dsum, saw]

/-! ### the permutation `r ↦ hr mod k` -/

lemma image_mulMod {h k : ℕ} (hk : 0 < k) (hc : Nat.Coprime h k) :
    Set.InjOn (fun r => h * r % k) (range k) ∧ (range k).image (fun r => h * r % k) = range k := by
  have hinj : Set.InjOn (fun r => h * r % k) (range k) := by
    intro a ha b hb hab
    have : h * a ≡ h * b [MOD k] := hab
    exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hc) this)
      (mem_range.mp ha) (mem_range.mp hb)
  refine ⟨hinj, eq_of_subset_of_card_le ?_ ?_⟩
  · intro x hx
    obtain ⟨r, -, rfl⟩ := mem_image.mp hx
    exact mem_range.mpr (Nat.mod_lt _ hk)
  · rw [card_image_of_injOn hinj]

lemma sum_mulMod {M : Type*} [AddCommMonoid M] {h k : ℕ} (hk : 0 < k) (hc : Nat.Coprime h k) (f : ℕ → M) :
    ∑ r ∈ range k, f (h * r % k) = ∑ r ∈ range k, f r := by
  obtain ⟨hinj, him⟩ := image_mulMod hk hc
  conv_rhs => rw [← him]
  rw [sum_image hinj]

lemma mulMod_eq_zero {h k r : ℕ} (hc : Nat.Coprime h k) (hr : r < k) (h0 : h * r % k = 0) : r = 0 := by
  have hd : k ∣ h * r := Nat.dvd_of_mod_eq_zero h0
  have : k ∣ r := (Nat.Coprime.symm hc).dvd_of_dvd_mul_left hd
  exact Nat.eq_zero_of_dvd_of_lt this hr

/-! ### `s(h,k)` in terms of `A(h,k) = Σ r·(hr mod k)` -/

/-- `A(h,k) = Σ_{r<k} r·(hr mod k)`. -/
def Asum (h k : ℕ) : ℤ := ∑ r ∈ range k, (r : ℤ) * (h * r % k : ℕ)

lemma sum_range_id_int {R : Type*} [CommRing R] (k : ℕ) : (∑ r ∈ range k, (r : R)) * 2 = k * (k - 1) := by
  induction k with
  | zero => simp
  | succ n ih => rw [sum_range_succ, add_mul, ih]; push_cast; ring

lemma sum_range_sq_int (k : ℕ) : (∑ r ∈ range k, (r : ℤ) ^ 2) * 6 = (k - 1) * k * (2 * k - 1) := by
  induction k with
  | zero => simp
  | succ n ih => rw [sum_range_succ, add_mul, ih]; push_cast; ring

lemma dsum_eq_Asum {h k : ℕ} (hk : 0 < k) (hc : Nat.Coprime h k) :
    dsum h k = (Asum h k : ℝ) / k ^ 2 - ((k : ℝ) - 1) / 4 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [dsum_eq_gk hk]
  have hterm : ∀ r ∈ range k, gk k r * gk k (h * r % k) =
      ((r : ℝ) / k - 1 / 2) * (((h * r % k : ℕ) : ℝ) / k - 1 / 2) - if r = 0 then 1 / 4 else 0 := by
    intro r hr
    by_cases h0 : r = 0
    · subst h0; simp [gk]; norm_num
    · have h1 : h * r % k ≠ 0 := fun h1 => h0 (mulMod_eq_zero hc (mem_range.mp hr) h1)
      simp [gk, h0, h1]
  rw [sum_congr rfl hterm, sum_sub_distrib, sum_ite_eq' (range k) 0, if_pos (mem_range.mpr hk)]
  have hperm : ∑ r ∈ range k, (((h * r % k : ℕ) : ℝ)) = ∑ r ∈ range k, (r : ℝ) :=
    sum_mulMod hk hc (fun n : ℕ => (n : ℝ))
  have hid : (∑ r ∈ range k, (r : ℝ)) * 2 = k * (k - 1) := sum_range_id_int k
  have hA : (Asum h k : ℝ) = ∑ r ∈ range k, (r : ℝ) * ((h * r % k : ℕ) : ℝ) := by
    rw [Asum]; push_cast; rfl
  have hexp : ∑ r ∈ range k, ((r : ℝ) / k - 1 / 2) * (((h * r % k : ℕ) : ℝ) / k - 1 / 2) =
      (∑ r ∈ range k, (r : ℝ) * ((h * r % k : ℕ) : ℝ)) / k ^ 2 -
        (∑ r ∈ range k, (((h * r % k : ℕ) : ℝ))) / (2 * k) - (∑ r ∈ range k, (r : ℝ)) / (2 * k) + k / 4 := by
    rw [sum_div, sum_div, sum_div, ← sum_sub_distrib, ← sum_sub_distrib]
    have : (k : ℝ) / 4 = ∑ r ∈ range k, (1 / 4 : ℝ) := by simp; ring
    rw [this, ← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    field_simp
    ring
  rw [hexp, hperm, ← hA]
  generalize (∑ r ∈ range k, (r : ℝ)) = S at hid ⊢
  have : S = k * (k - 1) / 2 := by linarith
  subst this
  field_simp
  ring

/-! ### the integer identities -/

/-- `T(h,k) = Σ_{r<k} r ⌊hr/k⌋`. -/
def Tsum (h k : ℕ) : ℤ := ∑ r ∈ range k, (r : ℤ) * (h * r / k : ℕ)

/-- `D(h,k) = Σ_{r<k} ⌊hr/k⌋`. -/
def Dsum (h k : ℕ) : ℤ := ∑ r ∈ range k, ((h * r / k : ℕ) : ℤ)

/-- `Q(h,k) = Σ_{r<k} ⌊hr/k⌋²`. -/
def Qsum (h k : ℕ) : ℤ := ∑ r ∈ range k, ((h * r / k : ℕ) : ℤ) ^ 2

lemma divmod (h k r : ℕ) : ((h * r % k : ℕ) : ℤ) = h * r - k * (h * r / k : ℕ) := by
  have := Nat.div_add_mod (h * r) k
  have : ((h * r : ℕ) : ℤ) = k * (h * r / k : ℕ) + (h * r % k : ℕ) := by exact_mod_cast this.symm
  push_cast at this ⊢; linarith

lemma Asum_eq (h k : ℕ) : Asum h k = h * ∑ r ∈ range k, (r : ℤ) ^ 2 - k * Tsum h k := by
  rw [Asum, Tsum, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun r _ => ?_
  rw [divmod]; ring

lemma Dsum_eq {h k : ℕ} (hk : 0 < k) (hc : Nat.Coprime h k) : 2 * Dsum h k = (h - 1) * (k - 1) := by
  have hperm : ∑ r ∈ range k, ((h * r % k : ℕ) : ℤ) = ∑ r ∈ range k, (r : ℤ) :=
    sum_mulMod hk hc (fun n : ℕ => (n : ℤ))
  simp only [divmod, sum_sub_distrib, ← mul_sum] at hperm
  rw [← Dsum] at hperm
  have hid := sum_range_id_int (R := ℤ) k
  have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  apply mul_left_cancel₀ hkz
  linear_combination (-2) * hperm + (h - 1) * hid

lemma Qsum_perm {h k : ℕ} (hk : 0 < k) (hc : Nat.Coprime h k) :
    ((h : ℤ) ^ 2 - 1) * ∑ r ∈ range k, (r : ℤ) ^ 2 - 2 * h * k * Tsum h k + k ^ 2 * Qsum h k = 0 := by
  have hperm : ∑ r ∈ range k, ((h * r % k : ℕ) : ℤ) ^ 2 = ∑ r ∈ range k, (r : ℤ) ^ 2 :=
    sum_mulMod hk hc (fun n : ℕ => (n : ℤ) ^ 2)
  have : ∑ r ∈ range k, ((h * r % k : ℕ) : ℤ) ^ 2 =
      (h : ℤ) ^ 2 * ∑ r ∈ range k, (r : ℤ) ^ 2 - 2 * h * k * Tsum h k + k ^ 2 * Qsum h k := by
    rw [Tsum, Qsum, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [divmod]; ring
  linear_combination this.symm.trans hperm

/-- `q² = Σ_{m ∈ [1,h), m ≤ q} (2m − 1)` for `q < h`. -/
lemma sq_eq_sum {q h : ℕ} (hq : q < h) :
    (q : ℤ) ^ 2 = ∑ m ∈ Ico 1 h, if m ≤ q then (2 * (m : ℤ) - 1) else 0 := by
  rw [← sum_filter, show (Ico 1 h).filter (fun m => m ≤ q) = Ico 1 (q + 1) by ext m; simp; omega]
  clear hq
  induction q with
  | zero => simp
  | succ n ih => rw [sum_Ico_succ_top (by omega), ← ih]; push_cast; ring

/-- the count `#{r < k : mk ≤ hr} = k − 1 − ⌊mk/h⌋` for `0 < m < h`. -/
lemma card_count {h k m : ℕ} (hk : 0 < k) (hc : Nat.Coprime h k) (hm1 : 1 ≤ m) (hmh : m < h) :
    (((range k).filter (fun r => m ≤ h * r / k)).card : ℤ) = k - 1 - (k * m / h : ℕ) := by
  have hh : 0 < h := by omega
  have hne : ∀ r, h * r ≠ k * m := by
    intro r hr
    have : h ∣ k * m := ⟨r, hr.symm⟩
    have := hc.dvd_of_dvd_mul_left this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have hlt : k * m / h < k := (Nat.div_lt_iff_lt_mul hh).mpr (by nlinarith)
  have hcompl : (range k).filter (fun r => ¬ m ≤ h * r / k) = range (k * m / h + 1) := by
    ext r
    simp only [mem_filter, mem_range, not_le]
    rw [Nat.div_lt_iff_lt_mul hk, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hh]
    constructor
    · rintro ⟨-, h2⟩; nlinarith
    · intro h2
      have h3 : r * h < k * m := lt_of_le_of_ne h2 (by rw [mul_comm]; exact hne r)
      refine ⟨?_, by nlinarith⟩
      by_contra h4
      push Not at h4
      nlinarith
  have := card_filter_add_card_filter_not (s := range k) (fun r => m ≤ h * r / k)
  rw [hcompl, card_range, card_range] at this
  have : (((range k).filter (fun r => m ≤ h * r / k)).card : ℤ) + (k * m / h + 1 : ℕ) = k := by
    exact_mod_cast this
  push_cast at this ⊢
  linarith

lemma Qsum_count {h k : ℕ} (hk : 0 < k) (hh : 0 < h) (hc : Nat.Coprime h k) :
    Qsum h k = (k - 1) * (h - 1) ^ 2 - 2 * Tsum k h + Dsum k h := by
  have hq : ∀ r ∈ range k, h * r / k < h := by
    intro r hr
    exact (Nat.div_lt_iff_lt_mul hk).mpr (by have := mem_range.mp hr; nlinarith)
  rw [Qsum, sum_congr rfl fun r hr => sq_eq_sum (hq r hr), sum_comm]
  have hinner : ∀ m ∈ Ico 1 h, (∑ r ∈ range k, if m ≤ h * r / k then (2 * (m : ℤ) - 1) else 0) =
      (2 * (m : ℤ) - 1) * (k - 1 - (k * m / h : ℕ)) := by
    intro m hm
    obtain ⟨hm1, hmh⟩ := mem_Ico.mp hm
    rw [← sum_filter, sum_const, nsmul_eq_mul, card_count hk hc hm1 hmh, mul_comm]
  rw [sum_congr rfl hinner]
  -- extend the sums over `Ico 1 h` to `range h` (the `m = 0` terms vanish)
  have hext : ∀ f : ℕ → ℤ, f 0 = 0 → ∑ m ∈ Ico 1 h, f m = ∑ m ∈ range h, f m := by
    intro f hf
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hh, hf, zero_add]
  have hodd : ∑ m ∈ Ico 1 h, (2 * (m : ℤ) - 1) = (h - 1) ^ 2 := by
    have := sq_eq_sum (q := h - 1) (h := h) (by omega)
    rw [sum_congr rfl fun m hm => if_pos (by have := mem_Ico.mp hm; omega)] at this
    rw [← this]; push_cast [Nat.cast_sub (by omega : 1 ≤ h)]; ring
  have hsplit : ∑ m ∈ Ico 1 h, (2 * (m : ℤ) - 1) * (k - 1 - (k * m / h : ℕ)) =
      (k - 1) * ∑ m ∈ Ico 1 h, (2 * (m : ℤ) - 1) - 2 * ∑ m ∈ Ico 1 h, (m : ℤ) * (k * m / h : ℕ) +
        ∑ m ∈ Ico 1 h, ((k * m / h : ℕ) : ℤ) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    ring
  rw [hsplit, hodd, hext _ (by simp), hext (fun m => ((k * m / h : ℕ) : ℤ)) (by simp), Tsum, Dsum]

lemma mod_add_mod_eq {H k h r : ℕ} (hc : Nat.Coprime k h) (hdvd : h ∣ H + k) (hr0 : 0 < r) (hr : r < h) :
    H * r % h + k * r % h = h := by
  have hh : 0 < h := by omega
  have hb : k * r % h ≠ 0 := fun h0 => by have := mulMod_eq_zero hc hr h0; omega
  have hdiv : h ∣ H * r % h + k * r % h := by
    rw [Nat.dvd_iff_mod_eq_zero, ← Nat.add_mod, ← add_mul]
    exact Nat.eq_zero_of_dvd_of_lt (by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_mod]; exact Nat.dvd_iff_mod_eq_zero.mp (dvd_mul_of_dvd_left hdvd r))
      (Nat.mod_lt _ hh) |> fun h => by rw [h]
  obtain ⟨c, hc'⟩ := hdiv
  have h1 := Nat.mod_lt (H * r) hh
  have h2 := Nat.mod_lt (k * r) hh
  rcases c with _ | _ | c
  · omega
  · omega
  · nlinarith

lemma coprime_of_dvd_add {H k h : ℕ} (hc : Nat.Coprime k h) (hdvd : h ∣ H + k) : Nat.Coprime H h := by
  show Nat.gcd H h = 1
  apply Nat.dvd_one.mp
  rw [← Nat.Coprime.gcd_eq_one hc]
  refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
  have h1 : Nat.gcd H h ∣ H + k := dvd_trans (Nat.gcd_dvd_right _ _) hdvd
  exact (Nat.dvd_add_right (Nat.gcd_dvd_left _ _)).mp h1

/-- `s(H,h) = −s(k,h)` when `H ≡ −k (mod h)`. -/
lemma dsum_neg {H k h : ℕ} (hh : 0 < h) (hc : Nat.Coprime k h) (hdvd : h ∣ H + k) :
    dsum H h = - dsum k h := by
  have hcH : Nat.Coprime H h := coprime_of_dvd_add hc hdvd
  rw [dsum_eq_Asum hh hcH, dsum_eq_Asum hh hc]
  have hA : Asum H h = h * ∑ r ∈ range h, (r : ℤ) - Asum k h := by
    rw [Asum, Asum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun r hr => ?_
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · simp
    · have := mod_add_mod_eq hc hdvd hr0 (mem_range.mp hr)
      have : ((H * r % h : ℕ) : ℤ) = h - (k * r % h : ℕ) := by omega
      rw [this]; ring
  have hid := sum_range_id_int (R := ℤ) h
  have hAR : (Asum H h : ℝ) = h * (h * (h - 1) / 2) - Asum k h := by
    have : (Asum H h : ℤ) * 2 = h * (h * (h - 1)) - 2 * Asum k h := by linear_combination 2 * hA + h * hid
    have : (Asum H h : ℝ) * 2 = h * (h * (h - 1)) - 2 * Asum k h := by exact_mod_cast this
    linarith
  have hhr : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [hAR]
  field_simp
  ring

/-- **Dedekind's reciprocity law**. -/
theorem dsum_reciprocity {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hc : Nat.Coprime h k) :
    dsum h k + dsum k h = ((h : ℝ) / k + k / h + 1 / (h * k)) / 12 - 1 / 4 := by
  rw [dsum_eq_Asum hk hc, dsum_eq_Asum hh hc.symm]
  have e1 := Asum_eq h k
  have e2 := Asum_eq k h
  have e3 := Qsum_perm hk hc
  have e4 := Qsum_count hk hh hc
  have e5 := Dsum_eq hh hc.symm
  have s1 := sum_range_sq_int k
  have s2 := sum_range_sq_int h
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hhr : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  generalize Asum h k = A1 at e1 ⊢
  generalize Asum k h = A2 at e2 ⊢
  generalize Qsum h k = Q at e3 e4
  generalize Tsum h k = T1 at e1 e3
  generalize Tsum k h = T2 at e2 e4
  generalize Dsum k h = D at e4 e5
  generalize ∑ r ∈ range k, (r : ℤ) ^ 2 = Sk at e1 e3 s1
  generalize ∑ r ∈ range h, (r : ℤ) ^ 2 = Sh at e2 s2
  -- solve the integer system for `12 h² A1 + 12 k² A2`
  have key : 12 * (h : ℤ) ^ 2 * A1 + 12 * k ^ 2 * A2 =
      h * k * (h ^ 2 + k ^ 2 + 1) + 3 * h ^ 2 * k ^ 2 * (h + k) - 9 * h ^ 2 * k ^ 2 := by
    linear_combination 12 * (h : ℤ) ^ 2 * e1 + 12 * (k : ℤ) ^ 2 * e2 + 6 * (h : ℤ) * e3 - 6 * (h : ℤ) * k ^ 2 * e4 -
      3 * (h : ℤ) * k ^ 2 * e5 + (h : ℤ) * (h ^ 2 + 1) * s1 + 2 * (k : ℤ) ^ 3 * s2
  have keyR : 12 * (h : ℝ) ^ 2 * A1 + 12 * k ^ 2 * A2 =
      h * k * (h ^ 2 + k ^ 2 + 1) + 3 * h ^ 2 * k ^ 2 * (h + k) - 9 * h ^ 2 * k ^ 2 := by exact_mod_cast key
  field_simp
  linear_combination 4 * keyR

end

end Rademacher
