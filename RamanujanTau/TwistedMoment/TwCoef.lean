/-
# The twisted coefficient sequences `ι_a(x) = [a ∣ x] λ(x/a)`

* `sum_dvd`: `Σ_{x≤N} [a∣x] f(x/a) = Σ_{M ≤ N/a} f(M)`.
* `iota_rankin`: `Σ_{x≤N} ι_a(x)² ≤ A N`.
* `prefix_eq`: `Σ_{x≤N} ι_a(x) ι_b(x+ℓ) = S(b,a;ℓ,N_t)` (`HeckeAFE.shiftSum2`) with `N_t ≤ N + ℓ`.
* `iota_scs`: `|Σ_{x≤N} ι_a(x) ι_b(x+ℓ)| ≤ C (N+ℓ)^{20/21} ℓ^{1/21} (ab)^{12}` (from `SCS2Coprime.scs2_general`).
-/
import RamanujanTau.TwistedMoment.GParam
import RamanujanTau.SCS2Coprime.Main3

set_option autoImplicit false

namespace RamanujanTau.TwistedMoment

open Finset

/-- `λ` of the repo (normalised Ramanujan `τ`). -/
noncomputable abbrev lamS : ℕ → ℝ := RamanujanTau.SubconvexityCond.lam

/-- `ι_a(x) = [a ∣ x] λ(x/a)`. -/
noncomputable def iota (a x : ℕ) : ℝ := if a ∣ x then lamS (x / a) else 0

lemma lamS_zero : lamS 0 = 0 := by simp [lamS, RamanujanTau.SubconvexityCond.lam, tau_zero]

lemma iota_zero (a : ℕ) : iota a 0 = 0 := by simp [iota, lamS_zero]

lemma sum_dvd {a : ℕ} (ha : 1 ≤ a) (f : ℕ → ℝ) (N : ℕ) :
    ∑ x ∈ Icc 1 N, (if a ∣ x then f (x / a) else 0) = ∑ M ∈ Icc 1 (N / a), f M := by
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun M => a * M) (Icc 1 (N / a) : Set ℕ) := fun x _ y _ h => by
    simpa [Nat.mul_left_cancel_iff (by omega : 0 < a)] using h
  have himg : (Icc 1 N).filter (fun x => a ∣ x) = (Icc 1 (N / a)).image (fun M => a * M) := by
    ext x
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨M, rfl⟩⟩
      refine ⟨M, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos M with h | h
        · subst h; simp at h1
        · exact h
      · exact (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact h2)
    · rintro ⟨M, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨M, rfl⟩⟩
      · exact le_trans h1 (Nat.le_mul_of_pos_left M (by omega))
      · have := (Nat.le_div_iff_mul_le (by omega)).1 h2
        rw [mul_comm]; exact this
  rw [himg, Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [Nat.mul_div_cancel_left M (by omega)]

lemma iota_rankin : ∃ A : ℝ, 0 ≤ A ∧ ∀ (a N : ℕ), 1 ≤ a → ∑ x ∈ Icc 1 N, iota a x ^ 2 ≤ A * N := by
  obtain ⟨A, hA0, hA⟩ := RamanujanTau.SubconvexityCond.exists_sum_lam_sq_le
  refine ⟨A, hA0, fun a N ha => ?_⟩
  have e : ∑ x ∈ Icc 1 N, iota a x ^ 2 = ∑ x ∈ Icc 1 N, (if a ∣ x then lamS (x / a) ^ 2 else 0) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold iota; split_ifs <;> simp
  rw [e, sum_dvd ha (fun M => lamS M ^ 2)]
  refine (hA (N / a)).trans ?_
  have : ((N / a : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N a
  exact mul_le_mul_of_nonneg_left this hA0

/-- The inner sum of `shiftSum2` over `m`. -/
lemma inner_m (a b ℓ n Nt : ℕ) (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) :
    ∑ m ∈ Icc 1 Nt, (if (b : ℤ) * m - a * n = (ℓ : ℤ) then lamS m * lamS n else 0) =
      if b ∣ a * n + ℓ ∧ (a * n + ℓ) / b ≤ Nt then lamS ((a * n + ℓ) / b) * lamS n else 0 := by
  have hc : ∀ m : ℕ, ((b : ℤ) * m - a * n = (ℓ : ℤ)) ↔ (b ∣ a * n + ℓ ∧ m = (a * n + ℓ) / b) := by
    intro m
    constructor
    · intro h
      have h' : b * m = a * n + ℓ := by exact_mod_cast (by linarith : (b : ℤ) * m = a * n + ℓ)
      refine ⟨⟨m, h'.symm⟩, ?_⟩
      rw [← h', Nat.mul_div_cancel_left m (by omega)]
    · rintro ⟨⟨q, hq⟩, rfl⟩
      rw [hq, Nat.mul_div_cancel_left q (by omega)]
      have : ((a * n + ℓ : ℕ) : ℤ) = b * q := by exact_mod_cast hq
      push_cast at this; linarith
  simp_rw [hc, ite_and]
  by_cases hd : b ∣ a * n + ℓ
  · simp only [hd, if_true]
    rw [Finset.sum_ite_eq' (Icc 1 Nt) ((a * n + ℓ) / b) (fun m => lamS m * lamS n)]
    have h1 : 1 ≤ (a * n + ℓ) / b := by
      obtain ⟨q, hq⟩ := hd
      rw [hq, Nat.mul_div_cancel_left q (by omega)]
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; omega
      · exact h
    by_cases h2 : (a * n + ℓ) / b ≤ Nt
    · rw [if_pos (by simp [mem_Icc]; omega), if_pos h2]
    · rw [if_neg (by simp [mem_Icc]; omega), if_neg h2]
  · simp [hd]

/-- **Prefix sums are two-sided shifted sums.** -/
theorem prefix_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (N : ℕ) :
    ∃ Nt : ℕ, Nt ≤ N + ℓ ∧
      ∑ x ∈ Icc 1 N, iota a x * iota b (x + ℓ) = RamanujanTau.HeckeAFE.shiftSum2 b a (ℓ : ℤ) Nt := by
  set m₀ := N / a with hm₀
  set n₀ := (a * m₀ + ℓ) / b with hn₀
  refine ⟨max m₀ n₀, ?_, ?_⟩
  · have h1 : m₀ ≤ N := Nat.div_le_self N a
    have h2 : n₀ ≤ a * m₀ + ℓ := Nat.div_le_self _ b
    have h3 : a * m₀ ≤ N := by rw [hm₀]; exact Nat.mul_div_le N a
    omega
  set Nt := max m₀ n₀ with hNt
  -- left side
  have hL : ∑ x ∈ Icc 1 N, iota a x * iota b (x + ℓ) =
      ∑ n ∈ Icc 1 m₀, lamS n * iota b (a * n + ℓ) := by
    rw [← sum_dvd ha (fun n => lamS n * iota b (a * n + ℓ)) N]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold iota
    by_cases hx : a ∣ x
    · obtain ⟨q, rfl⟩ := hx
      simp only [dvd_mul_right, if_true, Nat.mul_div_cancel_left q (by omega : 0 < a)]
    · simp [hx]
  rw [hL]
  unfold RamanujanTau.HeckeAFE.shiftSum2
  rw [Finset.sum_comm]
  simp_rw [inner_m a b ℓ _ Nt hb hℓ]
  -- both sides as sums over `Icc 1 Nt` with the cut `n ≤ m₀`
  have hsub : Icc 1 m₀ ⊆ Icc 1 Nt := Finset.Icc_subset_Icc le_rfl (le_max_left _ _)
  have hvan : ∀ n ∈ Icc 1 Nt, n ∉ Icc 1 m₀ →
      (if b ∣ a * n + ℓ ∧ (a * n + ℓ) / b ≤ Nt then lamS ((a * n + ℓ) / b) * lamS n else 0) = 0 := by
    intro n hn hn'
    simp only [mem_Icc] at hn hn'
    have hgt : m₀ < n := by omega
    rw [if_neg]
    rintro ⟨hd, hc⟩
    by_cases h0 : n₀ ≤ m₀
    · have : Nt = m₀ := max_eq_left h0
      omega
    · have hNt : Nt = n₀ := max_eq_right (by omega)
      have e1 : b * ((a * n + ℓ) / b) = a * n + ℓ := Nat.mul_div_cancel' hd
      have e2 : b * n₀ ≤ a * m₀ + ℓ := Nat.mul_div_le _ _
      have e3 : b * ((a * n + ℓ) / b) ≤ b * n₀ := Nat.mul_le_mul_left b (hNt ▸ hc)
      have e4 : a * n ≤ a * m₀ := by omega
      have := Nat.le_of_mul_le_mul_left e4 (by omega : 0 < a)
      omega
  rw [← Finset.sum_subset hsub hvan]
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [mem_Icc] at hn
  unfold iota
  by_cases hd : b ∣ a * n + ℓ
  · have hc : (a * n + ℓ) / b ≤ Nt :=
      calc (a * n + ℓ) / b ≤ (a * m₀ + ℓ) / b :=
            Nat.div_le_div_right (by have := Nat.mul_le_mul_left a hn.2; omega)
        _ ≤ Nt := le_max_right _ _
    rw [if_pos hd, if_pos ⟨hd, hc⟩, mul_comm]
  · rw [if_neg hd, if_neg (fun h => hd h.1), mul_zero]

end RamanujanTau.TwistedMoment
