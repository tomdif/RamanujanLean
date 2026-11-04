/-
# A bit-packed, kernel-checkable table of `p(n)`

`ptP B N` runs Euler's pentagonal recurrence, storing `p(m)` in the `B`-bit slot `m` of a single natural
number (`look B T m = ⌊T / 2^{mB}⌋ mod 2^B`). Lookups are then single GMP-accelerated kernel operations,
instead of the linear `List.getD` of `LogConcave.ptab` (which needs ~8 GB of kernel memory already at `N = 700`).
A flag `ok` records that every computed value lies in `[0, 2^B)`; under `ok = true` the table is exact:
`ptP_spec : (ptP B N).ok = true → ∀ m ≤ N, look B (ptP B N).T m = #(Nat.Partition m)`.
-/
import RamanujanTau.LogConcaveTable

set_option autoImplicit false

namespace JensenThreshold
open PowerSeries MockTheta5.JTP MockTheta5.Bailey LogConcave

/-- slot `m` (width `B` bits) of `T`. -/
def look (B T m : ℕ) : ℕ := T / 2 ^ (m * B) % 2 ^ B

/-- the pentagonal-recurrence value `p(N+1)` computed from a table holding `p(0..N)`. -/
def nextV (B T N : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (Nat.sqrt (N + 1) + 1), (-1 : ℤ) ^ m *
    ((if g1 m ≤ N + 1 then (look B T (N + 1 - g1 m) : ℤ) else 0) +
     (if g2 m ≤ N + 1 then (look B T (N + 1 - g2 m) : ℤ) else 0))

structure PT where
  T : ℕ
  ok : Bool
  deriving DecidableEq

/-- the packed table `p(0), …, p(N)` with a range flag. -/
def ptP (B : ℕ) : ℕ → PT
  | 0 => ⟨1, true⟩
  | N + 1 =>
    let r := ptP B N
    let v := nextV B r.T N
    ⟨r.T + v.toNat * 2 ^ ((N + 1) * B), r.ok && decide (0 ≤ v) && decide (v < 2 ^ B)⟩

lemma look_add_lt {B T k v m : ℕ} (hm : m < k) :
    look B (T + v * 2 ^ (k * B)) m = look B T m := by
  unfold look
  have hk : 2 ^ (k * B) = 2 ^ (m * B) * (2 ^ B * 2 ^ ((k - m - 1) * B)) := by
    rw [← pow_add, ← pow_add]; congr 1
    have : k = m + 1 + (k - m - 1) := by omega
    conv_lhs => rw [this]
    ring
  rw [hk, show v * (2 ^ (m * B) * (2 ^ B * 2 ^ ((k - m - 1) * B))) =
      (v * (2 ^ B * 2 ^ ((k - m - 1) * B))) * 2 ^ (m * B) by ring,
    Nat.add_mul_div_right _ _ (by positivity), Nat.add_mod,
    show v * (2 ^ B * 2 ^ ((k - m - 1) * B)) = 2 ^ B * (v * 2 ^ ((k - m - 1) * B)) by ring,
    Nat.mul_mod_right, add_zero, Nat.mod_mod]

lemma look_add_eq {B T k v : ℕ} (hT : T < 2 ^ (k * B)) (hv : v < 2 ^ B) :
    look B (T + v * 2 ^ (k * B)) k = v := by
  unfold look
  rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hT, zero_add, Nat.mod_eq_of_lt hv]

lemma nextV_eq {B T N : ℕ} (h : ∀ m ≤ N, (look B T m : ℤ) = coeff m partitionGF) :
    nextV B T N = coeff (N + 1) partitionGF := by
  rw [partition_pentagonal_recurrence (N + 1) (by omega), nextV]
  have hterm : ∀ m, (-1 : ℤ) ^ m * ((if g1 m ≤ N + 1 then (look B T (N + 1 - g1 m) : ℤ) else 0) +
        (if g2 m ≤ N + 1 then (look B T (N + 1 - g2 m) : ℤ) else 0)) =
      (-1 : ℤ) ^ m * ((if (m + 1) * (3 * m + 2) / 2 ≤ N + 1 then
          coeff (N + 1 - (m + 1) * (3 * m + 2) / 2) partitionGF else 0) +
        (if (m + 1) * (3 * m + 4) / 2 ≤ N + 1 then
          coeff (N + 1 - (m + 1) * (3 * m + 4) / 2) partitionGF else 0)) := by
    intro m
    have h1 := g1_pos m
    have h2 := g2_pos m
    unfold g1 g2 at *
    congr 2
    · by_cases hh : (m + 1) * (3 * m + 2) / 2 ≤ N + 1
      · rw [if_pos hh, if_pos hh, h _ (by omega)]
      · rw [if_neg hh, if_neg hh]
    · by_cases hh : (m + 1) * (3 * m + 4) / 2 ≤ N + 1
      · rw [if_pos hh, if_pos hh, h _ (by omega)]
      · rw [if_neg hh, if_neg hh]
  simp only [hterm]
  apply Finset.sum_subset
  · exact Finset.range_subset_range.mpr (by have := Nat.sqrt_le_self (N + 1); omega)
  · intro m _ hm
    simp only [Finset.mem_range, not_lt] at hm
    have h1 := sq_lt_g1 (N := N + 1) hm
    have h2 := g1_le_g2 m
    unfold g1 g2 at *
    rw [if_neg (by omega), if_neg (by omega)]; ring

theorem ptP_spec_aux {B : ℕ} (hB : 0 < B) (N : ℕ) (hok : (ptP B N).ok = true) :
    (ptP B N).T < 2 ^ ((N + 1) * B) ∧ ∀ m ≤ N, (look B (ptP B N).T m : ℤ) = coeff m partitionGF := by
  induction N with
  | zero =>
    refine ⟨by simp only [ptP, zero_add, one_mul]; exact Nat.one_lt_two_pow hB.ne', ?_⟩
    intro m hm
    obtain rfl : m = 0 := by omega
    simp only [ptP, look, zero_mul, pow_zero, Nat.div_one]
    rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow hB.ne'), coeff_partitionGF_eq_card]; rfl
  | succ N ih =>
    simp only [ptP, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hok0, hv0⟩, hv1⟩ := hok
    obtain ⟨hT, htab⟩ := ih hok0
    have hv := nextV_eq htab
    set v := nextV B (ptP B N).T N
    have hvn : v.toNat < 2 ^ B := by
      have : (v.toNat : ℤ) < 2 ^ B := by rw [Int.toNat_of_nonneg hv0]; exact hv1
      exact_mod_cast this
    refine ⟨?_, ?_⟩
    · simp only [ptP]
      calc (ptP B N).T + v.toNat * 2 ^ ((N + 1) * B)
          < 2 ^ ((N + 1) * B) + v.toNat * 2 ^ ((N + 1) * B) := by omega
        _ = (v.toNat + 1) * 2 ^ ((N + 1) * B) := by ring
        _ ≤ 2 ^ B * 2 ^ ((N + 1) * B) := Nat.mul_le_mul_right _ hvn
        _ = 2 ^ ((N + 1 + 1) * B) := by rw [← pow_add]; congr 1; ring
    · intro m hm
      simp only [ptP]
      rcases Nat.lt_or_ge m (N + 1) with hlt | hge
      · rw [look_add_lt hlt]; exact htab m (by omega)
      · obtain rfl : m = N + 1 := by omega
        rw [look_add_eq hT hvn, Int.toNat_of_nonneg hv0, hv]

/-- one recurrence step, from the table up to `N` to the table up to `N + 1`. -/
def stepPT (B N : ℕ) (r : PT) : PT :=
  let v := nextV B r.T N
  ⟨r.T + v.toNat * 2 ^ ((N + 1) * B), r.ok && decide (0 ≤ v) && decide (v < 2 ^ B)⟩

lemma ptP_succ (B N : ℕ) : ptP B (N + 1) = stepPT B N (ptP B N) := rfl

/-- `k` steps starting from the table up to `N`. -/
def iterPT (B : ℕ) : ℕ → PT → ℕ → PT
  | _, r, 0 => r
  | N, r, k + 1 => iterPT B (N + 1) (stepPT B N r) k

lemma iterPT_ptP (B : ℕ) : ∀ (k N : ℕ), iterPT B N (ptP B N) k = ptP B (N + k)
  | 0, N => rfl
  | k + 1, N => by
    rw [iterPT, ← ptP_succ, iterPT_ptP B k (N + 1), show N + 1 + k = N + (k + 1) by omega]

/-- segment-wise verification of the table (keeps each kernel check small). -/
lemma ptP_of_seg {B M k M' : ℕ} {r r' : PT} (hM : M + k = M') (h0 : ptP B M = r)
    (h : iterPT B M r k = r') : ptP B M' = r' := by
  rw [← hM, ← iterPT_ptP, h0, h]

/-- **The packed table is exact**: if the range flag is set, slot `m` holds `#(Nat.Partition m)`. -/
theorem ptP_spec {B N : ℕ} (hB : 0 < B) (hok : (ptP B N).ok = true) {m : ℕ} (hm : m ≤ N) :
    look B (ptP B N).T m = Fintype.card (Nat.Partition m) := by
  have := (ptP_spec_aux hB N hok).2 m hm
  rw [coeff_partitionGF_eq_card] at this
  exact_mod_cast this

end JensenThreshold
