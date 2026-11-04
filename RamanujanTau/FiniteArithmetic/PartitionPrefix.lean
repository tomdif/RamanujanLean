import RamanujanTau.FiniteArithmetic.PackedSeries
import RamanujanTau.BoylanWebb.Series
import RamanujanTau.MockTheta5PentagonalRecurrence

/-! # Certified partition prefixes modulo a small modulus

`pgfPrefix Q N J` computes the first `N` partition numbers modulo `Q` as one packed
natural number: Euler's pentagonal series with `J` pairs, then a Newton inverse certified by one product.
`rep_pgfPrefix` identifies the result with the actual partition generating function,
for any `Q ≤ 2^21` and `N ≤ 2^16`. -/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.PartitionPrefix

open PowerSeries Packed
open MockTheta5.JTP (qfacInf partitionGF pentSeries euler_pentagonal coeff_pentSeries_lt
  map_evm1_pentFiniteP sgn sgn_natCast sgn_neg sgn_succ)

/-! ### The program -/

/-- Generalized pentagonal exponents for `k = j + 1`. -/
def pentLow (j : ℕ) : ℕ := (j + 1) * (3 * (j + 1) - 1) / 2
def pentHigh (j : ℕ) : ℕ := (j + 1) * (3 * (j + 1) + 1) / 2
def pentSign (Q j : ℕ) : ℕ := if j % 2 = 0 then Q - 1 else 1

def mu (Q : ℕ) : ℕ := 2 ^ 40 / Q

/-- `1 + Σ_{j<J} (-1)^(j+1) (q^low + q^high)`, reduced. -/
def pentFold (Q N : ℕ) : ℕ → Option ℕ
  | 0 => some 1
  | j + 1 => do
    let a ← pentFold Q N j
    let b ← addR Q N (mu Q) a (shiftR N (pentLow j) (pentSign Q j))
    addR Q N (mu Q) b (shiftR N (pentHigh j) (pentSign Q j))

/-- A multiple of `Q` near `2^18`, where the untrusted reduction is tuned. -/
def bigQ (Q : ℕ) : ℕ := Q * (2 ^ 18 / Q)

/-- Untrusted Newton iteration modulo `bigQ Q`; an inverse there is one modulo `Q`.
Certified afterwards by `invOk` modulo `Q`. -/
def newton (Q N u : ℕ) : ℕ → ℕ → ℕ
  | 0, b => b
  | n + 1, b =>
    let v := (reduceRaw (bigQ Q) N (mu (bigQ Q)) ((u * b) % x ^ N)).1
    let w := fastMask (16 * bigQ Q) N - v + 2
    newton Q N u n (reduceRaw (bigQ Q) N (mu (bigQ Q)) ((b * w) % x ^ N)).1

/-- The partition prefix from `J` pentagonal pairs, or failure. -/
def pgfPrefix (Q N J : ℕ) : Option ℕ := do
  let P ← pentFold Q N J
  let B := newton Q N P 17 1
  if invOk Q N (mu Q) P B then some B else none

/-! ### Correctness -/

section
variable {Q N : ℕ}

noncomputable abbrev rd (Q : ℕ) : PowerSeries ℤ →+* PowerSeries (ZMod Q) :=
  PowerSeries.map (Int.castRingHom (ZMod Q))

lemma bind_some {α β : Type} {e : Option α} {f : α → Option β} {r : β}
    (h : (e >>= f) = some r) : ∃ a, e = some a ∧ f a = some r := by
  cases e with
  | none => simp at h
  | some a => exact ⟨a, rfl, h⟩

/-- The partial pentagonal sum computed by `pentFold`. -/
noncomputable def pentPartial (Q : ℕ) : ℕ → PowerSeries (ZMod Q)
  | 0 => 1
  | j + 1 => pentPartial Q j +
      X ^ pentLow j * PowerSeries.C (pentSign Q j : ZMod Q) +
      X ^ pentHigh j * PowerSeries.C (pentSign Q j : ZMod Q)

lemma pentSign_lt (hQ : Q ≤ 2 ^ 21) (j : ℕ) : pentSign Q j < 2 ^ 22 := by
  unfold pentSign
  split_ifs <;> omega

theorem pentFold_rep (hQ : Q ≤ 2 ^ 21) (hN : 0 < N) (J : ℕ) {a : ℕ}
    (h : pentFold Q N J = some a) : Rep N 22 a (pentPartial Q J) := by
  induction J generalizing a with
  | zero =>
    obtain rfl : 1 = a := Option.some.inj h
    have := rep_C (Q := Q) (c := 1) hN (by norm_num) (by norm_num : 22 ≤ 64)
    simpa [pentPartial] using this
  | succ j ih =>
    obtain ⟨a0, h0, h1⟩ := bind_some h
    obtain ⟨b, h2, h3⟩ := bind_some h1
    have hs := fun d => Rep.shiftR (d := d) (rep_C (Q := Q) hN (pentSign_lt hQ j)
      (by norm_num : 22 ≤ 64)) (by norm_num : 22 ≤ 64)
    exact Rep.addR hQ (Rep.addR hQ (ih h0) (hs _) h2) (hs _) h3

lemma cast_pentSign (hQ1 : 1 ≤ Q) (j : ℕ) :
    (pentSign Q j : ZMod Q) = ((-1 : ℤ) ^ (j + 1) : ℤ) := by
  unfold pentSign
  have hQ1' : ((Q - 1 : ℕ) : ZMod Q) = -1 := by
    rw [Nat.cast_sub hQ1, ZMod.natCast_self]
    simp
  split_ifs with h
  · have he : Even j := Nat.even_iff.mpr h
    rw [hQ1', pow_succ, he.neg_one_pow]
    simp
  · have ho : Odd j := Nat.odd_iff.mpr (by omega)
    rw [pow_succ, ho.neg_one_pow]
    simp

lemma sgn_pos (m : ℕ) : sgn ((m : ℤ) + 1) = (-1 : ℤ) ^ (m + 1) := by
  rw [sgn_succ, sgn_natCast, pow_succ]; ring

lemma pentLow_eq (m : ℕ) : pentLow m = (m + 1) * (3 * m + 2) / 2 := by
  unfold pentLow; congr 2

lemma pentHigh_eq (m : ℕ) : pentHigh m = (m + 1) * (3 * m + 4) / 2 := by
  unfold pentHigh; congr 2

lemma rd_truncation (hQ1 : 1 ≤ Q) (M : ℕ) :
    rd Q (1 + ∑ m ∈ Finset.range M,
        (X ^ ((m + 1) * (3 * m + 2) / 2) * PowerSeries.C (sgn ((m : ℤ) + 1))
          + X ^ ((m + 1) * (3 * m + 4) / 2) * PowerSeries.C (sgn (-((m : ℤ) + 1))))) =
      pentPartial Q M := by
  induction M with
  | zero => simp [pentPartial]
  | succ M ih =>
    rw [Finset.sum_range_succ, ← add_assoc, map_add, ih, pentPartial, map_add, map_mul, map_mul,
      map_pow, map_pow, PowerSeries.map_X, PowerSeries.map_C, PowerSeries.map_C, sgn_neg, sgn_pos,
      ← pentLow_eq, ← pentHigh_eq, cast_pentSign hQ1]
    simp only [eq_intCast]
    ring

lemma pentLow_mono {m n : ℕ} (h : m ≤ n) : pentLow m ≤ pentLow n := by
  rw [pentLow_eq, pentLow_eq]
  exact Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))

lemma pentHigh_mono {m n : ℕ} (h : m ≤ n) : pentHigh m ≤ pentHigh n := by
  rw [pentHigh_eq, pentHigh_eq]
  exact Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))

variable {J : ℕ}

lemma coeff_pentPartial_stable (hJ : N ≤ pentLow J) (i : ℕ) (hi : i < N) (k : ℕ) :
    PowerSeries.coeff i (pentPartial Q (J + k)) =
      PowerSeries.coeff i (pentPartial Q J) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, pentPartial, map_add, map_add, ih, mul_comm (X ^ pentLow _),
      mul_comm (X ^ pentHigh _), PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
    have h1 : N ≤ pentLow (J + k) :=
      le_trans hJ (pentLow_mono (Nat.le_add_right _ k))
    have h2 : pentLow (J + k) ≤ pentHigh (J + k) := by
      rw [pentLow_eq, pentHigh_eq]
      exact Nat.div_le_div_right (Nat.mul_le_mul le_rfl (by omega))
    rw [if_neg (by omega), if_neg (by omega)]
    simp

theorem coeff_rd_qfacInf (hQ1 : 1 ≤ Q) (hJ : N ≤ pentLow J) (i : ℕ) (hi : i < N) :
    PowerSeries.coeff i (rd Q qfacInf) = PowerSeries.coeff i (pentPartial Q J) := by
  rw [← coeff_pentPartial_stable (Q := Q) hJ i hi (i + 1), ← rd_truncation hQ1, euler_pentagonal,
    PowerSeries.coeff_map, PowerSeries.coeff_map,
    coeff_pentSeries_lt (M := J + (i + 1)) (by omega), map_evm1_pentFiniteP]

/-- **The certified prefix of the partition generating function.** -/
theorem rep_pgfPrefix (hQ1 : 1 ≤ Q) (hQ : Q ≤ 2 ^ 21) (hN0 : 0 < N) (hN : N ≤ 2 ^ 16)
    (hJ : N ≤ pentLow J) {B : ℕ}
    (h : pgfPrefix Q N J = some B) : Rep N 22 B (rd Q partitionGF) := by
  obtain ⟨P, hP, h⟩ := bind_some h
  have hPr : Rep N 22 P (rd Q qfacInf) :=
    (pentFold_rep hQ hN0 _ hP).congr fun i hi => (coeff_rd_qfacInf hQ1 hJ i hi).symm
  simp only at h
  split_ifs at h with hok
  obtain rfl := Option.some.inj h
  exact Rep.inv_of_ok hQ hN0 hPr (by rw [← map_mul, BoylanWebb.qfac_mul_pgf, map_one]) hN
    (by norm_num) hok

/-- Reading a coefficient of the partition generating function from the prefix. -/
theorem coeff_pgf (hQ1 : 1 ≤ Q) (hQ : Q ≤ 2 ^ 21) (hN0 : 0 < N) (hN : N ≤ 2 ^ 16)
    (hJ : N ≤ pentLow J) {B : ℕ}
    (h : pgfPrefix Q N J = some B) (i : ℕ) (hi : i < N) :
    ((PowerSeries.coeff i partitionGF : ℤ) : ZMod Q) = (lane B i : ZMod Q) := by
  rw [(rep_pgfPrefix hQ1 hQ hN0 hN hJ h).coeff i hi, rd, PowerSeries.coeff_map]
  rfl

end

/-! ### Long prefixes

For `N` up to a few million the pentagonal fold and the reductions above are too costly in the
kernel. Here the pentagonal polynomial is assembled from blocks built by halving (its exponents are
distinct, so no reduction is needed), the inverse is found by an untrusted Newton iteration that
doubles its working length, and the inverse check needs no reduction: with lanes of `u` below
`2^ku`, of `b` below `2^kb`, and `N ≤ 2^kN`, the product has lanes below `2^(ku+kb+kN) < 2^64`,
and `u * b ≡ 1` is `u * b = 1 + Q * c` with every lane of `c` below `2^kc`. -/

/-- `r` is `1` plus `Q` times a series with `kc`-bit lanes. -/
def isOneOkG (Q N kc r : ℕ) : Bool :=
  let c := (r - 1) / Q
  r == 1 + Q * c && decide (c < x ^ N) && (c &&& fastMask (highBits kc) N) == 0

/-- Certificate that `b` inverts `u`, with lane widths `ku` and `kb`. -/
def invOkG (Q N ku kb kc u b : ℕ) : Bool :=
  decide (u < x ^ N) && (u &&& fastMask (highBits ku) N) == 0 &&
    decide (b < x ^ N) && (b &&& fastMask (highBits kb) N) == 0 &&
    isOneOkG Q N kc ((u * b) % x ^ N)

/-- The pentagonal pairs `lo, …, lo + 2^d - 1`, divided by `q^(pentLow lo)`, built by halving. -/
def pentBlock (Q lo : ℕ) : ℕ → ℕ
  | 0 => pentSign Q lo + (pentSign Q lo <<< (64 * (pentHigh lo - pentLow lo)))
  | d + 1 => pentBlock Q lo d +
      (pentBlock Q (lo + 2 ^ d) d <<< (64 * (pentLow (lo + 2 ^ d) - pentLow lo)))

/-- The first `k` blocks of `2^d` pairs, divided by `q^(pentLow 0)`. -/
def pentMulti (Q d : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => pentMulti Q d k +
      (pentBlock Q (k * 2 ^ d) d <<< (64 * (pentLow (k * 2 ^ d) - pentLow 0)))

/-- `1 + Σ_{j < k 2^d} (-1)^(j+1) (q^low + q^high)`, truncated. -/
def pentFast (Q N d k : ℕ) : ℕ := (1 + (pentMulti Q d k <<< 64)) % x ^ N

/-- Untrusted Newton iteration modulo `R`, doubling the working length `p` each step. -/
def newtonG (R N u : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, b => b
  | n + 1, p, b =>
    let M := min N (2 * p)
    let v := (reduceRaw R M (mu R) ((u % x ^ M * b) % x ^ M)).1
    let w := (reduceRaw R M (mu R) (fastMask (16 * R) M - v + 2)).1
    newtonG R N u n M (reduceRaw R M (mu R) ((b * w) % x ^ M)).1

/-- The partition prefix modulo `Q`, from `k 2^d` pentagonal pairs and `n` Newton steps
modulo a multiple `R` of `Q` (untrusted; any `R` is sound). -/
def pgfPrefixG (Q R N d k n ku kb kc : ℕ) : Option ℕ :=
  let P := pentFast Q N d k
  let B := newtonG R N P n 1 1
  if invOkG Q N ku kb kc P B then some B else none

section
variable {Q N : ℕ}

/-- The pentagonal polynomial over `ℕ`. -/
noncomputable def pentPoly (Q : ℕ) (lo n : ℕ) : Polynomial ℕ :=
  ∑ j ∈ Finset.range n, (Polynomial.monomial (pentLow (lo + j)) (pentSign Q (lo + j)) +
    Polynomial.monomial (pentHigh (lo + j)) (pentSign Q (lo + j)))

lemma pentLow_le_pentHigh (j : ℕ) : pentLow j ≤ pentHigh j := by
  rw [pentLow_eq, pentHigh_eq]
  exact Nat.div_le_div_right (Nat.mul_le_mul le_rfl (by omega))

lemma x_pow_shift (a s t : ℕ) (h : s ≤ t) : x ^ s * (a <<< (64 * (t - s))) = x ^ t * a := by
  rw [Nat.shiftLeft_eq, pow_mul, show (2 : ℕ) ^ 64 = x from rfl, mul_comm a, ← mul_assoc, ← pow_add,
    Nat.add_sub_cancel' h]

lemma eval_pentBlock (lo d : ℕ) :
    x ^ pentLow lo * pentBlock Q lo d = (pentPoly Q lo (2 ^ d)).eval x := by
  induction d generalizing lo with
  | zero =>
    simp only [pentBlock, pentPoly, pow_zero, Finset.sum_range_one, add_zero,
      Polynomial.eval_add, Polynomial.eval_monomial]
    rw [mul_add, x_pow_shift _ _ _ (pentLow_le_pentHigh lo)]
    ring
  | succ d ih =>
    rw [pentBlock, mul_add, x_pow_shift _ _ _ (pentLow_mono (Nat.le_add_right _ _)), ih, ih,
      pentPoly, pentPoly, pentPoly, pow_succ, mul_two, Finset.sum_range_add, Polynomial.eval_add]
    simp only [add_assoc]

lemma eval_pentMulti (d k : ℕ) :
    x ^ pentLow 0 * pentMulti Q d k = (pentPoly Q 0 (k * 2 ^ d)).eval x := by
  induction k with
  | zero => simp [pentMulti, pentPoly]
  | succ k ih =>
    rw [pentMulti, mul_add, x_pow_shift _ _ _ (pentLow_mono (Nat.zero_le _)), ih, eval_pentBlock,
      pentPoly, pentPoly, pentPoly, add_mul, one_mul, Finset.sum_range_add, Polynomial.eval_add]
    simp only [zero_add]

/-- The polynomial behind `pentFast`. -/
noncomputable def fastPoly (Q n : ℕ) : Polynomial ℕ := 1 + pentPoly Q 0 n

lemma pentFast_eq (d k : ℕ) : pentFast Q N d k = (fastPoly Q (k * 2 ^ d)).eval x % x ^ N := by
  rw [pentFast, fastPoly, Polynomial.eval_add, Polynomial.eval_one, ← eval_pentMulti,
    Nat.shiftLeft_eq, show (2 : ℕ) ^ 64 = x ^ pentLow 0 from rfl, mul_comm]

lemma coeff_pentPoly_le (hQ : Q ≤ 2 ^ 21) (lo n i : ℕ) :
    (pentPoly Q lo n).coeff i ≤ n * 2 ^ 23 := by
  induction n with
  | zero => simp [pentPoly]
  | succ n ih =>
    rw [pentPoly, Finset.sum_range_succ, ← pentPoly, Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial]
    have h1 := pentSign_lt hQ (lo + n)
    split_ifs <;> nlinarith

lemma xc (n : ℕ) (a : ZMod Q) :
    (X ^ n * PowerSeries.C a : PowerSeries (ZMod Q)) = PowerSeries.monomial n a := by
  ext i
  rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow, PowerSeries.coeff_monomial]
  split_ifs <;> simp

lemma cast_fastPoly (n : ℕ) :
    ((fastPoly Q n).map (Nat.castRingHom (ZMod Q)) : PowerSeries (ZMod Q)) = pentPartial Q n := by
  rw [fastPoly]
  induction n with
  | zero => simp [pentPoly, pentPartial]
  | succ n ih =>
    rw [pentPoly, Finset.sum_range_succ, ← pentPoly, ← add_assoc, Polynomial.map_add,
      Polynomial.coe_add, ih, pentPartial, Polynomial.map_add, Polynomial.coe_add,
      Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.coe_monomial,
      Polynomial.coe_monomial, add_assoc, xc, xc]
    simp

theorem rep_pentFast (hQ1 : 1 ≤ Q) (hQ : Q ≤ 2 ^ 21) {d k : ℕ} (hn : k * 2 ^ d ≤ 2 ^ 20)
    (hJ : N ≤ pentLow (k * 2 ^ d)) : Rep N 64 (pentFast Q N d k) (rd Q qfacInf) := by
  have hc : ∀ i, (fastPoly Q (k * 2 ^ d)).coeff i < x := by
    intro i
    rw [fastPoly, Polynomial.coeff_add, Polynomial.coeff_one]
    have h1 := coeff_pentPoly_le hQ 0 (k * 2 ^ d) i
    have : k * 2 ^ d * 2 ^ 23 ≤ 2 ^ 20 * 2 ^ 23 := Nat.mul_le_mul_right _ hn
    norm_num [x] at this ⊢
    split_ifs <;> omega
  have heq : pentFast Q N d k = pack (fastPoly Q (k * 2 ^ d)).coeff N := by
    rw [pentFast_eq, eval_mod_of_low, Nat.mod_eq_of_lt (pack_lt _ hc N)]
  refine ⟨⟨heq ▸ pack_lt _ hc N, fun i => heq ▸ lane_lt _ i⟩, fun i hi => ?_⟩
  rw [heq, lane_pack _ hc N i hi, coeff_rd_qfacInf hQ1 hJ i hi, ← cast_fastPoly,
    Polynomial.coeff_coe, Polynomial.coeff_map]
  rfl

theorem Rep.inv_of_okG {k ku kb kc kN u b : ℕ} {f v : PowerSeries (ZMod Q)}
    (hk : ku + kb + kN < 64) (hno : 2 ^ 22 + Q * 2 ^ kc ≤ x)
    (hN0 : 0 < N) (hu : Rep N k u f) (hfv : f * v = 1) (hN : N ≤ 2 ^ kN)
    (h : invOkG Q N ku kb kc u b = true) : Rep N kb b v := by
  simp only [invOkG, isOneOkG, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hu1, hu2⟩, hb1⟩, hb2⟩, ⟨h4, h5⟩, h6⟩ := h
  rw [fastMask_eq] at hu2 hb2 h6
  have hu' : Rep N ku u f := ⟨small_of_land hu1 hu2, hu.coeff⟩
  have hb := rep_seriesOf (Q := Q) (small_of_land hb1 hb2)
  have hprod := hu'.mul hb hN hk
  have hone : Rep N 22 1 (f * seriesOf Q b) :=
    hprod.reduce h4 (small_one hN0) (small_of_land h5 h6) hno
  refine hb.congr (coeff_eq_of_mul_prefix hfv fun i hi => ?_)
  rw [← hone.coeff i hi, lane_one, PowerSeries.coeff_one]
  split_ifs <;> simp

/-- **The certified long prefix of the partition generating function.** -/
theorem rep_pgfPrefixG {R d k n ku kb kc kN : ℕ} (hQ1 : 1 ≤ Q) (hQ : Q ≤ 2 ^ 21)
    (hk : ku + kb + kN < 64) (hno : 2 ^ 22 + Q * 2 ^ kc ≤ x) (hN0 : 0 < N) (hN : N ≤ 2 ^ kN)
    (hn : k * 2 ^ d ≤ 2 ^ 20) (hJ : N ≤ pentLow (k * 2 ^ d)) {B : ℕ}
    (h : pgfPrefixG Q R N d k n ku kb kc = some B) : Rep N kb B (rd Q partitionGF) := by
  simp only [pgfPrefixG] at h
  split_ifs at h with hok
  obtain rfl := Option.some.inj h
  exact Rep.inv_of_okG hk hno hN0 (rep_pentFast hQ1 hQ hn hJ)
    (by rw [← map_mul, BoylanWebb.qfac_mul_pgf, map_one]) hN hok

theorem coeff_pgfG {R d k n ku kb kc kN : ℕ} (hQ1 : 1 ≤ Q) (hQ : Q ≤ 2 ^ 21)
    (hk : ku + kb + kN < 64) (hno : 2 ^ 22 + Q * 2 ^ kc ≤ x) (hN0 : 0 < N) (hN : N ≤ 2 ^ kN)
    (hn : k * 2 ^ d ≤ 2 ^ 20) (hJ : N ≤ pentLow (k * 2 ^ d)) {B : ℕ}
    (h : pgfPrefixG Q R N d k n ku kb kc = some B) (i : ℕ) (hi : i < N) :
    ((PowerSeries.coeff i partitionGF : ℤ) : ZMod Q) = (lane B i : ZMod Q) := by
  rw [(rep_pgfPrefixG hQ1 hQ hk hno hN0 hN hn hJ h).coeff i hi, rd, PowerSeries.coeff_map]
  rfl

end

end RamanujanTau.FiniteArithmetic.PartitionPrefix
