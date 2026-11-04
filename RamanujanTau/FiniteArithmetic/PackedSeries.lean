import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.LinearCombination

/-! # Packed power-series prefixes for kernel evaluation

A prefix of a power series over `ZMod Q` is stored in one natural number, one
coefficient in each base-`2^64` lane. The kernel multiplies such numbers with
GMP, so a 61,308-term product costs one kernel step rather than billions.

Reduction is certified rather than verified: an untrusted computation supplies
`a'` and `c`, and Lean checks `a = a' + Q * c` together with lane bounds. No
statement here depends on how `a'` and `c` were found. -/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.Packed

open Finset

/-- The lane base. -/
abbrev x : ℕ := 2 ^ 64

/-- The `i`-th base-`2^64` digit. -/
def lane (a i : ℕ) : ℕ := a / x ^ i % x

lemma x_pos : 0 < x := by norm_num [x]

lemma lane_lt (a i : ℕ) : lane a i < x := Nat.mod_lt _ x_pos

lemma lane_mod (a m i : ℕ) (hi : i < m) : lane (a % x ^ m) i = lane a i := by
  have hx : 0 < x ^ i := pow_pos x_pos i
  obtain ⟨R, hR⟩ : ∃ R, x ^ m = x ^ i * (x * R) :=
    ⟨x ^ (m - i - 1), by rw [← mul_assoc, ← pow_succ, ← pow_add]; congr 1; omega⟩
  unfold lane
  have hk := Nat.mod_add_div a (x ^ m)
  generalize a % x ^ m = r at hk ⊢
  generalize a / x ^ m = k at hk
  subst hk
  rw [hR, show x ^ i * (x * R) * k = x ^ i * (x * (R * k)) by ring,
    Nat.add_mul_div_left _ _ hx, Nat.add_mul_mod_self_left]

/-- `c 0 + c 1 x + ... + c (n-1) x^(n-1)`. -/
def pack (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => pack c n + c n * x ^ n

lemma pack_lt (c : ℕ → ℕ) (hc : ∀ i, c i < x) (n : ℕ) : pack c n < x ^ n := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    have h : (c n + 1) * x ^ n ≤ x * x ^ n := Nat.mul_le_mul_right _ (hc n)
    rw [pack, pow_succ']
    nlinarith

lemma pack_lane (a n : ℕ) : pack (lane a) n = a % x ^ n := by
  induction n with
  | zero => simp [pack, Nat.mod_one]
  | succ n ih =>
    rw [pack, ih, pow_succ, lane, Nat.mod_mul]
    ring

lemma eq_pack_lane {a n : ℕ} (h : a < x ^ n) : a = pack (lane a) n := by
  rw [pack_lane, Nat.mod_eq_of_lt h]

lemma pack_congr {c d : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, c i = d i) : pack c n = pack d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pack, pack, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- Digits of a packed number are its coefficients. -/
lemma lane_pack (c : ℕ → ℕ) (hc : ∀ i, c i < x) (n i : ℕ) (hi : i < n) :
    lane (pack c n) i = c i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [lane, pack]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
    · have hdvd : x ^ (i + 1) ∣ c n * x ^ n :=
        Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _
      obtain ⟨w, hw⟩ := hdvd
      have hx : 0 < x ^ i := pow_pos x_pos _
      have : (pack c n + c n * x ^ n) / x ^ i = pack c n / x ^ i + w * x := by
        rw [hw, pow_succ]
        rw [show x ^ i * x * w = x ^ i * (w * x) by ring, Nat.add_mul_div_left _ _ hx]
      rw [this, Nat.add_mul_mod_self_right]
      exact ih i h
    · have hp := pack_lt c hc i
      have hx : 0 < x ^ i := pow_pos x_pos _
      rw [Nat.add_mul_div_right _ _ hx, Nat.div_eq_of_lt hp, zero_add]
      exact Nat.mod_eq_of_lt (hc i)

/-- Polynomial with the given low coefficients. -/
noncomputable def poly (c : ℕ → ℕ) (n : ℕ) : Polynomial ℕ :=
  ∑ i ∈ range n, Polynomial.monomial i (c i)

lemma eval_poly (c : ℕ → ℕ) (n : ℕ) : (poly c n).eval x = pack c n := by
  induction n with
  | zero => simp [poly, pack]
  | succ n ih =>
    have : poly c (n + 1) = poly c n + Polynomial.monomial n (c n) := by
      simp [poly, sum_range_succ]
    rw [this, Polynomial.eval_add, ih, Polynomial.eval_monomial, pack]

lemma coeff_poly (c : ℕ → ℕ) (n i : ℕ) :
    (poly c n).coeff i = if i < n then c i else 0 := by
  simp only [poly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [sum_ite_eq' (range n) i]
  simp

lemma pack_add (c d : ℕ → ℕ) (n : ℕ) : pack (c + d) n = pack c n + pack d n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pack, ih, Pi.add_apply]; ring

lemma pack_monomial (i b N : ℕ) :
    pack (Polynomial.monomial i b).coeff N = if i < N then b * x ^ i else 0 := by
  induction N with
  | zero => simp [pack]
  | succ N ih =>
    rw [pack, ih, Polynomial.coeff_monomial]
    by_cases h : i = N
    · subst h; simp
    · have h' : i < N + 1 ↔ i < N := by omega
      simp [h, h']

/-- Low coefficients of a polynomial determine its value modulo `x^N`. -/
lemma eval_mod_of_low (P : Polynomial ℕ) (N : ℕ) :
    P.eval x % x ^ N = pack P.coeff N % x ^ N := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    have hc : (p + q).coeff = p.coeff + q.coeff := by
      funext i; simp
    rw [Polynomial.eval_add, hc, pack_add, Nat.add_mod, hp, hq, ← Nat.add_mod]
  | monomial i b =>
    rw [pack_monomial, Polynomial.eval_monomial]
    split_ifs with h
    · rfl
    · have hd : x ^ N ∣ b * x ^ i := Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _
      rw [Nat.mod_eq_zero_of_dvd hd, Nat.zero_mod]

/-- Coefficient `k` of a product, as a sum over the antidiagonal. -/
def conv (c d : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ p ∈ antidiagonal k, c p.1 * d p.2

lemma conv_lt {c d : ℕ → ℕ} {B C : ℕ} (hc : ∀ i, c i < B) (hd : ∀ i, d i < C) {k M : ℕ}
    (hk : k + 1 ≤ M) : conv c d k ≤ M * (B * C) := by
  calc conv c d k ≤ ∑ _p ∈ antidiagonal k, B * C :=
        sum_le_sum fun p _ => Nat.mul_le_mul (hc _).le (hd _).le
    _ = (k + 1) * (B * C) := by simp
    _ ≤ M * (B * C) := Nat.mul_le_mul_right _ hk

/-- All lanes are below `2^k`, and there are at most `N` of them. -/
structure Small (N k a : ℕ) : Prop where
  lt : a < x ^ N
  lane_lt : ∀ i, lane a i < 2 ^ k

/-- `a` packs a prefix of `f` through `q^(N-1)`, with lanes below `2^k`. -/
structure Rep {Q : ℕ} (N k a : ℕ) (f : PowerSeries (ZMod Q)) : Prop extends Small N k a where
  coeff : ∀ i < N, (lane a i : ZMod Q) = PowerSeries.coeff i f

variable {Q : ℕ}

/-- Truncated product. The lane bound uses only `N ≤ 2^kN`. -/
theorem Small.mul_spec {N ka kb kN a b : ℕ} (ha : Small N ka a) (hb : Small N kb b)
    (hN : N ≤ 2 ^ kN) (hk : ka + kb + kN < 64) :
    (a * b) % x ^ N = pack (conv (lane a) (lane b)) N ∧
      ∀ i < N, conv (lane a) (lane b) i ≤ 2 ^ (ka + kb + kN) := by
  have hbound : ∀ i < N, conv (lane a) (lane b) i ≤ 2 ^ (ka + kb + kN) := fun i hi => by
    have := conv_lt ha.lane_lt hb.lane_lt (k := i) (M := 2 ^ kN) (by omega)
    calc _ ≤ 2 ^ kN * (2 ^ ka * 2 ^ kb) := this
      _ = _ := by rw [pow_add, pow_add]; ring
  refine ⟨?_, hbound⟩
  let c := lane a
  let d := lane b
  have hea : a = (poly c N).eval x := by rw [eval_poly]; exact eq_pack_lane ha.lt
  have heb : b = (poly d N).eval x := by rw [eval_poly]; exact eq_pack_lane hb.lt
  have hprod : a * b = (poly c N * poly d N).eval x := by
    rw [Polynomial.eval_mul, ← hea, ← heb]
  have hco : ∀ i < N, (poly c N * poly d N).coeff i = conv c d i := by
    intro i hi
    rw [Polynomial.coeff_mul, conv]
    refine sum_congr rfl fun p hp => ?_
    have hsum := mem_antidiagonal.mp hp
    rw [coeff_poly, coeff_poly, if_pos (by omega), if_pos (by omega)]
  -- Replace the conv coefficients by a version bounded below `x` everywhere.
  let t : ℕ → ℕ := fun i => if i < N then conv c d i else 0
  have ht : ∀ i, t i < x := by
    intro i
    dsimp only [t]
    split_ifs with hi
    · exact lt_of_le_of_lt (hbound i hi) (Nat.pow_lt_pow_right (by norm_num) hk)
    · exact x_pos
  have hpk : pack (conv c d) N = pack t N :=
    pack_congr fun i hi => by simp [t, hi]
  rw [hprod, eval_mod_of_low]
  have h1 : pack (poly c N * poly d N).coeff N = pack t N :=
    pack_congr fun i hi => by simp [t, hi, hco i hi]
  rw [h1, Nat.mod_eq_of_lt (pack_lt t ht N), ← hpk]

/-- Multiplication of represented prefixes. -/
theorem Rep.mul {N ka kb kN a b : ℕ} {f g : PowerSeries (ZMod Q)}
    (ha : Rep N ka a f) (hb : Rep N kb b g) (hN : N ≤ 2 ^ kN) (hk : ka + kb + kN < 64) :
    Rep N (ka + kb + kN + 1) ((a * b) % x ^ N) (f * g) := by
  obtain ⟨hp, hbd⟩ := Small.mul_spec ha.toSmall hb.toSmall hN hk
  have hlt64 : (2 : ℕ) ^ (ka + kb + kN) < x := Nat.pow_lt_pow_right (by norm_num) hk
  let t : ℕ → ℕ := fun i => if i < N then conv (lane a) (lane b) i else 0
  have ht : ∀ i, t i < x := fun i => by
    dsimp only [t]
    split_ifs with hi
    · exact lt_of_le_of_lt (hbd i hi) hlt64
    · exact x_pos
  have hpt : pack (conv (lane a) (lane b)) N = pack t N :=
    pack_congr fun i hi => by simp [t, hi]
  have hlane : ∀ i < N, lane ((a * b) % x ^ N) i = conv (lane a) (lane b) i := fun i hi => by
    rw [hp, hpt, lane_pack t ht N i hi]
    simp [t, hi]
  refine ⟨⟨Nat.mod_lt _ (pow_pos x_pos _), fun i => ?_⟩, fun i hi => ?_⟩
  · by_cases hi : i < N
    · rw [hlane i hi]
      calc _ ≤ 2 ^ (ka + kb + kN) := hbd i hi
        _ < _ := Nat.pow_lt_pow_right (by norm_num) (by omega)
    · have hlt : (a * b) % x ^ N < x ^ i :=
        lt_of_lt_of_le (Nat.mod_lt _ (pow_pos x_pos _))
          (Nat.pow_le_pow_right x_pos (by omega))
      rw [lane, Nat.div_eq_of_lt hlt, Nat.zero_mod]
      positivity
  · rw [hlane i hi, PowerSeries.coeff_mul, conv, Nat.cast_sum]
    refine sum_congr rfl fun p hp => ?_
    have hsum := mem_antidiagonal.mp hp
    rw [Nat.cast_mul, ha.coeff _ (by omega), hb.coeff _ (by omega)]

/-- Certified reduction: lanes of `a` and of `a' + Q*c` agree when neither overflows. -/
theorem Rep.reduce {N k k' kc a a' c : ℕ} {f : PowerSeries (ZMod Q)} (ha : Rep N k a f)
    (he : a = a' + Q * c) (ha' : Small N k' a') (hc : Small N kc c)
    (hno : 2 ^ k' + Q * 2 ^ kc ≤ x) : Rep N k' a' f := by
  refine ⟨ha', fun i hi => ?_⟩
  let t : ℕ → ℕ := fun i => lane a' i + Q * lane c i
  have ht : ∀ i, t i < x := fun i => by
    have h1 := ha'.lane_lt i
    have h2 := hc.lane_lt i
    have h3 : Q * lane c i ≤ Q * 2 ^ kc := Nat.mul_le_mul_left _ h2.le
    dsimp only [t]
    omega
  have hpk : pack t N = a := by
    have add : ∀ n, pack t n = pack (lane a') n + Q * pack (lane c) n := by
      intro n
      induction n with
      | zero => simp [pack]
      | succ n ih => simp only [pack, ih, t]; ring
    rw [add, ← eq_pack_lane ha'.lt, ← eq_pack_lane hc.lt, he]
  have hl : lane a i = t i := by
    conv_lhs => rw [← hpk]
    exact lane_pack t ht N i hi
  rw [← ha.coeff i hi, hl]
  simp [t]

/-! ### One bitwise check bounds every lane -/

lemma testBit_lane (a i j : ℕ) (hj : j < 64) :
    (lane a i).testBit j = a.testBit (64 * i + j) := by
  have hx : x ^ i = 2 ^ (64 * i) := by rw [x, ← pow_mul]
  rw [lane, hx, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hj, add_comm]

/-- The mask with the bits of `m` in each of `n` lanes. -/
def mask (m n : ℕ) : ℕ := pack (fun _ => m) n

/-- The fast closed form evaluated by the kernel. -/
lemma mask_eq (m n : ℕ) : mask m n = (x ^ n - 1) / (x - 1) * m := by
  have hgeom : ∀ n, pack (fun _ => 1) n * (x - 1) = x ^ n - 1 := by
    intro n
    induction n with
    | zero => simp [pack]
    | succ n ih =>
      have h1 : 1 ≤ x ^ n := Nat.one_le_pow _ _ x_pos
      have h2 : pack (fun _ => 1) (n + 1) = pack (fun _ => 1) n + x ^ n := by simp [pack]
      rw [h2, add_mul, ih, pow_succ]
      have h3 : x ^ n * (x - 1) = x ^ n * x - x ^ n := by
        rw [Nat.mul_sub, mul_one]
      rw [h3]
      have h4 : x ^ n ≤ x ^ n * x := Nat.le_mul_of_pos_right _ x_pos
      omega
  have hmask : ∀ n, mask m n = pack (fun _ => 1) n * m := by
    intro n
    induction n with
    | zero => simp [mask, pack]
    | succ n ih =>
      have : mask m (n + 1) = mask m n + m * x ^ n := rfl
      rw [this, ih]
      simp only [pack]
      ring
  rw [hmask, ← hgeom n, Nat.mul_div_cancel _ (by norm_num [x])]

/-- The high bits, `k` through `63`, of a lane. -/
abbrev highBits (k : ℕ) : ℕ := 2 ^ 64 - 2 ^ k

lemma testBit_highBits {k j : ℕ} (hk : k ≤ j) (hj : j < 64) : (highBits k).testBit j = true := by
  have hk64 : k ≤ 64 := by omega
  have h : highBits k = (2 ^ (64 - k) - 1) * 2 ^ k := by
    rw [Nat.sub_mul, one_mul, ← pow_add, Nat.sub_add_cancel hk64]
  rw [h, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- If the high bits of all lanes are clear then every lane is below `2^k`. -/
theorem small_of_land {N k a : ℕ} (hlt : a < x ^ N)
    (h : a &&& mask (highBits k) N = 0) : Small N k a := by
  refine ⟨hlt, fun i => ?_⟩
  by_cases hi : i < N
  · apply Nat.lt_pow_two_of_testBit
    intro j hj
    by_cases hj64 : j < 64
    · have hm : highBits k < x := by
        have : 0 < 2 ^ k := by positivity
        simp only [highBits, x]
        omega
      have hmaskbit : (mask (highBits k) N).testBit (64 * i + j) = true := by
        rw [← testBit_lane _ _ _ hj64, mask, lane_pack _ (fun _ => hm) N i hi]
        exact testBit_highBits hj hj64
      have hzero := congrArg (fun z => Nat.testBit z (64 * i + j)) h
      simp only [Nat.testBit_and, hmaskbit, Bool.and_true, Nat.zero_testBit] at hzero
      rw [testBit_lane _ _ _ hj64, hzero]
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (lane_lt a i)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · have hle : a < x ^ i := lt_of_lt_of_le hlt (Nat.pow_le_pow_right x_pos (by omega))
    rw [lane, Nat.div_eq_of_lt hle, Nat.zero_mod]
    positivity

/-! ### Further operations on represented prefixes -/

lemma Small.mono {N k k' a : ℕ} (h : Small N k a) (hk : k ≤ k') : Small N k' a :=
  ⟨h.lt, fun i => lt_of_lt_of_le (h.lane_lt i) (Nat.pow_le_pow_right (by norm_num) hk)⟩

theorem Rep.mono {N k k' a : ℕ} {f : PowerSeries (ZMod Q)} (h : Rep N k a f) (hk : k ≤ k') :
    Rep N k' a f := ⟨h.toSmall.mono hk, h.coeff⟩

lemma lane_add_of_small {N k a b : ℕ} (ha : Small N k a) (hb : Small N k b) (hk : k < 64) :
    a + b < x ^ N ∧ ∀ i, lane (a + b) i = lane a i + lane b i := by
  have hk2 : (2 : ℕ) ^ (k + 1) ≤ x := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  let t : ℕ → ℕ := fun i => lane a i + lane b i
  have ht : ∀ i, t i < x := fun i => by
    have := ha.lane_lt i
    have := hb.lane_lt i
    dsimp only [t]
    omega
  have hpk : pack t N = a + b := by
    have add : pack t N = pack (lane a) N + pack (lane b) N := pack_add _ _ N
    rw [add, ← eq_pack_lane ha.lt, ← eq_pack_lane hb.lt]
  have hlt : a + b < x ^ N := hpk ▸ pack_lt t ht N
  refine ⟨hlt, fun i => ?_⟩
  by_cases hi : i < N
  · rw [← hpk, lane_pack t ht N i hi]
  · have hA : a < x ^ i := lt_of_lt_of_le ha.lt (Nat.pow_le_pow_right x_pos (by omega))
    have hB : b < x ^ i := lt_of_lt_of_le hb.lt (Nat.pow_le_pow_right x_pos (by omega))
    have hS : a + b < x ^ i := lt_of_lt_of_le hlt (Nat.pow_le_pow_right x_pos (by omega))
    simp [lane, Nat.div_eq_of_lt hA, Nat.div_eq_of_lt hB, Nat.div_eq_of_lt hS]

theorem Rep.add {N k a b : ℕ} {f g : PowerSeries (ZMod Q)} (ha : Rep N k a f) (hb : Rep N k b g)
    (hk : k < 64) : Rep N (k + 1) (a + b) (f + g) := by
  obtain ⟨hlt, hl⟩ := lane_add_of_small ha.toSmall hb.toSmall hk
  refine ⟨⟨hlt, fun i => ?_⟩, fun i hi => ?_⟩
  · have := ha.lane_lt i
    have := hb.lane_lt i
    rw [hl, pow_succ]
    omega
  · rw [hl, Nat.cast_add, ha.coeff i hi, hb.coeff i hi, map_add]

/-- Agreement of low coefficients transfers a representation. -/
theorem Rep.congr {N k a : ℕ} {f g : PowerSeries (ZMod Q)} (h : Rep N k a f)
    (hc : ∀ i < N, PowerSeries.coeff i f = PowerSeries.coeff i g) : Rep N k a g :=
  ⟨h.toSmall, fun i hi => (h.coeff i hi).trans (hc i hi)⟩

/-- Read one coefficient of a represented series. -/
theorem Rep.coeff_eq {N k a i : ℕ} {f : PowerSeries (ZMod Q)} (h : Rep N k a f) (hi : i < N) :
    PowerSeries.coeff i f = ((a >>> (64 * i)) % 2 ^ 64 : ℕ) := by
  rw [← h.coeff i hi, lane, Nat.shiftRight_eq_div_pow, x, ← pow_mul]

/-! ### The certified operations evaluated by the kernel -/

/-- Closed form of `mask`, which the kernel evaluates in one step. -/
def fastMask (m N : ℕ) : ℕ := (x ^ N - 1) / (x - 1) * m

lemma fastMask_eq (m N : ℕ) : fastMask m N = mask m N := (mask_eq m N).symm

/-- Untrusted lane-parallel quotient estimate; `mu` approximates `2^40 / Q`. -/
def quotEst (N mu a : ℕ) : ℕ :=
  ((((a >>> 18) &&& fastMask (2 ^ 42 - 1) N) * mu) >>> 22) &&& fastMask (2 ^ 42 - 1) N

/-- The output of a reduction: the remainder and the accumulated quotient. -/
def reduceRaw (Q N mu a : ℕ) : ℕ × ℕ :=
  let c1 := quotEst N mu a
  let a1 := a - Q * c1
  let c2 := quotEst N mu a1
  let a2 := a1 - Q * c2
  let c3 := quotEst N mu a2
  (a2 - Q * c3, c1 + c2 + c3)

/-- The check that makes a reduction trustworthy. -/
def reduceOk (Q N a r c : ℕ) : Bool :=
  a == r + Q * c && decide (r < x ^ N) && decide (c < x ^ N) &&
    (r &&& fastMask (highBits 22) N) == 0 && (c &&& fastMask (highBits 42) N) == 0

/-- Reduce all lanes, or fail. -/
def reduceR (Q N mu a : ℕ) : Option ℕ :=
  let rc := reduceRaw Q N mu a
  if reduceOk Q N a rc.1 rc.2 then some rc.1 else none

/-- Multiply, truncate, and reduce. -/
def mulR (Q N mu a b : ℕ) : Option ℕ := reduceR Q N mu ((a * b) % x ^ N)

theorem Rep.reduceR {N k mu a r : ℕ} {f : PowerSeries (ZMod Q)} (hQ : Q ≤ 2 ^ 21)
    (ha : Rep N k a f) (h : Packed.reduceR Q N mu a = some r) : Rep N 22 r f := by
  simp only [Packed.reduceR] at h
  split_ifs at h with hok
  obtain rfl : (reduceRaw Q N mu a).1 = r := Option.some.inj h
  simp only [reduceOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hok
  rw [fastMask_eq] at h4 h5
  have hsr := small_of_land h2 h4
  have hsc := small_of_land h3 h5
  refine ha.reduce h1 hsr hsc ?_
  have : Q * 2 ^ 42 ≤ 2 ^ 21 * 2 ^ 42 := Nat.mul_le_mul_right _ hQ
  norm_num [x] at this ⊢
  omega

theorem Rep.mulR {N kN mu a b r : ℕ} {f g : PowerSeries (ZMod Q)} (hQ : Q ≤ 2 ^ 21)
    (ha : Rep N 22 a f) (hb : Rep N 22 b g) (hN : N ≤ 2 ^ kN) (hk : kN < 20)
    (h : Packed.mulR Q N mu a b = some r) : Rep N 22 r (f * g) :=
  Rep.reduceR hQ (ha.mul hb hN (by omega)) h

/-- Addition followed by reduction. -/
def addR (Q N mu a b : ℕ) : Option ℕ := Packed.reduceR Q N mu (a + b)

theorem Rep.addR {N mu a b r : ℕ} {f g : PowerSeries (ZMod Q)} (hQ : Q ≤ 2 ^ 21)
    (ha : Rep N 22 a f) (hb : Rep N 22 b g) (h : Packed.addR Q N mu a b = some r) :
    Rep N 22 r (f + g) :=
  Rep.reduceR hQ (ha.add hb (by norm_num)) h

/-- A constant series is its own one-lane prefix. -/
theorem rep_C {N k c : ℕ} (hN : 0 < N) (hc : c < 2 ^ k) (hk : k ≤ 64) :
    Rep N k c (PowerSeries.C (c : ZMod Q)) := by
  have hcx : c < x := lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hk)
  have hlt : c < x ^ N :=
    lt_of_lt_of_le hcx (by simpa using Nat.pow_le_pow_right x_pos (Nat.succ_le_of_lt hN))
  have hl : ∀ i, lane c i = if i = 0 then c else 0 := by
    intro i
    rcases i with _ | i
    · simp [lane, Nat.mod_eq_of_lt hcx]
    · have : c < x ^ (i + 1) :=
        lt_of_lt_of_le hcx (by simpa using Nat.pow_le_pow_right x_pos (Nat.succ_le_succ (Nat.zero_le i)))
      simp [lane, Nat.div_eq_of_lt this]
  refine ⟨⟨hlt, fun i => ?_⟩, fun i _ => ?_⟩
  · rw [hl]
    split_ifs
    · exact hc
    · positivity
  · rw [hl, PowerSeries.coeff_C]
    split_ifs <;> simp

/-- Multiplication by `q^d`. -/
def shiftR (N d a : ℕ) : ℕ := (a <<< (64 * d)) % x ^ N

theorem Rep.shiftR {N k d a : ℕ} {f : PowerSeries (ZMod Q)} (ha : Rep N k a f) (hk : k ≤ 64) :
    Rep N k (Packed.shiftR N d a) (PowerSeries.X ^ d * f) := by
  have hsh : a <<< (64 * d) = a * x ^ d := by
    rw [Nat.shiftLeft_eq, x, ← pow_mul]
  have hlane : ∀ i < N, lane (Packed.shiftR N d a) i = if d ≤ i then lane a (i - d) else 0 := by
    intro i hi
    have hx : 0 < x ^ i := pow_pos x_pos _
    have hred : lane (Packed.shiftR N d a) i = lane (a * x ^ d) i := by
      rw [Packed.shiftR, hsh, lane_mod _ _ _ hi]
    rw [hred]
    split_ifs with hd
    · have hi' : x ^ i = x ^ (i - d) * x ^ d := by rw [← pow_add]; congr 1; omega
      rw [lane, lane, hi', Nat.mul_div_mul_right _ _ (pow_pos x_pos _)]
    · have hd' : x ^ d = x ^ i * x * x ^ (d - i - 1) := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      have : a * x ^ d / x ^ i = x * (x ^ (d - i - 1) * a) := by
        rw [hd', show a * (x ^ i * x * x ^ (d - i - 1)) = x ^ i * (x * (x ^ (d - i - 1) * a)) by ring,
          Nat.mul_div_cancel_left _ hx]
      rw [lane, this, Nat.mul_mod_right]
  refine ⟨⟨Nat.mod_lt _ (pow_pos x_pos _), fun i => ?_⟩, fun i hi => ?_⟩
  · by_cases hi : i < N
    · rw [hlane i hi]
      split_ifs
      · exact ha.lane_lt _
      · positivity
    · have hle : Packed.shiftR N d a < x ^ i :=
        lt_of_lt_of_le (Nat.mod_lt _ (pow_pos x_pos _)) (Nat.pow_le_pow_right x_pos (by omega))
      rw [lane, Nat.div_eq_of_lt hle, Nat.zero_mod]
      positivity
  · rw [hlane i hi, PowerSeries.coeff_X_pow_mul']
    split_ifs with hd
    · exact ha.coeff _ (by omega)
    · simp

/-! ### A function applied to each lane, by divide and conquer -/

/-- `h i (lane a i)` in lane `i`, for `2^l` lanes starting at index `s`. -/
def laneMap (h : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, s, a => h s (a % x)
  | l + 1, s, a =>
    laneMap h l s (a % x ^ (2 ^ l)) +
      laneMap h l (s + 2 ^ l) (a >>> (64 * 2 ^ l)) <<< (64 * 2 ^ l)

lemma pack_split (c : ℕ → ℕ) (m n : ℕ) :
    pack c (m + n) = pack c m + pack (fun i => c (m + i)) n * x ^ m := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    rw [← add_assoc, pack, ih, pack, pow_add]
    ring

lemma lane_shift (a m i : ℕ) : lane (a >>> (64 * m)) i = lane a (m + i) := by
  rw [lane, lane, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, pow_add]
  congr 3
  rw [x, ← pow_mul]

/-- The specification of `laneMap`. -/
theorem laneMap_eq (h : ℕ → ℕ → ℕ) (l s a : ℕ) :
    laneMap h l s a = pack (fun i => h (s + i) (lane a i)) (2 ^ l) := by
  induction l generalizing s a with
  | zero =>
    simp [laneMap, pack, lane]
  | succ l ih =>
    have hsh : ∀ b : ℕ, b <<< (64 * 2 ^ l) = b * x ^ 2 ^ l := fun b => by
      rw [Nat.shiftLeft_eq, x, ← pow_mul]
    have e1 : pack (fun i => h (s + i) (lane (a % x ^ 2 ^ l) i)) (2 ^ l) =
        pack (fun i => h (s + i) (lane a i)) (2 ^ l) :=
      pack_congr fun i hi => by rw [lane_mod _ _ _ hi]
    have e2 : pack (fun i => h (s + 2 ^ l + i) (lane (a >>> (64 * 2 ^ l)) i)) (2 ^ l) =
        pack (fun i => h (s + (2 ^ l + i)) (lane a (2 ^ l + i))) (2 ^ l) :=
      pack_congr fun i _ => by rw [lane_shift, add_assoc]
    rw [laneMap, ih, ih, pow_succ, mul_two, pack_split, hsh, e1, e2]

/-- `laneMap` sends a represented series to its coefficientwise image. -/
theorem Rep.laneMap {N k l a kOut : ℕ} {f g : PowerSeries (ZMod Q)} (h : ℕ → ℕ → ℕ)
    (ha : Rep N k a f) (hN : N ≤ 2 ^ l) (hkOut : kOut ≤ 64)
    (hbound : ∀ i v, v < 2 ^ k → h i v < 2 ^ kOut)
    (hcoeff : ∀ i < N, ∀ v : ℕ, (v : ZMod Q) = PowerSeries.coeff i f →
      (h i v : ZMod Q) = PowerSeries.coeff i g) :
    Rep N kOut ((Packed.laneMap h l 0 a) % x ^ N) g := by
  let c : ℕ → ℕ := fun i => h i (lane a i)
  have hcx : ∀ i, c i < x := fun i =>
    lt_of_lt_of_le (hbound _ _ (ha.lane_lt i)) (Nat.pow_le_pow_right (by norm_num) hkOut)
  have hval : Packed.laneMap h l 0 a = pack c (2 ^ l) := by
    rw [laneMap_eq]
    exact pack_congr fun i _ => by simp [c]
  have hlane : ∀ i < N, lane (Packed.laneMap h l 0 a % x ^ N) i = c i := fun i hi => by
    rw [lane_mod _ _ _ hi, hval, lane_pack c hcx _ i (by omega)]
  refine ⟨⟨Nat.mod_lt _ (pow_pos x_pos _), fun i => ?_⟩, fun i hi => ?_⟩
  · by_cases hi : i < N
    · rw [hlane i hi]
      exact hbound _ _ (ha.lane_lt i)
    · have hle : Packed.laneMap h l 0 a % x ^ N < x ^ i :=
        lt_of_lt_of_le (Nat.mod_lt _ (pow_pos x_pos _)) (Nat.pow_le_pow_right x_pos (by omega))
      rw [lane, Nat.div_eq_of_lt hle, Nat.zero_mod]
      positivity
  · rw [hlane i hi]
    exact hcoeff i hi _ (ha.coeff i hi)

/-! ### Certified inverses -/

/-- The series whose coefficients are the lanes of `b`. -/
noncomputable def seriesOf (Q b : ℕ) : PowerSeries (ZMod Q) :=
  PowerSeries.mk fun i => (lane b i : ZMod Q)

theorem rep_seriesOf {N k b : ℕ} (hb : Small N k b) : Rep N k b (seriesOf Q b) :=
  ⟨hb, fun i _ => by simp [seriesOf]⟩

/-- If `u * g` agrees with `1` through `N` terms and `u * v = 1`, then `g` agrees with `v`. -/
theorem coeff_eq_of_mul_prefix {N : ℕ} {u g v : PowerSeries (ZMod Q)} (huv : u * v = 1)
    (h : ∀ i < N, PowerSeries.coeff i (u * g) = PowerSeries.coeff i (1 : PowerSeries (ZMod Q))) :
    ∀ i < N, PowerSeries.coeff i g = PowerSeries.coeff i v := by
  have hd : PowerSeries.X ^ N ∣ u * g - 1 :=
    PowerSeries.X_pow_dvd_iff.mpr fun i hi => by rw [map_sub, h i hi, sub_self]
  have hd2 : PowerSeries.X ^ N ∣ g - v := by
    have he : g - v = v * (u * g - 1) := by
      linear_combination (-g) * huv
    rw [he]
    exact Dvd.dvd.mul_left hd _
  intro i hi
  have := PowerSeries.X_pow_dvd_iff.mp hd2 i hi
  rwa [map_sub, sub_eq_zero] at this

/-- The packed prefix of the constant series `1`. -/
theorem lane_one (i : ℕ) : lane 1 i = if i = 0 then 1 else 0 := by
  rcases i with _ | i
  · simp [lane]
  · have h1 : 1 < x ^ (i + 1) := Nat.one_lt_pow (by omega) (by norm_num [x])
    simp [lane, Nat.div_eq_of_lt h1]

/-- The packed number `1` as a small prefix. -/
theorem small_one {N : ℕ} (hN : 0 < N) : Small N 22 1 := by
  refine ⟨Nat.one_lt_pow (by omega) (by norm_num [x]), fun i => ?_⟩
  rw [lane_one]
  split_ifs <;> norm_num

/-- `r` is congruent to `1` lanewise, with an explicit small quotient. -/
def isOneOk (Q N r : ℕ) : Bool :=
  let c := (r - 1) / Q
  r == 1 + Q * c && decide (c < x ^ N) && (c &&& fastMask (highBits 42) N) == 0

/-- A candidate inverse is certified by one product. -/
def invOk (Q N mu u b : ℕ) : Bool :=
  decide (b < x ^ N) && (b &&& fastMask (highBits 22) N) == 0 &&
    match mulR Q N mu u b with
    | some r => isOneOk Q N r
    | none => false

theorem Rep.inv_of_ok {N kN mu u b : ℕ} {f v : PowerSeries (ZMod Q)} (hQ : Q ≤ 2 ^ 21)
    (hN0 : 0 < N) (hu : Rep N 22 u f) (hfv : f * v = 1) (hN : N ≤ 2 ^ kN) (hk : kN < 20)
    (h : invOk Q N mu u b = true) : Rep N 22 b v := by
  simp only [invOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [fastMask_eq] at h2
  have hsb := small_of_land h1 h2
  have hb := rep_seriesOf (Q := Q) hsb
  cases hm : Packed.mulR Q N mu u b with
  | none => simp [hm] at h3
  | some r =>
    simp only [hm, isOneOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h3
    obtain ⟨⟨h4, h5⟩, h6⟩ := h3
    rw [fastMask_eq] at h6
    have hprod := Rep.mulR hQ hu hb hN hk hm
    have hone : Rep N 22 1 (f * seriesOf Q b) := hprod.reduce h4 (small_one hN0)
      (small_of_land h5 h6) (by
        have : Q * 2 ^ 42 ≤ 2 ^ 21 * 2 ^ 42 := Nat.mul_le_mul_right _ hQ
        norm_num [x] at this ⊢
        omega)
    refine hb.congr (coeff_eq_of_mul_prefix hfv fun i hi => ?_)
    rw [← hone.coeff i hi, lane_one, PowerSeries.coeff_one]
    split_ifs <;> simp

end RamanujanTau.FiniteArithmetic.Packed
