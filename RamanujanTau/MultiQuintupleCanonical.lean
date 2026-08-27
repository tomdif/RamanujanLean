/-
# The canonical infinite family of multi-quintuple vanishings

For an odd integer `p >= 5`, multiply every canonical specialization

  Q(q,q^p) Q(q^2,q^p) ... Q(q^((p-1)/2),q^p).

The five Pochhammer factors in these specializations exhaust all nonzero residue classes
modulo `p` and all odd residue classes modulo `2p`, with only diagonal factors left over.
Consequently the whole product is `phi(-q)` times a series supported on multiples of `p`.
This yields coefficient vanishings in every nonsquare residue class modulo `p` and, in
particular, in every quadratic nonresidue class when `p` is prime.

All identities are identities of formal power series over `Z`; no analytic convergence and
no `sorry` are used.
-/
import RamanujanTau.MultiQuintuplePochhammer
import RamanujanTau.MockTheta5RamanujanTheta

namespace Ramanujan.MultiQuintuple
open PowerSeries
open MockTheta5.JTP
open MockTheta5.Bailey

/-! ### Generic residue-class reassembly -/

/-- A finite product of all positive residue classes modulo `d`. -/
noncomputable def residueProductFinite (d N : ℕ) : PowerSeries ℤ :=
  ∏ a ∈ Finset.range d, pochhammerFinite (a + 1) d N

/-- The corresponding infinite residue-class product. -/
noncomputable def residueProductInf (d : ℕ) : PowerSeries ℤ :=
  ∏ a ∈ Finset.range d, pochhammerInf (a + 1) d

/-- A finite product of all odd residue classes modulo `2p`. -/
noncomputable def oddResidueProductFinite (p N : ℕ) : PowerSeries ℤ :=
  ∏ a ∈ Finset.range p, pochhammerFinite (2 * a + 1) (2 * p) N

/-- The corresponding infinite odd-residue product. -/
noncomputable def oddResidueProductInf (p : ℕ) : PowerSeries ℤ :=
  ∏ a ∈ Finset.range p, pochhammerInf (2 * a + 1) (2 * p)

/-- Residue classes `1,...,d` reassemble a finite Euler product. -/
lemma residueProductFinite_eq_qfac (d N : ℕ) :
    residueProductFinite d N = qfac (d * N) := by
  induction N with
  | zero => simp [residueProductFinite, pochhammerFinite, qfac]
  | succ N ih =>
      rw [residueProductFinite]
      simp_rw [pochhammerFinite_succ]
      rw [Finset.prod_mul_distrib]
      change residueProductFinite d N
          * (∏ a ∈ Finset.range d, (1 - X ^ (a + 1 + d * N))) = _
      rw [ih]
      simp only [qfac]
      rw [show d * (N + 1) = d * N + d by ring, Finset.prod_range_add]
      congr 1
      refine Finset.prod_congr rfl fun a _ => ?_
      congr 2
      ring

/-- Odd residue classes modulo `2p` reassemble a finite odd Euler product. -/
lemma oddResidueProductFinite_eq_oddFac (p N : ℕ) :
    oddResidueProductFinite p N = oddFac (p * N) := by
  induction N with
  | zero => simp [oddResidueProductFinite, pochhammerFinite, oddFac]
  | succ N ih =>
      rw [oddResidueProductFinite]
      simp_rw [pochhammerFinite_succ]
      rw [Finset.prod_mul_distrib]
      change oddResidueProductFinite p N
          * (∏ a ∈ Finset.range p, (1 - X ^ (2 * a + 1 + 2 * p * N))) = _
      rw [ih]
      simp only [oddFac]
      rw [show p * (N + 1) = p * N + p by ring, Finset.prod_range_add]
      congr 1
      refine Finset.prod_congr rfl fun a _ => ?_
      congr 2
      ring

/-- A finite product of stabilized Pochhammer series may be computed from one common,
sufficiently long finite truncation. -/
lemma coeff_finset_pochhammerInf {α : Type*} [DecidableEq α] {s : Finset α}
    {a d : α → ℕ} (ha : ∀ x ∈ s, 0 < a x) (hd : ∀ x ∈ s, 0 < d x)
    {k N : ℕ} (hN : k + 1 ≤ N) :
    coeff k (∏ x ∈ s, pochhammerInf (a x) (d x))
      = coeff k (∏ x ∈ s, pochhammerFinite (a x) (d x) N) := by
  induction s using Finset.induction_on generalizing k with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.prod_insert hx,
        PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun pair hpair => ?_
      have hpair_sum : pair.1 + pair.2 = k := Finset.mem_antidiagonal.mp hpair
      rw [coeff_pochhammerInf (ha x (by simp)) (hd x (by simp))
          (show pair.1 + 1 ≤ N by omega),
        ih (fun y hy => ha y (by simp [hy])) (fun y hy => hd y (by simp [hy]))
          (show pair.2 + 1 ≤ N by omega)]

/-- All positive residue classes modulo `d` reassemble `(q;q)_inf`. -/
lemma residueProductInf_eq_qfacInf (d : ℕ) (hd : 0 < d) :
    residueProductInf d = qfacInf := by
  ext k
  rw [residueProductInf,
    coeff_finset_pochhammerInf
      (fun a _ => by omega) (fun _ _ => hd) (le_refl (k + 1)),
    ← residueProductFinite, residueProductFinite_eq_qfac,
    coeff_qfacInf (show k + 1 ≤ d * (k + 1) by nlinarith)]

/-- All odd residue classes modulo `2p` reassemble `(q;q^2)_inf`. -/
lemma oddResidueProductInf_eq_oddPochInf (p : ℕ) (hp : 0 < p) :
    oddResidueProductInf p = oddPochInf := by
  ext k
  rw [oddResidueProductInf,
    coeff_finset_pochhammerInf
      (fun a _ => by omega) (fun _ _ => by omega) (le_refl (k + 1)),
    ← oddResidueProductFinite, oddResidueProductFinite_eq_oddFac,
    coeff_oddPochInf (show k + 1 ≤ p * (k + 1) by nlinarith)]

/-! ### The two canonical index reassemblies -/

/-- Reflection changes the descending upper half of the nonzero residues into ascending order. -/
private lemma upperResidues_reflect (p m d : ℕ) (hpm : p = 2 * m + 1) :
    (∏ i ∈ Finset.range m, pochhammerInf (p - (i + 1)) d)
      = ∏ j ∈ Finset.range m, pochhammerInf (m + 1 + j) d := by
  calc
    (∏ i ∈ Finset.range m, pochhammerInf (p - (i + 1)) d)
        = ∏ i ∈ Finset.range m, pochhammerInf (m + 1 + (m - 1 - i)) d := by
            refine Finset.prod_congr rfl fun i hi => ?_
            congr 2
            have hi' : i < m := Finset.mem_range.mp hi
            omega
    _ = ∏ j ∈ Finset.range m, pochhammerInf (m + 1 + j) d :=
      Finset.prod_range_reflect (fun j => pochhammerInf (m + 1 + j) d) m

/-- Reflection changes the descending lower odd residues into ascending order. -/
private lemma lowerOddResidues_reflect (p m d : ℕ) (hpm : p = 2 * m + 1) :
    (∏ i ∈ Finset.range m, pochhammerInf (p - 2 * (i + 1)) d)
      = ∏ j ∈ Finset.range m, pochhammerInf (2 * j + 1) d := by
  calc
    (∏ i ∈ Finset.range m, pochhammerInf (p - 2 * (i + 1)) d)
        = ∏ i ∈ Finset.range m, pochhammerInf (2 * (m - 1 - i) + 1) d := by
            refine Finset.prod_congr rfl fun i hi => ?_
            congr 2
            have hi' : i < m := Finset.mem_range.mp hi
            omega
    _ = ∏ j ∈ Finset.range m, pochhammerInf (2 * j + 1) d :=
      Finset.prod_range_reflect (fun j => pochhammerInf (2 * j + 1) d) m

/-- The `q^i`, `q^(p-i)`, and one diagonal factor from all canonical specializations
exhaust every positive residue class modulo `p`. -/
lemma canonicalResidues_reassembly (p m : ℕ) (hpm : p = 2 * m + 1) :
    (∏ i ∈ Finset.range m, pochhammerInf (i + 1) p)
      * (∏ i ∈ Finset.range m, pochhammerInf (p - (i + 1)) p)
      * pochhammerInf p p = qfacInf := by
  rw [upperResidues_reflect p m p hpm,
    ← residueProductInf_eq_qfacInf p (by omega), residueProductInf]
  subst p
  rw [show 2 * m + 1 = m + (m + 1) by omega, Finset.prod_range_add,
    Finset.prod_range_succ]
  simp only [add_assoc, add_comm, add_left_comm]
  ring

/-- The two base-`q^(2p)` factors from all canonical specializations, together with the
missing central class `(q^p;q^(2p))_inf`, exhaust all odd residue classes modulo `2p`. -/
lemma canonicalOddResidues_reassembly (p m : ℕ) (hpm : p = 2 * m + 1) :
    (∏ i ∈ Finset.range m, pochhammerInf (p + 2 * (i + 1)) (2 * p))
      * (∏ i ∈ Finset.range m, pochhammerInf (p - 2 * (i + 1)) (2 * p))
      * pochhammerInf p (2 * p) = oddPochInf := by
  rw [lowerOddResidues_reflect p m (2 * p) hpm,
    ← oddResidueProductInf_eq_oddPochInf p (by omega), oddResidueProductInf]
  subst p
  rw [show 2 * m + 1 = m + (m + 1) by omega, Finset.prod_range_add,
    Finset.prod_range_succ']
  simp only [add_assoc, add_comm, add_left_comm, mul_add, mul_one]
  ring_nf

/-! ### Splitting the diagonal residue class -/

private lemma diagonal_split_finite (p N : ℕ) :
    pochhammerFinite p (2 * p) N * pochhammerFinite (2 * p) (2 * p) N
      = pochhammerFinite p p (2 * N) := by
  induction N with
  | zero => simp [pochhammerFinite]
  | succ N ih =>
      rw [pochhammerFinite_succ, pochhammerFinite_succ,
        show 2 * (N + 1) = (2 * N + 1) + 1 by ring,
        pochhammerFinite_succ, pochhammerFinite_succ, ← ih]
      ring

/-- Odd and even multiples of `p` reassemble all multiples of `p`. -/
lemma diagonal_split (p : ℕ) (hp : 0 < p) :
    pochhammerInf p (2 * p) * pochhammerInf (2 * p) (2 * p)
      = pochhammerInf p p := by
  rw [show pochhammerInf p (2 * p) * pochhammerInf (2 * p) (2 * p)
      = pochhammerProductInf [(p, 2 * p), (2 * p, 2 * p)] from by
        simp [pochhammerProductInf]]
  ext k
  have hvalid : ∀ factor ∈ ([(p, 2 * p), (2 * p, 2 * p)] : List (ℕ × ℕ)),
      0 < factor.1 ∧ 0 < factor.2 := by
    intro factor hfactor
    simp at hfactor
    rcases hfactor with rfl | rfl <;> constructor <;> omega
  rw [coeff_pochhammerProductInf hvalid (le_refl (k + 1)),
    show pochhammerProductFinite [(p, 2 * p), (2 * p, 2 * p)] (k + 1)
      = pochhammerFinite p (2 * p) (k + 1)
          * pochhammerFinite (2 * p) (2 * p) (k + 1) from by
        simp [pochhammerProductFinite],
    diagonal_split_finite,
    ← coeff_pochhammerInf hp hp (show k + 1 ≤ 2 * (k + 1) by omega)]

/-! ### Canonical product factorization -/

/-- Product of all canonical one-variable specializations `Q(q^i,q^p)`. -/
noncomputable def allCanonicalQuintupleProduct (p : ℕ) : PowerSeries ℤ :=
  ∏ i ∈ Finset.range ((p - 1) / 2), quintupleSpecialized p (i + 1)

/-- The diagonal tail left after the canonical factors reassemble `phi(-q)`. -/
noncomputable def allCanonicalTail (p : ℕ) : PowerSeries ℤ :=
  pochhammerInf p p ^ (((p - 1) / 2) - 2) * pochhammerInf (2 * p) (2 * p)

/-- Mechanical collection of the five factors from every specialized quintuple product. -/
private lemma collect_quintupleSpecialized (p m : ℕ) :
    (∏ i ∈ Finset.range m, quintupleSpecialized p (i + 1))
      = (∏ i ∈ Finset.range m, pochhammerInf (i + 1) p)
        * (∏ i ∈ Finset.range m, pochhammerInf (p - (i + 1)) p)
        * pochhammerInf p p ^ m
        * (∏ i ∈ Finset.range m, pochhammerInf (p + 2 * (i + 1)) (2 * p))
        * (∏ i ∈ Finset.range m, pochhammerInf (p - 2 * (i + 1)) (2 * p)) := by
  simp only [quintupleSpecialized, pochhammerProductInf, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  simp_rw [Finset.prod_mul_distrib]
  rw [Finset.prod_const, Finset.card_range]
  ring

/-- **Canonical multi-quintuple factorization.** For every odd `p = 2m+1` with `m >= 2`,
the product of all canonical specializations is `phi(-q)` times a diagonal tail. -/
theorem allCanonicalQuintupleProduct_factorization (p m : ℕ)
    (hm : 2 ≤ m) (hpm : p = 2 * m + 1) :
    allCanonicalQuintupleProduct p = phiNeg * allCanonicalTail p := by
  have hp : 0 < p := by omega
  have hmdiv : (p - 1) / 2 = m := by omega
  apply mul_right_cancel₀
    (isUnit_pochhammerInf hp (show 0 < 2 * p by omega)).ne_zero
  rw [allCanonicalQuintupleProduct, hmdiv, collect_quintupleSpecialized,
    allCanonicalTail, hmdiv]
  let lower := ∏ i ∈ Finset.range m, pochhammerInf (i + 1) p
  let upper := ∏ i ∈ Finset.range m, pochhammerInf (p - (i + 1)) p
  let diagonal := pochhammerInf p p
  let oddUpper := ∏ i ∈ Finset.range m, pochhammerInf (p + 2 * (i + 1)) (2 * p)
  let oddLower := ∏ i ∈ Finset.range m, pochhammerInf (p - 2 * (i + 1)) (2 * p)
  let oddDiagonal := pochhammerInf p (2 * p)
  let evenDiagonal := pochhammerInf (2 * p) (2 * p)
  have hres : lower * upper * diagonal = qfacInf := by
    exact canonicalResidues_reassembly p m hpm
  have hodd : oddUpper * oddLower * oddDiagonal = oddPochInf := by
    exact canonicalOddResidues_reassembly p m hpm
  have hsplit : oddDiagonal * evenDiagonal = diagonal := by
    exact diagonal_split p hp
  have hpowm : diagonal ^ m = diagonal * diagonal ^ (m - 1) := by
    calc
      diagonal ^ m = diagonal ^ ((m - 1) + 1) := by congr 1; omega
      _ = diagonal ^ (m - 1) * diagonal := pow_succ _ _
      _ = diagonal * diagonal ^ (m - 1) := mul_comm _ _
  have hpowpred : diagonal ^ (m - 1) = diagonal ^ (m - 2) * diagonal := by
    calc
      diagonal ^ (m - 1) = diagonal ^ ((m - 2) + 1) := by congr 1; omega
      _ = diagonal ^ (m - 2) * diagonal := pow_succ _ _
  change lower * upper * diagonal ^ m * oddUpper * oddLower * oddDiagonal
      = (phiNeg * (diagonal ^ (m - 2) * evenDiagonal)) * oddDiagonal
  calc
    lower * upper * diagonal ^ m * oddUpper * oddLower * oddDiagonal
        = (lower * upper * diagonal) * diagonal ^ (m - 1)
            * (oddUpper * oddLower * oddDiagonal) := by rw [hpowm]; ring
    _ = qfacInf * diagonal ^ (m - 1) * oddPochInf := by rw [hres, hodd]
    _ = phiNeg * diagonal ^ (m - 1) := by
          rw [← qfac2Inf_mul_oddPochInf, phiNeg_product]
          ring
    _ = phiNeg * (diagonal ^ (m - 2) * evenDiagonal) * oddDiagonal := by
          rw [hpowpred, ← hsplit]
          ring

/-! ### Support and coefficient vanishings -/

/-- A formal power series is supported on exponent multiples of `p`. -/
def SupportedOnMultiples (p : ℕ) (f : PowerSeries ℤ) : Prop :=
  ∀ n, ¬p ∣ n → coeff n f = 0

lemma supportedOnMultiples_mul {p : ℕ} {f g : PowerSeries ℤ}
    (hf : SupportedOnMultiples p f) (hg : SupportedOnMultiples p g) :
    SupportedOnMultiples p (f * g) := by
  intro n hn
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun pair hpair => ?_
  obtain ⟨a, b⟩ := pair
  have hab : a + b = n := Finset.mem_antidiagonal.mp hpair
  by_cases ha : p ∣ a
  · have hb : ¬p ∣ b := by
      intro hb
      exact hn (hab ▸ dvd_add ha hb)
    rw [hg b hb, mul_zero]
  · rw [hf a ha, zero_mul]

lemma supportedOnMultiples_pow {p e : ℕ} {f : PowerSeries ℤ}
    (hf : SupportedOnMultiples p f) : SupportedOnMultiples p (f ^ e) := by
  induction e with
  | zero =>
      intro n hn
      have hn0 : n ≠ 0 := by
        intro hnzero
        subst n
        exact hn (dvd_zero p)
      simp [hn0]
  | succ e ih =>
      rw [pow_succ]
      exact supportedOnMultiples_mul ih hf

/-- A diagonal Pochhammer `(q^d;q^d)_inf` is supported on multiples of `d`. -/
lemma supportedOnMultiples_pochhammerInf_diag (d : ℕ) (hd : 0 < d) :
    SupportedOnMultiples d (pochhammerInf d d) := by
  intro n hn
  rw [coeff_pochhammerInf hd hd (le_refl (n + 1)),
    pochhammerFinite_diag d (n + 1) hd]
  exact PowerSeries.coeff_expand_of_not_dvd d hd.ne' _ hn

/-- The canonical tail contains only powers `q^(pk)`. -/
lemma allCanonicalTail_supported (p : ℕ) (hp : 0 < p) :
    SupportedOnMultiples p (allCanonicalTail p) := by
  rw [allCanonicalTail]
  apply supportedOnMultiples_mul
  · exact supportedOnMultiples_pow (supportedOnMultiples_pochhammerInf_diag p hp)
  · intro n hn
    exact supportedOnMultiples_pochhammerInf_diag (2 * p) (by omega) n
      (fun h2p => hn (dvd_trans (by exact ⟨2, by ring⟩ : p ∣ 2 * p) h2p))

/-- `phi(-q)` has zero coefficient at every exponent that is not a square modulo `p`. -/
lemma coeff_phiNeg_zero_of_not_square_mod {p a : ℕ}
    (ha : ∀ x : ℕ, x ^ 2 % p ≠ a % p) : coeff a phiNeg = 0 := by
  rw [phiNeg, MockTheta5.JTP.coeff_map_evm1_bilateralTheta]
  have ha0 : a ≠ 0 := by
    intro hazero
    subst a
    exact ha 0 (by simp)
  rw [if_neg ha0, zero_add]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [if_neg]
  intro hax
  apply ha (x + 1)
  rw [hax]

/-- **The canonical infinite vanishing family.** If `p = 2m+1 >= 5`, every coefficient
whose residue modulo `p` is not a square vanishes in the product of all canonical
specializations `Q(q^i,q^p)`, `1 <= i <= (p-1)/2`. -/
theorem allCanonicalQuintupleProduct_vanishing (p m n r : ℕ)
    (hm : 2 ≤ m) (hpm : p = 2 * m + 1)
    (hr : ∀ x : ℕ, x ^ 2 % p ≠ r % p) :
    coeff (p * n + r) (allCanonicalQuintupleProduct p) = 0 := by
  rw [allCanonicalQuintupleProduct_factorization p m hm hpm,
    PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun pair hpair => ?_
  obtain ⟨a, b⟩ := pair
  have hab : a + b = p * n + r := Finset.mem_antidiagonal.mp hpair
  by_cases hb : p ∣ b
  · have ha_mod : a % p = r % p := by
      calc
        a % p = (a + b) % p := by
          simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hb]
        _ = (p * n + r) % p := by rw [hab]
        _ = r % p := by simp [Nat.add_mod]
    have ha_nonsquare : ∀ x : ℕ, x ^ 2 % p ≠ a % p := by
      intro x hx
      exact hr x (hx.trans ha_mod)
    rw [coeff_phiNeg_zero_of_not_square_mod ha_nonsquare, zero_mul]
  · rw [allCanonicalTail_supported p (by omega) b hb, mul_zero]

end Ramanujan.MultiQuintuple
