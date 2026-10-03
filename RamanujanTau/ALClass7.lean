/-
# Residue classes of exponents mod 7 in `ℂ((t))`

`InCls c f`: every exponent in the support of `f` is `≡ c (mod 7)`. Series in class `0` form a subfield
(the image of `t ↦ t⁷`), products add classes, and summable families of class-`c` terms sum to class `c`.
-/
import RamanujanTau.ALSplitM

set_option autoImplicit false

namespace ALz
open HahnSeries

/-- all exponents of `f` are `≡ c (mod 7)`. -/
def InCls (c : ℤ) (f : L) : Prop := ∀ n, f.coeff n ≠ 0 → n % 7 = c

lemma InCls.zero (c : ℤ) : InCls c 0 := fun n h => (h rfl).elim

lemma InCls.add {c : ℤ} {f g : L} (hf : InCls c f) (hg : InCls c g) : InCls c (f + g) := by
  intro n h
  rw [coeff_add] at h
  by_cases h1 : f.coeff n = 0
  · rw [h1, zero_add] at h; exact hg n h
  · exact hf n h1

lemma InCls.neg {c : ℤ} {f : L} (hf : InCls c f) : InCls c (-f) := by
  intro n h; rw [coeff_neg, neg_ne_zero] at h; exact hf n h

lemma InCls.sub {c : ℤ} {f g : L} (hf : InCls c f) (hg : InCls c g) : InCls c (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

lemma InCls.mul {a b : ℤ} {f g : L} (hf : InCls a f) (hg : InCls b g) : InCls ((a + b) % 7) (f * g) := by
  intro n h
  rw [coeff_mul] at h
  obtain ⟨⟨i, j⟩, hij, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mem_addAntidiagonal] at hij
  obtain ⟨hi, hj, rfl⟩ := hij
  have := hf i hi; have := hg j hj
  omega

lemma InCls.of_mono (e : ℤ) (c : ℂ) : InCls (e % 7) (ALz.mono e c) := by
  intro n h
  simp only [ALz.mono, coeff_single] at h
  split_ifs at h with he
  · rw [he]
  · exact (h rfl).elim

lemma InCls.mono_mul {f : L} (hf : InCls 0 f) (e : ℤ) (a : ℂ) : InCls (e % 7) (ALz.mono e a * f) := by
  have := (InCls.of_mono e a).mul hf
  simpa using this

/-- `t ↦ t⁷`. -/
noncomputable def emb7 : L →+* L :=
  embDomainRingHom (AddMonoidHom.mul 7 : ℤ →+ ℤ) (fun a b h => by simp at h; omega)
    (fun a b => by simp only [AddMonoidHom.mul_apply]; omega)

lemma emb7_coeff (g : L) (k : ℤ) : (emb7 g).coeff (7 * k) = g.coeff k :=
  embDomain_coeff (a := k)

lemma emb7_cls (g : L) : InCls 0 (emb7 g) := by
  intro n h
  by_contra hn
  apply h
  refine embDomain_notin_range ?_
  rintro ⟨k, hk⟩
  apply hn
  simp at hk
  omega

/-- every class-`0` series is in the image of `t ↦ t⁷`. -/
lemma cls0_range {f : L} (hf : InCls 0 f) : ∃ g : L, emb7 g = f := by
  refine ⟨⟨fun k => f.coeff (7 * k), ?_⟩, ?_⟩
  · refine Set.IsWF.isPWO (BddBelow.isWF ⟨min f.order 0, fun k hk => ?_⟩)
    have h1 : f.order ≤ 7 * k := order_le_of_coeff_ne_zero hk
    have h2 : min f.order 0 ≤ f.order := min_le_left _ _
    have h3 : min f.order 0 ≤ 0 := min_le_right _ _
    omega
  · ext n
    by_cases hn : n % 7 = 0
    · obtain ⟨k, rfl⟩ : ∃ k, n = 7 * k := ⟨n / 7, by omega⟩
      rw [emb7_coeff]
    · rw [show (emb7 _).coeff n = 0 from ?_]
      · by_contra h; exact hn (hf n (Ne.symm h))
      · refine embDomain_notin_range ?_
        rintro ⟨k, hk⟩; apply hn; simp at hk; omega

/-- class `0` is closed under inverses. -/
lemma InCls.inv {f : L} (hf : InCls 0 f) : InCls 0 f⁻¹ := by
  obtain ⟨g, rfl⟩ := cls0_range hf
  rw [← map_inv₀]
  exact emb7_cls _

lemma InCls.one : InCls 0 (1 : L) := by
  have := InCls.of_mono 0 1
  simpa [ALz.mono] using this

lemma InCls.hsum {c : ℤ} {ι : Type*} (s : SummableFamily ℤ ℂ ι) (h : ∀ i, InCls c (s i)) : InCls c (hs s) := by
  intro n hn
  by_contra hc
  apply hn
  rw [hs, SummableFamily.coeff_hsum]
  exact finsum_eq_zero_of_forall_eq_zero fun i => by
    by_contra hi; exact hc (h i n hi)

section Base7
variable {N : ℕ} (hN : 1 ≤ N) (h7N : (7 : ℤ) ∣ N)
include hN h7N

lemma InCls.θ {e : ℤ} (he : (7 : ℤ) ∣ e) (c : ℂ) : InCls 0 (θ hN e c) := by
  refine InCls.hsum _ fun k => ?_
  have h := InCls.of_mono (thE N e k) (thC c k)
  have : thE N e k % 7 = 0 := by
    unfold thE; obtain ⟨a, ha⟩ := h7N; obtain ⟨b, hb⟩ := he; rw [ha, hb]; ring_nf; omega
  rw [this] at h
  exact h

lemma InCls.Ab {a β : ℤ} (ha : (7 : ℤ) ∣ a) (hb : (7 : ℤ) ∣ β) (hlo : -N < a + β) (hhi : a + β < N)
    {cx cp : ℂ} (hx : cx ≠ 0) (hp : cp ≠ 0) : InCls 0 (Ab hN hlo hhi cx cp) := by
  rw [Ab_eq_sum]
  refine InCls.hsum _ fun r => ?_
  rw [aSumF_apply _ _ _ hx hp]
  unfold aTerm
  obtain ⟨n, hn⟩ := h7N; obtain ⟨x, hx'⟩ := ha; obtain ⟨y, hy⟩ := hb
  have h1 := InCls.of_mono (N * c2 r + β * r) ((-1) ^ r * cp ^ r)
  have h2 := InCls.of_mono (N * (r - 1) + a + β) (cx * cp)
  have e1 : (N * c2 r + β * r : ℤ) % 7 = 0 := by rw [hn, hy]; ring_nf; omega
  have e2 : ((N : ℤ) * (r - 1) + a + β) % 7 = 0 := by rw [hn, hx', hy]; ring_nf; omega
  rw [e1] at h1; rw [e2] at h2
  have := h1.mul (InCls.one.sub h2).inv
  simpa using this

end Base7

/-- no exponent `≡ 5 (mod 7)`. -/
def No5 (f : L) : Prop := ∀ n, n % 7 = 5 → f.coeff n = 0

lemma No5.add {f g : L} (hf : No5 f) (hg : No5 g) : No5 (f + g) := fun n h => by
  rw [coeff_add, hf n h, hg n h, add_zero]

lemma No5.neg {f : L} (hf : No5 f) : No5 (-f) := fun n h => by rw [coeff_neg, hf n h, neg_zero]

lemma No5.sub {f g : L} (hf : No5 f) (hg : No5 g) : No5 (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

lemma No5.zero : No5 0 := fun _ _ => rfl

lemma No5.of_cls {c : ℤ} {f : L} (hf : InCls c f) (hc : c ≠ 5) : No5 f := fun n hn => by
  by_contra h; exact hc (by rw [← hf n h]; exact hn)


end ALz
