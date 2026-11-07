/-
# Degree-7 Jensen polynomials of p(n): finite range and last failure, by kernel computation

* `jensen7_finite` : `J^{7,n}` is hyperbolic for every `908 ≤ n ≤ 1675` (sign-alternation certificates).
* `jensen7_fails`  : `J^{7,907}` is not hyperbolic (Laguerre's inequality fails at `x = −79/82`).
* `jensen7_threshold` : given the named tail hypothesis `JensenTail 7 1676` (proved on paper with certified
  interval arithmetic, `scripts/jensen/tail_cert.py`, `docs/JENSEN_THRESHOLDS.md`), `J^{d,n}` is hyperbolic for
  all `n ≥ 908` and not at `n = 907`.
The table `p(0..1682)` is computed once by the kernel (`tab7_spec`) and then used as a literal.
-/
import RamanujanTau.JensenThreshold.Cert
import RamanujanTau.JensenThreshold.Data7

set_option autoImplicit false

namespace JensenThreshold

theorem seg7_0 : iterPT 147 0 ⟨1, true⟩ 200 = ⟨tab7_s1, true⟩ := by decide +kernel

theorem seg7_1 : iterPT 147 200 ⟨tab7_s1, true⟩ 200 = ⟨tab7_s2, true⟩ := by decide +kernel

theorem seg7_2 : iterPT 147 400 ⟨tab7_s2, true⟩ 200 = ⟨tab7_s3, true⟩ := by decide +kernel

theorem seg7_3 : iterPT 147 600 ⟨tab7_s3, true⟩ 200 = ⟨tab7_s4, true⟩ := by decide +kernel

theorem seg7_4 : iterPT 147 800 ⟨tab7_s4, true⟩ 200 = ⟨tab7_s5, true⟩ := by decide +kernel

theorem seg7_5 : iterPT 147 1000 ⟨tab7_s5, true⟩ 200 = ⟨tab7_s6, true⟩ := by decide +kernel

theorem seg7_6 : iterPT 147 1200 ⟨tab7_s6, true⟩ 200 = ⟨tab7_s7, true⟩ := by decide +kernel

theorem seg7_7 : iterPT 147 1400 ⟨tab7_s7, true⟩ 200 = ⟨tab7_s8, true⟩ := by decide +kernel

theorem seg7_8 : iterPT 147 1600 ⟨tab7_s8, true⟩ 82 = ⟨tab7, true⟩ := by decide +kernel

theorem tab7_eq : ptP 147 1682 = ⟨tab7, true⟩ := by
  have h0 : ptP 147 0 = ⟨1, true⟩ := rfl
  have h1 : ptP 147 200 = ⟨tab7_s1, true⟩ := ptP_of_seg (by norm_num) h0 seg7_0
  have h2 : ptP 147 400 = ⟨tab7_s2, true⟩ := ptP_of_seg (by norm_num) h1 seg7_1
  have h3 : ptP 147 600 = ⟨tab7_s3, true⟩ := ptP_of_seg (by norm_num) h2 seg7_2
  have h4 : ptP 147 800 = ⟨tab7_s4, true⟩ := ptP_of_seg (by norm_num) h3 seg7_3
  have h5 : ptP 147 1000 = ⟨tab7_s5, true⟩ := ptP_of_seg (by norm_num) h4 seg7_4
  have h6 : ptP 147 1200 = ⟨tab7_s6, true⟩ := ptP_of_seg (by norm_num) h5 seg7_5
  have h7 : ptP 147 1400 = ⟨tab7_s7, true⟩ := ptP_of_seg (by norm_num) h6 seg7_6
  have h8 : ptP 147 1600 = ⟨tab7_s8, true⟩ := ptP_of_seg (by norm_num) h7 seg7_7
  have h9 : ptP 147 1682 = ⟨tab7, true⟩ := ptP_of_seg (by norm_num) h8 seg7_8
  exact h9

theorem tab7_spec : (ptP 147 1682).T = tab7 ∧ (ptP 147 1682).ok = true := by
  rw [tab7_eq]; exact ⟨rfl, rfl⟩

lemma look7 {m : ℕ} (hm : m ≤ 1682) : look 147 tab7 m = pc m := by
  rw [← tab7_spec.1]; exact ptP_spec (by norm_num) tab7_spec.2 hm

lemma hyp7_of_check {n : ℕ} (hn : n + 7 ≤ 1682) (pts : List (ℕ × ℕ))
    (h : checkPts 147 tab7 7 n pts = true) : Hyperbolic (jensen 7 n) := by
  rw [← tab7_spec.1] at h
  exact hyperbolic_of_checkPts (by norm_num) tab7_spec.2 hn pts h

theorem chunk7_0 : checkAll 147 tab7 7 908 certs7_0 = true := by decide +kernel

theorem len7_0 : certs7_0.length = 100 := by decide +kernel

theorem jensen7_range0 {n : ℕ} (h1 : 908 ≤ n) (h2 : n < 1008) : Hyperbolic (jensen 7 n) := by
  have := checkAll_spec certs7_0 908 chunk7_0 (n - 908) (by rw [len7_0]; omega)
  rw [show 908 + (n - 908) = n by omega] at this
  exact hyp7_of_check (by omega) _ this

theorem chunk7_1 : checkAll 147 tab7 7 1008 certs7_1 = true := by decide +kernel

theorem len7_1 : certs7_1.length = 100 := by decide +kernel

theorem jensen7_range1 {n : ℕ} (h1 : 1008 ≤ n) (h2 : n < 1108) : Hyperbolic (jensen 7 n) := by
  have := checkAll_spec certs7_1 1008 chunk7_1 (n - 1008) (by rw [len7_1]; omega)
  rw [show 1008 + (n - 1008) = n by omega] at this
  exact hyp7_of_check (by omega) _ this

theorem chunk7_2 : checkAll 147 tab7 7 1108 certs7_2 = true := by decide +kernel

theorem len7_2 : certs7_2.length = 100 := by decide +kernel

theorem jensen7_range2 {n : ℕ} (h1 : 1108 ≤ n) (h2 : n < 1208) : Hyperbolic (jensen 7 n) := by
  have := checkAll_spec certs7_2 1108 chunk7_2 (n - 1108) (by rw [len7_2]; omega)
  rw [show 1108 + (n - 1108) = n by omega] at this
  exact hyp7_of_check (by omega) _ this

theorem chunk7_3 : checkAll 147 tab7 7 1208 certs7_3 = true := by decide +kernel

theorem len7_3 : certs7_3.length = 100 := by decide +kernel

theorem jensen7_range3 {n : ℕ} (h1 : 1208 ≤ n) (h2 : n < 1308) : Hyperbolic (jensen 7 n) := by
  have := checkAll_spec certs7_3 1208 chunk7_3 (n - 1208) (by rw [len7_3]; omega)
  rw [show 1208 + (n - 1208) = n by omega] at this
  exact hyp7_of_check (by omega) _ this

theorem chunk7_4 : checkAll 147 tab7 7 1308 certs7_4 = true := by decide +kernel

theorem len7_4 : certs7_4.length = 100 := by decide +kernel

theorem jensen7_range4 {n : ℕ} (h1 : 1308 ≤ n) (h2 : n < 1408) : Hyperbolic (jensen 7 n) := by
  have := checkAll_spec certs7_4 1308 chunk7_4 (n - 1308) (by rw [len7_4]; omega)
  rw [show 1308 + (n - 1308) = n by omega] at this
  exact hyp7_of_check (by omega) _ this

theorem chunk7_5 : checkAll 147 tab7 7 1408 certs7_5 = true := by decide +kernel

theorem len7_5 : certs7_5.length = 100 := by decide +kernel

theorem jensen7_range5 {n : ℕ} (h1 : 1408 ≤ n) (h2 : n < 1508) : Hyperbolic (jensen 7 n) := by
  have := checkAll_spec certs7_5 1408 chunk7_5 (n - 1408) (by rw [len7_5]; omega)
  rw [show 1408 + (n - 1408) = n by omega] at this
  exact hyp7_of_check (by omega) _ this

theorem chunk7_6 : checkAll 147 tab7 7 1508 certs7_6 = true := by decide +kernel

theorem len7_6 : certs7_6.length = 100 := by decide +kernel

theorem jensen7_range6 {n : ℕ} (h1 : 1508 ≤ n) (h2 : n < 1608) : Hyperbolic (jensen 7 n) := by
  have := checkAll_spec certs7_6 1508 chunk7_6 (n - 1508) (by rw [len7_6]; omega)
  rw [show 1508 + (n - 1508) = n by omega] at this
  exact hyp7_of_check (by omega) _ this

theorem chunk7_7 : checkAll 147 tab7 7 1608 certs7_7 = true := by decide +kernel

theorem len7_7 : certs7_7.length = 68 := by decide +kernel

theorem jensen7_range7 {n : ℕ} (h1 : 1608 ≤ n) (h2 : n < 1676) : Hyperbolic (jensen 7 n) := by
  have := checkAll_spec certs7_7 1608 chunk7_7 (n - 1608) (by rw [len7_7]; omega)
  rw [show 1608 + (n - 1608) = n by omega] at this
  exact hyp7_of_check (by omega) _ this

theorem jensen7_finite {n : ℕ} (h1 : 908 ≤ n) (h2 : n ≤ 1675) : Hyperbolic (jensen 7 n) := by
  rcases Nat.lt_or_ge n 1008 with c0 | c0
  · exact jensen7_range0 (by omega) c0
  rcases Nat.lt_or_ge n 1108 with c1 | c1
  · exact jensen7_range1 (by omega) c1
  rcases Nat.lt_or_ge n 1208 with c2 | c2
  · exact jensen7_range2 (by omega) c2
  rcases Nat.lt_or_ge n 1308 with c3 | c3
  · exact jensen7_range3 (by omega) c3
  rcases Nat.lt_or_ge n 1408 with c4 | c4
  · exact jensen7_range4 (by omega) c4
  rcases Nat.lt_or_ge n 1508 with c5 | c5
  · exact jensen7_range5 (by omega) c5
  rcases Nat.lt_or_ge n 1608 with c6 | c6
  · exact jensen7_range6 (by omega) c6
  exact jensen7_range7 (by omega) (by omega)

theorem jensen7_fails : ¬ Hyperbolic (jensen 7 907) := by
  have h : lagOK 147 tab7 7 907 lagPt7.1 lagPt7.2 = true := by decide +kernel
  rw [← tab7_spec.1] at h
  exact not_hyperbolic_of_lagOK (by norm_num) tab7_spec.2 (by norm_num) (by norm_num) _ _ h

/-- **Jensen threshold `N(7) = 908`**, conditional only on the named tail hypothesis `JensenTail 7 1676`. -/
theorem jensen7_threshold (htail : JensenTail 7 1676) :
    (∀ n, 908 ≤ n → Hyperbolic (jensen 7 n)) ∧ ¬ Hyperbolic (jensen 7 907) := by
  refine ⟨fun n hn => ?_, jensen7_fails⟩
  rcases Nat.lt_or_ge n 1676 with h | h
  · exact jensen7_finite hn (by omega)
  · exact htail n h

end JensenThreshold
