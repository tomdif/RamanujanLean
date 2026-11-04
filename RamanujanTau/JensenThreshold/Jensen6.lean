/-
# Degree-6 Jensen polynomials of p(n): finite range and last failure, by kernel computation

* `jensen6_finite` : `J^{6,n}` is hyperbolic for every `610 ≤ n ≤ 1258` (sign-alternation certificates).
* `jensen6_fails`  : `J^{6,609}` is not hyperbolic (Laguerre's inequality fails at `x = −24/25`).
* `jensen6_threshold` : given the named tail hypothesis `JensenTail 6 1259` (proved on paper with certified
  interval arithmetic, `scripts/jensen/tail_cert.py`, `docs/JENSEN_THRESHOLDS.md`), `J^{d,n}` is hyperbolic for
  all `n ≥ 610` and not at `n = 609`.
The table `p(0..1264)` is computed once by the kernel (`tab6_spec`) and then used as a literal.
-/
import RamanujanTau.JensenThreshold.Cert
import RamanujanTau.JensenThreshold.Data6

set_option autoImplicit false

namespace JensenThreshold

theorem seg6_0 : iterPT 127 0 ⟨1, true⟩ 200 = ⟨tab6_s1, true⟩ := by decide +kernel

theorem seg6_1 : iterPT 127 200 ⟨tab6_s1, true⟩ 200 = ⟨tab6_s2, true⟩ := by decide +kernel

theorem seg6_2 : iterPT 127 400 ⟨tab6_s2, true⟩ 200 = ⟨tab6_s3, true⟩ := by decide +kernel

theorem seg6_3 : iterPT 127 600 ⟨tab6_s3, true⟩ 200 = ⟨tab6_s4, true⟩ := by decide +kernel

theorem seg6_4 : iterPT 127 800 ⟨tab6_s4, true⟩ 200 = ⟨tab6_s5, true⟩ := by decide +kernel

theorem seg6_5 : iterPT 127 1000 ⟨tab6_s5, true⟩ 200 = ⟨tab6_s6, true⟩ := by decide +kernel

theorem seg6_6 : iterPT 127 1200 ⟨tab6_s6, true⟩ 64 = ⟨tab6, true⟩ := by decide +kernel

theorem tab6_eq : ptP 127 1264 = ⟨tab6, true⟩ := by
  have h0 : ptP 127 0 = ⟨1, true⟩ := rfl
  have h1 : ptP 127 200 = ⟨tab6_s1, true⟩ := ptP_of_seg (by norm_num) h0 seg6_0
  have h2 : ptP 127 400 = ⟨tab6_s2, true⟩ := ptP_of_seg (by norm_num) h1 seg6_1
  have h3 : ptP 127 600 = ⟨tab6_s3, true⟩ := ptP_of_seg (by norm_num) h2 seg6_2
  have h4 : ptP 127 800 = ⟨tab6_s4, true⟩ := ptP_of_seg (by norm_num) h3 seg6_3
  have h5 : ptP 127 1000 = ⟨tab6_s5, true⟩ := ptP_of_seg (by norm_num) h4 seg6_4
  have h6 : ptP 127 1200 = ⟨tab6_s6, true⟩ := ptP_of_seg (by norm_num) h5 seg6_5
  have h7 : ptP 127 1264 = ⟨tab6, true⟩ := ptP_of_seg (by norm_num) h6 seg6_6
  exact h7

theorem tab6_spec : (ptP 127 1264).T = tab6 ∧ (ptP 127 1264).ok = true := by
  rw [tab6_eq]; exact ⟨rfl, rfl⟩

lemma look6 {m : ℕ} (hm : m ≤ 1264) : look 127 tab6 m = pc m := by
  rw [← tab6_spec.1]; exact ptP_spec (by norm_num) tab6_spec.2 hm

lemma hyp6_of_check {n : ℕ} (hn : n + 6 ≤ 1264) (pts : List (ℕ × ℕ))
    (h : checkPts 127 tab6 6 n pts = true) : Hyperbolic (jensen 6 n) := by
  rw [← tab6_spec.1] at h
  exact hyperbolic_of_checkPts (by norm_num) tab6_spec.2 hn pts h

theorem chunk6_0 : checkAll 127 tab6 6 610 certs6_0 = true := by decide +kernel

theorem len6_0 : certs6_0.length = 100 := by decide +kernel

theorem jensen6_range0 {n : ℕ} (h1 : 610 ≤ n) (h2 : n < 710) : Hyperbolic (jensen 6 n) := by
  have := checkAll_spec certs6_0 610 chunk6_0 (n - 610) (by rw [len6_0]; omega)
  rw [show 610 + (n - 610) = n by omega] at this
  exact hyp6_of_check (by omega) _ this

theorem chunk6_1 : checkAll 127 tab6 6 710 certs6_1 = true := by decide +kernel

theorem len6_1 : certs6_1.length = 100 := by decide +kernel

theorem jensen6_range1 {n : ℕ} (h1 : 710 ≤ n) (h2 : n < 810) : Hyperbolic (jensen 6 n) := by
  have := checkAll_spec certs6_1 710 chunk6_1 (n - 710) (by rw [len6_1]; omega)
  rw [show 710 + (n - 710) = n by omega] at this
  exact hyp6_of_check (by omega) _ this

theorem chunk6_2 : checkAll 127 tab6 6 810 certs6_2 = true := by decide +kernel

theorem len6_2 : certs6_2.length = 100 := by decide +kernel

theorem jensen6_range2 {n : ℕ} (h1 : 810 ≤ n) (h2 : n < 910) : Hyperbolic (jensen 6 n) := by
  have := checkAll_spec certs6_2 810 chunk6_2 (n - 810) (by rw [len6_2]; omega)
  rw [show 810 + (n - 810) = n by omega] at this
  exact hyp6_of_check (by omega) _ this

theorem chunk6_3 : checkAll 127 tab6 6 910 certs6_3 = true := by decide +kernel

theorem len6_3 : certs6_3.length = 100 := by decide +kernel

theorem jensen6_range3 {n : ℕ} (h1 : 910 ≤ n) (h2 : n < 1010) : Hyperbolic (jensen 6 n) := by
  have := checkAll_spec certs6_3 910 chunk6_3 (n - 910) (by rw [len6_3]; omega)
  rw [show 910 + (n - 910) = n by omega] at this
  exact hyp6_of_check (by omega) _ this

theorem chunk6_4 : checkAll 127 tab6 6 1010 certs6_4 = true := by decide +kernel

theorem len6_4 : certs6_4.length = 100 := by decide +kernel

theorem jensen6_range4 {n : ℕ} (h1 : 1010 ≤ n) (h2 : n < 1110) : Hyperbolic (jensen 6 n) := by
  have := checkAll_spec certs6_4 1010 chunk6_4 (n - 1010) (by rw [len6_4]; omega)
  rw [show 1010 + (n - 1010) = n by omega] at this
  exact hyp6_of_check (by omega) _ this

theorem chunk6_5 : checkAll 127 tab6 6 1110 certs6_5 = true := by decide +kernel

theorem len6_5 : certs6_5.length = 100 := by decide +kernel

theorem jensen6_range5 {n : ℕ} (h1 : 1110 ≤ n) (h2 : n < 1210) : Hyperbolic (jensen 6 n) := by
  have := checkAll_spec certs6_5 1110 chunk6_5 (n - 1110) (by rw [len6_5]; omega)
  rw [show 1110 + (n - 1110) = n by omega] at this
  exact hyp6_of_check (by omega) _ this

theorem chunk6_6 : checkAll 127 tab6 6 1210 certs6_6 = true := by decide +kernel

theorem len6_6 : certs6_6.length = 49 := by decide +kernel

theorem jensen6_range6 {n : ℕ} (h1 : 1210 ≤ n) (h2 : n < 1259) : Hyperbolic (jensen 6 n) := by
  have := checkAll_spec certs6_6 1210 chunk6_6 (n - 1210) (by rw [len6_6]; omega)
  rw [show 1210 + (n - 1210) = n by omega] at this
  exact hyp6_of_check (by omega) _ this

theorem jensen6_finite {n : ℕ} (h1 : 610 ≤ n) (h2 : n ≤ 1258) : Hyperbolic (jensen 6 n) := by
  rcases Nat.lt_or_ge n 710 with c0 | c0
  · exact jensen6_range0 (by omega) c0
  rcases Nat.lt_or_ge n 810 with c1 | c1
  · exact jensen6_range1 (by omega) c1
  rcases Nat.lt_or_ge n 910 with c2 | c2
  · exact jensen6_range2 (by omega) c2
  rcases Nat.lt_or_ge n 1010 with c3 | c3
  · exact jensen6_range3 (by omega) c3
  rcases Nat.lt_or_ge n 1110 with c4 | c4
  · exact jensen6_range4 (by omega) c4
  rcases Nat.lt_or_ge n 1210 with c5 | c5
  · exact jensen6_range5 (by omega) c5
  exact jensen6_range6 (by omega) (by omega)

theorem jensen6_fails : ¬ Hyperbolic (jensen 6 609) := by
  have h : lagOK 127 tab6 6 609 lagPt6.1 lagPt6.2 = true := by decide +kernel
  rw [← tab6_spec.1] at h
  exact not_hyperbolic_of_lagOK (by norm_num) tab6_spec.2 (by norm_num) (by norm_num) _ _ h

/-- **Jensen threshold `N(6) = 610`**, conditional only on the named tail hypothesis `JensenTail 6 1259`. -/
theorem jensen6_threshold (htail : JensenTail 6 1259) :
    (∀ n, 610 ≤ n → Hyperbolic (jensen 6 n)) ∧ ¬ Hyperbolic (jensen 6 609) := by
  refine ⟨fun n hn => ?_, jensen6_fails⟩
  rcases Nat.lt_or_ge n 1259 with h | h
  · exact jensen6_finite hn (by omega)
  · exact htail n h

end JensenThreshold
