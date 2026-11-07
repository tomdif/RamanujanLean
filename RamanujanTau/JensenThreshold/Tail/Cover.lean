/-
# Covering `t₀ ∈ (0, t_max]` by the box list, and `t₀(n) ≤ t_max` for `n ≥ n₀`
-/
import RamanujanTau.JensenThreshold.Tail.Newton

set_option autoImplicit false

namespace JensenThreshold.Tail

open Real Rademacher

theorem coverOK_spec : ∀ (L : List BoxD) (pq : ℤ × ℤ), coverOK L pq = true → 0 < pq.2 →
    ∀ t : ℝ, 0 ≤ t → t ≤ (pq.1 : ℝ) / pq.2 →
      ∃ B ∈ L, (B.tlp : ℝ) / B.tlq ≤ t ∧ t ≤ (B.thp : ℝ) / B.thq
  | [], _, h, _, _, _, _ => by simp [coverOK] at h
  | B :: Bs, (p, q), h, hq, t, ht0, ht => by
    simp only [coverOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    have hthq : (0 : ℝ) < B.thq := by exact_mod_cast h1
    have htlq : (0 : ℝ) < B.tlq := by exact_mod_cast h2
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have heq : (B.thp : ℝ) / B.thq = (p : ℝ) / q := by
      rw [div_eq_div_iff hthq.ne' hqR.ne']; exact_mod_cast h4
    by_cases hz : B.tlp = 0
    · refine ⟨B, List.mem_cons_self, ?_, ?_⟩
      · rw [hz]; simpa using ht0
      · rw [heq]; exact ht
    · simp only [hz, if_false] at h5
      by_cases hle : (B.tlp : ℝ) / B.tlq ≤ t
      · exact ⟨B, List.mem_cons_self, hle, by rw [heq]; exact ht⟩
      · obtain ⟨B', hB', h'⟩ := coverOK_spec Bs (B.tlp, B.tlq) h5 h2 t ht0 (by push_neg at hle; exact hle.le)
        exact ⟨B', List.mem_cons_of_mem _ hB', h'⟩

lemma t0v_le_of {U th : ℝ} (hU : 0 < U) (hth : 0 < th) (h : th⁻¹ ^ 4 ≤ U ^ 2) : t0v U ≤ th := by
  unfold t0v
  have hs : 0 < Real.sqrt U := Real.sqrt_pos.mpr hU
  rw [inv_le_comm₀ hs hth]
  have h1 : th⁻¹ ^ 2 ≤ U := by
    have := (pow_le_pow_iff_left₀ (by positivity) hU.le (two_ne_zero)).mp
      (show (th⁻¹ ^ 2) ^ 2 ≤ U ^ 2 by rw [← pow_mul]; exact h)
    exact this
  rw [Real.le_sqrt (by positivity) hU.le]; exact h1

lemma t0v_nonneg (U : ℝ) : 0 ≤ t0v U := by unfold t0v; positivity

/-- `π > 3.14159` gives `aC (n − 1/24) ≥ (q/p)^4` for all `n ≥ n₀` once it holds at `n₀`. -/
lemma t0_le_tmax {p q : ℤ} (hp : 0 < p) (hq : 0 < q) {n₀ : ℕ} (hn₀ : 1 ≤ n₀)
    (hnum : q ^ 4 * 720000000000 ≤ 2 * 314159 ^ 2 * (24 * (n₀ : ℤ) - 1) * p ^ 4) {n : ℕ} (hn : n₀ ≤ n) :
    t0v (uk 1 n) ≤ (p : ℝ) / q := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  apply t0v_le_of (uk1_pos (by omega)) (div_pos hpR hqR)
  rw [uk1_sq (by omega), inv_div]
  have hpi := Real.pi_gt_d6
  have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hn0R : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hnumR : ((q : ℝ) / p) ^ 4 ≤ 2 * (314159 / 100000 : ℝ) ^ 2 / 3 * ((n₀ : ℝ) - 1 / 24) := by
    have h : (q : ℝ) ^ 4 * 720000000000 ≤ 2 * 314159 ^ 2 * (24 * (n₀ : ℝ) - 1) * (p : ℝ) ^ 4 := by
      exact_mod_cast hnum
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  have ha : 2 * (314159 / 100000 : ℝ) ^ 2 / 3 ≤ aC := by
    unfold aC; nlinarith
  calc ((q : ℝ) / p) ^ 4 ≤ 2 * (314159 / 100000 : ℝ) ^ 2 / 3 * ((n₀ : ℝ) - 1 / 24) := hnumR
    _ ≤ aC * ((n : ℝ) - 1 / 24) := by
        apply mul_le_mul ha (by linarith) (by linarith) (le_of_lt aC_pos)

end JensenThreshold.Tail
