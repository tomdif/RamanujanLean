/-
# Real-number bookkeeping for the averaged sandwich

`H = εT/2`. Upper window `[T, T+H]` with `N ≤ 3T`, lower window `[T−H, T]` with `N ≤ 2T`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.ZetaCritical

lemma upper_alg (T ε h N I L CE : ℝ) (hT : 2 ≤ T) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hN0 : 0 ≤ N) (hN : N ≤ 3 * T) (hh0 : 0 ≤ h) (hh : h ≤ 3 + L) (hL : 0 ≤ L) (hCE : 0 ≤ CE)
    (main : ε * T / 2 * I ≤ (1 + ε) * (((T + ε * T / 2) ^ 2 - T ^ 2) / 2 * h + 20 * N ^ 2) +
      ε * T / 2 * ((1 + 1 / ε) * (CE * (T + ε * T / 2)))) :
    I ≤ (1 + 2 * ε) * T * L + (729 + 3 * CE) * T / ε := by
  have hT0 : 0 < T := by linarith
  set X : ℝ := (1 + ε) * (1 + ε / 4) * T * h + 40 * (1 + ε) * N ^ 2 / T / ε +
    (1 + 1 / ε) * (CE * (T + ε * T / 2)) with hX
  have hXe : ε * T / 2 * X = (1 + ε) * (((T + ε * T / 2) ^ 2 - T ^ 2) / 2 * h + 20 * N ^ 2) +
      ε * T / 2 * ((1 + 1 / ε) * (CE * (T + ε * T / 2))) := by
    rw [hX]; field_simp; ring
  have hIX : I ≤ X := by
    rw [← hXe] at main
    exact le_of_mul_le_mul_left main (by positivity)
  have hie : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε0]; linarith
  have t1 : (1 + ε) * (1 + ε / 4) * T * h ≤ (1 + 2 * ε) * T * L + 9 * T / ε := by
    have a : (1 + ε) * (1 + ε / 4) ≤ 1 + 2 * ε := by nlinarith
    have b : (1 + ε) * (1 + ε / 4) * T * h ≤ (1 + 2 * ε) * T * (3 + L) := by
      have : 0 ≤ T * h := by positivity
      calc (1 + ε) * (1 + ε / 4) * T * h = (1 + ε) * (1 + ε / 4) * (T * h) := by ring
        _ ≤ (1 + 2 * ε) * (T * (3 + L)) := by
            apply mul_le_mul a (by gcongr) this (by linarith)
        _ = (1 + 2 * ε) * T * (3 + L) := by ring
    have c : 9 * T ≤ 9 * T / ε := by
      rw [le_div_iff₀ hε0]; nlinarith
    nlinarith
  have t2 : 40 * (1 + ε) * N ^ 2 / T / ε ≤ 720 * T / ε := by
    apply div_le_div_of_nonneg_right _ hε0.le
    rw [div_le_iff₀ hT0]
    have : N ^ 2 ≤ 9 * T ^ 2 := by nlinarith
    nlinarith
  have t3 : (1 + 1 / ε) * (CE * (T + ε * T / 2)) ≤ 3 * CE * T / ε := by
    have a : 1 + 1 / ε ≤ 2 / ε := by
      have : 2 / ε = 1 / ε + 1 / ε := by ring
      linarith
    have b : CE * (T + ε * T / 2) ≤ CE * (3 / 2 * T) := by gcongr; nlinarith
    calc (1 + 1 / ε) * (CE * (T + ε * T / 2)) ≤ 2 / ε * (CE * (3 / 2 * T)) := by
          apply mul_le_mul a b (by positivity) (by positivity)
      _ = 3 * CE * T / ε := by ring
  have e : (729 + 3 * CE) * T / ε = 9 * T / ε + 720 * T / ε + 3 * CE * T / ε := by ring
  rw [e]; linarith

lemma lower_alg (T ε h N I L CE g1 : ℝ) (hT : 2 ≤ T) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hN0 : 0 ≤ N) (hN : N ≤ 2 * T) (hhL : L ≤ h) (hL : 0 ≤ L) (hCE : 0 ≤ CE)
    (hg0 : 0 ≤ g1) (hg : g1 ≤ 4 * N)
    (main : (1 - ε) * ((T ^ 2 - (T - ε * T / 2) ^ 2) / 2 * h - 20 * N ^ 2 - ε * T / 2 * g1) ≤
      ε * T / 2 * (I + (1 + 1 / ε) * (CE * T))) :
    (1 - 2 * ε) * T * L - (168 + 2 * CE) * T / ε ≤ I := by
  have hT0 : 0 < T := by linarith
  set Y : ℝ := (1 - ε) * ((1 - ε / 4) * T * h - 40 * N ^ 2 / T / ε - g1) with hY
  have hYe : ε * T / 2 * Y =
      (1 - ε) * ((T ^ 2 - (T - ε * T / 2) ^ 2) / 2 * h - 20 * N ^ 2 - ε * T / 2 * g1) := by
    rw [hY]; field_simp; ring
  have hYI : Y ≤ I + (1 + 1 / ε) * (CE * T) := by
    rw [← hYe] at main
    exact le_of_mul_le_mul_left main (by positivity)
  have hie : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε0]; linarith
  have q0 : 0 ≤ (1 - ε) * (1 - ε / 4) := by nlinarith
  have t1 : (1 - 2 * ε) * T * L ≤ (1 - ε) * (1 - ε / 4) * T * h := by
    have a : (1 - 2 * ε) ≤ (1 - ε) * (1 - ε / 4) := by nlinarith
    have hTL : 0 ≤ T * L := by positivity
    calc (1 - 2 * ε) * T * L = (1 - 2 * ε) * (T * L) := by ring
      _ ≤ (1 - ε) * (1 - ε / 4) * (T * L) := by gcongr
      _ ≤ (1 - ε) * (1 - ε / 4) * (T * h) := by gcongr
      _ = (1 - ε) * (1 - ε / 4) * T * h := by ring
  have t2 : 40 * N ^ 2 / T / ε ≤ 160 * T / ε := by
    apply div_le_div_of_nonneg_right _ hε0.le
    rw [div_le_iff₀ hT0]
    nlinarith
  have t3 : g1 ≤ 8 * T / ε := by
    have : 8 * T ≤ 8 * T / ε := by rw [le_div_iff₀ hε0]; nlinarith
    linarith
  have t4 : (1 - ε) * (40 * N ^ 2 / T / ε + g1) ≤ 168 * T / ε := by
    have h0 : 0 ≤ 40 * N ^ 2 / T / ε + g1 := by positivity
    have : (1 - ε) * (40 * N ^ 2 / T / ε + g1) ≤ 40 * N ^ 2 / T / ε + g1 := by nlinarith
    have e : 168 * T / ε = 160 * T / ε + 8 * T / ε := by ring
    linarith
  have t5 : (1 + 1 / ε) * (CE * T) ≤ 2 * CE * T / ε := by
    have a : 1 + 1 / ε ≤ 2 / ε := by
      have : 2 / ε = 1 / ε + 1 / ε := by ring
      linarith
    calc (1 + 1 / ε) * (CE * T) ≤ 2 / ε * (CE * T) := by gcongr
      _ = 2 * CE * T / ε := by ring
  have hYexp : Y = (1 - ε) * (1 - ε / 4) * T * h - (1 - ε) * (40 * N ^ 2 / T / ε + g1) := by
    rw [hY]; ring
  have e : (168 + 2 * CE) * T / ε = 168 * T / ε + 2 * CE * T / ε := by ring
  rw [e]; linarith

/-- Combining the two sides. -/
lemma abs_alg {I T L ε K1 K2 : ℝ} (hK : K1 ≤ K2)
    (hu : I ≤ (1 + 2 * ε) * T * L + K2 * T / ε)
    (hl : (1 - 2 * ε) * T * L - K1 * T / ε ≤ I) (hT : 0 ≤ T) (hε : 0 < ε) :
    |I - T * L| ≤ 2 * ε * (T * L) + K2 * T / ε := by
  have : K1 * T / ε ≤ K2 * T / ε := by gcongr
  rw [abs_le]; constructor <;> nlinarith

end RamanujanTau.ZetaCritical
