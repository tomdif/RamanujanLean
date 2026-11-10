/-- `SR3y`: `B = (1 0; 0 2)`, shifts `i (0, 1)`, `i ∈ {0, 1}`. -/
def BR3y : ECS where
  b11 := 1
  b12 := 0
  b21 := 0
  b22 := 2
  r1 := 0
  r2 := 1
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((2 * (m - 0 * ((0 * m + 1 * n - 0) % 2 + 0)) - 0 * (n - 1 * ((0 * m + 1 * n - 0) % 2 + 0))) / 2), ((1 * (n - 1 * ((0 * m + 1 * n - 0) % 2 + 0)) - 0 * (m - 0 * ((0 * m + 1 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem SR3y : QS (qmono 6 1 8 0 0 0 0) = QS (qmono 6 2 32 0 0 0 0) + mono 8 1 * QS (qmono 6 2 32 2 32 0 0) := by
  have h := QS_sub 6 1 8 0 0 0 0 BR3y (fun i hi => by
    simp only [BR3y, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, BR3y])
      (by norm_num [sA, sB, sC, BR3y]))
  simp only [BR3y] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `SR3y0p`: `B = (2 0; 0 1)`, shifts `i (1, 0)`, `i ∈ {0, 1}`. -/
def BR3y0p : ECS where
  b11 := 2
  b12 := 0
  b21 := 0
  b22 := 1
  r1 := 1
  r2 := 0
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), ((2 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem SR3y0p : QS (qmono 6 2 32 0 0 0 0) = QS (qmono 24 4 32 0 0 0 0) + mono 6 1 * QS (qmono 24 4 32 24 4 0 0) := by
  have h := QS_sub 6 2 32 0 0 0 0 BR3y0p (fun i hi => by
    simp only [BR3y0p, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, BR3y0p])
      (by norm_num [sA, sB, sC, BR3y0p]))
  simp only [BR3y0p] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `SR3y0m`: `B = (2 0; 0 1)`, shifts `i (1, 0)`, `i ∈ {0, 1}`. -/
def BR3y0m : ECS where
  b11 := 2
  b12 := 0
  b21 := 0
  b22 := 1
  r1 := 1
  r2 := 0
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), ((2 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem SR3y0m : QS (qmono 6 2 32 0 0 1 0) = QS (qmono 24 4 32 0 0 0 0) - mono 6 1 * QS (qmono 24 4 32 24 4 0 0) := by
  have h := QS_sub 6 2 32 0 0 1 0 BR3y0m (fun i hi => by
    simp only [BR3y0m, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, BR3y0m])
      (by norm_num [sA, sB, sC, BR3y0m]))
  simp only [BR3y0m] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  simp only [qmono_par 24 4 32 0 0 2 0 0 0 (by decide) (by decide), qmono_par 24 4 32 24 4 2 0 0 0 (by decide) (by decide)] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `SR3y1`: `B = (2 0; 0 1)`, shifts `i (1, 0)`, `i ∈ {0, 1}`. -/
def BR3y1 : ECS where
  b11 := 2
  b12 := 0
  b21 := 0
  b22 := 1
  r1 := 1
  r2 := 0
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), ((2 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem SR3y1 : QS (qmono 6 2 32 2 32 0 0) = QS (qmono 24 4 32 4 32 0 0) + mono 8 1 * QS (qmono 24 4 32 28 36 0 0) := by
  have h := QS_sub 6 2 32 2 32 0 0 BR3y1 (fun i hi => by
    simp only [BR3y1, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, BR3y1])
      (by norm_num [sA, sB, sC, BR3y1]))
  simp only [BR3y1] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `SR3w`: `B = (0 1; 1 0)`, shifts `i (0, 0)`, `i ∈ {0}`. -/
def BR3w : ECS where
  b11 := 0
  b12 := 1
  b21 := 1
  b22 := 0
  r1 := 0
  r2 := 0
  I := {0}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 0 * n - 0) % 1 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((0 * (m - 0 * ((0 * m + 0 * n - 0) % 1 + 0)) - 1 * (n - 0 * ((0 * m + 0 * n - 0) % 1 + 0))) / (-1)), ((0 * (n - 0 * ((0 * m + 0 * n - 0) % 1 + 0)) - 1 * (m - 0 * ((0 * m + 0 * n - 0) % 1 + 0))) / (-1)), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem SR3w : QS (qmono 8 2 24 0 0 0 0) = QS (qmono 24 2 8 0 0 0 0) := by
  have h := QS_sub 8 2 24 0 0 0 0 BR3w (fun i hi => by
    simp only [BR3w, mem_insert, mem_singleton] at hi
    rcases hi with rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, BR3w])
      (by norm_num [sA, sB, sC, BR3w]))
  simp only [BR3w] at h
  rw [sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `SR3wy`: `B = (1 0; 0 2)`, shifts `i (0, 1)`, `i ∈ {0, 1}`. -/
def BR3wy : ECS where
  b11 := 1
  b12 := 0
  b21 := 0
  b22 := 2
  r1 := 0
  r2 := 1
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((2 * (m - 0 * ((0 * m + 1 * n - 0) % 2 + 0)) - 0 * (n - 1 * ((0 * m + 1 * n - 0) % 2 + 0))) / 2), ((1 * (n - 1 * ((0 * m + 1 * n - 0) % 2 + 0)) - 0 * (m - 0 * ((0 * m + 1 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem SR3wy : QS (qmono 24 2 8 0 0 0 0) = QS (qmono 24 4 32 0 0 0 0) + mono 8 1 * QS (qmono 24 4 32 4 32 0 0) := by
  have h := QS_sub 24 2 8 0 0 0 0 BR3wy (fun i hi => by
    simp only [BR3wy, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, BR3wy])
      (by norm_num [sA, sB, sC, BR3wy]))
  simp only [BR3wy] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `SR3v`: `B = (1 1; -1 1)`, shifts `i (1, 0)`, `i ∈ {0, 1}`. -/
def BR3v : ECS where
  b11 := 1
  b12 := 1
  b21 := (-1)
  b22 := 1
  r1 := 1
  r2 := 0
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 1 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 1 * n - 0) % 2 + 0)) - 1 * (n - 0 * ((1 * m + 1 * n - 0) % 2 + 0))) / 2), ((1 * (n - 0 * ((1 * m + 1 * n - 0) % 2 + 0)) - (-1) * (m - 1 * ((1 * m + 1 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem SR3v : QS (qmono 12 2 16 0 0 0 0) = QS (qmono 24 (-4) 32 0 0 0 0) + mono 12 1 * QS (qmono 24 (-4) 32 20 28 0 0) := by
  have h := QS_sub 12 2 16 0 0 0 0 BR3v (fun i hi => by
    simp only [BR3v, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, BR3v])
      (by norm_num [sA, sB, sC, BR3v]))
  simp only [BR3v] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `SR3va`: `B = (-1 0; 0 1)`, shifts `i (0, 0)`, `i ∈ {0}`. -/
def BR3va : ECS where
  b11 := (-1)
  b12 := 0
  b21 := 0
  b22 := 1
  r1 := 0
  r2 := 0
  I := {0}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 0 * n - 0) % 1 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 0 * ((0 * m + 0 * n - 0) % 1 + 0)) - 0 * (n - 0 * ((0 * m + 0 * n - 0) % 1 + 0))) / (-1)), (((-1) * (n - 0 * ((0 * m + 0 * n - 0) % 1 + 0)) - 0 * (m - 0 * ((0 * m + 0 * n - 0) % 1 + 0))) / (-1)), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem SR3va : QS (qmono 24 (-4) 32 0 0 0 0) = QS (qmono 24 4 32 0 0 0 0) := by
  have h := QS_sub 24 (-4) 32 0 0 0 0 BR3va (fun i hi => by
    simp only [BR3va, mem_insert, mem_singleton] at hi
    rcases hi with rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, BR3va])
      (by norm_num [sA, sB, sC, BR3va]))
  simp only [BR3va] at h
  rw [sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `SR3vb`: `B = (-1 0; 0 1)`, shifts `i (-1, 0)`, `i ∈ {1}`. -/
def BR3vb : ECS where
  b11 := (-1)
  b12 := 0
  b21 := 0
  b22 := 1
  r1 := (-1)
  r2 := 0
  I := {1}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 0 * n - 1) % 1 + 1), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - (-1) * ((0 * m + 0 * n - 1) % 1 + 1)) - 0 * (n - 0 * ((0 * m + 0 * n - 1) % 1 + 1))) / (-1)), (((-1) * (n - 0 * ((0 * m + 0 * n - 1) % 1 + 1)) - 0 * (m - (-1) * ((0 * m + 0 * n - 1) % 1 + 1))) / (-1)), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem SR3vb : QS (qmono 24 (-4) 32 20 28 0 0) = mono 4 1 * QS (qmono 24 4 32 28 36 0 0) := by
  have h := QS_sub 24 (-4) 32 20 28 0 0 BR3vb (fun i hi => by
    simp only [BR3vb, mem_insert, mem_singleton] at hi
    rcases hi with rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, BR3vb])
      (by norm_num [sA, sB, sC, BR3vb]))
  simp only [BR3vb] at h
  rw [sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `LRY1`: `B = (1 -1; 0 3)`, shifts `i (0, 1)`, `i ∈ {(-3), (-2), (-1)}`. -/
def BRY1 : ECS where
  b11 := 1
  b12 := (-1)
  b21 := 0
  b22 := 3
  r1 := 0
  r2 := 1
  I := {(-3), (-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-3)) % 3 + (-3)), by simp only [mem_insert, mem_singleton]; omega,
    ((3 * (m - 0 * ((0 * m + 1 * n - (-3)) % 3 + (-3))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-3)) % 3 + (-3)))) / 3), ((1 * (n - 1 * ((0 * m + 1 * n - (-3)) % 3 + (-3))) - 0 * (m - 0 * ((0 * m + 1 * n - (-3)) % 3 + (-3)))) / 3), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem LRY1 : QS (qmono 6 2 32 2 32 0 0) = 2 * (θ hm12 4 (-1) * θ hm564 188 (-1)) + (mono 64 1 * (θ hm12 0 (-1) * θ hm564 0 (-1))) := by
  have h := (QS_orth 6 2 32 2 32 0 0 BRY1 hm12 hm564 (by norm_num [BRY1])
    (by norm_num [BRY1]) (by norm_num [BRY1])).2
  simp only [BRY1] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfrm hm12 4 (-1) (-4) 1 (e := (-4)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm564 188 (-1) (-188) 1 (e := (-188)) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `LRY0m`: `B = (1 -1; 0 3)`, shifts `i (0, 1)`, `i ∈ {(-3), (-2), (-1)}`. -/
def BRY0m : ECS where
  b11 := 1
  b12 := (-1)
  b21 := 0
  b22 := 3
  r1 := 0
  r2 := 1
  I := {(-3), (-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-3)) % 3 + (-3)), by simp only [mem_insert, mem_singleton]; omega,
    ((3 * (m - 0 * ((0 * m + 1 * n - (-3)) % 3 + (-3))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-3)) % 3 + (-3)))) / 3), ((1 * (n - 1 * ((0 * m + 1 * n - (-3)) % 3 + (-3))) - 0 * (m - 0 * ((0 * m + 1 * n - (-3)) % 3 + (-3)))) / 3), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem LRY0m : QS (qmono 6 2 32 0 0 1 0) = (θ hm12 6 1 * θ hm564 282 1) + 2 * (mono 32 1 * (θ hm12 2 1 * θ hm564 94 1)) := by
  have h := (QS_orth 6 2 32 0 0 1 0 BRY0m hm12 hm564 (by norm_num [BRY0m])
    (by norm_num [BRY0m]) (by norm_num [BRY0m])).2
  simp only [BRY0m] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm12 2 (-1) (-2) (-1) (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm564 94 (-1) (-94) (-1) (e := (-94)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm12 6 (-1) one_ne_zero (-6) (-1) (e := (-6)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm564 282 (-1) one_ne_zero (-282) (-1) (e := (-282)) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `LRW2`: `B = (1 -1; 0 4)`, shifts `i (0, 1)`, `i ∈ {(-4), (-3), (-2), (-1)}`. -/
def BRW2 : ECS where
  b11 := 1
  b12 := (-1)
  b21 := 0
  b22 := 4
  r1 := 0
  r2 := 1
  I := {(-4), (-3), (-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-4)) % 4 + (-4)), by simp only [mem_insert, mem_singleton]; omega,
    ((4 * (m - 0 * ((0 * m + 1 * n - (-4)) % 4 + (-4))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-4)) % 4 + (-4)))) / 4), ((1 * (n - 1 * ((0 * m + 1 * n - (-4)) % 4 + (-4))) - 0 * (m - 0 * ((0 * m + 1 * n - (-4)) % 4 + (-4)))) / 4), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem LRW2 : QS (qmono 8 2 24 0 0 0 0) = (θ hm16 8 (-1) * θ hm752 376 (-1)) + 2 * (mono 24 1 * (θ hm16 4 (-1) * θ hm752 188 (-1))) + (mono 96 1 * (θ hm16 0 (-1) * θ hm752 0 (-1))) := by
  have h := (QS_orth 8 2 24 0 0 0 0 BRW2 hm16 hm752 (by norm_num [BRW2])
    (by norm_num [BRW2]) (by norm_num [BRW2])).2
  simp only [BRW2] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfrm hm16 4 (-1) (-4) 1 (e := (-4)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm752 188 (-1) (-188) 1 (e := (-188)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm16 8 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-8) 1 (e := (-8)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm752 376 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-376) 1 (e := (-376)) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `LRW3`: `B = (1 -1; 0 6)`, shifts `i (0, 1)`, `i ∈ {(-6), (-5), (-4), (-3), (-2), (-1)}`. -/
def BRW3 : ECS where
  b11 := 1
  b12 := (-1)
  b21 := 0
  b22 := 6
  r1 := 0
  r2 := 1
  I := {(-6), (-5), (-4), (-3), (-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-6)) % 6 + (-6)), by simp only [mem_insert, mem_singleton]; omega,
    ((6 * (m - 0 * ((0 * m + 1 * n - (-6)) % 6 + (-6))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-6)) % 6 + (-6)))) / 6), ((1 * (n - 1 * ((0 * m + 1 * n - (-6)) % 6 + (-6))) - 0 * (m - 0 * ((0 * m + 1 * n - (-6)) % 6 + (-6)))) / 6), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem LRW3 : QS (qmono 12 2 16 0 0 0 0) = (θ hm24 12 (-1) * θ hm1128 564 (-1)) + 2 * (mono 16 1 * (θ hm24 8 (-1) * θ hm1128 376 (-1))) + 2 * (mono 64 1 * (θ hm24 4 (-1) * θ hm1128 188 (-1))) + (mono 144 1 * (θ hm24 0 (-1) * θ hm1128 0 (-1))) := by
  have h := (QS_orth 12 2 16 0 0 0 0 BRW3 hm24 hm1128 (by norm_num [BRW3])
    (by norm_num [BRW3]) (by norm_num [BRW3])).2
  simp only [BRW3] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfrm hm1128 188 (-1) (-188) 1 (e := (-188)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm1128 376 (-1) (-376) 1 (e := (-376)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm24 4 (-1) (-4) 1 (e := (-4)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm24 8 (-1) (-8) 1 (e := (-8)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm1128 564 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-564) 1 (e := (-564)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm24 12 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-12) 1 (e := (-12)) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `LRW33`: `B = (1 -1; 0 6)`, shifts `i (0, 1)`, `i ∈ {(-6), (-5), (-4), (-3), (-2), (-1)}`. -/
def BRW33 : ECS where
  b11 := 1
  b12 := (-1)
  b21 := 0
  b22 := 6
  r1 := 0
  r2 := 1
  I := {(-6), (-5), (-4), (-3), (-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-6)) % 6 + (-6)), by simp only [mem_insert, mem_singleton]; omega,
    ((6 * (m - 0 * ((0 * m + 1 * n - (-6)) % 6 + (-6))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-6)) % 6 + (-6)))) / 6), ((1 * (n - 1 * ((0 * m + 1 * n - (-6)) % 6 + (-6))) - 0 * (m - 0 * ((0 * m + 1 * n - (-6)) % 6 + (-6)))) / 6), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem LRW33 : QS (qmono 24 4 32 0 0 0 0) = (θ hm48 24 (-1) * θ hm2256 1128 (-1)) + 2 * (mono 32 1 * (θ hm48 16 (-1) * θ hm2256 752 (-1))) + 2 * (mono 128 1 * (θ hm48 8 (-1) * θ hm2256 376 (-1))) + (mono 288 1 * (θ hm48 0 (-1) * θ hm2256 0 (-1))) := by
  have h := (QS_orth 24 4 32 0 0 0 0 BRW33 hm48 hm2256 (by norm_num [BRW33])
    (by norm_num [BRW33]) (by norm_num [BRW33])).2
  simp only [BRW33] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfrm hm2256 376 (-1) (-376) 1 (e := (-376)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm2256 752 (-1) (-752) 1 (e := (-752)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm48 16 (-1) (-16) 1 (e := (-16)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm48 8 (-1) (-8) 1 (e := (-8)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm2256 1128 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-1128) 1 (e := (-1128)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm48 24 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-24) 1 (e := (-24)) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `SR2y`: `B = (1 0; 0 2)`, shifts `i (0, 1)`, `i ∈ {0, 1}`. -/
def BR2y : ECS where
  b11 := 1
  b12 := 0
  b21 := 0
  b22 := 2
  r1 := 0
  r2 := 1
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((2 * (m - 0 * ((0 * m + 1 * n - 0) % 2 + 0)) - 0 * (n - 1 * ((0 * m + 1 * n - 0) % 2 + 0))) / 2), ((1 * (n - 1 * ((0 * m + 1 * n - 0) % 2 + 0)) - 0 * (m - 0 * ((0 * m + 1 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem SR2y : QS (qmono 4 1 12 0 0 0 0) = QS (qmono 4 2 48 0 0 0 0) + mono 12 1 * QS (qmono 4 2 48 2 48 0 0) := by
  have h := QS_sub 4 1 12 0 0 0 0 BR2y (fun i hi => by
    simp only [BR2y, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, BR2y])
      (by norm_num [sA, sB, sC, BR2y]))
  simp only [BR2y] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `SR2z1p`: `B = (2 0; 0 1)`, shifts `i (1, 0)`, `i ∈ {0, 1}`. -/
def BR2z1p : ECS where
  b11 := 2
  b12 := 0
  b21 := 0
  b22 := 1
  r1 := 1
  r2 := 0
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), ((2 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem SR2z1p : QS (qmono 4 2 48 2 48 0 0) = QS (qmono 16 4 48 4 48 0 0) + mono 6 1 * QS (qmono 16 4 48 20 52 0 0) := by
  have h := QS_sub 4 2 48 2 48 0 0 BR2z1p (fun i hi => by
    simp only [BR2z1p, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, BR2z1p])
      (by norm_num [sA, sB, sC, BR2z1p]))
  simp only [BR2z1p] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `SR2z1m`: `B = (2 0; 0 1)`, shifts `i (1, 0)`, `i ∈ {0, 1}`. -/
def BR2z1m : ECS where
  b11 := 2
  b12 := 0
  b21 := 0
  b22 := 1
  r1 := 1
  r2 := 0
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), ((2 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem SR2z1m : QS (qmono 4 2 48 2 48 1 0) = QS (qmono 16 4 48 4 48 0 0) - mono 6 1 * QS (qmono 16 4 48 20 52 0 0) := by
  have h := QS_sub 4 2 48 2 48 1 0 BR2z1m (fun i hi => by
    simp only [BR2z1m, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, BR2z1m])
      (by norm_num [sA, sB, sC, BR2z1m]))
  simp only [BR2z1m] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  simp only [qmono_par 16 4 48 4 48 2 0 0 0 (by decide) (by decide), qmono_par 16 4 48 20 52 2 0 0 0 (by decide) (by decide)] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `SR2w`: `B = (0 1; 1 0)`, shifts `i (0, 0)`, `i ∈ {0}`. -/
def BR2w : ECS where
  b11 := 0
  b12 := 1
  b21 := 1
  b22 := 0
  r1 := 0
  r2 := 0
  I := {0}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 0 * n - 0) % 1 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((0 * (m - 0 * ((0 * m + 0 * n - 0) % 1 + 0)) - 1 * (n - 0 * ((0 * m + 0 * n - 0) % 1 + 0))) / (-1)), ((0 * (n - 0 * ((0 * m + 0 * n - 0) % 1 + 0)) - 1 * (m - 0 * ((0 * m + 0 * n - 0) % 1 + 0))) / (-1)), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem SR2w : QS (qmono 12 2 16 0 0 0 0) = QS (qmono 16 2 12 0 0 0 0) := by
  have h := QS_sub 12 2 16 0 0 0 0 BR2w (fun i hi => by
    simp only [BR2w, mem_insert, mem_singleton] at hi
    rcases hi with rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, BR2w])
      (by norm_num [sA, sB, sC, BR2w]))
  simp only [BR2w] at h
  rw [sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `SR2wy`: `B = (1 0; 0 2)`, shifts `i (0, 1)`, `i ∈ {0, 1}`. -/
def BR2wy : ECS where
  b11 := 1
  b12 := 0
  b21 := 0
  b22 := 2
  r1 := 0
  r2 := 1
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((2 * (m - 0 * ((0 * m + 1 * n - 0) % 2 + 0)) - 0 * (n - 1 * ((0 * m + 1 * n - 0) % 2 + 0))) / 2), ((1 * (n - 1 * ((0 * m + 1 * n - 0) % 2 + 0)) - 0 * (m - 0 * ((0 * m + 1 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem SR2wy : QS (qmono 16 2 12 0 0 0 0) = QS (qmono 16 4 48 0 0 0 0) + mono 12 1 * QS (qmono 16 4 48 4 48 0 0) := by
  have h := QS_sub 16 2 12 0 0 0 0 BR2wy (fun i hi => by
    simp only [BR2wy, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, BR2wy])
      (by norm_num [sA, sB, sC, BR2wy]))
  simp only [BR2wy] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `LRZ0`: `B = (1 -1; 0 2)`, shifts `i (0, 1)`, `i ∈ {(-2), (-1)}`. -/
def BRZ0 : ECS where
  b11 := 1
  b12 := (-1)
  b21 := 0
  b22 := 2
  r1 := 0
  r2 := 1
  I := {(-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-2)) % 2 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((2 * (m - 0 * ((0 * m + 1 * n - (-2)) % 2 + (-2))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-2)) % 2 + (-2)))) / 2), ((1 * (n - 1 * ((0 * m + 1 * n - (-2)) % 2 + (-2))) - 0 * (m - 0 * ((0 * m + 1 * n - (-2)) % 2 + (-2)))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem LRZ0 : QS (qmono 4 2 48 0 0 0 0) = (θ hm8 4 (-1) * θ hm376 188 (-1)) + (mono 48 1 * (θ hm8 0 (-1) * θ hm376 0 (-1))) := by
  have h := (QS_orth 4 2 48 0 0 0 0 BRZ0 hm8 hm376 (by norm_num [BRZ0])
    (by norm_num [BRZ0]) (by norm_num [BRZ0])).2
  simp only [BRZ0] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_sh hm376 188 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-188) 1 (e := (-188)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm8 4 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-4) 1 (e := (-4)) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `LRZ1m`: `B = (1 -1; 0 2)`, shifts `i (0, 1)`, `i ∈ {(-2), (-1)}`. -/
def BRZ1m : ECS where
  b11 := 1
  b12 := (-1)
  b21 := 0
  b22 := 2
  r1 := 0
  r2 := 1
  I := {(-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-2)) % 2 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((2 * (m - 0 * ((0 * m + 1 * n - (-2)) % 2 + (-2))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-2)) % 2 + (-2)))) / 2), ((1 * (n - 1 * ((0 * m + 1 * n - (-2)) % 2 + (-2))) - 0 * (m - 0 * ((0 * m + 1 * n - (-2)) % 2 + (-2)))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem LRZ1m : QS (qmono 4 2 48 2 48 1 0) = 2 * (θ hm8 2 1 * θ hm376 94 1) := by
  have h := (QS_orth 4 2 48 2 48 1 0 BRZ1m hm8 hm376 (by norm_num [BRZ1m])
    (by norm_num [BRZ1m]) (by norm_num [BRZ1m])).2
  simp only [BRZ1m] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm376 94 (-1) (-94) (-1) (e := (-94)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm8 2 (-1) (-2) (-1) (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `LRW22`: `B = (1 -1; 0 4)`, shifts `i (0, 1)`, `i ∈ {(-4), (-3), (-2), (-1)}`. -/
def BRW22 : ECS where
  b11 := 1
  b12 := (-1)
  b21 := 0
  b22 := 4
  r1 := 0
  r2 := 1
  I := {(-4), (-3), (-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-4)) % 4 + (-4)), by simp only [mem_insert, mem_singleton]; omega,
    ((4 * (m - 0 * ((0 * m + 1 * n - (-4)) % 4 + (-4))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-4)) % 4 + (-4)))) / 4), ((1 * (n - 1 * ((0 * m + 1 * n - (-4)) % 4 + (-4))) - 0 * (m - 0 * ((0 * m + 1 * n - (-4)) % 4 + (-4)))) / 4), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem LRW22 : QS (qmono 16 4 48 0 0 0 0) = (θ hm32 16 (-1) * θ hm1504 752 (-1)) + 2 * (mono 48 1 * (θ hm32 8 (-1) * θ hm1504 376 (-1))) + (mono 192 1 * (θ hm32 0 (-1) * θ hm1504 0 (-1))) := by
  have h := (QS_orth 16 4 48 0 0 0 0 BRW22 hm32 hm1504 (by norm_num [BRW22])
    (by norm_num [BRW22]) (by norm_num [BRW22])).2
  simp only [BRW22] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfrm hm1504 376 (-1) (-376) 1 (e := (-376)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm32 8 (-1) (-8) 1 (e := (-8)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm1504 752 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-752) 1 (e := (-752)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm32 16 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-16) 1 (e := (-16)) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h
