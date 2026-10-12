import Stern.Basic
import Stern.Index

namespace Stern

/-- The source quadratic identity derived only from concatenation and recurrence. -/
theorem quadratic_aux (k r : ℕ) (hk : 2 ^ r = 3 * k + 1) (t : ℝ) :
    B (4 * 2 ^ r * k + 2 * k + 1) t =
      (t ^ 2 + t + 1) * (B k t) ^ 2 + (t + 2) * B k t * B (k + 1) t +
        (B (k + 1) t) ^ 2 := by
  have hp4 : (2 : ℕ) ^ (r + 2) = 4 * 2 ^ r := by
    rw [pow_add]
    ring
  have hs1 : 2 * k ≤ 2 ^ r := by omega
  have hs2 : 2 * k + 1 ≤ 2 ^ r := by omega
  have hs3 : 2 * k + 1 ≤ 2 ^ (r + 2) := by rw [hp4]; omega
  have hsub1 : 2 ^ r - 2 * k = k + 1 := by omega
  have hsub2 : 2 ^ r - (2 * k + 1) = k := by omega
  have c1 := concatenation 1 r (2 * k) t hs1
  have c2 := concatenation 1 r (2 * k + 1) t hs2
  simp only [one_mul, hsub1, B_one, mul_one, B_even, B_odd] at c1
  simp only [one_mul, hsub2, B_one, mul_one, B_even, B_odd] at c2
  have btwo : B 2 t = t := by simpa using B_even 1 t
  rw [btwo] at c1 c2
  have c3 := concatenation k (r + 2) (2 * k + 1) t hs3
  have he : k * 2 ^ (r + 2) + (2 * k + 1) = 4 * 2 ^ r * k + 2 * k + 1 := by
    rw [hp4]
    ring
  have hs : 2 ^ (r + 2) - (2 * k + 1) = 2 * (2 ^ r + 2 * k) + 1 := by
    rw [hp4]
    omega
  rw [he, hs, B_odd, B_odd, c1] at c3
  have hc2 : B (2 ^ r + 2 * k + 1) t = B k t + (B k t + B (k + 1) t) * t := by
    simpa [Nat.add_assoc] using c2
  rw [hc2] at c3
  rw [c3]
  ring

/-- The quadratic formula is for the actual source index h. -/
theorem h_quadratic (n : ℕ) (t : ℝ) :
    B (h n) t = (t ^ 2 + t + 1) * (B (a n) t) ^ 2 +
      (t + 2) * B (a n) t * B (a n + 1) t + (B (a n + 1) t) ^ 2 := by
  have hk : (2 : ℕ) ^ (2 * n) = 3 * a n + 1 := by rw [two_pow_even, four_pow]
  simpa only [two_pow_even, ← h_eq] using quadratic_aux (a n) (2 * n) hk t

theorem h_sum_of_squares (n : ℕ) (t : ℝ) :
    4 * B (h n) t = (2 * B (a n + 1) t + (t + 2) * B (a n) t) ^ 2 +
      3 * (t * B (a n) t) ^ 2 := by
  rw [h_quadratic]
  ring

theorem quadratic_positive (t A C : ℝ) (ht : t ≠ 0) (hAC : A ≠ 0 ∨ C ≠ 0) :
    0 < (t ^ 2 + t + 1) * A ^ 2 + (t + 2) * A * C + C ^ 2 := by
  have heq : 4 * ((t ^ 2 + t + 1) * A ^ 2 + (t + 2) * A * C + C ^ 2) =
      (2 * C + (t + 2) * A) ^ 2 + 3 * (t * A) ^ 2 := by ring
  by_cases ha : A = 0
  · have hc : C ≠ 0 := hAC.resolve_left (not_not.mpr ha)
    simpa [ha] using sq_pos_of_ne_zero hc
  · have hp := sq_pos_of_ne_zero (mul_ne_zero ht ha)
    have hn := sq_nonneg (2 * C + (t + 2) * A)
    nlinarith

theorem h_at_zero (n : ℕ) : B (h n) 0 = 1 := by
  have hh : h n = 2 * (2 * 4 ^ n * a n + a n) + 1 := by rw [h_eq]; ring
  rw [hh, B_odd_zero]

/-- Conjecture 4.4, with strict positivity for every natural n and real t. -/
theorem h_positive (n : ℕ) (t : ℝ) : 0 < B (h n) t := by
  by_cases ht : t = 0
  · subst t
    rw [h_at_zero]
    norm_num
  · rw [h_quadratic]
    exact quadratic_positive t (B (a n) t) (B (a n + 1) t) ht (adjacent_nonzero (a n) t ht)

theorem h_no_real_root (n : ℕ) : ¬ ∃ t : ℝ, B (h n) t = 0 := by
  rintro ⟨t, ht⟩
  exact (ne_of_gt (h_positive n t)) ht

end Stern
