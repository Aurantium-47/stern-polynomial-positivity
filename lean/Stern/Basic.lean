import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

namespace Stern

/-- The value at a real argument of the Stern polynomial with index `n`.
The definition is the usual halving recurrence, with explicit base cases. -/
noncomputable def B (n : ℕ) (t : ℝ) : ℝ :=
  if _hn : n = 0 then 0 else
  if _h1 : n = 1 then 1 else
  if _hp : n % 2 = 0 then t * B (n / 2) t
  else B (n / 2) t + B (n / 2 + 1) t
termination_by n
decreasing_by all_goals omega

@[simp] theorem B_zero (t : ℝ) : B 0 t = 0 := by rw [B]; simp

@[simp] theorem B_one (t : ℝ) : B 1 t = 1 := by rw [B]; simp

theorem B_even (m : ℕ) (t : ℝ) : B (2 * m) t = t * B m t := by
  by_cases hm : m = 0
  · simp [hm]
  · rw [B]
    simp [show 2 * m ≠ 0 by omega, show 2 * m ≠ 1 by omega,
      Nat.mul_div_right, Nat.mul_mod]

theorem B_odd (m : ℕ) (t : ℝ) : B (2 * m + 1) t = B m t + B (m + 1) t := by
  by_cases hm : m = 0
  · simp [hm]
  · rw [B]
    simp [hm, show 2 * m + 1 ≠ 0 by omega, show 2 * m + 1 ≠ 1 by omega,
      Nat.mul_add_div, Nat.mul_mod]

/-- Adjacent Stern polynomials cannot vanish simultaneously at a nonzero argument. -/
theorem adjacent_nonzero (m : ℕ) (t : ℝ) (ht : t ≠ 0) :
    B m t ≠ 0 ∨ B (m + 1) t ≠ 0 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m = 0
    · simp [hm]
    have hi := ih (m / 2) (by omega)
    by_contra h
    push_neg at h
    rcases h with ⟨hleft, hright⟩
    rcases Nat.mod_two_eq_zero_or_one m with he | ho
    · have hm' : m = 2 * (m / 2) := by omega
      rw [hm', B_even] at hleft
      rw [hm', B_odd] at hright
      have hz : B (m / 2) t = 0 := (mul_eq_zero.mp hleft).resolve_left ht
      rcases hi with hi | hi
      · exact hi hz
      · exact hi (by simpa [hz] using hright)
    · have hm' : m = 2 * (m / 2) + 1 := by omega
      have hm1 : m + 1 = 2 * (m / 2 + 1) := by omega
      rw [hm', B_odd] at hleft
      rw [hm1, B_even] at hright
      have hz : B (m / 2 + 1) t = 0 := (mul_eq_zero.mp hright).resolve_left ht
      rcases hi with hi | hi
      · exact hi (by simpa [hz] using hleft)
      · exact hi hz

theorem adjacent_sum_zero (m : ℕ) : B m 0 + B (m + 1) 0 = 1 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m = 0
    · simp [hm]
    have hi := ih (m / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one m with he | ho
    · have hm' : m = 2 * (m / 2) := by omega
      rw [hm', B_even, B_odd]
      simpa using hi
    · have hm' : m = 2 * (m / 2) + 1 := by omega
      have hm1 : m + 1 = 2 * (m / 2 + 1) := by omega
      rw [hm1, hm', B_odd, B_even]
      simpa using hi

@[simp] theorem B_odd_zero (m : ℕ) : B (2 * m + 1) 0 = 1 := by
  rw [B_odd, adjacent_sum_zero]

/-- Binary concatenation identity, including both endpoints of the interval. -/
theorem concatenation (m r s : ℕ) (t : ℝ) (hs : s ≤ 2 ^ r) :
    B (m * 2 ^ r + s) t =
      B (2 ^ r - s) t * B m t + B s t * B (m + 1) t := by
  induction r generalizing m s with
  | zero =>
    have hs' : s = 0 ∨ s = 1 := by simp only [pow_zero] at hs; omega
    rcases hs' with rfl | rfl <;> simp
  | succ r ih =>
    have hs' : s ≤ 2 * 2 ^ r := by simpa [pow_succ, Nat.mul_comm] using hs
    rcases Nat.mod_two_eq_zero_or_one s with he | ho
    · have se : s = 2 * (s / 2) := by omega
      have hu : s / 2 ≤ 2 ^ r := by omega
      have hidx : m * 2 ^ (r + 1) + s = 2 * (m * 2 ^ r + s / 2) := by
        conv_lhs => rw [pow_succ, se]
        ring
      have hcomp : 2 ^ (r + 1) - s = 2 * (2 ^ r - s / 2) := by
        rw [pow_succ]
        omega
      rw [hidx, hcomp, B_even, B_even, ih m (s / 2) hu]
      rw [show B s t = t * B (s / 2) t by conv_lhs => rw [se, B_even]]
      ring
    · have so : s = 2 * (s / 2) + 1 := by omega
      have hu : s / 2 < 2 ^ r := by omega
      have hidx : m * 2 ^ (r + 1) + s = 2 * (m * 2 ^ r + s / 2) + 1 := by
        conv_lhs => rw [pow_succ, so]
        ring
      have hidx1 : m * 2 ^ r + s / 2 + 1 = m * 2 ^ r + (s / 2 + 1) := by omega
      have hcomp : 2 ^ (r + 1) - s = 2 * (2 ^ r - (s / 2 + 1)) + 1 := by
        rw [pow_succ]
        omega
      have hsub : 2 ^ r - (s / 2 + 1) + 1 = 2 ^ r - s / 2 := by omega
      rw [hidx, hcomp, B_odd, B_odd, hsub, hidx1,
        ih m (s / 2) (by omega), ih m (s / 2 + 1) (by omega)]
      rw [show B s t = B (s / 2) t + B (s / 2 + 1) t by conv_lhs => rw [so, B_odd]]
      ring

end Stern
