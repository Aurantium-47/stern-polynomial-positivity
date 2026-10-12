import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Stern

def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => 4 * a n + 1

/-- The source index, with exact natural-number division. -/
def h (n : ℕ) : ℕ := 2 * (2 ^ (2 * n) - 1) * (2 ^ (2 * n + 1) + 1) / 3 + 1

theorem four_pow (n : ℕ) : 4 ^ n = 3 * a n + 1 := by
  induction n with
  | zero => simp [a]
  | succ n ih => simp only [pow_succ, a]; nlinarith

theorem two_pow_even (n : ℕ) : (2 : ℕ) ^ (2 * n) = 4 ^ n := by
  rw [pow_mul]
  norm_num

theorem a_eq_source (n : ℕ) : a n = (4 ^ n - 1) / 3 := by
  rw [four_pow]
  omega

theorem h_eq (n : ℕ) : h n = 4 * 4 ^ n * a n + 2 * a n + 1 := by
  have hp : (2 : ℕ) ^ (2 * n + 1) = 2 * 4 ^ n := by
    rw [pow_succ, two_pow_even]
    omega
  unfold h
  rw [two_pow_even, hp, four_pow]
  have hs : 3 * a n + 1 - 1 = 3 * a n := by omega
  rw [hs]
  have hm : 2 * (3 * a n) * (2 * (3 * a n + 1) + 1) =
      3 * (4 * (3 * a n + 1) * a n + 2 * a n) := by ring
  rw [hm, Nat.mul_div_right]
  norm_num

theorem h_source_exact (n : ℕ) :
    (h n : ℚ) = (2 / 3 : ℚ) * ((2 : ℚ) ^ (2 * n) - 1) *
      ((2 : ℚ) ^ (2 * n + 1) + 1) + 1 := by
  have hp := four_pow n
  have h2 := two_pow_even n
  have hpq : (4 : ℚ)^n = 3 * (a n : ℚ) + 1 := by exact_mod_cast hp
  have h2q : (2 : ℚ)^(2*n) = 4^n := by exact_mod_cast h2
  rw [h_eq]
  push_cast
  rw [pow_succ, h2q, hpq]
  ring

end Stern


