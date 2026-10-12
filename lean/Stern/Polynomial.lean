import Stern.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace Stern

/-- Every recursively defined Stern function is the evaluation of an integer
polynomial. The induction constructs the standard polynomial witnesses. -/
theorem B_integer_polynomial (n : ℕ) :
    ∃ p : Polynomial ℤ, ∀ t : ℝ,
      p.eval₂ (Int.castRingHom ℝ) t = B n t := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      exact ⟨0, by simp⟩
    by_cases h1 : n = 1
    · subst n
      exact ⟨1, by simp⟩
    rcases ih (n / 2) (by omega) with ⟨p, hp⟩
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · have hn' : n = 2 * (n / 2) := by omega
      refine ⟨Polynomial.X * p, ?_⟩
      intro t
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_X, hp]
      conv_rhs => rw [hn', B_even]
    · have hn' : n = 2 * (n / 2) + 1 := by omega
      rcases ih (n / 2 + 1) (by omega) with ⟨q, hq⟩
      refine ⟨p + q, ?_⟩
      intro t
      rw [Polynomial.eval₂_add, hp, hq]
      conv_rhs => rw [hn', B_odd]

end Stern
