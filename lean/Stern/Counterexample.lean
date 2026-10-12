import Stern.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
An exact counterexample to the increasing-function clause of Conjecture 4.3
in M. Ulas, *Strong arithmetic property of certain Stern polynomials* (2020).
The unique-real-root statement for the general family is not addressed here.
-/

namespace Stern

open Filter Set
open scoped Topology

/-- The paper's integer index, for the family used in the counterexample.
Only `n = 2` is needed below, so no claim about truncated subtraction at the
small parameters is needed. -/
def s0 (n : ℕ) : ℕ := 2 ^ (2 * n + 4) - 9 * 2 ^ (n + 1) - 1

theorem s0_two : s0 2 = 183 := by norm_num [s0]

/-- Expansion derived from the defining Stern recurrence. -/
theorem B183_explicit (t : ℝ) :
    B 183 t = t ^ 5 + 3 * t ^ 4 + 7 * t ^ 3 + 9 * t ^ 2 + 5 * t + 1 := by
  have h183 : B 183 t = B 91 t + B 92 t := B_odd 91 t
  have h91 : B 91 t = B 45 t + B 46 t := B_odd 45 t
  have h92 : B 92 t = t * B 46 t := B_even 46 t
  have h45 : B 45 t = B 22 t + B 23 t := B_odd 22 t
  have h46 : B 46 t = t * B 23 t := B_even 23 t
  have h22 : B 22 t = t * B 11 t := B_even 11 t
  have h23 : B 23 t = B 11 t + B 12 t := B_odd 11 t
  have h11 : B 11 t = B 5 t + B 6 t := B_odd 5 t
  have h12 : B 12 t = t * B 6 t := B_even 6 t
  have h5 : B 5 t = B 2 t + B 3 t := B_odd 2 t
  have h6 : B 6 t = t * B 3 t := B_even 3 t
  have h3 : B 3 t = B 1 t + B 2 t := B_odd 1 t
  have h2 : B 2 t = t * B 1 t := B_even 1 t
  simp only [h183, h91, h92, h45, h46, h22, h23, h11, h12, h5, h6, h3, h2, B_one]
  ring

theorem B183_hasDerivAt (t : ℝ) :
    HasDerivAt (B 183) (5 * t ^ 4 + 12 * t ^ 3 + 21 * t ^ 2 + 18 * t + 5) t := by
  have hfun : B 183 = fun x : ℝ =>
      x ^ 5 + 3 * x ^ 4 + 7 * x ^ 3 + 9 * x ^ 2 + 5 * x + 1 :=
    funext B183_explicit
  rw [hfun]
  have hd := HasDerivAt.add_const 1
    (HasDerivAt.add
      (HasDerivAt.add
        (HasDerivAt.add
          (HasDerivAt.add (hasDerivAt_pow 5 t)
            (HasDerivAt.const_mul 3 (hasDerivAt_pow 4 t)))
          (HasDerivAt.const_mul 7 (hasDerivAt_pow 3 t)))
        (HasDerivAt.const_mul 9 (hasDerivAt_pow 2 t)))
      (HasDerivAt.const_mul 5 (hasDerivAt_id t)))
  convert hd using 1
  norm_num
  ring

theorem B183_deriv (t : ℝ) :
    deriv (B 183) t = 5 * t ^ 4 + 12 * t ^ 3 + 21 * t ^ 2 + 18 * t + 5 :=
  (B183_hasDerivAt t).deriv

theorem B183_deriv_neg_two_thirds :
    deriv (B 183) (-2 / 3) = -19 / 81 := by
  rw [B183_deriv]
  norm_num

/-- The real root `-1` is simple. -/
theorem B183_deriv_neg_one : deriv (B 183) (-1) = 1 := by
  rw [B183_deriv]
  norm_num

theorem B183_hasDerivAt_neg_two_thirds :
    HasDerivAt (B 183) (-19 / 81) (-2 / 3) := by
  convert B183_hasDerivAt (-2 / 3) using 1
  norm_num

/-- A negative derivative at an interior point contradicts nondecreasingness.
This uses the limit of right-hand slopes, so the derivative certificate is
connected directly to the monotonicity conclusion. -/
theorem not_monotoneOn_of_hasDerivAt_neg {f : ℝ → ℝ} {a b x d : ℝ}
    (hx : x ∈ Ioo a b) (hd : HasDerivAt f d x) (hdneg : d < 0) :
    ¬ MonotoneOn f (Ioo a b) := by
  intro hm
  have ht : Tendsto (slope f x) (𝓝[>] x) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsGT_le_nhdsNE x)
  have he : ∀ᶠ y in 𝓝[>] x, 0 ≤ slope f x y := by
    have hn : ∀ᶠ y in 𝓝[>] x, y ∈ Ioo a b :=
      nhdsWithin_le_nhds (Ioo_mem_nhds hx.1 hx.2)
    filter_upwards [self_mem_nhdsWithin, hn] with y hy hyab
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.mpr (hm hx hyab (le_of_lt hy)))
      (sub_nonneg.mpr (le_of_lt hy))
  have hnonneg : 0 ≤ d := ge_of_tendsto ht he
  exact (not_le_of_gt hdneg) hnonneg

theorem B183_not_monotoneOn : ¬ MonotoneOn (B 183) (Ioo (-1) 0) := by
  exact not_monotoneOn_of_hasDerivAt_neg (by norm_num)
    B183_hasDerivAt_neg_two_thirds (by norm_num)

theorem B183_not_strictMonoOn : ¬ StrictMonoOn (B 183) (Ioo (-1) 0) :=
  fun h => B183_not_monotoneOn h.monotoneOn

/-- A second, entirely rational certificate of the failure on `(-1,0)`. -/
theorem B183_two_point_certificate :
    (-2 / 3 : ℝ) ∈ Ioo (-1) 0 ∧ (-3 / 5 : ℝ) ∈ Ioo (-1) 0 ∧
    (-2 / 3 : ℝ) < -3 / 5 ∧ B 183 (-2 / 3) = 13 / 243 ∧
    B 183 (-3 / 5) = 122 / 3125 ∧ B 183 (-3 / 5) < B 183 (-2 / 3) := by
  norm_num [B183_explicit]

theorem B_s0_two_not_monotoneOn : ¬ MonotoneOn (B (s0 2)) (Ioo (-1) 0) := by
  simpa only [s0_two] using B183_not_monotoneOn

theorem B_s0_two_not_strictMonoOn : ¬ StrictMonoOn (B (s0 2)) (Ioo (-1) 0) := by
  simpa only [s0_two] using B183_not_strictMonoOn

theorem B183_not_monotone : ¬ Monotone (B 183) :=
  fun h => B183_not_monotoneOn (h.monotoneOn _)

theorem B183_not_strictMono : ¬ StrictMono (B 183) :=
  fun h => B183_not_monotone h.monotone

/-- This particular counterexample still has exactly one real root. -/
theorem B183_factor (t : ℝ) :
    B 183 t = (t + 1) * ((t * (t + 1)) ^ 2 + (2 * t + 1) ^ 2) := by
  rw [B183_explicit]
  ring

theorem B183_quotient_pos (t : ℝ) :
    0 < (t * (t + 1)) ^ 2 + (2 * t + 1) ^ 2 := by
  by_cases hz : 2 * t + 1 = 0
  · have ht : t = -1 / 2 := by linarith
    rw [ht]
    norm_num
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hz)

theorem B183_zero_iff (t : ℝ) : B 183 t = 0 ↔ t = -1 := by
  rw [B183_factor, mul_eq_zero]
  have hn := ne_of_gt (B183_quotient_pos t)
  constructor
  · intro h
    rcases h with h | h
    · linarith
    · exact (hn h).elim
  · intro ht
    left
    linarith

end Stern
