# Verified scope and build status

Date: 2026-10-13. **COMPLETE for the requested mathematical claims.**
The general unique-real-root assertion in Conjecture 4.3 is not established or disproved.

## Definitions and scope

`Stern.B n t` is defined by terminating recursion on the natural index, with base values 0 and 1 and the standard even/odd Stern recurrence. It is not defined by the desired quadratic formula. `B_integer_polynomial` constructs an integer polynomial representing each function `B n`.

`Stern.h n` is the source's integer index:

```text
2 * (2^(2*n) - 1) * (2^(2*n+1) + 1) / 3 + 1
```

Here `/` is natural-number division. `h_source_exact` proves equality, after casting to the rationals, with the literal source formula `(2/3)*(2^(2*n)-1)*(2^(2*n+1)+1)+1`; no rounding or replacement sequence is assumed. The internal helper `a` is proved equal to `(4^n-1)/3` by `a_eq_source`.

The identities are formalized pointwise at real arguments. The polynomial bridge gives existence in `Polynomial ℤ`; the project does not construct a canonical polynomial-valued sequence and then prove coefficient equalities in that type. This representation suffices for every real-valued assertion below.

## Theorems checked by Lean

All names below have prefix `Stern.`.

| Claim | Theorem names |
|---|---|
| Defining recurrence, all applicable indices | `B_zero`, `B_one`, `B_even`, `B_odd` |
| Integer-polynomial representation | `B_integer_polynomial` |
| Exact source index and helper identity | `h_source_exact`, `a_eq_source`, `h_eq`, `four_pow`, `two_pow_even` |
| Binary concatenation, including both endpoints | `concatenation` |
| Adjacent values do not vanish together for nonzero real argument | `adjacent_nonzero` |
| Odd indices evaluate to 1 at zero | `adjacent_sum_zero`, `B_odd_zero` |
| Quadratic identity derived from the recurrence | `quadratic_aux`, `h_quadratic` |
| Sum of squares and zero-argument boundary | `h_sum_of_squares`, `h_at_zero` |
| Strict positivity for every `n : ℕ` and `t : ℝ` | `h_positive` |
| No real root for every `n : ℕ` | `h_no_real_root` |
| Source subfamily index `s0 2 = 183` | `s0_two` |
| Actual recurrence expansion of `B 183` | `B183_explicit` |
| Derivative formula and exact value `-19/81` at `-2/3` | `B183_hasDerivAt`, `B183_deriv`, `B183_hasDerivAt_neg_two_thirds`, `B183_deriv_neg_two_thirds` |
| Negative derivative at an interior point contradicts nondecreasingness | `not_monotoneOn_of_hasDerivAt_neg` |
| Failure of nondecreasing and strictly increasing behavior on `(-1,0)` | `B183_not_monotoneOn`, `B183_not_strictMonoOn`, `B_s0_two_not_monotoneOn`, `B_s0_two_not_strictMonoOn` |
| Failure of both notions on the whole real line | `B183_not_monotone`, `B183_not_strictMono` |
| Exact decreasing pair `-2/3 < -3/5` | `B183_two_point_certificate` |
| This example has exactly the root `-1`; derivative there is 1 | `B183_factor`, `B183_quotient_pos`, `B183_zero_iff`, `B183_deriv_neg_one` |

The proof of `h_positive` includes `n=0` and `t=0`. It uses the derived quadratic identity and the adjacent-value theorem. No finite computation substitutes for that universal proof. The nonmonotonicity theorem is deduced directly from the negative derivative through the limit of right-hand slopes; the rational pair is an additional independent certificate. The nonzero derivative at `-1` supports the note's simple-root claim; a separate algebraic root-multiplicity API theorem is not included.

## Actual checks

- Lean 4.19.0, Windows release; mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b` (tag `v4.19.0`).
- All five modules, aggregate `Stern.lean`, and `Audit.lean` compiled with exit code 0. Full command/output record: `BUILD.log`.
- Every theorem in these modules was audited with `#print axioms`. `AXIOMS.log` records only subsets of `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, ad hoc axioms, or native-evaluation axioms occur.
- The standalone Python checker passed using only exact integer and rational arithmetic. Its quadratic checks cover `0 ≤ n ≤ 20`; they are finite consistency checks. See `check_results.json`.
- The English LaTeX note compiled to PDF. Compiler details are recorded in the release verification record.

The actual local build reused the installed Lean executable and already compiled mathlib dependencies read-only, while producing all project `.olean` files in the new project's own build directory. The saved manifest pins dependency revisions. A fresh dependency download and source build in a new environment was not run during this check.

## Reproduction

With Lean/elan installed and network access, use the pinned standard Lake project:

```sh
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
cd ..
python check.py
pdflatex -interaction=nonstopmode -halt-on-error note.tex
pdflatex -interaction=nonstopmode -halt-on-error note.tex
```

The optional cache step downloads precompiled mathlib dependencies; `lake build` can build dependencies from source instead. `lean-toolchain` and `lake-manifest.json` preserve the version choices.

## Remaining boundaries

There are no unfinished formal obligations for the two requested claims. The general unique-real-root assertion of Conjecture 4.3 remains open within this work. Literature priority is unconfirmed; the journal full text and the 2025 thesis were inaccessible, and forward citations were not exhaustively checked. No first-priority, human expert review, or journal-ranking claim is made.

The package is prepared locally for inspection. Publication, remote repository creation, and licensing of the newly prepared files are separate release decisions. Third-party source texts and PDFs are excluded from the public whitelist. This work was prepared with AI assistance.
