# Stern polynomial positivity and a monotonicity counterexample

This note proves, from the standard Stern recurrence, that

\[
B_{h_n}(t)>0\quad(n\geq0,\ t\in\mathbb R),\qquad
h_n=\frac23(2^{2n}-1)(2^{2n+1}+1)+1.
\]

It also proves that `B_183(t) = t^5 + 3t^4 + 7t^3 + 9t^2 + 5t + 1`, with derivative `-19/81` at `t = -2/3`. An exact pair of rational points in `(-1,0)` shows a decrease. These establish the assertion of Ulas's Conjecture 4.4 and disprove the final monotonicity clause of Conjecture 4.3 as stated in [arXiv:1909.10844v1](https://arxiv.org/abs/1909.10844v1).

The quadratic identity used in the proof already appears in Ulas's paper and is credited there. The general unique-real-root clause of Conjecture 4.3 is **not settled**. The example `B_183` itself has exactly one real root, `-1`.

The Lean project verifies the all-parameter positivity result and the counterexample, including the implication from a negative derivative to failure of monotonicity on `(-1,0)`. It proves pointwise real identities and integer-polynomial representability; it does not separately build a canonical integer-polynomial sequence or formalize root multiplicity.

- Read [the complete proof](note.tex), or `note.pdf` when present.
- Consult `STATUS.md` for the exact Lean theorem coverage, build results, and axiom dependencies.
- See [SOURCES.md](SOURCES.md) for attribution, source-access limitations, and redistribution boundaries.

To build the formalization with Lean and mathlib **v4.19.0**:

```sh
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
cd ..
```

The recorded local validation uses the installed Lean toolchain and existing mathlib dependencies. A fresh network download and build of the dependency graph has not been tested; see `STATUS.md` for the actual commands and scope.

For the supplementary exact-arithmetic checker, use Python **3.8 or newer** with no third-party packages (tested with Python 3.8.3):

```sh
python check.py
```

Its finite checks include `n = 0,...,20`; results are in `check_results.json`. These tests do not replace the general proof.

To compile the standalone note with a standard LaTeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error note.tex
pdflatex -interaction=nonstopmode -halt-on-error note.tex
```

The complete natural-language proof applies to all parameters; finite computation is supplementary. No priority claim is made: journal full-text access and the relevant 2025 thesis were unavailable, and the literature search was not exhaustive.

This work was prepared with AI assistance. No human expert peer-review claim is made.
