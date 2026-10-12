# Sources and attribution

## Primary mathematical source

Maciej Ulas, *Strong arithmetic property of certain Stern polynomials*, [arXiv:1909.10844v1](https://arxiv.org/abs/1909.10844v1), 2019. Published in *Publicationes Mathematicae Debrecen* **96** (3–4) (2020), 401–422, [DOI: 10.5486/PMD.2020.8683](https://doi.org/10.5486/PMD.2020.8683).

The checked version is the 17-page arXiv v1 PDF. Relevant PDF pages are:

| Page | Material used |
|---|---|
| 2 | Standard Stern recurrence in the body of the paper |
| 9 | The family `s_(0,n)` in Theorem 2.6 |
| 12–13 | The integer sequence `h_n` and the quadratic identity in the proof of Theorem 3.1 |
| 16 | Conjectures 4.3 and 4.4 |

The quadratic identity is attributed to Ulas. Its rederivation here makes the connection to the defining recurrence explicit. Page references in the note are to the arXiv version. The journal metadata were checked, but the journal PDF request returned a subscription restriction page; no claim of page-by-page journal verification is made.

The recurrence follows the body of the source. The abstract contains a conflicting odd-index subscript. The proof does not rely on the later displayed substitution or the printed initial values on preprint pages 13–14.

## Background attribution

Sandi Klavžar, Uroš Milutinović, and Ciril Petr, *Stern polynomials*, *Advances in Applied Mathematics* **39** (2007), 86–95. This is the original Stern-polynomial reference cited by Ulas for the definition. The present proof is self-contained and does not require an unproved result from this article.

## Related literature and access limits

- David Altizio, *Zeros of Stern polynomials in the complex plane*, [arXiv:2511.03847v1](https://arxiv.org/abs/2511.03847v1), 2025. The accessible 27-page text was checked. Its results on zero-free regions and prime-index irreducibility do not by themselves establish the two conclusions of this note.
- David Altizio, *On Stern polynomials and their zeroes*, Ph.D. thesis, University of Illinois Urbana-Champaign, 2025. The [official thesis record](https://www.ideals.illinois.edu/items/136452) was checked. Full-text requests were inaccessible, so the thesis's coverage of these questions remains undetermined.

These checks do not establish literature priority. The full forward-citation literature was not exhaustively reviewed. This package does not claim a first resolution or a journal ranking.

## Redistribution and licenses

Third-party articles, thesis files, page images, and source text extracts are not part of this public package. Use the source links above to obtain them from their providers, subject to those providers' terms. Mathematical attribution is retained; no ownership of the cited authors' writings or diagrams is asserted, and this package grants no additional rights to their materials.

Any included Lean or checker source is distinct from the cited third-party articles. Lean 4 and mathlib 4, both at version 4.19.0, are licensed under Apache 2.0; their local license files were inspected. The upstream license texts are [Lean 4 LICENSE](https://github.com/leanprover/lean4/blob/v4.19.0/LICENSE) and [mathlib 4 LICENSE](https://github.com/leanprover-community/mathlib4/blob/v4.19.0/LICENSE). These dependencies are not redistributed in this package. Installing dependencies does not relicense them.

The release license for newly prepared files is unspecified. It must be stated separately by the releasing rights holder rather than inferred from the cited works or dependencies.

This work was prepared with AI assistance. No claim of human expert peer review is made.
