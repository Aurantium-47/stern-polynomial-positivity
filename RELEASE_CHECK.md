# Release verification record

Verified locally on 2026-10-13. This record describes this package only.

| Check | Result |
|---|---|
| Lean compiler | 4.19.0, release commit `6caaee842e94` |
| mathlib | `v4.19.0`, revision `c44e0c8ee63ca166450922a373c7409c5d26b00b` |
| Library build | Five modules plus aggregate compiled, exit 0 |
| Theorem axiom audit | 39 declarations; only subsets of `propext`, `Classical.choice`, `Quot.sound` |
| Source scan | No admitted proofs or ad hoc axiom declarations |
| Released Lean files | Byte-for-byte identical to the compiled project sources/configuration |
| Exact checker | Passed under Python 3.8.3, standard library only |
| LaTeX | Final direct `pdflatex` compilation exited 0 |
| PDF | 5 pages, 354,697 bytes; all fonts embedded |
| PDF layout/reference check | No unresolved references, citations, or overfull/underfull box warnings |
| Disclosure scan | No prohibited service/model names, private paths, or private conversation links in public text, extracted PDF text, or PDF metadata |
| Packaging | Explicit `PUBLIC_FILES.md`; per-file hashes in `SHA256SUMS.txt` |

The theorem audit and build results are preserved in `AXIOMS.log` and `BUILD.log`. The recorded build commands used a local wrapper around the pinned Lean executable and existing read-only mathlib artifacts. The public source/configuration supports the standard Lake commands in the READMEs; a fresh network installation was not separately tested.

The initial `latexmk` attempt was unavailable because Perl was absent. Direct `pdflatex` produced the final PDF successfully. The local TeX installation emitted operating-system support and update-check notices; these did not prevent compilation. Raw compiler logs contain environment paths and are excluded from the public package.

This directory is prepared for local inspection, without a remote repository or publication action. The newly prepared files have no release license assigned; the releasing rights holder should choose one. Upstream mathematical attribution and dependency-license references are preserved in `SOURCES.md`.
