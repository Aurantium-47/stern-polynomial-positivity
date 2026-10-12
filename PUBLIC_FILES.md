# Public file whitelist

Only the following files are intended for release. Paths are relative to this directory. Do not publish the parent workspace, source/review archives, caches, local compiler wrappers, raw compiler logs, rendered scratch images, or an enclosing Git history. No third-party article or thesis PDF is included.

```text
README.md
README_zh.md
STATUS.md
SOURCES.md
RELEASE_CHECK.md
PUBLIC_FILES.md
SHA256SUMS.txt
note.tex
note.pdf
check.py
check_results.json
BUILD.log
AXIOMS.log
lean/lean-toolchain
lean/lakefile.toml
lean/lake-manifest.json
lean/Stern.lean
lean/Audit.lean
lean/Stern/Basic.lean
lean/Stern/Index.lean
lean/Stern/Polynomial.lean
lean/Stern/Positivity.lean
lean/Stern/Counterexample.lean
```

`SHA256SUMS.txt` hashes every listed file except itself. The empty scratch directory, if present, is not part of the package. The release rights holder must choose the license for the newly prepared files separately; dependency licensing is described in `SOURCES.md`.
