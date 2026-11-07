# P1 version 1.7 - draft following the Lean formalization

This separate revision is dated 7 November 2026. The article and companion
retain their 167 labelled results. The version 1.6 package remains unchanged.

The draft integrates two necessary statement corrections:

- Companion T1.10 uses the alignment radius of the actual old enclosing
  interval, with the proved dyadic and expanded old-centre domains and the
  explicit large-prime cutoff interval. Its compressed-source applications
  use the same enlarged radius in their aligned sectors.
- Companion T5.1 includes the trivial exponent 1 in the minimum. The
  displayed exact affine comparison is then valid without an additional
  range restriction. The uncapped counting bound remains available.

The T19.17 proof now uses the internally proved sufficient two-smooth-integer
census. The formalization appendix describes the exact Gaussian comparison,
physical localization, scope of the result, and canonical declarations.
It also records the distinction from the stronger general sharp
short-average theorem and Dickman asymptotic.

The PDFs are in the pdf directory. The TeX sources and their source-only
SHA-256 manifest are in sources. Build both documents from the repository
root with:

    python3 scripts/build_manuscript_v17.py

The controlled builder disables shell escape, checks Ubuntu free space
before and after every pass, and waits for both documents' cross-references
to stabilize.

Check the preserved baseline and the revised inventory with:

    python3 scripts/check_revised_sources.py

After the revised statement aliases have passed their full validation:

    python3 scripts/check_revised_sources.py --require-proved

The separate revised proof ledger is docs/manuscript-results-v1.7.json at
the repository root. The original ledger continues to record both false
version 1.6 statements as such. The revision report is
docs/MANUSCRIPT_REVISION_V1_7.md. No Palomar registration is claimed here.
