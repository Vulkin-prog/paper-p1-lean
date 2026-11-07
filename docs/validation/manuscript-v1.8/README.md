# Version 1.8 source and compiled-type checks

The full proof replay is recorded separately at
[checkpoint 0998](../checkpoint-0998/validation.json). This directory binds
the actual compiled types to the manuscript correspondence and preserves
source/metadata guard controls, the TeX build log and the PDF comparison.

Reproduce the source checks with:

```sh
python3 scripts/check_revised_sources_v18.py --require-proved
```

After building the pinned project, reproduce the type extraction into a new
working directory with:

```sh
python3 scripts/extract_manuscript_scope.py \
  --names docs/manuscript-v1.8-scope-declarations.json \
  --output-dir work/v1.8-replayed-scope
```

The diagnostic module creates no mathematical theorem. It reads actual types
and invokes Lean's axiom printer for every proposition. Its return code and
checksums are recorded. The axiom audit of all substantive theorems remains
the separate full-project check.

In this compiler's module system, public theorem signatures can be presented
as axioms to importing modules. The checker records both the exported form
and the original declaration kind using
[Lean.getOriginalConstKind?](https://lean-lang.org/doc/api/Lean/OriginalConstKind.html).
It also requires manuscript proof endpoints to occur in the source-discovered
theorem audit. The [module-kind control](module-kind-controls.json) distinguishes
two proved theorems from the genuine propext kernel axiom; exported signatures
are not treated as new mathematical assumptions.

The PDF review covers all 169 pages at contact-sheet level and 27 selected
complete mathematical/editorial pages at 110 dpi. It does not claim a detailed
visual reading of every changed page or an external human mathematical review.
