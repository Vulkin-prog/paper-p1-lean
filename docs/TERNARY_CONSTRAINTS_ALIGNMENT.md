# Constraints meeting three blocks — companion T2.3

**Status: proved.** Source: companion V1.6, page 21,
`companion_sections/supplemental_arithmetic.tex:107`, label
`p1:arith:ternary-degree`. Exact statement SHA-256:
`f8e7ced365fdb9782d8b9ebfb18345eb41508ac34014ccb646872dfc355e995c`.

## Actual original and restricted rows

The input is an actual binary subspace R and a finite family of constraint
supports. The sum of its actual coordinate functionals on each support is
zero. A map to `Fin 3`, injective on each support, encodes at most one
occurrence in each of the three blocks. It proves the support size is at
most three; no row-cardinality conclusion is assumed in its place.

`finalLabels` restricts these same functionals to the space selected by T2.2.
`restricted_row_sum` proves their sum remains zero. `finalRows` intersects
each original support with the exact set of nonzero remaining labels.
Taking a finite image identifies repeated supports. `final_rows_checked`
proves the size bound, nonzero-label condition and zero sum after deletion.

## The three possible weights and binary components

`row_card_zero_two_three` excludes weight one and proves the alternatives
zero, two or three. `binary_labels_equal` proves equality of the two
nonzero labels on a binary row. `ternary_labels_injective` proves all three
labels on a ternary row are distinct; their actual sum remains zero.

`binaryGraph` is the simple graph of the binary supports. Labels are equal
along every actual graph walk and hence on every connected component.
`componentVertices` is its exact reachable-vertex set. Starting at any
remaining vertex, its cardinality is at most the multiplicity K of that
nonzero label. Deleted zero-label vertices are not included in this claim.

## Ternary incidence and the improved constant

`PairDecompositions.pairs` counts unordered two-element label subsets. For
each decomposition of the label at x, choose its first label once; the
second is determined. `assignedSupports` chooses one coordinate from each
of the two full label classes and forms the support with x. There are at
most K² such supports. Every actual ternary support incident to x is
proved to belong to this cover. There are at most d decompositions, giving

`number of ternary supports incident to x ≤ d K²`.

The full classes already include coordinates from both other blocks; a
second assignment factor is unnecessary. `companion_T2_3` retains the
original sufficient bound 2dK². `after_regularisation_sharp` gives the
improved constant with every original conclusion.

`companion_T2_3_exists` constructs the selected D by the proved T2.2 theorem,
including its exact codimension and active-coordinate budget. Thus no
regularizer output is an unproved premise. The general counting lemma
`ternary_degree_bound` uses only support size at most three, nonzero labels,
zero row sums and the two regularity bounds. A three-block coloring is
unnecessary for that more general statement. These improvements form
`P1-MATH-0012`; no optimality of dK² is claimed.

## Inputs and validation

All row transformations, unordered covers and counts are proved internally.
Mathlib at commit `9d581dfff2e41de989072ea63abf3daf69311520` supplies finite
product/image cardinalities and the definitions and induction of graph
walks. T2.2 is an internal proved input. No graph-degree bound, component
bound or arithmetic input is assumed. No further Paper C proof is ported.

The full Lean v4.36.0-rc2 build passed (8,771 jobs), followed by the actual
axiom audit of all 1,834 project theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Coverage is 25 / 167 numbered
results: 9 main and 16 companion. No Palomar registration is made.

Validated implementation for P1-MATH-0012:
[0f8350f2eecede15560958e20acac059f016bc05](https://github.com/Vulkin-prog/paper-p1-lean/commit/0f8350f2eecede15560958e20acac059f016bc05).
All 221 distinct coverage/finding declaration names were checked by Lean.
