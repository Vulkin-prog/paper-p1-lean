# Companion T17.2: the complete actual retained-reference evaluation

Source: `p1:close:retained-reference`, `companion_sections/closure.tex:151`, page62. Status: **proved**.

CompanionT17.2 is now proved in full, including the literal source
cardinality coefficients, their binomial counts, every zero convention,
the total weighted deficits, actual signed-measure identity and ordinary
l1 estimate. The theorem holds for everyN>=2,L>0 and real cutoffH;
the critical-band instance needs no further asymptotic argument.

`directAt` is exactly the r-element subfamilies of the actual regular
set whose addition map is injective. `gamma` is exactly the h-element
subsets of G\e whose singleton spaces and the actual compressed block
are in direct sum. Both source interpretations are proved. The actual
complement counts equal

    choose(n,r)-#directAt(r),
    choose(n-2,h)-#gamma(e,h).

Their nonnegativity and the equality between natural subtraction and
the corresponding real difference are proved. The actual F_r is
p^r times the first difference. Each edge contributes to G_r its
actual joint moment times p^(r-2) times the second difference, with
G_0=G_1=0 by the literal r<2 guard. F_0=F_1=0, all coefficients
are nonnegative, and both sequences vanish for r>n.

An exact finite fiber partition by cardinality proves every polynomial
and weighted-mass regrouping. In particular the two subset-defined
deficit polynomials sum to

    sum_r scalar(F_r+G_r)*Delta^r,

and their independent masses are the exact source sums of2^r F_r
and2^r G_r. These totals are also proved equal to the infinite tsums,
using the verified zero tails. No finite/infinite grouping or binomial
coefficient convention is assumed.

`companion_T17_2` proves the literal retained-reference identity and
ordinary l1 bound. `companion_T17_2_measures` transports them to actual
atomic signed measures and the sum of absolute singleton masses.
The actual coefficients are Bochner joint moments of the original
infinite prime-sign model. All direct/compressed probability formulas,
affine-zero cases and unique-pair enumeration were proved internally
in the preceding finite checkpoint.

P1-MATH-0083 remains the heterogeneous finite extension. Its equal-
marginal specialization now has the complete source cardinality form.
No new mathematical finding, BCN input, literature premise, Paper C
port, dependency download, manuscript-byte change or Palomar
registration. Proved coverage77/167 (main28/73, companion49/94),
confirmed findings83.

## Validation

Lean v4.36.0-rc2 full build passed (10581 jobs); actual axiom audit passed for all6070 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All3787 distinct ledger/finding declarations were directly checked. All138 original manifest entries and167 numbered records are intact. Ubuntu available space:15.82 GiB. Literal source directAt and gamma definitions are proved equivalent to actual addition-map and compressed directness. Exact binomial complement counts, valid natural-to-real subtraction, nonnegative F_r,G_r, r=0,1 and r>n zero conventions, shifted-cardinality fiber grouping, both deficit polynomials and both independent weighted masses are proved. Ftotal,Gtotal equal the source infinite weighted tsums. companion_T17_2 proves the exact source reference identity and l1 bound, and companion_T17_2_measures proves their actual atomic signed-measure and absolute singleton-tsum forms. All probability coefficients are actual Bochner moments and all direct/compressed factorization and unique-pair enumeration steps are proved internally. The complete source theorem holds for everyN>=2,L>0 and realH, without needing a critical-band argument. T17.2 is proved. P1-MATH-0083 remains the heterogeneous finite extension; no new finding is added. Coverage77/167 (main28/73, companion49/94), confirmed findings83. No BCN input, new literature premise, Paper C port, dependency download, manuscript-byte change or Palomar registration.
