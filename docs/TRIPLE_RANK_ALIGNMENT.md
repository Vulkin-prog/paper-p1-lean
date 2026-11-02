# Actual triple rank and maximum joint probability under explicit BCN

Source: article13.8, `p13:rig:triple`, `main_sections/pair_rigidity.tex:355`. Status: **conditional**.

All three source conclusions of article13.8 are now proved under
the same ordinary explicit field-polynomial BCN input as13.5 and13.6.
The external BCN proof and geometric presentation remain unformalized;
this row is conditional and adds no proved numbered coverage.

The actual finite-dimensional relation spaces satisfy

    rho({x,y,z}) <= L + min(d_xy,d_xz,d_yz).

This is proved from actual insertion-nullity and pair-intersection
identities, not assumed. Every actual three-element set can be
reconstructed from any two of its distinct members. Known alignments
use the proved compatible half-window bound13.7, including exact
contact; nonaligned pairs use the proved reduction13.6 under BCN.
The actual enlarged alignment predicate is transported with exact
coefficient heights. The B=L+1 to L conversion is proved uniformly.
Thus compatible triple nullity is at most(3/2+epsilon)L. A triple
containing a nonaligned pair has nullity at most
(1+(2/3)log2+epsilon)L, even without compatibility.

The probability step can be shortened. The proved critical local
rigidity gives the actual cap p_x<=2*2^(-L), including zero marginals.
The exact compatible pair identity, and a separate zero-mass case,
give the unconditional finite bridge

    q(I) <= q({x,y}) <= 4*2^(-2L+d_xy)

whenever I contains distinct x,y with the stated local marginal caps.
The cap itself is proved uniformly for all actual dyadic starts.
No third-window rank or marginal estimate enters this step.
The exponential identity for this finite mass, the exact critical
band error and absorption of its fixed constant into N^epsilon are
proved. Under the same BCN input, one threshold precedes all actual
families of cardinality at least2, giving q(I)<=N^(-3/2+epsilon),
with no order bound or compatibility restriction. In particular all
actual triples satisfy the source probability bound. An actual finite
maximum over the three-element subsets is constructed by a zero-
adjoined max fold and satisfies the same uniform estimate.

P1-MATH-0081 records the shorter pair-based probability proof, explicit
finite factor4 and extension to every larger family. P1-MATH-0082
records removal of compatibility from the stronger nonaligned-triple
rank bound. Neither claims an improved N exponent or a proof of BCN.
Proved coverage76/167 (main28/73, companion48/94), confirmed findings82.
No added Paper C source, dependency download, manuscript-byte change
or Palomar registration.

## Validation

Lean v4.36.0-rc2 full build passed (10561 jobs); actual axiom audit passed for all5988 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All3705 distinct ledger/finding declarations were directly checked. All138 original manifest entries and167 numbered records are intact. Ubuntu available space:15.85 GiB. Actual triple insertion/nullity, the minimum pair-rank bound, reconstruction from any pair, the exact critical local marginal cap and the finite pair/family probability bound with factor4 are proved without BCN. The B=L+1 to L conversion, exact binary-mass exponential identity and critical N-exponent absorption are proved. Under the same single field-polynomial BCN input as13.5 and13.6, all compatible pairs have a uniform half-window rank bound, all compatible triples have nullity<=(3/2+epsilon)L, every triple containing a nonaligned pair has the stronger1+(2/3)log2 bound without compatibility, and every actual family of cardinality>=2 has joint mass<=N^(-3/2+epsilon). The literal finite triple-probability maximum is constructed and bounded. P1-MATH-0081 and0082 record the larger-family probability proof and compatibility-free nonaligned-triple scope. BCN itself and its geometric presentation remain unformalized;13.8 is conditional, not proved coverage. Coverage76/167 (main28/73, companion48/94), confirmed findings82. No added Paper C source, dependency download, manuscript-byte change or Palomar registration.
