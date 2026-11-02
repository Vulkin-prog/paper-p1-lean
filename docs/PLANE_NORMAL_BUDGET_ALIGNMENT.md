# T20.4: actual planar supports and small integer normals

Companion T20.4 is proved for the literal population of distinct
offset triples supplied by shared odd-valuation primes above Y>=L+1.
The finite population is proved equivalent to the original prime/offset
description. A finite minimum vertex cover is defined and shown equivalent
to hitting every actual shared-prime hyperedge on the plane. Repeated
prime supports are included and counted once, as in the manuscript.

Let B=L+1 and let A be a primitive integer normal. Its Lean height is
max_i |A_i|, exactly the source infinity norm. For N>=10, B<=N+1,
dyadic centers, an injective first even-selection map and direct first
two square-class spaces, the checked finite bound is

    m_(A,Y) <= M_Y + 4 B^2 / ||A||_infinity,
    M_Y = 1 + log(6NB)/log Y.

This strengthens the source constant 6. No effective-rank condition on
the third window is needed for this finite estimate.

The proof uses a primitive integer direction obtained by dividing a
nonzero difference of two actual offsets by its content. Its height d
is at most B. Bezout coordinates for the primitive normal give integer
parallel-line levels. There are at most 1+2Bd/||A||_infinity levels,
and each line has at most 1+B/d integer points in the cube. Treating one
fibre with the checked M_Y line bound and the remaining fibres with
the cube bound gives M_Y+4B^2/||A||_infinity. No shortest vector,
Euclidean lattice basis, covolume theorem or unformalized geometric
count is assumed.

For fixed delta>0, uniformly after one critical-window threshold and
for all Y>=B, a minimum hyperedge vertex cover of size at least delta L
forces

    ||A||_infinity <= 16 B/delta,
    |h| <= 48 B^2/delta,

strengthening the source constants 24 and 72. The existing uniform
M_Y=o(B) estimate proves the needed small majorant; the existence of
an actual support bounds h. For each delta, a fixed integer K is chosen
before C and N. Every such (A,h) belongs to a finite box of at most
(2K+1)^4 B^5 integer planes. The complete aligned source statement is
PaperP1.OffsetPlaneNormalBudget.companion_T20_4; its full-rank and
pairwise directness assumptions specialize the stronger finite APIs.

No BCN premise or new external input is used. T20.4 moves from not
started to proved. Coverage becomes 78/167 (main 28/73, companion 50/94).
The improved constants and integer-fibre proof are recorded as confirmed
improvement P1-MATH-0095 for the next manuscript version. The weighted
dense nonaligned sector and the complete pair profile remain open.
No dependency download, original manuscript edit or Palomar registration
is introduced.

Verified under Lean v4.36.0-rc2: full lake build (11055 jobs), source and ledger checks, actual axiom audit of 7086 declarations (only propext, Classical.choice and Quot.sound), and 4803 direct ledger/evidence declaration checks; Ubuntu root free space 14.99 GiB. Original manuscript bytes and all 167 statement hashes preserved.
