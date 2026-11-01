# Article Lemma 3.5 — Exact compression of the actual good edges

Source: Lemma 3.5, page 16, `p1:arith:compression`,
`main_sections/arithmetic.tex:230`. Original statement SHA-256:
`4b5ad33b5095a54af69a7b243e7e6c652772ff666d9271ec067e63cfe9fb126d`.
The original source bytes are preserved.

`GoodEdgeCompression.main_3_5` proves every source conclusion. The
deterministic `goodEdges H N L` consists of the unordered positive-mass
dependent pairs in the actual dyadic block, with the two leading slopes
and the source private-prime condition on their distinct normalized
values. The orientation x<y is chosen before forming the unordered pair.
Compatibility means positivity of the actual infinite-model joint moment.
Regularity is a proved consequence of the private-prime condition.

The complete window is exactly [x-1,x+L), with B=L+1 values. The
normalized union U=b*V_x union a*V_y is an ordinary finite set: coincident
normalized values are included once. Its zero-sum selection space is
literally the space of even subsets over F2, as checked by
`FiniteEvenSquareClasses.zero_sum_iff_even_selected`.

## Checked conclusions

- The actual parity map on the even selections of U is injective, and
  its range is exactly the sum of the two actual square-class spaces.
- Its rank equals card(U)-1, with the explicit finite bound
  rank >= (2-1/b)*L-1. No critical-band asymptotic is needed.
- At most (L+1)^2 fixed integer motifs occur. For one shared unit with
  offsets (i,j), U is a translate of
  {b*(v-i):0<=v<=L} union {a*(w-j):0<=w<=L}.
  Every motif lies in [-bL,bL]. In the leading slopes b<=4, this is
  a fixed logarithmic width.
- Once the offset pattern is fixed, the integer anchor
  b*(x-1+i)=a*(y-1+j) determines both centres uniquely.
  `NormalizedMotifs.anchor_injective` proves this parameter assertion;
  the argument does not merely represent an already chosen finite set.

## Proof and scope of the improvement

`EvenImage.image_eq_span_differences` proves a general zero-sum image
identity over an arbitrary division ring. Anchored difference generators
then prove the even-image union rule for intersecting finite sets.
Multiplication of every positive value by a common constant preserves
its even square-class image. Private prime coordinates prove injectivity
by evaluating the actual linear combination at one private coordinate.

`PrivateEvenImages` proves that a dependent pair under this condition
must have at least two normalized coincidences. Thus the good-edge
definition supplies the actual shared units; their existence is not an
extra rank or compression assumption. The channel lattice-point count
controls their number by 1+(L+1)/b and proves the finite lower bound.

The general `GoodEdgeCompression.finite_compression` only needs one
normalized coincidence and the private-coordinate property, along with
positive starts and positive coprime coefficients a<=b. Affine
compatibility, dependence, separation and a prior local-regularity
assumption are unnecessary for this finite compression. The latter
regularity follows from the same private coordinates. These finite
constants, the explicit pattern count and weaker hypotheses are
P1-MATH-0035.

Four elementary Paper C arithmetic modules are ported at an exact
commit and blob, with their original B=L+1 convention preserved and
all proofs recompiled under Lean v4.36.0-rc2. P1 passes (b,a) to their
channel equation a*i-b*j=h, because its normalized coincidence is
b*(x+i)=a*(y+j). See [reuse ledger](PAPER_C_REUSE.md).
The much larger Paper C rational-channel-code module is inspected but
not ported; the even-image/normalization proof here is new P1 code.

No good-edge count, mass asymptotic or pair-profile estimate is assumed
or proved by this compression lemma. Those are separate numbered results.
No revised manuscript or Palomar registration is made.

Validated implementation of article Lemma 3.5 and P1-MATH-0035:
[37c99c7ea71d70271902fd12d1b52494646ec919](https://github.com/Vulkin-prog/paper-p1-lean/commit/37c99c7ea71d70271902fd12d1b52494646ec919).
