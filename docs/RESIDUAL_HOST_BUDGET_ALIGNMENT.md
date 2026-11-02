# Actual covered residual spaces: host counts and six-vertex packing

The prescribed-plane and unrestricted host assertions of T20.8 are
proved on the actual covered three-window relation space. For each
arbitrary cover, its unpinned components meeting all three blocks give
an exact finite family of pairwise disjoint transverse motifs. Their
natural products equal the component products used by T20.7, so their
small-prime square constraints are literal. Component-to-vertex-set
injectivity preserves their exact count. The finite small-prime rank
cost is uniformly below any fixed fraction of B.

Consequently, if any cover has residual dimension at least eta*L,
then the triple admits at least (eta/4)*B actual disjoint transverse
square products, eventually and uniformly in all covers. T20.6 then
gives N^(1+epsilon) hosts and N^(-1+epsilon) original affine mass on
every prescribed polynomial family of integer planes. The cover stays
inside an existential host predicate and is never enumerated. The
bound holds before primitive filtering, and hence for the literal
primitive mass as well. The real cutoff H=C0*B is retained exactly.

The unrestricted N^(3/2+epsilon) count of primitive triples is also
proved. In fact it follows from the stronger elementary fixed-order
count of all primitive hosts, without a residual-dimension premise.
A new exact finite conversion from unordered families to injective
center functions supplies the r! enumeration factor and works at
every fixed r>=2. It preserves the original primitive predicate.

The six-vertex packing calculation itself is now exact and checked:
6*dim(R_D)+|D| <= 3B+3*s(D)+18*(pi(H)+2), where s(D) is the literal
number of free transverse components of size at most five. Its real
form gives (3B-|D|)/6+s(D)/2+3*(pi(H)+2). This includes arbitrary
covers and pins. The remaining unproved part of T20.8 is the exceptional
mass N^(-1+epsilon) needed to bound s(D) by a fixed constant simultaneously
for every cover. That small-component exclusion still needs the
unrestricted degree-one geometric count. It is not inferred from
packing or from the planar proposition.

T20.8 moves from not started to in progress; coverage stays 79/167
(main 28/73, companion 51/94), with 97 confirmed improvements. These
are applications and exact interfaces for existing improvements,
not a new counted finding. No external premise, manuscript edit,
dependency download or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11107 jobs), actual axiom audit of all 7200 theorem/lemma declarations, direct Lean checks of all 4917 ledger/finding references, source integrity (138 manifest entries and 167 numbered statements), and git diff --check. Only propext, Classical.choice and Quot.sound occur. Ubuntu root space after verification: 14.91 GiB.
