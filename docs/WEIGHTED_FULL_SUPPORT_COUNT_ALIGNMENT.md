# Unconditional completion of companion T22.1

Source: `companion_sections/uniform_appendix.tex:21`, including the actual separated regular lists, the exact factorial quotient and all orders.

Companion Proposition T22.1 is now proved UNCONDITIONALLY,
including the literal ordered-list sum with weights u^r/r!
and nominal factor p^r, p=2^(-L). The actual manuscript list
population requires distinct dyadic starts, full effective
support, rank L at every window, and pairwise distance greater
than L. FullSupportOrderedLists.mem_manuscriptLists identifies
all these actual conditions. No minimality or affine
compatibility is imposed. The printed bound is exactly
N^(-2*s/(2*s+1)+epsilon) for each fixed s>=2.
T22.1 moves from not_started to proved. Unconditional numbered
coverage rises from83 to84/167; the16 conditional results stay
separate. P1-MATH-0128 records a stronger N^(-1+epsilon) bound.

FamilyEnumerationUpper proves the reverse factorial inequality
by injecting actual ordered tuples into their actual finite
family and the permutation of its canonical enumeration.
Together with the previously proved forward injection it gives
the exact identity #lists=r!*#unorderedFamilies. It includes
empty and singleton orders as well. FullSupportOrderedLists
proves the exact cardinality identity for the real full-support
tuple population, cancels the actual factorial, and identifies
the sum over all orders with the actual unordered family sum.
The nominal-weight formula is exactly the expression printed
in T22.1. The manuscript population is a proved subset of this
larger actual list population, so its weighted count follows
without a counting assumption.

OriginalParticipatingMass.fixed_mass proves independent mass
at most N^(-r/2+epsilon) at each fixed order r, for arbitrary
nonnegative heterogeneous weights bounded by M/N and actual
coordinatewise participating families. It uses the proved
relative half-count with no old sources, and the actual family
inclusion, not a supplied desired host estimate.
OriginalParticipatingMass.uniform_mass combines these finitely
many fixed-order bounds with OriginalParticipatingTail's uniform
all-cardinality tail. The small-order cutoff is chosen before N;
only the finitely many orders below that cutoff use their own
fixed-order thresholds. The large orders use the already proved
uniform certificate generator. The total mass of ALL such
families of size at least two is at most N^(-1+epsilon).
The threshold precedes every actual weight function and family
population; zero weights and all actual overlaps are allowed.

FullSupportWeightedCount.uniform_ordered_mass specializes to
the nominal constant weight u*2^(-L), whose cap is proved from
the critical-band condition. It gives N^(-1+epsilon) for the
larger actual injective full-support list population, without
regularity or separation, with one threshold before EVERY
cutoff s>=2. The stated source exponent follows because
2*s/(2*s+1)<=1. FullSupportWeightedCount.companion_T22_1 then
restricts to the literal separated regular manuscript lists.

The strengthening concerns INDEPENDENT product weights. It
does not establish positive joint or centered masses containing
the factor2^rho, nor the separate compressed-block assertion of
main15.8. No geometric input, dependency download, PaperC port,
original manuscript edit or Palomar registration is added.

The JSON result row and finding128 record full validation and its exact proof commit.
