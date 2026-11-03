# The primitive clause of main15.12 with stronger exponent7/5

Source: main_sections/exact_transfer.tex:776, second displayed bound and its final proof paragraph. The connected first bound remains open.

The primitive clause of main15.12 is now proved
UNCONDITIONALLY, with a stronger exponent7/5 instead of4/3.
It includes every cardinality at least256, and proves the
larger actual joint-plus-absolute-centered mass, as well as
the actual heterogeneous rank mass. Main15.12 moves from
not_started to in_progress because its separate CONNECTED
clause remains OPEN. Numbered coverage87/167 and20 conditional
results are unchanged. Confirmed improvement133 records the
stronger primitive tail and its shorter fixed-rank split.

MaximalSupportWord proves an elementary finite coding fact:
some binary codeword has weight at least the code dimension.
Choose a word of maximal support; restriction of the code to
that support is injective, since a nonzero kernel word has
disjoint support and increases the chosen support after
addition. The dimension is bounded by that restriction's
target dimension. For an even code and even t, dimension
at least t-1 therefore yields a word of weight at least t.
No pivot coordinates or simultaneous block support are
assumed or supplied as external data.

PrimitiveCoordinateProjection proves every coordinate
projection of a minimal effective relation kernel is
INJECTIVE. A kernel vector vanishing at that coordinate
restricts to the proper erased family; its nullity zero
forces the restriction to vanish, and extension by zero
recovers the whole vector. Hence every projection image has
dimension equal to the entire primitive nullity.
HeavyPhysicalRelations uses the previously proved
effective_projection_rank_le and the actual surjection
from physical even relations to effective relations.
The coding lemma then constructs an ACTUAL global physical
even relation with at least t selected values at any
prescribed block. PrimitiveAnchorWitnesses consequently
gives the literal15.11 witness predicate whenever
rho>=t-1. Different blocks may use different relations.
In particular every primitive has two-anchor witnesses,
and nullity at least9 gives ten-anchor witnesses.

PrimitiveIndependentBudgets supplies a uniform general
all-cardinality bound from the PROVED15.11 budgets,
using actual independent weights u*p_x and the
unconditional cap p_x<=2*2^C/N. Two explicit specializations
start at cardinality256:
  t=2,A=14,b=59/70,sigma=93/100:
    delta=11/1000, theta=1/7,
    moderate exponent=-7/5,
    saturated exponent=-176/125.
  t=10,A=12,b=31/60,sigma=23/25:
    delta=29/750, theta=5/6,
    moderate exponent=-7/2,
    saturated exponent=-1856/375.
The strict cutoff and graph gaps are verified by exact
rational arithmetic. Both estimates have one threshold
before all sizes, lengths and actual primitive populations.

Primitive256RankTail splits ONLY at the FIXED integer
nullity9. When rho<9, rank amplification is at most2^8=256,
so the two-anchor independent bound gives rank mass
N^(-7/5+epsilon). When rho>=9, the ten-anchor independent
bound applies, and the already proved primitive inequality
rho<=L costs at most2^L<=2^C*N. That branch has the stronger
rank mass N^(-5/2+epsilon). The exact finite filtered sum
then proves the FULL primitive rank mass at every
cardinality at least256 is N^(-7/5+epsilon).
No comparison rho versus a growing fraction of L, no
core deletion, compatibility split, or cardinality upper
cutoff is needed for this primitive argument.

PrimitiveActualMass extends the exact centered-to-rank
comparison to ALL actual marginal patterns. If some actual
marginal is zero, the existing finite probability transport
proves its whole centered coefficient is zero. Otherwise
the actual heterogeneous Fourier inequality applies.
Together with the already proved joint inequality this
gives q(I)+|c(I)|<=2*rankWeight(I), including contacts,
local irregularities, affine incompatibility and zero
marginals. The ground is the FULL dyadic block, with no
regularity filter or separation assumption.

Primitive256Tail.uniform_actual and uniform_centered prove
the stronger all-size exponent7/5. The named
article_15_12_primitive proves the literal printed4/3
bound for all primitive sets of cardinality>256 above
ANY actual ground subset of the dyadic block. It therefore
includes every source-family restriction in the paper.
The independent per-block weight remains fixed before N.
No geometric property, desired arithmetic mass, or new
axiom is an input. The connected part of15.12 is not
claimed, and the all-size T14.2 total still has its recorded
conditional small-size step. No original manuscript byte,
dependency download, Paper C port or Palomar action changes.

The JSON result row and finding133 record full validation and the exact proof commit.
