# Complete companion Theorem T16.1

Source: companion_sections/cores.tex:549. The formal bound is stronger, with exponent min(1,2-eta), and covers all actual cardinalities at a common threshold.

Companion T16.1 is complete conditionally under the same three explicit
finite geometric inputs. The all-cardinality bound improves from
N^(-min(4/5,2-eta)+epsilon) to N^(-min(1,2-eta)+epsilon).
It holds for every actual subground of the full dyadic block and every
actual connected subpopulation with at least three elements and compatible
nullity at most eta*L. There is no upper cardinality cutoff. The proof in
fact allows every eta>=0; the source's nontrivial decay regime eta<2 is
included. Zero marginals and affine incompatibility are retained.

ConnectedParticipatingWindows.witnesses proves that each coordinate of a
connected family of cardinality at least two participates in an actual
relation. Its relation is allowed to depend on the chosen coordinate.
No simultaneous binary relation with full support is asserted or assumed.

ConnectedBoundedNullityTail.uniform_bound is unconditional. For fixed
eta,u,C,epsilon it selects a fixed integer s and then a common N threshold,
and bounds all actual connected families of cardinality at least s by
N^(-(2-eta)+epsilon). It applies the completed original participating
all-cardinality independent-weight tail to the exact heterogeneous weights
2*u*p_x, whose actual marginal cap is proved. The actual compatible-nullity
majorant contributes at most N^(eta+small margin), proved uniformly from
the critical window band and the actual rank cap. No geometric counting
input or homogeneous substitution for the actual marginals is needed in
this large-cardinality sector.

FixedConnectedWeightedUnderInputs.uniform_bound sums the completed full
fixed connected activity over every order from 3 to a prescribed R. The
weight u^r and the finite number of cardinality fibers are absorbed only
after R and u have been fixed. This includes incompatible systems, using
the completed T14.1 proof rather than a compatible-only estimate.

AllCardinalityConnectedUnderInputs.uniform_bound chooses s from the
unconditional large-cardinality theorem before selecting the finite
geometric parameter bundles for the remaining cardinalities 3<=r<s.
Only after these choices and the explicit geometric hypotheses does it
choose N0. An exact disjoint cardinality split and a fixed-factor
absorption give exponent min(1,2-eta), with one N0 for all actual grounds,
lengths in the critical band and all cardinalities. The final geometric
margins are epsilon/64 and epsilon/256 for two existing coarse parameter
bundles of order s, and sizeCap(epsilon/262144) for the existing pair-input
bundle. These premises are exactly previously recorded geometric
properties, not a desired activity bound. companion_T16_1 supplies the
literal printed exponent min(4/5,2-eta) by monotonicity.

Finding P1-MATH-0138 records the improved exponent and the coordinatewise
participation argument. Unconditional coverage remains 87/167; conditional
coverage increases from 22 to 23; confirmed improvements increase from
137 to 138. T16.2 and T16.3, sharp main15.10 and the final stopped expansion
are not claimed here. No original manuscript byte, external dependency,
axiom or Palomar registration is changed.

The JSON ledger and finding P1-MATH-0138 record the validation and exact proof commit.
