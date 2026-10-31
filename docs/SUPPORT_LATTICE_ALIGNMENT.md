# Companion T19.1: support and factorial lattice

**Status: proved**, the complete proposition. Coverage is 15 / 167:
8 / 73 main and 7 / 94 companion. Original locator: companion V1.6,
page 67, `p1:limits:lattice`, `companion_sections/limits_appendix.tex:17`.
The source statement hash and all manuscript bytes are unchanged.

## Exact deterministic support

`RunSeparation.startEvent_separated` proves directly for any binary value
function that two distinct active starts x<y satisfy x+L≤y. If y<x+L,
both y-1 and y are inside the first constant run, contradicting the opposite
sign prescribed at the later boundary. Complete multiplicativity is not
needed for this deterministic step.

`infiniteStartIndicator_separated` instantiates that fact for the actual
infinite prime-sign model. Its active-start set has cardinality equal to
`infiniteStartCount`; no zero-probability outcome is discarded.

`SeparatedPacking.card_separated_interval` maps a separated set in [U,U+N)
injectively to the integer quotient bins floor((x-U)/L). It proves the exact
cardinality bound, and `ceil_ratio_eq` proves

`ceil((N:real)/L) = (N-1)/L + 1`

for positive natural N and L. The quotient on the left is real, and that on
the right is natural division; their rounding equality is proved explicitly.

`dyadic_count_support` gives the literal source assertion

`0 ≤ Z_N(ω) ≤ ceil(N/L)`

for every sample ω, every N≥2 and every L≥1. This is stronger than an almost
everywhere assertion and uses no critical-band or regularity hypothesis.
`dyadicCountLaw_coeff_eq_zero_above_support` and
`dyadicCountLaw_support_subset` transport it to the actual count-law
coefficients and their finite support.

## Exact binary probability lattice

`Affine.uniformSolutionMass_integer_multiple` proves that an affine binary
system with effective rank at most m has probability

`k * (2^m)^(-1)` for some actual natural k.

If the system is incompatible, k=0. Otherwise its rank is r≤m and the
proof takes k=2^(m-r), checking the exact power identity and division.

The simultaneous start prescriptions on a finite I have codomain
`I × Fin L → F₂`, whose dimension is proved to be |I|L. Their rank is at
most that dimension. `joint_moment_nominal_lattice` therefore proves

`q(I) = k_I p^|I|`, with k_I a natural number and p=2^(-L).

Here q(I) is the actual infinite-measure joint probability, transported
exactly to a sufficiently large cylinder inside the proof. Every window is
retained, including irregular windows, heterogeneous marginals and all
incompatible joint systems. The nominal p is the lattice scale, not an
assertion that every individual probability equals p.

## The factorial j! factor

`SubsetFactorials.powersetCard_activeSites` identifies the active j-subsets
with the corresponding filter inside all j-subsets of the ground set.
Their cardinality is the binomial coefficient of the active count.
The proved natural identity `(z)_j=j! choose(z,j)` gives the pointwise
`factorial_subset_expansion`.

`RunCountLattice.factorialCountMoment_eq_subset_sum` integrates this exact
identity under the actual infinite model:

`E[(Z_G)_j] = j! sum_{I subset G, |I|=j} q(I)`.

Substitution of the actual natural coefficients k_I gives
`factorial_count_lattice`. The complete `companion_T19_1` theorem states
both deterministic support and, for every j≥1,

`E[(Z_N)_j] = j! * p^j * m` for some m : natural.

This is exactly membership in the source's nonnegative integer lattice.
No divisibility conclusion is inferred merely from ordered-tuple counting;
the j! factor is proved by the unordered-subset expansion. The auxiliary
identity also includes zero order and deterministic subsets of the dyadic
block, with their exact actual moments.

## Validation

Lean v4.36.0-rc2 and the pinned matching Mathlib are used. The full build,
source checks and actual 1,350-declaration kernel audit are run before
publication, allowing only `propext`, `Classical.choice` and `Quot.sound`.
No new external mathematical input, Paper C port or mathematical correction
is introduced. No Palomar registration is made.
