# Companion T19.9 — An actual connected component of quadratic nullity

Target: Proposition T19.9, page 72, `p1:limits:large-component`,
`companion_sections/limits_appendix.tex:474`. This numbered result is
**proved**, including the original infinite-model moments. Statement SHA-256:
`ef2ba2a70f7f7142acd1a2c4f2d8bb352f5e23ff835664fbad49b9d07150ab3f`.
The source's single-family quantifier order is retained.

## Actual arithmetic population

Along N=2^(q-1), L=q-1, `LatePrimeStarts` uses the integer parameter
interval beginning at floor(3N/(2q))+5 and ending before floor(2N/q).
The actual starts are x=q*u+1, with neither u nor u+1 divisible by q.
The interval may be empty at small parameters; all finite statements
include that case. The actual cardinality satisfies

    N/(2q)-4N/q^2-8 <= card(starts) <= N/(2q)+1.

Every such start is dyadic and satisfies 3N+8q<=2(x-1). Every raw value
of its length-(q-1) window lies between 3N/2 and 2N. The construction
is a subset of the source late population, losing only bounded endpoint
choices before the residue exclusions. No hypothetical host count is
supplied as a premise.

`LatePrimeWindows` gives one explicit prime-sign sample making all
these starts active when q is prime. Every actual subfamily has positive
joint probability under the original infinite measure. The late position
excludes every exact leading 2:3 or 3:4 unit with a later dyadic window.
Consequently no good pair is contained in this population, independently
of its private-prime threshold.

## Actual prime support and rank

`LateWindowPrimes` proves a finite three-band cover for each prime divisor
of any n with 3N<=2n and n<2N. A multiplier is one, two, or at least
three, giving respectively the high, middle or low prime band. The
literal finite cover is

    primes <=floor(2N/3),
    primes in (floor(3N/4)-1, N],
    primes in (floor(3N/2)-1, 2N].

`ScaledPrimeCounts` transports the already proved inclusive PNT through
arbitrary asymptotically linear integer cutoffs. Floors, fixed natural
subtractions and the logarithmic ratio are included. `LatePrimeBudget`
therefore proves that the cover's actual cardinality is eventually at
most (17/12+eta)*N/log(N), for every eta>0. One threshold precedes all
finite raw-value subsets.

`RawPrimeRank` injects the actual raw square-class span into the coordinate
space on its actual prime set. Its dimension is at most that cardinality.
Every original run's effective row space lies in the image of that span
under the real finite-cylinder character map. Thus `LateWindowRank`
bounds the actual total finite-character rank of every subfamily by the
actual prime cover. No assumed rank or private-prime estimate is used.

## Regular population and peeling scales

`LatePrimePopulation.population` intersects the constructed starts with
the actual regular set. Its cardinality times q/N tends to 1/2. The proof
uses the finite count above and the already proved irregular-start count;
the scaled square-root error tends to zero. The critical band is exact
because log(N)/log(2)=q-1. The population is eventually nonempty, all its
local effective ranks equal L, and compatibility and absence of good
pairs survive restriction.

`LatePrimeRankDensity` uses the actual row spaces in the finite sample
space with cutoff 2N+q. A proved density envelope tends to

    D0=17/(6 log 2),

and bounds the actual total rank divided by the actual population size.
Its common sample solves all local original run equations.

`LatePeelingOrder` defines the literal integer t=Nat.log(2,L)/2. It tends
to infinity, is at most L and satisfies 2^t<=sqrt(L). The actual mass-loss
coefficient card(population)*2^(-L)*2^t is at most 2/sqrt(L) and tends to
zero. Neither a real order substituted for t nor an unproved growing-order
estimate appears.

## Actual peeling and transport to the source objects

`LatePeelingDensity.actual_density_envelope` proves positivity of the
literal denominator m-R/t and bounds the actual density by

    D(q) = envelopeDensity(q)/(1-envelopeDensity(q)/t(q)).

This explicit envelope tends to D0. `LateFiniteCore.actual_component`
instantiates every hypothesis of the proved private-rank peeling theorem
with the actual row spaces, common sample and integer order. It obtains
an actual part of the canonical relation partition after deletion, with
size at least L/D(q), nullity at least L^2/D(q)-L and positive centered
mass at least (1-loss(q)) times its positive joint mass.

`CanonicalPartConnected.part_connected` proves that each canonical part
is connected under restriction. A nontrivial relation-preserving cut
would refine the original finest partition. Coefficient and index
transport preserve this characterization. `CanonicalSquareClasses`
uses the explicit square-class/character equivalences to identify the
two actual canonical partitions, without a connectedness premise.

`FinitePartImage` turns a part of a finite subtype into a literal finite
set I of distinct natural starts. Its explicit equivalence preserves
cardinality, nullity, products and connectedness. `CommonRunMoments`
identifies the actual local witnesses with the common solving sample;
the exact heterogeneous marginals are unchanged. `FinitePartMoments`
and the existing cylinder integral transport then identify both original
infinite-model moments with the peeled component's moments.

`LateOriginalCore.actual_component` supplies an actual regular, nonempty,
compatible, connected family I. Positive joint mass gives equality of
compatible and full square-class nullities. No good pair is contained in
I, for any private-prime threshold. All component and transport claims
are proved, rather than supplied as assumptions.

## One fixed family and all asymptotic tolerances

`QuadraticComponent.selected` chooses one family for each q before any
epsilon is introduced. The explicit lower-bound coefficients are

    a(q)=1/D(q),   b(q)=1/D(q)-1/L,

and both tend to kappa=6 log(2)/17. The literal source conclusion is
`QuadraticComponent.companion_T19_9`, along the already proved nontrivial
odd-prime filter. It gives |I|>=a(q)L and rho(I)>=b(q)L^2 for this same
family, and the explicit strictly positive comparison

    c(I) >= (1-2/sqrt(L))*q(I) > 0.

`fixed_family_epsilon` also states both bounds with kappa-epsilon for
every epsilon>0 and the same selected family. No interchange of the
family choice and asymptotic tolerance is used. The witnessing cylinder
probability is not identified with the component joint probability.

Coverage is 68/167 (main 23/73, companion 45/94); confirmed improvements
stay 67. This closes the source argument with a quantitative constant
for its error term; no new independent mathematical correction is
counted. No new Paper C port, external assumption, manuscript edit or
Palomar registration is introduced.

Validated input checkpoint: [f4f13e7e119cced9399a101cabb825472f2c417d](https://github.com/Vulkin-prog/paper-p1-lean/commit/f4f13e7e119cced9399a101cabb825472f2c417d).

Completion validation: Lean v4.36.0-rc2 full build passed (9905 jobs); actual axiom audit passed for all 4713 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2428 distinct ledger/finding declarations were checked directly by Lean. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.72 GiB. Full T19.9 is complete, with a fixed family before every epsilon and the actual infinite-model moments. Coverage is 68/167 (main 23/73, companion 45/94); confirmed improvements remain 67. No target component assumption, external input, Paper C port, manuscript-byte change or Palomar registration.
