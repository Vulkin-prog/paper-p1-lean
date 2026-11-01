# Companion T19.9 — Actual late population and quantitative inputs

Target: Proposition T19.9, page 72, `p1:limits:large-component`,
`companion_sections/limits_appendix.tex:474`. This numbered result is
**in progress**. Statement SHA-256:
`ef2ba2a70f7f7142acd1a2c4f2d8bb352f5e23ff835664fbad49b9d07150ab3f`.
No selected large component is yet counted as proved.

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

## Remaining source obligations

The next steps are to control the denominator in the actual peeling
rank density, instantiate the proved private-rank core theorem, and
transport its selected canonical component to an actual finite set of
original starts with its original infinite-model moments and square-class
nullity. Connectedness and compatible nullity must also be aligned. The
full size, quadratic-nullity and strict positive-activity conclusions,
with their common quantified asymptotic regime, remain open here.

Coverage stays 67/167 and confirmed findings stay 67. These are proofs of
inputs already used in the source, not a new independent mathematical
correction. No new Paper C port, external assumption, manuscript edit or
Palomar registration is introduced.
