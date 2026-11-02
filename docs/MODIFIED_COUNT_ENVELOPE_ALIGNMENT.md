# CompanionT19.3: actual direct maximum and all-order envelope

Source: `p1:limits:modified`. Status: **in progress** for the specified modified count and exceptional-event/coupling estimate.

The complete actual direct-maximum envelope used in the proof of
companionT19.3 is now constructed and bounded, unconditionally and
at every order. For any deterministic regular ground setG, letR be
the maximum cardinality of an active subfamily whose actual effective
square-class spaces have zero relative nullity. The maximum is an
actual random variable under the original infinite prime signs;
a maximizing family is proved to exist and R<=Z_G pointwise.
Its value is transported exactly through a concrete finite cylinder.
Every real observable ofR is integrable, and its Bochner expectation
equals the explicit finite probability sum. Tail probabilities are
identified as actual event probabilities too.

The finite counting principle is proved for any hereditary family
containing the empty set. Allr-subsets of a maximizing active member
remain admissible and active. Thus choose(R,r) is bounded pointwise
by the number of active admissible r-subsets. Taking actual finite
expectations gives the sum of their actual joint probabilities.
For actual direct regular windows, the already proved joint formula
is exactlyp^|I|, p=2^(-L), and is supplied as a checked equality.
It is not an arithmetic estimate or an assumed target moment bound.

Writingn=|G| andmu=np, which is proved equal to the actual count mean
onG, the following hold for everyN>=2, L>0, everyr>=0 and everys>=1:

    E choose(R,r) <= choose(n,r)*p^r <= mu^r/r!,
    E (R)_r <= mu^r,
    P(R>=r) <= mu^r/r!,
    E s^R <= (1+p*(s-1))^n <= exp((s-1)*mu).

The exponential estimate is proved by the full finite subset
generator of the actual maximizing member. No independence of the
random maximum, stochastic binomial domination or unproved moment
generating-function identity is assumed.

The actual shifted envelopeV=R+1 consequently satisfies, for allk>=1,
r>=1 ands>=1,

    P(V>=k) <= mu^(k-1)/(k-1)!,
    E (V)_r <= mu^r+r*mu^(r-1),
    E s^V <= s*(1+p*(s-1))^n <= s*exp((s-1)*mu).

The exact falling-factorial shift retains its repeated-index term.
The empty ground set, zero mean and orders beyond the ground size
are included. These are finite all-order inequalities; no fixed-order
asymptotic theorem is used uniformly at growing order and no BCN
input or limiting argument is needed.

These statements concernR and its envelopeV, not a bound of the full
original count byV. The paper's modified count, its structural
domination outside the specified exceptional event and the numerical
exceptional-event/coupling error still require the open core estimates.
They are not assumed or counted proved. CompanionT19.3 moves from
not_started to in_progress for those remaining parts.
No numbered completion is added: coverage77/167 (main28/73,
companion49/94), findings87 unchanged. No new mathematical finding,
external input, BCN premise, PaperC port, dependency download,
manuscript-byte change or Palomar registration is introduced.

Lean v4.36.0-rc2 full build passed (10755 jobs); actual axiom audit passed for all 6534 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4251 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.56 GiB. The maximum actual direct active subfamily is constructed, attained and bounded by the original regular count. Every real observable is integrable and transported exactly to a concrete finite cylinder. Actual direct regular-window joint equalities prove binomial/Poisson choose/factorial bounds, actual tail probabilities and binomial/exponential moment bounds at every order, for every N>=2,L>0. The shifted maximum has all source envelope inequalities, retaining the falling-factorial repeated-index term. No fixed-order theorem is used at growing order and no BCN or numerical probability estimate is assumed. The specified modified original count, structural domination and exceptional-event/coupling estimate remain open; T19.3 is in progress. Coverage77/167 (main28/73, companion49/94), confirmed findings87 unchanged. No new mathematical finding, external input, PaperC port, dependency download, manuscript-byte change or Palomar registration.
