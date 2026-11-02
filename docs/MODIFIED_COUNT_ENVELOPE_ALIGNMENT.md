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


## Regularity-free direct maximum and shifted envelope

Regularity is unnecessary for the actual direct-maximum moment
envelope. The same constructedR andV=R+1 now have every-order
Poisson-type bounds on ANY finite actual ground setG, using

    p_x = actual infinite marginal atx,
    mu = sum_(x inG) p_x.

The displayed mu is proved equal to the actual original count mean
for every dyadic ground subset. No nominal substitution is used.
The statements require onlyL>0; there is no critical band, BCN input,
positive-local-marginal requirement or regularity assumption.

The actual direct-family joint identity is proved in full scope:

    rho(I)=0 => q(I)=product_(x inI) p_x.

If all local marginals are positive, the existing direct Fourier
identity applies. If one marginal is zero, its singleton joint bound
forces the whole joint mass zero, and the product has that zero
factor. The empty family is included. Thus even local impossibility
is handled by the actual model, not by assuming consistency or
removing windows before the argument.

A finite all-order heterogeneous counting theorem first gives
E choose(R,r)<=e_r(p). The elementary symmetric inequality
r!*e_r(p)<=mu^r is proved by finite ground-set induction and a
nonnegative binomial lower bound, with no moment estimate as input.
The actual full subset generator gives

    E s^R <= product_(x inG) (1+(s-1)*p_x)
          <= exp((s-1)*mu)       (s>=1).

It follows for everyr>=0 that E(R)_r<=mu^r and
P(R>=r)<=mu^r/r!. ForV, every positive-order factorial moment is
at mostmu^r+r*mu^(r-1), its tail is at most
mu^(k-1)/(k-1)! for everyk>=1, and

    E s^V <= s*product_(x inG)(1+(s-1)*p_x)
           <= s*exp((s-1)*mu).

The bounds concern actual Bochner integrals and actual infinite-law
event probabilities, using the previously checked observable
integrability and exact finite-cylinder transport. No generating
function is asserted to be a distribution without construction.
All natural orders, zero means, zero marginals and empty ground sets
are included, without a growing-order asymptotic substitution.

P1-MATH-0088 records removal of regularity for this direct-maximum
envelope part ofT19.3. This does not remove regularization from the
full approximation theorem, or prove domination of the full original
count byV. The specified modified count, exceptional-event structure
and numerical coupling/error estimate remain open;T19.3 stays in
progress. Coverage77/167 (main28/73, companion49/94), findings88.
No new external input, BCN premise, PaperC port, dependency download,
manuscript-byte change or Palomar registration is introduced.

Lean v4.36.0-rc2 full build passed (10761 jobs); actual axiom audit passed for all 6555 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4272 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.56 GiB. Actual direct-family joint factorization is proved for all finite actual ground sets, including zero marginals. The constructed maximum and its shifted envelope have all-order elementary-symmetric, Poisson factorial/tail and heterogeneous product/exponential bounds with the exact sum of actual marginals. This sum is identified with the actual dyadic count mean. All integrals and probabilities are transported through the actual finite cylinder; no regularity, critical band, BCN or unproved numerical estimate is assumed. P1-MATH-0088 records the regularity-free envelope extension. The specified modified count, structural domination and numerical exceptional-event/coupling estimate remain open; T19.3 stays in progress. Coverage77/167 (main28/73, companion49/94), confirmed mathematical improvements88. No new external input, PaperC port, dependency download, manuscript-byte change or Palomar registration.
