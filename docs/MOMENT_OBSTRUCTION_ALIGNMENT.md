# Companion T23.1: the exact positive moment perturbation

**Status: proved**, every assertion of the numbered proposition.
At this checkpoint coverage is 20 / 167: 9 / 73 main and 11 / 94 companion.
Original locator: companion V1.6, page 93, `p1:obstruction:fixed`,
`companion_sections/moment_obstruction.tex:8`; statement hash
`c652d9e1cd007089e2c95a960fa33e1d963832a5f3da703257669a40da70cc64`.

## Actual probability laws and exact perturbation

`MomentObstructionMass.qMass` is the already proved quadratic reference at
mean one. `qLaw_signed_identity` identifies its actual probability measure
with `QuadraticPoisson.reference 1 a`. The scalar definitions are literally

`c(a)=(1-a/2) exp(-1)`, `epsilon(m,a)=c(a)/(2 m!)`.

`pMass` adds epsilon times the actual coefficient of Δ^m. The finite
convolution ring embeds injectively into actual signed measures;
`pLaw_signed_identity` proves the full signed-measure identity
`P=Q+epsilon Δ^m`. `AtomicProbability.ofMass` constructs canonical actual
probability measures from the proved nonnegative, normalized singleton masses.

The integer minimum from Lemma 8.1 gives `Q{k}≥c(a)/k!`. The exact finite
difference coefficients are

`(Δ^m){k}=(-1)^(m-k) choose(m,k)`.

The binomial-factorial identity bounds their absolute value by m!/k!.
It follows that `|epsilon(Δ^m){k}|≤Q{k}/2`. Thus every singleton satisfies
`Q/2≤P≤3Q/2`, including indices outside the perturbation support. The
perturbation has sum zero for every m≥1, so P has mass one.

## Factorial moments and their actual integrability

`FactorialGeneratingPolynomial.transform` is the ordinary generating
polynomial evaluated at 1+t. It sends Δ^m to t^m. The coefficient formula
therefore gives the exact finite identity

`sum_k (Δ^m){k} (k)_j = m! if j=m, and 0 otherwise`.

The infinite laws require a separate integrability argument. The proved
exponential series gives the exact Poisson sum, then the shifted-mass
identities give

`sum_k Q{k} exp(tk)=exp(exp(t)-1)(1+(a/2)(exp(t)-1)^2)`.

Every real t is allowed. The elementary bound `(k)_j≤j! exp(k)` proves
integrability at every factorial order for Q. The finite perturbation
proves it for P as well. `factorial_moment_difference` is an equality of
actual Bochner expectations, equal to epsilon m! at order m and zero at
all other orders. At the changed order the difference is c(a)/2.
For a<2 it is strictly positive, and `factorial_moment_eq_iff` proves that
equality occurs exactly at orders j≠m, also for orders larger than m.

## Exact distance and uniform exponential control

The finite coefficient calculation proves `||Δ^m||₁=2^m` exactly.
The full actual singleton distance therefore gives

`TV(P,Q)=(1-a/2) 2^(m-2)/(exp(1) m!)` for m≥2.

Here TV is half the ordinary countable sum of absolute singleton mass
differences, exactly the manuscript convention. No bound is substituted for
the norm in this equality.

The pointwise bound P≤3Q/2 and the exact exponential sum prove, uniformly
in every m and every 0≤a≤A≤2,

`E_P exp(tX)≤(3/2) exp(exp(t)-1)(1+(A/2)(exp(t)-1)^2)`.

The source's original bound is the literal A=1 specialization.
`companion_T23_1` combines pointwise bounds, both laws' factorial
integrability, equality exactly off order m, the exact distance and the
original uniform exponential bound for m≥3 and 0≤a≤1.

## Confirmed parameter extension

The same construction works on 0≤a≤2. It remains a nonzero perturbation
for a<2; at a=2 epsilon is zero, so P=Q and all moments agree. The distance
formula and the pointwise factors 1/2 and 3/2 remain unchanged. The uniform
exponential bound on the larger interval uses A=2. This is `P1-MATH-0009`;
no error in the original statement is claimed. The original A=1 estimate is
retained separately, rather than asserted unchanged on the larger interval.

## Validation and remaining scope

The full Lean v4.36.0-rc2 build passed (8,727 jobs), followed by the actual
axiom audit of all 1,647 project theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Original manuscript identities
remain checked separately. There is no unproved external probability input.

At the original 1,647-declaration checkpoint, the unnumbered continuation
selecting m_N=floor(sqrt(log N)), its Stirling expansion and the polynomial-rate
comparison were still open. They are now proved separately, for actual
probability families, with a full 1,680-declaration audit. See the
[complete asymptotic continuation](MOMENT_OBSTRUCTION_ASYMPTOTICS.md).
The numbered count remains unchanged. This family has no claimed
multiplicative-model realization, just as in the original text.
No Palomar registration is made.
