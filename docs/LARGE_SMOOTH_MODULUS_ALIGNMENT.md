# Complete deterministic smooth-modulus exception — companion T6.2

Companion Lemma T6.2 is proved, with its actual deterministic exceptional
set, its cardinal bound and the full selection-to-membership implication.
Coverage is 61/167 (main 19/73, companion 42/94). The final source declaration
is `LargeSmoothExceptionalSet.companion_T6_2`; the stronger core is
`constant_selection`.

## A constant selection size suffices

The stronger core requires only t+26 distinct selected values. Its threshold
precedes t, H and the entire selected family. The exceptional set is common
to all those choices, and all natural cutoffs Y<=(logN)^A are covered.
The full source theorem uses the literal real cutoff Y=(logN)^A, the
critical scale B=L+1 and every fixed comparable positive centre interval.
The original condition |S|>c*loglogN implies |S|>=t+26 eventually for each
fixed t and c>0. Positivity of every selected signed value and equality
with its natural absolute-value representation are proved.

The pair exclusion is imposed only on actual selected values: each pair
of distinct selected offsets has product of its actual K_H kernels greater
than N^(1/2). Thus the source exclusion from X_(1/2) supplies it even for
irregular blocks. No additional separation or evenness hypothesis is used.

## Full canonical squares and squarefree smooth parts

For every positive integer v, the proved canonical decomposition is

    v = smallOddPart(Y,v)*K_Y(v)*canonicalSquarePart(v)^2.

Unlike the printed proof, the square part includes the halves of every
prime valuation, and smallOddPart is squarefree. For any H, K_H(v) is at
most sf(v), so K_H(v)*canonicalSquarePart(v)^2<=v. Two selected values with
full square parts squared greater than N^(19/25) would violate the pair
exclusion, since all actual values are O(N). The fixed coefficient is
absorbed using the exact exponent gap 1/50.

At most one such large square part and fewer than t large Y-kernels are
removed. Twenty-six distinct selected values remain. Their squarefree
Y-small parts are at least alpha*N^(1/25), with an explicit positive
interval constant alpha. These statements are proved on the actual
selected finite set, without an assumed supply of smooth parts.

## A large actual squarefree modulus is constructed

Each small part divides its actual value. The gcd of two such parts divides
the difference of two distinct actual values, and is at most twice the
window radius. A proved finite inequality gives

    product_i s_i <= lcm_i(s_i)*(2W)^(26^2).

This deliberately coarser fixed power still has only a polylogarithmic
cost. Since 26/25>1, the lcm exceeds the entire centre interval height X.
It divides the product of the union of the actual small prime supports.
A proved first-passage lemma extracts a subset T of those primes with

    X < product(T) <= X*Y.

The modulus m=product(T) is proved squarefree and K_Y(m)=1. Every prime is
allocated to a selected value on which it occurs. The resulting factors
are positive, pairwise coprime, divide their actual selected values and
have product m. This is the literal congruence certificate used in the
exceptional-set definition; no modulus-existence premise is left open.

## The exceptional set is actually counted

At a fixed modulus m, all offset functions and divisor functions are
finite and explicitly counted by

    (2W+1)^26*tau(m)^26.

A fixed valid code determines at most one centre: its coprime product is
at least the whole centre interval height. The proof uses actual signed
linear values, integer divisibility, natural congruences and the elementary
short-interval uniqueness theorem. The uniform divisor estimate and the
fixed polylogarithmic width absorb both code costs.

The actual modulus family has m<=C*N*(logN)^A and K_Y(m)=1. Its Rankin count
is at most N^(1-1/A+epsilon), proved from the existing small-kernel Euler
bound. A tilt strictly between 1-1/A and 1 makes the Euler exponential
subpolynomial. All heights, constants and error exponents are controlled
before the varying modulus family. The finite modulus cover is then
summed. Neither its count nor a target centre count is assumed.

## One deterministic set for all selections

A rounded logarithmic radius contains every admissible offset in every
critical length. The exceptional set is defined by actual squarefree
moduli and actual congruence certificates in this common radius. It depends
on N,Y and the fixed interval/width data, independently of t, H and any
selection. The source theorem chooses Y=floor((logN)^A) and proves the exact
dictionary with the real truncated kernel.

Improvement P1-MATH-0062 records the constant-size hypothesis, the sufficiency
of squarefree parts/moduli, and the independence from H and t. No condition
H>diameter or H<=Y is needed. No new unproved literature input, Paper C port,
manuscript-byte change or Palomar registration is introduced. The private
incoming/outgoing certificate lemma and conditional full-support theorem
remain open.

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,731 jobs); actual axiom audit passed for all 4,318 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,033 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.35 GiB. No unproved modulus/centre count, new literature input, new Paper C port, manuscript-byte change or Palomar registration.
