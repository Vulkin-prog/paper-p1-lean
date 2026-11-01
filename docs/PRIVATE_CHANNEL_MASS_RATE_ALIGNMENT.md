# Actual fixed-channel mass with an explicit square-logarithmic remainder

This extends P1-MATH-0045. The actual critical-scale remainder in the
first displayed assertion of companion T2.5 is proved for the literal
integer-cutoff family. Its positive phase equivalent remains open, so
neither T2.5 nor article 3.3 is newly counted complete.

## Direct unsigned sum and critical powers

`ChannelUnsignedBound` proves

    sum_(1<=d<=m) A_d <= 2^m,
    0 <= U_{a,b}(L) <= B^2 * 2^floor(L/b).

Every literal placement count is at most B. The exact weight moment
gives the total A_d bound, including the empty sum. The real upper
bound U<=B^2*2^(B/b) is derived with the actual integer quotient.

`CriticalChannelPowers` proves explicit critical-band bounds for the
word power, window-root power and nominal square probability:

    2^L <= 2^C*N,
    2^(B/b) <= 2^((C+1)/b) * N^(1/b),
    p^2 <= (2^C)^2 * N^-2.

No residual-rank theorem or unproved arithmetic input is used.

## The three actual error terms

The earlier [actual finite mass bound](PRIVATE_CHANNEL_MASS_ALIGNMENT.md)
is

    |M-p^2*N*w*S|
      <= p^2*(6B*U + 2B^2*N + 2*#badSources*2^(B/b)).

For positive integral a<b<2a, necessarily b>=3. The actual exceptional
host estimate with exponent slack 1/12 gives #badSources<=N^(7/12).
The root weight is at most 2^((C+1)/b)*N^(1/3). Thus the deleted term
has exponent at most -13/12, which is below -1. The endpoint term is
controlled using the uniform eventual inequality B<=N^(2/3).
The baseline is already a B^2/N term.

`FixedChannelErrorAlgebra.error_scale` proves this finite comparison
with all elementary power inequalities explicit. It is instantiated by
the actual previously proved probability, sum and host bounds.

## Explicit remainder and quantifier order

Define

    K(C,b) = (2^C)^2 * (8*2^((C+1)/b)+2) > 0.

`PrivateChannelMassRate.mass_error_square_log` proves, for fixed positive
reduced a<b<2a, fixed natural D and critical-band width C, that one
threshold precedes every critical length L and every integer cutoff H
with

    2bB <= H <= DB.

Above it, the actual symmetric retained private-channel mass satisfies

    |M-p^2*N*w*S| <= K(C,b)*B^2/N.

The coefficient K is chosen independently of D and a; the threshold may
depend on C,D,a,b. Actual zero-probability pairs remain in the family,
both orientations are counted and the main term retains signed S.

`mass_error_rpow` absorbs the square-logarithmic factor: for every
epsilon>0, a larger threshold gives

    |M-p^2*N*w*S| <= N^(-1+epsilon).

The eventual coefficient one follows by enlarging the threshold; it is
not a uniform finite-size assertion independent of the channel parameters.

## Remaining source alignment

The positive fixed-channel phase equivalent M comparable to
L*N^(-1+1/b) still requires the positive leading behavior of S and its
critical-scale comparison. If the literal source threshold is a fixed
real coefficient times B, its integer cutoff convention must also be
transported exactly. These remaining assertions prevent declaring the
whole numbered T2.5 proved. Article 3.3 retains other arithmetic regimes
beyond this fixed-channel statement.

The stronger O(B^2/N) remainder is recorded as part of the existing
proof simplification P1-MATH-0045. No new literature premise, Paper C
port, manuscript revision or Palomar registration is introduced.
Original manuscript bytes are unchanged.
