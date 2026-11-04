# A necessary alignment-scope correction to companion T1.10

Source: companion_sections/arithmetic_appendix.tex:811-860; main definition: main_sections/arithmetic.tex:90-96.

Companion T1.10 has a confirmed ALIGNMENT-SCOPE CORRECTION,
P1-MATH-0162. Its printed assertion cannot hold with the main article's
literal definition of nonalignment, namely reduced positive slopes up
to B^3 and displacement at most (r+s)*B. The old set is allowed a wider
interval X+[-D*B,D*B], but the exclusion has not been enlarged with it.
This is a source-statement correction, separate from the 161 improvements.
Numbered coverage remains87/167 unconditional and48 conditional. T1.10
is in progress; neither its printed estimate nor a corrected replacement
is marked proved or used as a new input.

The unconditional checked family has L=3k, B=3k+1, X=2t,
z=3t+3B and U_X=[X,X+3B] (so the permitted old-width constant is D=3).
For j=0,...,k-1, target index3j+1 has actual value3(t+B+j), while
the old set contains2(t+B+j). Above EVERY cutoff H>=3 these two values
have identical parity vectors. Their zero-sum selections give
delta*(X,z)>=k-1. The loss is the literal preimage dimension of the
new even-selection map under the old RAW value span after forgetting
small-prime coordinates; no old parity or selected-map injectivity
is silently imposed. EvenPreimageRank proves the general injection
underlying this dimension lower bound.

For t>5B^4 these pairs are nonaligned at the ORIGINAL radius,
uniformly over ALL reduced slopes up to B^3. The determinant estimate
forces any possible slope to be2:3, whose displacement is6B>5B.
The same pairs ARE aligned at radius2. Thus the radius enlargement
suggested below actually excludes this entire obstruction. The new
window is separated from the source by more than L.

For m=2^(3k), N=6m and 3m<=t<4m-B, both centres lie in [N,2N).
There are exactly m-B distinct pairs. The full actual nonaligned
profile for the deterministic rule U_X=[X,X+3B] is at least
(m-B)*(2^(k-1)-1), and for all sufficiently large k it is at least
m^(4/3)/8. The sequence lies in the literal critical band with C=3.
At epsilon=1/48 the printed exponent is31/24+1/48=21/16<4/3.
AsymmetricAlignmentScopeObstruction.no_uniform_radius_one_bound
therefore rules out ANY uniform constant and threshold, for EVERY
fixed positive integer multiple H=q*(L+1), including arbitrarily large
fixed multiples. Its profile definition sums (2^delta*-1) over the
literal dyadic radius-one nonaligned population, with the actual old
interval and even-selection loss. The obstruction does not depend on
any external geometry, Reuss estimate, probabilistic input or conjecture.

Suggested revision: explicitly define asymmetric nonalignment with an
exclusion radius depending on D, for example max(1,D)*(r+s)*B, or the
corresponding sharper bound from the two unequal offset widths. Reprove
T1.10 with that exclusion and check how the enlarged aligned sector is
handled wherever T1.10 is used. The present result proves that a change
is NECESSARY and that radius2 already removes this test family; it does
NOT prove that this change alone suffices for the asserted31/24 bound
or all downstream estimates. No main-article conclusion is refuted by
this counterexample. The original manuscripts remain byte-for-byte
unchanged. Palomar remains a later milestone.

The JSON result and finding record the exact full verification and proof commit.
