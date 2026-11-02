# Two individually small odd kernels: the complete lower count

The complete lower-count portion of companion T1.5 is now proved on
literal dyadic windows, with a stronger explicit scope. For every
fixed 1/2<beta<1 and epsilon>0, one threshold precedes N, every
natural prime cutoff H and every length L>=2. The number of actual
dyadic windows containing at least two distinct values whose
individual large odd kernels are at most N^beta is at least
N^(beta-epsilon). Taking H=B=L+1 and a critical-band length gives
the source lower count. This concerns two individual bounds, rather
than the different existing product-cap upper count.

The proof makes the source CRT construction effective. In the box
[1,M]^2, a common-divisor cover and the elementary finite bound
sum_(d=2)^M 1/d^2 <= 3/4 supply at least M^2/4 coprime pairs.
Restricting to [D,10D]^2 leaves at least 5D^2 such pairs. For each
positive coprime d,e, CRT constructs at least N/(d^2*e^2)-1 integer
solutions in the exact interval [N,2N). If N>=40000*D^4, their
literal square-divisibility incidence count is at least
N/(4000*D^2). Each integer has at most tau(n)*tau(n+1) witnesses,
and the proved uniform divisor bound absorbs this multiplicity.
A squared divisor d^2 of n proves K_H(n)*d^2<=n for arbitrary H.
The scale D=ceil(2*N^((1-beta)/2)) then yields the asserted exponent.
The neighboring values n,n+1 are proved to belong to the actual
complete window at x=n for every L>=2.

This is P1-MATH-0100: the lower exponent and its all-cutoff uniformity
are isolated explicitly, with finite constants. The CRT idea and the
condition beta>1/2 were already present in the source proof; no error
in a manuscript conclusion is asserted. The upper count
N^(max(beta,7/12)+epsilon) still requires the unresolved determinant
estimate. Hence T1.5 moves from not_started to in_progress and is
not counted complete; neither is its full sharpness equality.
Coverage stays 79/167. Improvements now total 100. There are no new
external estimates, dependency changes or Palomar claims, and the
original manuscript sources remain byte-for-byte unchanged.

Verified with Lean v4.36.0-rc2: full lake build (11261 jobs), actual kernel-axiom audit (7593 declarations; only propext, Classical.choice and Quot.sound), 5310 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.60 GiB free on Ubuntu root.
