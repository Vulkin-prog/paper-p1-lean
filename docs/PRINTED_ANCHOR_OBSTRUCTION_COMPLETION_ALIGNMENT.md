# T19.17 complete conditionally at the exact printed parameters

Companion T19.17, limits_appendix.tex:1293-1383. Primary analytic dependency: [Matomäki–Radziwiłł2016, Corollary6, p.1019](https://annals.math.princeton.edu/wp-content/uploads/annals-v183-n3-p06-p.pdf). Original statement hashes are preserved; analytic input remains explicit and unformalized.

Companion T19.17 is now COMPLETE CONDITIONALLY on the explicit
fixed-parameter ordinary smooth short-interval input recorded in
P1-MATH-0196. Both its deterministic assertion for every arithmetic
anchor and its randomized assertion for every measurable allowed
private forcing are proved at the exact printed parameters and
nominal scale. The analytic literature input remains unformalized;
this is not an unconditional completion or a new kernel axiom.

PrintedAnchorObstructionParameters proves, uniformly in every moving
critical L and maximal width B*=L+E+2<=D*log(N), that L>=1 and
2*B*<=floor(log(N)^5) for sufficiently large N. Thus the proof's
auxiliary full-good cutoff is compatible with the ORIGINAL retained
population at the EXACT printed Y=2*B*. Neither an extra small-Y
premise nor an assumed positive critical length remains.

Its nominal scale is the literal manuscript quantity

  2^(-2i) * (N*2^(-L))^2 * N^(-a).

It is proved exactly equal to q_(L+i)^2*N^(2-a), using the already
proved identity q_(L+i)=2^(-L-i). No retained mean is substituted for
the nominal lambda_N=N*2^(-L): the separate actual retained mean
remains |G|*q_(L+i).

PrintedDeterministicAnchorObstruction proves for every eta>0,
0<a<1/10 and both i=0,1,

  actual_offsite >= (1-eta)*2^(-2i)*lambda_N^2*N^(-a).

The original field G is precisely the translated dyadic population
with at most one small pivot in its maximal support, at Y=2*B*.
Every admissible deterministic arithmetic anchor is covered by the
previously constructed actual anchored data. Every raw template is
covered; in particular the original start word and unsigned exact
excess-zero word are identified with their original Boolean events
by the existing indicator_start and indicator_exact theorems.
The source and target are ORIGINAL retained labels throughout.

PrintedRandomizedPrivateObstruction proves the SAME printed bound
with the additional factor 1/2 for every independent auxiliary
probability space and every measurable actual map F in the indicated
private-pivot class. Its hypotheses are the literal prescribed
source word b+g(U,xi)*1 and preservation of all nonpivot prime signs
on full-good sources. Behavior on the remaining original sources
is arbitrary. The actual offsite integral cost of F is retained,
including every source and target. No assumed cost bound, finite
auxiliary restriction or abstract comparison cost enters the result.
The bound even holds without fairness; the separately proved fair
conditional-law constructions certify the Palm interpretation when
that interpretation is required.

Both uniform thresholds precede ALL moving lengths, maximal excess
widths, prime cylinders, arithmetic anchor rules, actual templates,
auxiliary spaces, orientation rules and private maps. Fixed constants
C,D,a and the tolerance eta precede the threshold, as required for
a fixed logarithmic-width bound and the printed little-o statement.
The independent source census is discharged internally from
CorollarySixLogInput(a). The latter is the only unformalized analytic
input: a fixed u=2/a consequence of Matomaki--Radziwill 2016,
Corollary 6, with positive limiting density, verified against the
primary published PDF and explicitly parameterized in Lean.

P1-MATH-0197 records the complete printed-parameter assembly. T19.17
changes from in_progress to conditional. Coverage is now 88 proved
and 70 conditional out of 167: 158 numbered statements complete in
these explicitly distinguished senses, with nine incomplete.
There are 196 improvements and one statement-scope correction.
The remaining exact signed logarithmic cost T19.16 is separate and
still open. Original manuscripts are byte-identical; no new axiom,
dependency or compiler change is introduced. Palomar remains deferred
because the complete two-document formalization is not finished.
