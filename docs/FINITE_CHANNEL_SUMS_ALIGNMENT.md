# Finite channel sums — preparatory to article 3.3 and companion T2.5

The finite computation is proved. Neither numbered asymptotic result is
counted complete. Original V1.6 source bytes are unchanged.

- Article 3.3, page 16, `p1:arith:pairs`,
  `main_sections/arithmetic.tex:162`, statement hash
  `2129f1e0418039211e95fa065f6ae434fe46849de797ea291acb0e08da94b412`.
- Companion T2.5, page 22, `p1:arith:fixed-channel-mass`,
  `companion_sections/supplemental_arithmetic.tex:164`, statement hash
  `3f277bcb49753b0c57c75eaa012cdfc127c5f3253a66fb6fe0c40707b4e533e4`.

The exact unnumbered equations are `p1:arith:diametersign` at article
source line 124, `p1:arith:channelidentity` at line 139, and the two
leading-channel formulas `p1:arith:S23` and `p1:arith:S34` at lines 156–159.

## Actual even selections and prescribed extremes

For a gap d=m+1, there are m interior unit positions and two extreme
positions. `ChannelSelectionCount.EndpointSelections m` is the actual
binary coefficient space on Fin(m+2), with both extreme coefficients
one and total sum zero over F_2. An explicit equivalence adds the two
selected endpoints to the zero-sum space on the m interior coordinates.
Its cardinality is 2^(m-1), including m=0 where the interior space is
zero-dimensional and there is one selection. Therefore the actual count
is A_1=1 and A_d=2^(d-2) for d>=2.

## Actual placements and the predecessor sign

A selected support of diameter D has the literal placement indices
0,...,L-D when D<=L; there are none otherwise. Exactly the index zero
placement uses the predecessor and has sign -1. Every other placement
has sign +1. `ChannelPlacements` proves

    card(placements L D)=L+1-D,
    sum(placement signs)=L-1-D,        D<=L.

At D=L, the true single placement has signed contribution -1.
The two-window unsigned and signed placement products, weighted by A_d,
are exactly the source U_{a,b}(L) and S_{a,b}(L). Their upper index is
floor(L/b); positive b and a<=b ensure that both physical diameters fit.
No arithmetic source-host count is a premise of these finite identities.

## All weighted moments and arbitrary integer shifts

`ChannelSumIdentity.moments` proves the three source moment identities
for sum A_d, sum d*A_d and sum d^2*A_d, for 1<=d<=m and m>=1.
The range-indexed representation is proved equal to the literal Icc sum.
Expanding a quadratic product then proves, for every integer shift s,

    sum A_d*(L+s-a*d)*(L+s-b*d)
      = 2^(m-1)*[(b-a)*(b+r+s)*m+(r+s)^2+(a+b)*(r+s)+3*a*b]
        -(a+b)*(L+s)-a*b,

whenever L=b*m+r and m>=1. All coefficients may be integers; their
positivity, coprimality and Euclidean remainder range are unnecessary
for this algebraic identity. `euclidean_identity` specializes to
m=L/b, r=L mod b. The original signed and unsigned cases are s=-1
and s=1. For m=0, both defining sums are explicitly zero.

## Exact leading signed formulas

For m>=1 and the indicated remainder ranges, the source formulas are
proved exactly:

    S_{2,3}(3m+r)=2^(m-1)*[(r+2)*m+r^2+3r+14]-5*(3m+r)-1,
    S_{3,4}(4m+r)=2^(m-1)*[(r+3)*m+r^2+5r+30]-7*(4m+r)-5.

These are integer equalities, retaining every finite boundary term.
The arbitrary-shift identity and explicit counting interpretation are
recorded in P1-MATH-0043.

## Remaining source statements

Actual dyadic source translations, exceptional defective normalizations,
nonaligned arithmetic residual mass, full pair profiles and asymptotic
phase equivalents remain open. The finite calculation is not substituted
for those missing estimates. There is no new external mathematical
hypothesis, Paper C port, manuscript revision or Palomar registration.
