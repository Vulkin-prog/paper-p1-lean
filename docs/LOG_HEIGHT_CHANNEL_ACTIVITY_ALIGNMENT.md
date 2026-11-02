# Uniform actual channel activity up to logarithmic height

The channel weight bounds are now uniform simultaneously over all
reduced a:b with 0<a<b, b0<=b<=(L+1)^3, where only b0,C,epsilon are fixed
before the threshold. Actual joint and absolute centered weights of every
exact-unit pair are at most N^(-2+1/b0+epsilon), without BCN, private
normalizations or regular-site assumptions. The proof uses the genuinely
uniform aligned rank theorem; it does not take a growing maximum of
fixed-channel thresholds.

The literal unordered union over all these channels is constructed. A
finite weighted cover has cost at most 4(L+1)^8*N times a common pointwise
weight cap. It counts at most 4(L+1)^6 coefficient pairs and uses the
actual N(L+1)^2 source cover in each channel. Duplicate edge or source
representations require no disjointness assumption. The whole logarithmic
factor is absorbed only after these finite counts.
Consequently both joint mass and absolute centered activity of the full
exact-unit channel union are at most

    N^(-1+1/b0+epsilon).

For b0=3 this gives N^(-2/3+epsilon) over every channel of height up to
(L+1)^3. For b0=5 it proves the source residual N^(-4/5+epsilon) for the
entire exact-unit high-channel tail, including nonprivate and irregular
sources. The parameter varying with N here is the channel height, not the
number of windows or moment order.

This proves another source-scale part of main 3.3 and T7.1. It does not
identify all aligned pairs with exact-unit pairs, treat zero-unit enlarged
alignments, prove the macroscopic nonaligned sector, or complete the signed
pair profile. Main 3.3 and T7.1 stay in progress. Coverage stays 77/167
(main 28/73, companion 49/94), confirmed improvements 94. No new correction,
external premise, axiom, dependency download, original-source change or
Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full lake build (10991 jobs), source and ledger checks, actual axiom audit of 6975 declarations (only propext, Classical.choice and Quot.sound), and 4692 direct ledger/evidence declaration checks; Ubuntu root free space 15.12 GiB. Original manuscript bytes and all 167 statement hashes preserved.
