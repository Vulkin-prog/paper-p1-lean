# T1.9 scope correction

The source convention is explicit in the unchanged V1.6 article:
`main_sections/arithmetic.tex:90` and `main_sections/pair_rigidity.tex:62`
define enlarged geometric alignment by positive coprime a,b<=B^3 and

    |b*x-a*y| <= (a+b)*B.

This condition does not require an actual normalized coincidence. The
statement of companion T1.9, original hash
`7de9608ecc780ef5a448579b04b2ebeabe5e1157579ce3025b0303a047157acc`,
uses that broader convention.

The first completed wrapper assumed a nonempty actual unit set. Its Lean
proof is valid, including the fixed-height enlarged-prime residual, but
the claim that this completed the full numbered source result was an
incorrect coverage mapping. The wrapper is renamed
`AlignedPairTheorem.one_unit_T1_9`; all its hypotheses remain explicit.
At that correction checkpoint, T1.9 was restored to **in progress** and
coverage to 48/167. The zero-unit case and the actual enlarged-alignment
interval geometry had to be proved before counting the result complete again.

P1-MATH-0039 describes the valid one-unit subcase without separation. One
unit is an additional restriction relative to enlarged alignment, not a
weakening of every source assumption. No Lean theorem is retracted and
no manuscript bytes are changed. Historical validation commits remain
in the ledger, with this correction stated explicitly.

Validated scope correction (full build 9,285 jobs; 3,294 audited declarations;
1,009 directly checked coverage/finding names):
[50889df7921f8374971c70d4d33878cc2a9326d4](https://github.com/Vulkin-prog/paper-p1-lean/commit/50889df7921f8374971c70d4d33878cc2a9326d4).

## Closure of the missing enlarged-alignment case

The new `EnlargedPairGeometry.Geometric` is the literal inequality above.
It places the true normalized union in an interval of radius 3*b*B in
one orientation, without assuming a coincidence. The Runge--Hamming--graph
argument now gives the uniform residual for this interval. A separate
finite two-even-space argument proves the pair-loss inequality when u=0;
no nonexistent common anchor is used in that case.

`EnlargedAlignedPairTheorem.companion_T1_9` covers positive coprime a,b
with max(a,b)<=B^3 in both orientations. It includes the fixed-height
large-prime residual for every 6*max(a,b)*B<=H<=D*B, with its constant
chosen before the critical-band width. The full value-kernel and pair-loss
fixed-height rates are proved as well. No separation, compatibility or
local-regularity assumption is needed. The result is now counted complete,
restoring coverage to 49/167 (main 16/73; companion 33/94).

This completes the missing proof; it does not erase the prior coverage
error or modify its historical validation records. Original manuscript
bytes remain unchanged.
