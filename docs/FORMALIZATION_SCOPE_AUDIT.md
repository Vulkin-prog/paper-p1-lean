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
T1.9 is restored to **in progress**, and current coverage is 48/167.
The zero-unit case and the actual enlarged-alignment interval geometry
must be proved before the numbered result is counted complete again.

P1-MATH-0039 describes the valid one-unit subcase without separation. One
unit is an additional restriction relative to enlarged alignment, not a
weakening of every source assumption. No Lean theorem is retracted and
no manuscript bytes are changed. Historical validation commits remain
in the ledger, with this correction stated explicitly.

Validated scope correction (full build 9,285 jobs; 3,294 audited declarations;
1,009 directly checked coverage/finding names):
[50889df7921f8374971c70d4d33878cc2a9326d4](https://github.com/Vulkin-prog/paper-p1-lean/commit/50889df7921f8374971c70d4d33878cc2a9326d4).
