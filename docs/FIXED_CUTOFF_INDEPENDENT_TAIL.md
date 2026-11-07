# Fix the full-support tail size before epsilon

Checkpoint P1-MATH-1000 exposes the quantifier order in article15.8
directly. For fixed range and width constants D,Q, critical-band constant
C, positive weight v and target exponent a<2, there are s>=3 and N0>=10
such that both independent tail masses are at most N^(-a) for every
N>=N0 and every critical length.

The first mass uses the original heterogeneous factors v*p_x. The second
has one arbitrary actual finite label set in a fixed bounded-width
window, paid once with its nominal block factor v*2^(-L), and the original
heterogeneous factors for the remaining windows. Its size threshold is
s-1 for the remaining windows. The arbitrary label sets and actual window
centres follow the common scale threshold. D and Q stay fixed before N.

The cutoff s and scale threshold N0 can both be chosen before any later
epsilon. In particular the existing printed N^(-a+epsilon) conclusion has
one s independent of epsilon.

This follows from the already proved estimate with

```text
a' = (a+2)/2,
epsilon' = (2-a)/4,
a'-epsilon' = a+(2-a)/4 > a.
```

Since N>=10, the resulting N^(-a'+epsilon') bound is at most N^(-a).
There is no new arithmetic assumption. This is not a claim at a=2 or for
block ranges or widths that grow with N.

The exact interfaces in
[FixedCutoffIndependentTail.lean](../PaperP1/Asymptotics/FixedCutoffIndependentTail.lean)
are:

- `PaperP1.FixedCutoffIndependentTail.uniform_tail`
- `PaperP1.FixedCutoffIndependentTail.article_15_8_fixed_cutoff`

The [complete pinned replay](validation/checkpoint-1000/validation.json)
passed 18,621 build jobs, 19,967 theorem axiom checks and 19,890 distinct
reference checks, all with actual exit zero. Both new compiled types and
their individual axiom reports are preserved in
[the scope report](validation/checkpoint-1000/scope/compiled-types.json).
All 528 previously compared manuscript types were replayed and remained
byte-identical. Only propext, Classical.choice and Quot.sound are permitted.

The 167 numbered statements, the earlier proof interfaces and all frozen
v1.8 source/PDF bytes are preserved. This is an exact additional proof
interface for the unchanged source statement. It adds no registration
selection; Palomar remains on hold at the user's request.
