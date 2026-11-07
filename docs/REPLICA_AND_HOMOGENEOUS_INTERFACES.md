# Exact replica and homogeneous-mass interfaces

Checkpoints P1-MATH-1001 and P1-MATH-1002 close two scope interfaces needed
by the complete [167-result proof index](MANUSCRIPT_ENDPOINTS_V1_8.md).
The version 1.8 TeX sources and PDFs remain unchanged. These are direct
interfaces to the printed claims, rather than additional registry targets.

## Replica kernels and repeated occurrences

[NominalRunReplicaFormula](../PaperP1/Model/NominalRunReplicaFormula.lean)
states the nominal identity for the actual infinite-prime run events.
The factor p^r uses `ker(relationMap(jointSystem))`: the kernel of the
colored valuation on the rL formal occurrence coordinates, before any
local quotient. It includes internal relations of irregular windows.
The function of occurrence centres need not be injective; repeated
centres keep distinct formal coordinates.

The separate heterogeneous identity uses the product of the actual
original marginals and the effective relative nullity. It retains zero
marginals and the exact affine compatibility indicator. The existing
regular formula remains its valid regular specialization.

`NominalRunReplicaFormula.companion_T22_7` closes the first replica formula.
The proposition's conditional-propagation and random-sum moment clauses
retain their separate endpoints. This distinction is explicit in the index.

The [checkpoint1001 replay](validation/checkpoint-1001/validation.json)
passed 18,623 build jobs, 19,971 axiom checks and 19,894 references, all
actual exits zero. Its four actual compiled types were subsequently
replayed under the checkpoint1002 source tree; the module bytes are unchanged.

## Actual homogeneous mass of dense primitive triples

[DensePrimitiveHomogeneousMass](../PaperP1/Asymptotics/DensePrimitiveHomogeneousMass.lean)
uses the actual homogeneous event probability. It does not substitute the
original affine marginal, which can vanish even when the homogeneous
event has positive probability.

The exact homogeneous factorization, the proved local cap and primitive
relative nullity at most L give a uniform point bound K_C/N^2, with
K_C=8*(2^C)^4, for every primitive triple of true windows. The internally
proved dense host count then gives total homogeneous mass N^(-2+epsilon).
The proof assumes neither local regularity nor affine compatibility.

`DensePrimitiveHomogeneousMass.companion_T8_2` contains all three printed
clauses under one common threshold: dense host count, actual homogeneous
mass, and total absolute centered activity of all primitive triples.
The existing original-affine mass theorem remains valid and separate.

The [checkpoint1002 replay](validation/checkpoint-1002/validation.json)
passed 18,625 build jobs, 19,975 axiom checks and 19,898 references, all
actual exits zero. The eight new theorem types and their individual axiom
reports are archived with the two checkpoints. Only propext,
Classical.choice and Quot.sound occur.

The two modules were also [read by the separate review instance](reviews/2026-11-07/post-interface.json).
That instance checked objects, hypotheses and quantifiers; it did not run
the parent's builds. This is an AI-assisted mathematical scope review,
not a claim of independent human certification. The six planned Palomar
dossiers and their 68 selections remain unchanged and on hold.
