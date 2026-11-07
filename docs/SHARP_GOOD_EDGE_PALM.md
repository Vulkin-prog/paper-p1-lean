# Sharp positive Palm costs on the regular target set

The four new interfaces in
[SharpGoodEdgePositivePalm.lean](../PaperP1/Asymptotics/SharpGoodEdgePositivePalm.lean)
make the positive conditional cost an explicit consequence of the already-proved
homogeneous effective crossing mass. This is checkpoint P1-MATH-1005, an
interface improvement rather than a new geometric input or a new false-original
statement. Every existing manuscript, preview and registry selection is preserved.

For a fixed interior reduced channel a:b, write beta for its compatible source
mass, and M(G) for the source-weighted positive conditional excess summed over
fresh targets in an arbitrary G contained in the regular-start set. In the
critical band the new bounds are:

| Quantity | New bound | Conditions |
|---|---|---|
| Positive unnormalized Palm mass M(G) | N^(-41/30+epsilon) | Fixed 0<a<b<2a, coprime a,b; every natural source cutoff H |
| Normalized mass M(G)/beta | N^(-11/30-1/b+epsilon) | Also 2b(L+1)<=H<=D(L+1), D fixed; beta>0 is proved |
| Normalized 2:3 cost | N^(-7/10+epsilon) | Common cutoff 8(L+1)<=H<=D(L+1) |
| Normalized 3:4 cost | N^(-37/60+epsilon) | Same common cutoff |

All channel parameters, C, D and epsilon precede the scale threshold. Targets G,
N, L and H are quantified after that threshold. This is not a claim for growing
channel heights or arbitrary irregular target sets. The finite inclusion alone
requires only N>=2, L>0 and G contained in the regular-start set.

## Why the finite comparison matters

For each compatible source e, multiplication by its positive probability gives

`q(e) * (P(J_z=1 | J_e=1) - p)_+ = (q(e union {z}) - q(e)*p)_+`.

A positive summand forces an actual positive joint event, hence separation of
the starts; distance exactly L remains allowed. On a regular target its marginal
is exactly p, and a zero crossing would make the joint factor, so positivity
also forces a nonzero crossing. The positive support thus embeds in the genuine
homogeneous effective edge/target population. The finite rank probability bounds
the affine joint point by point, including incompatible configurations of the
larger raw family. No signed cancellation or assumed asymptotic bound enters this
comparison.

The namespace `HomogeneousGoodPairExtensionsUnderInputs` in the finite bridge
names an existing finite population definition. Its appearance does not supply
an unproved mass estimate. The new proof replaces membership in regularStarts
by membership in dyadicBlock and preserves freshness, separation and crossing.
The terminal asymptotic theorem is the unconditional
`HomogeneousEffectiveGoodPairExtensions.uniform_mass`.

For normalization, the source phase theorem proves beta positive under the stated
cutoffs. Division occurs only after this proof. Subtracting the source exponent
-1+1/b from -41/30 gives -11/30-1/b; constant absorption fixes the final threshold.
Compared with the previous generic 4/3-based interface, the improvement is 1/30
for each fixed interior channel. The printed 3:4 bound was already weaker than
that old generic interface; its comparison must not be misstated as only 1/30.
No optimality of these conditional powers is asserted.

## Validation

The [complete replay](validation/checkpoint-1005/validation.json) was actually
performed at source `d342b507332315c67b1463009061c03f14b5be9b`, with Lean
4.36.0-rc2, compiler b35cb10 and the pinned Mathlib revision:

- 18,631 full build jobs, 19,995 theorem axiom checks and 19,918 distinct reference
  checks, all three actual exits zero; only propext, Classical.choice and
  Quot.sound occur.
- Four new propositions were [extracted](validation/checkpoint-1005/scope/compiled-types.json)
  and audited. All 528 original manuscript types, the prior expanded 535 types,
  264 proof-entry/object types, nine examples and the seven fixed-arity
  interfaces replayed byte-identically. The expanded inventory is now 539 types,
  of which 496 are audited propositions.
- Of the 4,739 prior proof-manifest files, 4,737 are byte-identical; only
  the aggregate root and audit extend. One new mathematical module is added; compiler,
  dependency and build pins are unchanged.
- The [independent frozen review](reviews/2026-11-07/sharp-good-edge-palm.json)
  read all four bodies, actual compiled types, objects and quantifier order,
  with no confirmed gap or required correction. It is AI-assisted review,
  distinct from kernel checking and human certification. Original absolute work
  paths in this frozen review are preserved; identical input bytes are packaged
  at the canonical validation paths linked here.

The live manuscript endpoint checker binds these four reviewed interfaces to
their actual source, proposition role, audit inventory and compiled scope. Its
in-memory controls distinguish an actual proof from a definition, a changed
quantifier type, an omitted support bridge or a stale body read.

## Editorial use

The latest [unified preview](editorial-proposals/2026-11-07/common-seed-simplification/README.md)
now applies the shorter T3.1 proof while keeping its old weaker printed bounds.
Its source phase proves beta positive before division. The coupled T1.12,
T1.17 and one-target T4.4 simplifications also appear there; the autonomous
nonaligned estimate and pointwise T1.11 stay intact. The original
[proposal report](editorial-proposals/2026-11-07/two-edge-simplification/independent-proposals.json)
remains frozen as a historical input, and the new capsule records its applied
dispositions. It saves 51 source lines and no additional PDF page: 64 article
and 101 companion pages remain. All earlier copies and registry scopes are
preserved. Palomar remains on hold at the user's request.
