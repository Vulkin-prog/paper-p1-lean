# Further common-seed simplification — proposal only

This [independent proposal](independent-proposals.json) is not yet applied.
Its source base is the preserved strengthened preview at commit 3427655c;
no existing TeX or PDF byte is changed here. All thirteen previously applied
simplifications and the five scientific dispositions remain preserved.

The proposal couples four proof blocks:

- T1.12 would use the separated homogeneous triple argument for its second
  clause and retain an autonomous nonaligned two-edge estimate in the third.
  A common positive interaction estimate would also give the stronger pure
  squared-scale bound for its third clause.
- T1.17 would reuse this interaction estimate and exact direct factorization,
  with the diagonal/strict-contact baseline error retained. This removes its
  repeated local rational-slope classification.
- The one-target clause of T4.4 would cite T1.12(2).
- T3.1 would use the actual positive-support Palm comparison while keeping its
  old weaker printed statement. The four explicit Palm bridge proofs are now
  compiled and independently reviewed in checkpoint 1005.

The proposed proof blocks save 53 lines in the report's comparison. This is not
an applied source-line gain: statement and guide edits remain to be measured
on the future exact diff, and no PDF page gain is claimed. The report includes
concrete replacement TeX, the required domains and the acyclic reading route.
The pointwise T1.11 lemma is retained; a total mass estimate does not replace it.

The aligned four-window argument must include both cases for z in the second
pair: a positive singleton crossing gives a connected triple, while zero
singleton crossing permits the product upper bound on NB^O(1) aligned hosts.
The second case includes a positive crossing between the two pair spaces even
when each singleton crossing vanishes. Do not silently discard that population.
The nonaligned estimate's 27 lines remain in the proposal.

The necessary dependency direction is 14.3 -> T1.12(2) -> T4.4, with the positive
homogeneous triple proof independent of the moment theorem and final law
reconstruction. The report rechecks 1,712 actual local source digests in the
second-moment import closure. Import inspection is not semantic certification.

The [19 actual compiled types](scope/compiled-types.json) were extracted at
proof source d342b507, with actual exit 0 and standard axioms. The independent
instance read their bodies/types; it did not execute Lean. Frozen reports retain
their original absolute input paths. The identical packaged files are supplied
here. The separate new-proof review is linked from
[the sharp Palm note](../../../SHARP_GOOD_EDGE_PALM.md).

Before integration, apply an exact patch to a NEW source copy, recheck the
numbered statements and references, have the concrete diff read separately,
and build and inspect both resulting PDFs. Preserve all older copies/reports.
Palomar remains on hold; no new selection or dossier is proposed.
