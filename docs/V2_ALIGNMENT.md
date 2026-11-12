# P1 V2.0 alignment

The current edition is the V2 dossier dated 9 November2026, aligned on 12 November.
It contains **118 numbered results:26 article and92 companion**, with 199
clause endpoints. Nine retained auxiliary claims bring the extracted current
scope to **212 distinct proved propositions**. The index preserves the printed
conditional premise of the finite-transfer theorem; the principal approximation
is separately proved unconditionally.

- [French mathematical/editorial review](reviews/2026-11-12/V2_REVIEW_FR.md).
- [Source/type-bound complete index](manuscript-results-v2.0.json) and
  [version correspondence](manuscript-v2.0-correspondence.csv).
- [Current Lean entry point](../PaperP1/V2.lean).
- [Actual proof replay](validation/v2.0/validation.json),
  [compiled current types](validation/v2.0/v2-scope/compiled-types.json),
  [24 new propositions](validation/v2.0/new-scope/compiled-types.json).
- [Preservation receipt](validation/v2.0/preservation.json):547 prior manuscript
  files and all prior mathematical Lean modules unchanged.
- [Original received dossier](../manuscripts/paper-p1/v2.0/received/),
  [unaltered archive](../manuscripts/paper-p1/v2.0/archive/P1_V2_0_Dossier_2026-11-09.zip)
  and [receipt](../manuscripts/paper-p1/v2.0/RECEIVED_PROVENANCE.json).
- [Active editable sources](../manuscripts/paper-p1/v2.0/sources/),
  [article PDF,32 pages](../manuscripts/paper-p1/v2.0/pdf/P1_V2_0_Main_EN.pdf) and
  [companion PDF,84 pages](../manuscripts/paper-p1/v2.0/pdf/P1_V2_0_Companion_EN.pdf).

All received scientific sources are unchanged. Only the active shared
formalization notice was updated to describe the completed alignment.
The 107 unchanged statement blocks, ten changed blocks and one new lemma
are bound to actual source bytes and compiled PDF numbering. The 50 omitted
results remain historical, with their proofs; removal from this scalar-count
scope is not invalidation.

## Proof changes and limits

Six new mathematical modules prove 24 comparison, composition and uniformity
propositions. They expose the all-target exact/nominal positive Palm sums,
one support-count threshold before every minimum size, the sharp ordered
primitive masses, the finite envelope and a common sharp raw-seed interface.
Strong existing interfaces also cover T12.4 and T12.7. Prior strengthening
clauses use their strong endpoints: the local exponent 5m and compressed
target power41/30 are not justified solely by their weaker historical aliases.

Proof source:`aa12e797ce895f6b7aef6e4f1f0c6e5e9a58aab4`.
The full pinned build passed 18,645 jobs; the actual audit checked 20,019
theorems, and 19,942 distinct references resolved. Only propext,
Classical.choice and Quot.sound occur. Old 528/539/264-type inventories,
nine examples, seven fixed-arity types and four prior Palm types replayed
byte-identically. Lean v4.36.0-rc2 and the Mathlib pin remain unchanged.

Six actual pdfLaTeX executions stabilized both documents, without overfull
boxes or unresolved references. All 116 pages were inspected in ten contact
sheets and eleven selected pages separately; [visual evidence](validation/v2.0/pdf/visual-review.json)
records exactly those inspected views. The independent received reports
remain historical inputs, not new Lean replay receipts.

Source hashes and clause checks protect recorded identity and scope. They do
not prove the translation from TeX into Lean, provide independent human review,
or constitute Palomar certification. The V2 comparison in this session was
AI-assisted; prior independent reviews retain their own exact source snapshots.

The [small T13.1 proof simplification](reviews/2026-11-12/S01-uniform-support-proof.patch)
is proposed, not applied. It preserves every statement and label; no page gain
is claimed. The French review also proposes an optional shorter companion notice.

## Palomar

Submissions remain **on hold at the user's request**. The six historical
consolidated dossiers and their author metadata (Brice Pouly,
ORCID 0009-0008-8491-2467) are unchanged. Their former qualification concerns
their historical statement scopes, not an automatic qualification of V2.
No official check, intake or submission was launched. When the user resumes
this milestone, compare the six scopes to V2, preserve the target of fewer
than ten total submissions, and update statements/evidence before any filing.

## Reproduce

```sh
python3 scripts/check_manuscript_v20.py
python3 -m unittest discover -s tests
lake build
lake env lean Audit.lean > axiom-audit.txt
python3 scripts/check_axioms.py axiom-audit.txt
python3 scripts/build_manuscript_v20.py --evidence-dir /absolute/temporary/directory
```

The PDF build needs TeX Live and the packages declared in preamble.tex.
The source/type guard is read-only and runs in CI; it never triggers Palomar.
All 75 local tests passed, including 18 V2 controls (17 intentional invalid scopes).
On the Ubuntu workstation use the existing wrapper and disk checks specified
in AGENTS.md before invoking Lake. No dependency download is needed for checks.

## Current result map

The stable Lean names retain historical numbering to preserve downstream users.
Current numbers below come from the newly compiled V2 documents. Each row links
the complete source/type-bound bundle, including all additional clauses, in JSON.

### Article

| Number | Label | Result |
|---|---|---|
| [1.1](../manuscripts/paper-p1/v2.0/sources/main_sections/introduction.tex#L70) | `p1:thm:main` | Optimal quadratic approximation with exact parameters |
| [1.2](../manuscripts/paper-p1/v2.0/sources/main_sections/introduction.tex#L104) | `p1:cor:tv` | Exact Poisson total variation scale |
| [2.1](../manuscripts/paper-p1/v2.0/sources/main_sections/event_algebra.tex#L148) | `p1:alg:centred` | Centered Bernoulli expansion |
| [2.2](../manuscripts/paper-p1/v2.0/sources/main_sections/event_algebra.tex#L182) | `p1:alg:fourier` | Full-support Fourier formula |
| [2.3](../manuscripts/paper-p1/v2.0/sources/main_sections/event_algebra.tex#L214) | `p2:homogeneous:envelope` | A common homogeneous envelope |
| [2.4](../manuscripts/paper-p1/v2.0/sources/main_sections/event_algebra.tex#L265) | `p1:alg:compatible` | Compatible-nullity majorant |
| [2.5](../manuscripts/paper-p1/v2.0/sources/main_sections/event_algebra.tex#L298) | `p1:alg:components` | Existence, uniqueness, and factorization |
| [3.1](../manuscripts/paper-p1/v2.0/sources/main_sections/scales.tex#L64) | `p1:arith:pairs` | Complete pair profile |
| [3.2](../manuscripts/paper-p1/v2.0/sources/main_sections/scales.tex#L118) | `p1:cor:explicit` | An explicit probability reference |
| [3.3](../manuscripts/paper-p1/v2.0/sources/main_sections/scales.tex#L196) | `p13:third:main` | Optimal power of the third factorial cumulant |
| [3.4](../manuscripts/paper-p1/v2.0/sources/main_sections/scales.tex#L216) | `p13:third:activity` | Absolute third-order activity |
| [4.1](../manuscripts/paper-p1/v2.0/sources/main_sections/stopped.tex#L40) | `p1:stop:polynomial` | Expansion at the first excluded prefix |
| [4.2](../manuscripts/paper-p1/v2.0/sources/main_sections/stopped.tex#L97) | `p1:stop:measure` | A positive remainder kernel |
| [5.1](../manuscripts/paper-p1/v2.0/sources/main_sections/reconstruction.tex#L81) | `p13:transfer:conversion` | Conversion with heterogeneous marginals |
| [5.2](../manuscripts/paper-p1/v2.0/sources/main_sections/reconstruction.tex#L169) | `p13:transfer:finite` | Finite transfer to the complete law |
| [5.3](../manuscripts/paper-p1/v2.0/sources/main_sections/reconstruction.tex#L264) | `p13:transfer:reconstruction` | Reconstruction from triple activity |
| [6.1](../manuscripts/paper-p1/v2.0/sources/main_sections/quartic_lower.tex#L28) | `p13:lower:quartic` | The fourth factorial cumulant |
| [6.2](../manuscripts/paper-p1/v2.0/sources/main_sections/quartic_lower.tex#L113) | `p13:lower:optimal` | Optimal power for the exact quadratic reference |
| [7.1](../manuscripts/paper-p1/v2.0/sources/main_sections/completion.tex#L38) | `p1:close:positivity` | Positivity of the quadratic Poisson correction |
| [7.2](../manuscripts/paper-p1/v2.0/sources/main_sections/completion.tex#L144) | `p13:optimal:weighted` | Every fixed polynomial weight |
| [7.3](../manuscripts/paper-p1/v2.0/sources/main_sections/completion.tex#L188) | `p13:optimal:zero` | No retained start |
| [7.4](../manuscripts/paper-p1/v2.0/sources/main_sections/completion.tex#L208) | `p13:optimal:nominal` | The quantized mean bias |
| [8.1](../manuscripts/paper-p1/v2.0/sources/main_sections/channel_hierarchy.tex#L28) | `p13:channels:hierarchy` | The optimal error of every fixed height truncation |
| [8.2](../manuscripts/paper-p1/v2.0/sources/main_sections/channel_hierarchy.tex#L66) | `p13:channels:weighted-nonaligned` | Weighted nonaligned pairs |
| [8.3](../manuscripts/paper-p1/v2.0/sources/main_sections/channel_hierarchy.tex#L199) | `p13:channels:height-five` | The error of the two-channel reference |
| [8.4](../manuscripts/paper-p1/v2.0/sources/main_sections/channel_hierarchy.tex#L273) | `p1:cor:compound` | Hermite approximation with single and double jumps |

### Companion

| Number | Label | Result |
|---|---|---|
| [T1.1](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L19) | `p1:arith:runge` | A split-product bound uniform in the degree |
| [T1.2](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L62) | `p1:arith:pell` | Uniform quadratic equation count |
| [T1.3](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L90) | `p1:arith:defects` | Local and global defect counts |
| [T1.4](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L139) | `p1:arith:reuss` | Uniform determinant estimate |
| [T1.5](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L360) | `p1:arith:twokernel` | Two small odd kernels |
| [T1.6](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L416) | `p1:arith:anchor` | A large selected kernel |
| [T1.7](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L480) | `p1:arith:geometric` | The uniform geometric counts |
| [T1.8](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L745) | `p1:arith:dense` | The dense weighted sector |
| [T1.9](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L770) | `p1:arith:alignedrank` | Uniform residual rank on an aligned pair |
| [T1.10](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L812) | `p1:arith:asymmetric` | An asymmetric pair profile |
| [T1.11](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L900) | `p1:arith:palmrank` | Aligned loss above a rational pair |
| [T1.12](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L960) | `p1:arith:fixed-homogeneous-seeds` | Homogeneous seeds for fixed extensions |
| [T1.13](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L1073) | `p1:arith:small-kernels` | Small-kernel counts for fixed-width blocks |
| [T1.14](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L1095) | `p1:arith:fixed-support` | A relative relation meeting several blocks |
| [T1.15](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L1127) | `p1:arith:fixed-branching` | A fixed number of exposed source windows |
| [T1.16](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L1166) | `p1:arith:ternary-budget` | A ternary group budget |
| [T1.17](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L1251) | `p1:arith:twogoodpositive` | A positive second moment for good edges |
| [T1.18](../manuscripts/paper-p1/v2.0/sources/companion_sections/basic_arithmetic.tex#L1299) | `p1:limits:local-rigidity` | Local rigidity |
| [T2.1](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_profiles.tex#L49) | `p1:arith:core` | Regular set |
| [T2.2](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_profiles.tex#L98) | `p1:arith:hosts` | Support and residual mass |
| [T2.3](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_profiles.tex#L127) | `p1:arith:edgefamily` | The pair input for the expansion |
| [T2.4](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_profiles.tex#L146) | `p1:arith:compression` | Exact compression of a good edge |
| [T3.1](../manuscripts/paper-p1/v2.0/sources/companion_sections/channel_counts.tex#L19) | `p1:arith:smallpart-budget` | A small-prime coefficient budget |
| [T3.2](../manuscripts/paper-p1/v2.0/sources/companion_sections/channel_counts.tex#L51) | `p1:arith:coordinate-regularisation` | Coordinate regularisation |
| [T3.3](../manuscripts/paper-p1/v2.0/sources/companion_sections/channel_counts.tex#L107) | `p1:arith:ternary-degree` | Constraints meeting three blocks |
| [T3.5](../manuscripts/paper-p1/v2.0/sources/companion_sections/channel_counts.tex#L164) | `p1:arith:fixed-channel-mass` | Mass of a fixed channel |
| [T3.6](../manuscripts/paper-p1/v2.0/sources/companion_sections/channel_counts.tex#L209) | `p1:arith:fixed-channel-rank` | Additional rank in a fixed channel |
| [T3.7](../manuscripts/paper-p1/v2.0/sources/companion_sections/channel_counts.tex#L261) | `p1:arith:fixed-channel-palm` | Palm mean for a fixed channel |
| [T3.8](../manuscripts/paper-p1/v2.0/sources/companion_sections/channel_counts.tex#L321) | `p1:arith:finite-family-triples` | Triples containing a good pair |
| [T4.1](../manuscripts/paper-p1/v2.0/sources/companion_sections/fixed_moments.tex#L30) | `p1:fixed:recovery` | Disjoint recovery |
| [T4.2](../manuscripts/paper-p1/v2.0/sources/companion_sections/fixed_moments.tex#L89) | `p1:fixed:targets` | Large rank loss after fixed sources |
| [T4.3](../manuscripts/paper-p1/v2.0/sources/companion_sections/fixed_moments.tex#L105) | `p1:fixed:propagation` | Conditional sums and propagation |
| [T4.4](../manuscripts/paper-p1/v2.0/sources/companion_sections/fixed_moments.tex#L152) | `p1:fixed:moments` | Fixed factorial moments |
| [T4.5](../manuscripts/paper-p1/v2.0/sources/companion_sections/fixed_moments.tex#L211) | `p1:fixed:curve` | Several disjoint square equations |
| [T4.6](../manuscripts/paper-p1/v2.0/sources/companion_sections/fixed_moments.tex#L263) | `p1:fixed:CRT` | A product certificate with fixed sources |
| [T4.7](../manuscripts/paper-p1/v2.0/sources/companion_sections/fixed_moments.tex#L379) | `p1:fixed:primitive` | Primitive families at a fixed order |
| [T4.8](../manuscripts/paper-p1/v2.0/sources/companion_sections/fixed_moments.tex#L397) | `p1:fixed:compressed` | Fixed primitive mass after pair compression |
| [T5.1](../manuscripts/paper-p1/v2.0/sources/companion_sections/short_supports.tex#L27) | `p13:short:moments` | Uniform moments for short split products |
| [T5.2](../manuscripts/paper-p1/v2.0/sources/companion_sections/short_supports.tex#L49) | `p13:short:old-space` | Short projections in an old space |
| [T5.3](../manuscripts/paper-p1/v2.0/sources/companion_sections/short_supports.tex#L103) | `p13:short:quadratic` | A quadratic kernel with a prescribed divisor |
| [T5.4](../manuscripts/paper-p1/v2.0/sources/companion_sections/short_supports.tex#L179) | `p13:short:split` | Kernels of a split product |
| [T6.1](../manuscripts/paper-p1/v2.0/sources/companion_sections/half_counts.tex#L21) | `p13:half:conditional` | Conditional full-support count |
| [T6.2](../manuscripts/paper-p1/v2.0/sources/companion_sections/half_counts.tex#L68) | `p13:half:connected` | Connected and primitive families at fixed order |
| [T6.3](../manuscripts/paper-p1/v2.0/sources/companion_sections/half_counts.tex#L100) | `p13:half:pairs` | Dependent pairs |
| [T6.4](../manuscripts/paper-p1/v2.0/sources/companion_sections/half_counts.tex#L145) | `p13:half:small-kernels` | Two small kernels |
| [T6.5](../manuscripts/paper-p1/v2.0/sources/companion_sections/half_counts.tex#L175) | `p13:half:smooth` | A large smooth modulus |
| [T6.6](../manuscripts/paper-p1/v2.0/sources/companion_sections/half_counts.tex#L234) | `p13:half:saturation` | Incoming and outgoing certificate counts |
| [T7.1](../manuscripts/paper-p1/v2.0/sources/companion_sections/confinement.tex#L48) | `p13:conf:near-primitive` | Dense triples with weak proper intersections |
| [T7.2](../manuscripts/paper-p1/v2.0/sources/companion_sections/confinement.tex#L63) | `p13:conf:strong-profile` | A strong nonaligned pair in a triple |
| [T7.3](../manuscripts/paper-p1/v2.0/sources/companion_sections/confinement.tex#L94) | `p13:conf:groups` | Polynomial confinement of common divisors |
| [T7.4](../manuscripts/paper-p1/v2.0/sources/companion_sections/confinement.tex#L265) | `p13:conf:dense-primitive` | Dense primitive triples |
| [T7.5](../manuscripts/paper-p1/v2.0/sources/companion_sections/confinement.tex#L293) | `p13:conf:dense-pairs` | Dense nonaligned pairs |
| [T8.1](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_rigidity.tex#L88) | `p13:rig:short-basis` | A short basis with a controlled loss of dimension |
| [T8.2](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_rigidity.tex#L127) | `p13:rig:common-curve` | A common curve |
| [T8.3](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_rigidity.tex#L166) | `p13:rig:grid-fibres` | Integer fibres in the offset grid |
| [T8.4](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_rigidity.tex#L214) | `p13:rig:bcn` | Binyamini--Cluckers--Novikov |
| [T8.5](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_rigidity.tex#L231) | `p13:rig:sublinear-grid` | Sublinear counts in the offset box |
| [T8.6](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_rigidity.tex#L270) | `p13:rig:nonaligned` | A uniform nonaligned rank bound |
| [T8.7](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_rigidity.tex#L342) | `p13:rig:aligned` | Rank on a known alignment |
| [T8.8](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_rigidity.tex#L366) | `p13:rig:triple` | Triple rank and maximum joint probability |
| [T8.9](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_rigidity.tex#L446) | `p13:rig:local-square` | A local square threshold |
| [T8.10](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_rigidity.tex#L463) | `p13:rig:defective` | Few defective positions in every critical window |
| [T8.11](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_rigidity.tex#L518) | `p13:rig:components` | Free components |
| [T8.12](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_rigidity.tex#L640) | `p13:rig:factor-height` | Height of a bivariate factor |
| [T8.13](../manuscripts/paper-p1/v2.0/sources/companion_sections/pair_rigidity.tex#L666) | `p13:rig:two-witnesses` | Two complete witnesses |
| [T9.1](../manuscripts/paper-p1/v2.0/sources/companion_sections/triple_activities.tex#L11) | `p13:activity:deficit` | The independent cost of one target after a pair |
| [T9.2](../manuscripts/paper-p1/v2.0/sources/companion_sections/triple_activities.tex#L33) | `p13:activity:incompatible` | Absolute activity of incompatible triples |
| [T9.3](../manuscripts/paper-p1/v2.0/sources/companion_sections/triple_activities.tex#L62) | `p13:activity:kappa3` | The third cumulant and the positive activity |
| [T9.4](../manuscripts/paper-p1/v2.0/sources/companion_sections/triple_activities.tex#L108) | `p13:activity:pair-partition` | A finite partition of the pair activity |
| [T10.1](../manuscripts/paper-p1/v2.0/sources/companion_sections/third_cumulant.tex#L59) | `p13:third:rational-rank` | A sharp rational overlap inequality |
| [T10.2](../manuscripts/paper-p1/v2.0/sources/companion_sections/third_cumulant.tex#L125) | `p13:third:aligned-family` | Triples meeting finitely many aligned channels |
| [T10.3](../manuscripts/paper-p1/v2.0/sources/companion_sections/third_cumulant.tex#L150) | `p13:third:aligned` | Strong aligned pairs |
| [T10.4](../manuscripts/paper-p1/v2.0/sources/companion_sections/third_cumulant.tex#L182) | `p13:third:lower` | The rational lower bound |
| [T10.5](../manuscripts/paper-p1/v2.0/sources/companion_sections/third_cumulant.tex#L527) | `p1:arith:palm` | Positive Palm cost of a fixed channel |
| [T11.1](../manuscripts/paper-p1/v2.0/sources/companion_sections/certificates.tex#L24) | `p1:core:rankin` | Counting a small truncated squarefree kernel |
| [T11.2](../manuscripts/paper-p1/v2.0/sources/companion_sections/certificates.tex#L65) | `p1:core:moderate` | Counting moderate certificates |
| [T11.3](../manuscripts/paper-p1/v2.0/sources/companion_sections/certificates.tex#L92) | `p1:core:degrees` | Incoming and outgoing saturation degrees |
| [T11.4](../manuscripts/paper-p1/v2.0/sources/companion_sections/certificates.tex#L111) | `p1:core:generator` | A generating function with marked isolated vertices |
| [T12.1](../manuscripts/paper-p1/v2.0/sources/companion_sections/exact_reconstruction.tex#L20) | `p13:transfer:dense-targets` | Conditional dense pair estimate |
| [T12.2](../manuscripts/paper-p1/v2.0/sources/companion_sections/exact_reconstruction.tex#L63) | `p13:transfer:compressed-target` | A dense compressed target |
| [T12.3](../manuscripts/paper-p1/v2.0/sources/companion_sections/exact_reconstruction.tex#L93) | `p13:transfer:small-kernels` | Several small kernels in one window |
| [T12.4](../manuscripts/paper-p1/v2.0/sources/companion_sections/exact_reconstruction.tex#L111) | `p13:transfer:primitive` | Homogeneous mass at fixed primitive arity |
| [T12.5](../manuscripts/paper-p1/v2.0/sources/companion_sections/exact_reconstruction.tex#L198) | `p13:transfer:independent-deficit` | Uniform independent deficit |
| [T12.6](../manuscripts/paper-p1/v2.0/sources/companion_sections/exact_reconstruction.tex#L292) | `p13:transfer:fixed-deficit` | A fixed number of extensions of a pair |
| [T12.7](../manuscripts/paper-p1/v2.0/sources/companion_sections/exact_reconstruction.tex#L336) | `p13:transfer:independent-tail` | Independent full-support tails |
| [T12.8](../manuscripts/paper-p1/v2.0/sources/companion_sections/exact_reconstruction.tex#L407) | `p13:transfer:pair-deficit` | The pair deficit over all cardinalities |
| [T12.9](../manuscripts/paper-p1/v2.0/sources/companion_sections/exact_reconstruction.tex#L448) | `p13:transfer:fixed-activities` | Reduction of connected activities |
| [T12.10](../manuscripts/paper-p1/v2.0/sources/companion_sections/exact_reconstruction.tex#L593) | `p13:transfer:anchor-budgets` | Certificate budgets with several anchors |
| [T12.11](../manuscripts/paper-p1/v2.0/sources/companion_sections/exact_reconstruction.tex#L663) | `p13:transfer:uniform-tail` | Uniform connected and primitive tails |
| [T13.1](../manuscripts/paper-p1/v2.0/sources/companion_sections/uniform_support.tex#L15) | `p1:uniform:full-support` | A uniform weighted count of full supports |
| [T14.1](../manuscripts/paper-p1/v2.0/sources/companion_sections/poisson_calculus.tex#L19) | `p1:discussion:charlier-norm` | Norms of Poisson differences |
| [T15.1](../manuscripts/paper-p1/v2.0/sources/companion_sections/moment_obstruction.tex#L8) | `p1:obstruction:fixed` | A perturbation invisible at each fixed order |
