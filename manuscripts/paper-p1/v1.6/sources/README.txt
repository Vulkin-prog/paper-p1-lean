P1 VERSION 1.6 -- 31 OCTOBER 2026
Sharp Poisson approximation and second-order correction
for long multiplicative runs
Author: Brice Pouly
Mathematical and editorial assistance: ChatGPT (GPT-6 Astra)

ONE WORK IN TWO ASSOCIATED DOCUMENTS
-----------------------------------
main.tex builds the main article.
companion.tex builds its technical companion.
editorial/note_revision_fr.tex builds the French revision note and response.

The article follows the exact-marginal proof. The companion contains
necessary technical proofs and further results. Both documents are needed
to assess the complete argument. Companion references begin with T.
The V1.6 revision incorporates the follow-up audit of V1.5 supplied on
31 October 2026. It consolidates the reference comparisons, explains the
ternary witness and the larger two-pair scale, separates the three errors
in reconstruction, and adds local proof-return routes. It preserves the
numbered mathematical statements and the two-document architecture.

ONE VERIFICATION COMMAND
------------------------
From this directory run:

    python3 check_all.py

This command performs, in order:
1. Alternating builds of main.tex and companion.tex until all internal
   and external references stabilize.
2. The five finite diagnostics listed below.
3. Conservation, numbering, cross-reference, layout-log and PDF-link checks.
4. The French revision-note build, using the verified page/link counts.

The execution record is editorial/verification_run.json. Temporary logs
are under build/checks/. A nonzero return code stops the command and
identifies the failed step. This command checks documents and selected
finite identities; it does not verify the asymptotic mathematical proofs.

For a manuscript-only rebuild use python3 build.py or sh build.sh.
The circulation filenames are:

    build/P1_V1_6_Main_Article_2026-10-31_EN.pdf
    build/P1_V1_6_Technical_Companion_2026-10-31_EN.pdf

Keep these PDFs together with these exact names for cross-document links.
Printed T references remain usable if a PDF reader does not follow them.
An isolated pdflatex call is not a complete build of this edition.
The French note can be rebuilt after the reference check with:

    sh editorial/build_note.sh

It produces editorial/build/note_revision_fr.pdf.

DEPENDENCIES
------------
Python 3 and a conventional TeX installation with pdflatex and latexmk.
Packages: amsmath/amssymb/amsthm, mathtools, mathrsfs, lmodern, microtype,
geometry, booktabs, longtable, array, tabularx, xcolor, enumitem, fancyhdr,
needspace, etoolbox, placeins, xr-hyper, hyperref, bookmark and xurl. The note
requires French babel support. The reference audit needs Python pypdf.
All five exact diagnostic scripts use Python's standard library.

The supplied PDFs were compiled with pdfTeX 1.40.25 and LaTeX2e 2023-11-01.
No bibliography processor is needed: bibliography.tex is shared by both
articles. Citation labels are not imported through xr-hyper, so each
PDF has its own complete bibliography.

SOURCE ORGANIZATION
-------------------
main_sections/       Main statements, exact marginals, stopped expansion,
                     reconstruction, quartic lower bound and consequences.
companion_sections/  Detailed arithmetic and conditional proofs, regular-set
                     reconstruction, positions and supplementary results.
preamble.tex         Common notation and typesetting.
assistance.tex       AI-assistance statement and source information.
editorial/           French note, version correspondence, proof-review records,
                     reference baseline, checks and revision history.
diagnostics/         Five exact finite scripts and their result files.

The companion guide separates the technical inputs to the scalar theorem,
the regular-set branch used for positions, and the supplements T19--T23.
Within those last sections, the positional proof in T19 supplies main
Lemma 20.1; the other results are not inputs to the optimal scalar theorem.

CONSERVATION AND TRACEABILITY
----------------------------
The 545 labels of V1.5 are retained exactly once. The 167 numbered
results retain their document and number: 73 in the main article,
94 in the companion. The 166 proof environments are retained.

editorial/correspondance_V1_5_V1_6.csv maps all V1.5 labels to their new
pages and source files. editorial/resultats_V1_5_V1_6.csv selects the
167 theorem/proposition/lemma/corollary statements.
editorial/v15_reference_baseline.json contains the label baseline;
editorial/v15_statement_baseline.json records the exact statement hashes.
The earlier baselines and correspondence files remain available.

After a build, python3 editorial/check_references.py checks label
conservation, statement counts, numbers and exact text, unresolved
references, overfull boxes, and internal/cross-document PDF destinations.
It writes editorial/references_audit.json,
editorial/statement_text_preservation.json and editorial/production_metrics.tex.
The last file supplies actual counts to the French note.

editorial/reviews/ contains the V1.6 targeted reviews of T5--T6, T9,
T11 and the uniform reconstruction, plus the editorial nonregression
review. These records describe their exact scope; they do not certify
all asymptotic proofs. editorial/revision_response.json maps E1--E6,
S1 and N1 to the changes. editorial/reviews_v15/ and
editorial/history_v15/ retain the prior edition's records, alongside
those from V1.4. Private audit reports are not scientific references.

FINITE DIAGNOSTICS: EXACT IDENTITIES AND RANGES
---------------------------------------------
Each script uses integers or rational arithmetic. Each writes JSON next
to itself. The single verification command runs all five; individual
scripts can also be run with python3 diagnostics/FILENAME.py.

heterogeneous_formal_checks.py:
    Eight finite joint Bernoulli laws and 112 checks of heterogeneous marginals,
    centered coefficients, pair-corrected Bernoulli identities and formal
    factorial-cumulant identities through order four.

stopped_exact_checks.py:
    Every hereditary class containing the empty set on 1, 2, 3 or 4 sites,
    for every binary indicator state: exact first-excluded-prefix identity.
    Also the fully dependent suffix example, the retained-pair deficit
    identity, and positivity thresholds at means 1/3, 1, 5/2 and 7.

coefficient_exact_checks.py:
    Finite channel formula for all coprime 1 <= a < b <= 12, b >= 2,
    lengths 1..96 and both endpoint signs. Signed placements for lengths
    1..100. Exact second Charlier-difference norms at means 1 and 2,
    and the total-variation coefficient 1/(12e) at unit mean.

channel_and_triple_checks.py:
    Channel identities at lengths 5..150 and reduced interior heights
    3..10 with L >= b, the combined height-five identity, and rational prefactors of the
    phase constants at heights 4, 5 and 6. Primitive triples with 2 <= u < 150 and
    u < v < w < 2u, testing the 19/30 bound in this finite range.
    The canonical 10:12:15 witness nullity for lengths 31..300.

certify_biquadratic.py:
    One exact rational symbolic instance of the biquadratic auxiliary
    construction and the associated cancellation identities.

These finite checks do not establish the general 19/30 inequality,
coefficient/degree-uniform arithmetic estimates, growing-order tails,
or the full asymptotic law. Their domain is deliberately explicit.

MAIN V1.6 CHANGES
----------------
- E1: one table in the introduction separates six references/observations,
  their parameters, and the precision actually established.
- E2: the 10:12:15 witness is previewed through its 19L/30 nullity;
  the two-pair fourth-order scale is compared with the ternary scale.
- E3: Section 15 begins with the three norm errors through T_D2 and B2,
  preserving incompatible-pair covariances and the full B2 conversion.
- E4: the companion guide links each of five article entries to the
  complete proof subsection and its next application in the article.
- E5: repeated end-of-article scope summaries are replaced with precise
  references, and eventual moment equality is explicitly quantified.
- E6: the full diffusion bundle keeps both manuscript PDFs, the French
  response note and this source archive together under the supplied names.
- S1: separate targeted counter-reads reconstruct the degree dependence,
  conditional induction, common curve, dense targets and uniform tail.
- N1: exact statement-text conservation supplements the existing number,
  label and PDF-link checks; the editorial scope distinctions are reviewed.

DISTRIBUTION
------------
P1_V1_6_Complete_2026-10-31.zip contains both English manuscripts, the
French revision note, P1_V1_6_Sources_2026-10-31.zip, and a short reading
and rebuild guide. Extract its files together; keep the two scientific
PDF filenames unchanged for the cross-document links.

SCOPE PRESERVED
---------------
The exact quadratic reference has optimal power 4/3 with arbitrary fixed
epsilon margins, without a complete leading remainder constant.
The third factorial cumulant has optimal power 41/30, with a positive
10:12:15 witness, without a general leading constant.
Fixed-height explicit references have optimal power h/(h+1) and the
first-omitted-height equivalent; h does not grow with N.
The exact Hermite reference retains an upper bound of power 4/3. The
quadratic lower bound is not asserted for that reference.
The positional comparison has power 4/5 and every fixed polynomial
count weight; it retains unsigned integer positions.
The Bernoulli conversion uses all covariance terms. Raw arithmetic rank
and effective relative rank retain their explicitly separate conventions.

No independent human verification, proof-assistant certification, journal
submission or publication is claimed by this revision. The author remains
responsible for the claims and any submission.

MANIFEST
--------
MANIFEST_SHA256.txt records hashes of all archived source and review files,
excluding itself. Build products, temporary renders and file-transfer
helpers are not part of this source archive.
