# P1 six-registration preparation

Exactly six registrations are planned, with one complete cycle open at a time. All 68 component selections are preserved; the seventeen old component receipts remain separate evidence.

| Order | Registration | Selected declarations | Configuration and metadata |
|---:|---|---:|---|
| 1 | Arithmetic and geometry | 12 | [configuration](../../comparator/registrations/p1_arithmetic_geometry.json), [metadata](arithmetic_geometry/formalization.yaml) |
| 2 | Arithmetic profiles and smooth logarithmic windows | 6 | [configuration](../../comparator/registrations/p1_profiles_smooth.json), [metadata](profiles_smooth/formalization.yaml) |
| 3 | Finite affine structure, conditioning and dependent expansions | 12 | [configuration](../../comparator/registrations/p1_affine_conditioning.json), [metadata](affine_conditioning/formalization.yaml) |
| 4 | Factorial cumulants, moments and private obstructions | 14 | [configuration](../../comparator/registrations/p1_cumulants_obstructions.json), [metadata](cumulants_obstructions/formalization.yaml) |
| 5 | Poisson approximation, scales and positional reference fields | 16 | [configuration](../../comparator/registrations/p1_poisson_fields.json), [metadata](poisson_fields/formalization.yaml) |
| 6 | Exponential moments and prime cylinders | 8 | [configuration](../../comparator/registrations/p1_exponential_cylinders.json), [metadata](exponential_cylinders/formalization.yaml) |

Every complete original proof body and local model definition is relocated coherently into a distinct model namespace in each consolidated Challenge/Solution pair. The [plan](../REGISTRATION_PLAN.json) records the exact bijection and original source hashes. The [reconstruction checker](../../scripts/check_registry_consolidation.py) rejects any other change to those bodies. The original statement scopes, hypotheses and quantifiers are retained.

All active author, responsible-maintainer and self-paper source records contain `name: Brice Pouly`, `github: Vulkin-prog`, `orcid: 0009-0008-8491-2467`. The official Palomar parser recognizes the structured association. The published community v0.4 schema permits only name strings: a name-only projection is checked separately, and is never described as validation of the actual structured file. The [ORCID check](supplementary/metadata-orcid-validation.json) records the parser and the public current-record lookup; that lookup does not authenticate the person or attest the submitter relationship.

Standalone six-checker results, frozen-root qualification, the full Palomar workflow, intake, private editorial review, the human publication decision and permanent registration are distinct stages. The workflow mutex only covers execution. The operator must close the whole current cycle before starting the next, as specified by [the procedure](../../docs/PALOMAR_PLAN.md). No submission or registry identifier is claimed.

All six consolidated pairs passed exact standalone statement comparison and all six local checkers. The frozen-root replay at `aed23a21dea8eb62e73df3e281db9583716fe106` passed **18,611 build jobs**, **19,935 theorem axiom checks** and **19,854 declaration references**, with all three actual exits zero. The substantive inventory remains 19,507; 214 preserved component wrappers and 214 consolidated wrappers complete the audit. The [full replay](../../docs/validation/registry-six-registrations/validation.json) preserves its source and logs.

- Arithmetic and geometry: [frozen-root qualification](arithmetic_geometry/qualification.json), [standalone six-checker report](supplementary/arithmetic_geometry-draft-checks.json).
- Arithmetic profiles and smooth logarithmic windows: [frozen-root qualification](profiles_smooth/qualification.json), [standalone six-checker report](supplementary/profiles_smooth-draft-checks.json).
- Finite affine structure, conditioning and dependent expansions: [frozen-root qualification](affine_conditioning/qualification.json), [standalone six-checker report](supplementary/affine_conditioning-draft-checks.json).
- Factorial cumulants, moments and private obstructions: [frozen-root qualification](cumulants_obstructions/qualification.json), [standalone six-checker report](supplementary/cumulants_obstructions-draft-checks.json).
- Poisson approximation, scales and positional reference fields: [frozen-root qualification](poisson_fields/qualification.json), [standalone six-checker report](supplementary/poisson_fields-draft-checks.json).
- Exponential moments and prime cylinders: [frozen-root qualification](exponential_cylinders/qualification.json), [standalone six-checker report](supplementary/exponential_cylinders-draft-checks.json).
