# Actual imaginary quadratic fields and integral norm coordinates

Source: main13.4 conic preparation. Trace/norm basis proofs adapt Paper C commit b9fa9ba490f201b408a302a86f1594ee620b228b, blob 6b970b5d96de14a796c4f0ec8fcd30cf3ebe2d11, Vulkin-prog, Apache-2.0; trace unchanged and norm sign changed, all rechecked under Lean v4.36.0-rc2.

ImaginaryQuadraticOrder constructs the actual quadratic number field Q(sqrt(-D)) and its full ring of integers for every positive natural D. The negative defining coefficient cannot be a rational square; the field, number-field and quadratic-extension instances are proved internally. D need not be squarefree. No conductor comparison or imported norm-counting assumption is used.

The module proves integrality of sqrt(-D), its exact square, the trace formula 2*re and the positive norm formula re^2+D*im^2. The actual integral element alpha(x,y)=x+y*sqrt(-D) is injective on signed integer pairs and has norm x^2+D*y^2. A solution of this norm equation yields the actual integral identity alpha*beta=m. Every integral element has an integer trace, with a chosen trace integer and a proved coordinate equality.

The basis trace and norm calculations are adapted from the existing QuadraticOrderConductor module, whose Paper C source is Vulkin-prog, Apache-2.0, commit b9fa9ba490f201b408a302a86f1594ee620b228b, blob 6b970b5d96de14a796c4f0ec8fcd30cf3ebe2d11. The precise statement comparison is recorded: replacing D by -D leaves the trace formula unchanged and replaces re^2-D*im^2 by re^2+D*im^2. The adapted proofs compile anew under Lean v4.36.0-rc2; no earlier compiled artifact is reused.

This checkpoint provides the field, integral norm and trace foundation for negative-discriminant conics. It does not yet prove their point count or a finite unit bound. Hyperbolic conics remain proved by checkpoint389, while the negative-discriminant counting step, parabolas and the stronger general BCN and original all-dimensional main13.4 remain open. No numbered result is promoted.

P1-MATH-0390 adds twelve theorems, six definitions or abbreviations and three proved instances. Coverage stays92 proved and72 conditional out of167, with164 completed and three in_progress. The ledger records388 improvements and two statement-scope corrections. No new axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
