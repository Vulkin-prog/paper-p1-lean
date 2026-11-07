# One-sided prime-cylinder strengthening

Checkpoint P1-MATH-0986. Source: companion proposition T19.7 and its original one-negative-prime cylinder proof. Original source hashes and all numbered statement blocks are preserved.

In the one-negative-prime sample, starts q*u+1 of length at least q-1 require only q not dividing u. The condition q not dividing u+1 enforces the next opposite sign and is unnecessary for the actual run-start observable. Keeping the larger one-sided parameter set proves the finite lower bound N/q-N/q^2-3, improves the previous valid N/q-2N/q^2-4 bound, and strengthens the actual positive and total exponential-moment lower bounds. The original odd-prime scale, t>2 range and (t-2)log(2) liminf coefficient are preserved.

For every prime q<=N and real t>=0, the exponential of

```text
t * (N/q - N/q^2 - 3) - primeCount(2*N+q-1) * log(2)
```

is a lower bound for each actual positive and total run-start exponential moment at length q-1. The probability law is the original independent fair prime-sign law. The finite sample event has the same exact probability as in the earlier construction. Only the retained start set grows.

The positive start needs a preceding negative sign and the next q-1 positive signs. Removing the extra right-end restriction keeps every original forced start. A single residue-class exclusion gives the sharper cardinality budget, including all floor and endpoint errors. The finite lower bound strictly improves the previous algebraic bound. The threshold t>2 and its asymptotic coefficient are unchanged; sharpness of that threshold is not asserted.

Full Lean v4.36.0-rc2 replay passed at source 1f25a899d04ff2bac781747b2e7fe5cef42e6c7c: 18,563 build jobs, 19,452 source-discovered theorem axiom checks and 19,625 distinct declaration-reference checks, all actual process exits 0. Proof warnings are errors; only propext, Classical.choice and Quot.sound occur.

The complete replay and original compressed logs are preserved in [the validation record](validation/checkpoint-0986/validation.json).

The stronger finite bound is integrated in the unnumbered version 1.7 companion formalization appendix. Both revised PDFs were rebuilt and reviewed; all 167 numbered statement blocks are unchanged. See [the manuscript validation](manuscript-v1.7-validation.json).

The later [supported-cylinder refinement](SUPPORTED_PRIME_CYLINDER.md) retains this count and reduces its probability charge to the prime signs actually used by these starts.
