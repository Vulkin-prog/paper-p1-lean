# One-sided prime-cylinder strengthening

Checkpoint P1-MATH-0986. Source: companion proposition T19.7 and its original one-negative-prime cylinder proof. Original source hashes and all numbered statement blocks are preserved.

In the one-negative-prime sample, starts q*u+1 of length at least q-1 require only q not dividing u. The condition q not dividing u+1 enforces the next opposite sign and is unnecessary for the actual run-start observable. Keeping the larger one-sided parameter set proves the finite lower bound N/q-N/q^2-3, improves the previous valid N/q-2N/q^2-4 bound, and strengthens the actual positive and total exponential-moment lower bounds. The original odd-prime scale, t>2 range and (t-2)log(2) liminf coefficient are preserved.

For every prime q<=N and real t>=0, the exponential of

```text
t * (N/q - N/q^2 - 3) - primeCount(2*N+q-1) * log(2)
```

is a lower bound for each actual positive and total run-start exponential moment at length q-1. The probability law is the original independent fair prime-sign law. The finite sample event has the same exact probability as in the earlier construction. Only the retained start set grows.

The positive start needs a preceding negative sign and the next q-1 positive signs. Removing the extra right-end restriction keeps every original forced start. A single residue-class exclusion gives the sharper cardinality budget, including all floor and endpoint errors. The finite lower bound strictly improves the previous algebraic bound. The threshold t>2 and its asymptotic coefficient are unchanged; sharpness of that threshold is not asserted.

Direct Lean v4.36.0-rc2 verification passed for all 12 new theorems with proof warnings as errors. Full project build, source-discovered axiom audit and declaration-reference replay are pending at this source checkpoint.
