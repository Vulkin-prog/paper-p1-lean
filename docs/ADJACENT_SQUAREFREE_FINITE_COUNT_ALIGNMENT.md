# Unconditional finite lower count and arbitrarily large adjacent-squarefree witnesses

Source: companion T5.1, companion_sections/short_supports.tex:9; its exact exponent comparison and the qualification recorded in P1-MATH-0054. Original source hashes remain preserved.

The adjacent-squarefree source construction is now unconditional. For every natural endpoint X, the actual good population consists of n in [1,X] for which both n and n+1 are squarefree. Its complement is covered by a finite union of the actual square-divisor events for modulus4 and odd square moduli. Every nonsquarefree positive integer supplies a prime square divisor; the corresponding modulus index and finite range membership are proved explicitly.

For each shift t and positive modulus d, the number of starts n in [1,X] with d dividing n+t is at most (X+t)/d. This uses the injective translation into actual positive multiples and the earlier proved divisible_card lemma, with no additive floor error. For t=0 and t=1, each pair of bad events has total cardinality at most 2(X+1)/d. Applying the exact reciprocal budget from P1-MATH-0313 proves bad(X) <=35(X+1)/36 and therefore good(X)>=(X-35)/36.

The explicit finite lower bound proves that for every M there is N>max(1,M) with both N and N+1 squarefree: take X=36(max(1,M)+2)+35, then the good population cannot fit inside [1,max(1,M)]. No squarefree-density theorem, asymptotic input, computational primality assertion or target count is assumed.

P1-MATH-0314 completes the elementary source-witness existence theorem. The conversion of these witnesses into actual T5.1 kernel data and a quantified failure of its unqualified exact exponent display remains for the next step. The actual T5.1 count conclusions remain already proved; this preparatory arithmetic theorem does not change numbered coverage. Coverage stays89 proved and75 conditional out of167 (164 completed). There are313 improvements and one statement-scope correction. No new ordinary input, axiom, dependency download, compiler change or manuscript edit is introduced. Palomar remains deferred.
