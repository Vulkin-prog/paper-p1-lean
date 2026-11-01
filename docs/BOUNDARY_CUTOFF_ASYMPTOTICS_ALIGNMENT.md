# The source least cutoff: its exact asymptotic and critical range

The unnumbered cutoff claims accompanying T12.2 are now proved:

    K_N / (log N / loglog N) -> 3,
    K_N / log N -> 0,
    K_N -> infinity,
    K_N <= floor(L/4) eventually throughout the fixed critical band.

The cutoff is the exact least integer satisfying the manuscript's two
requirements, with a fixed arbitrary positive real upper mean Lambda.
It is not replaced by a trial order. This extends P1-MATH-0052 and its
source alignment; numbered coverage remains 56/167.

Source context: companion Section T12,
`companion_sections/stopped.tex:100-117`, immediately before
`p1:stop:tail` (T12.2, page 50; statement hash
`58419af8ab6f89d036eca8383642d845b56d29aec345513766e926272b6359ce`).

## Trial orders and the least cutoff

The previously audited actual moderate order has normalized limit 2/A.
`ModerateOrderLogarithm` proves its logarithm divided by loglog N tends
to one, its real value tends to infinity, and its actual logarithmic
cutoff cost divided by log N tends to 2/A. All statements concern the
literal rounded order, not a continuous surrogate.

For every A>0 with 2/A>3, that order eventually satisfies both source
cutoff conditions. Minimality then bounds the actual K_N by the trial.
In particular K_N/log N tends to zero. Together with the lower critical
length bound, this proves the literal integer inequality K_N<=L/4,
under one threshold before all critical lengths. These thresholds may
depend on the fixed band and upper mean, as in the source.

## The coefficient three

`BoundaryCutoffScale` supplies a matching normalized lower bound from
the defining cost. Once K_N<=log N,

    3 / (1 + |log(2*exp(1)*Lambda)|/loglog N)
      <= K_N*loglog N/log N.

The left side tends to three. For every upper comparison strictly
above three, choose a trial whose normalized limit lies between it
and three. This gives both order-topology conditions for convergence
of the normalized actual cutoff to three. The displayed source
asymptotic follows by exact algebraic transport of the denominator.
Comparison with one growing trial also proves divergence of the
actual cutoff, first as a real sequence and then as a natural sequence.

No manuscript bytes, numbered-result completion, new finding,
unproved literature input or Paper C port are added at this checkpoint.
The earlier full T12.2 and improved N^(-5/3) mass bounds remain proved.

The full build passed (9,551 jobs), the actual axiom audit passed for
all 3,870 declarations, and Lean checked all 1,585 distinct
coverage/finding names. Only propext, Classical.choice and Quot.sound
occur; original manuscript bytes are unchanged.

Validated exact cutoff-asymptotic checkpoint (9,551 build jobs;
3,870 audited declarations; 1,585 directly checked names):
[e220886c65aecc4b2f1f7ca78165ab6b2b6a60a1](https://github.com/Vulkin-prog/paper-p1-lean/commit/e220886c65aecc4b2f1f7ca78165ab6b2b6a60a1).
