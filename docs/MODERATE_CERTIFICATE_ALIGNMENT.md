# Moderate certificates — article Lemma 7.2

**Status: in progress; not a completed numbered result.** Source: article
V1.6, page 23, `main_sections/cores.tex:65`, label `p1:core:moderate`.
Exact statement SHA-256:
`9594d0ca09a407ca09f83dbf5e3e3a35c779690b9000a1041eb967ba1042956a`.

## Proved actual receiving-centre population

For a fixed finite congruence certificate, receiver i has actual modules
G(i,p) and offsets w(i,p). `ModerateReceiverCost.assignments` is exactly the
finite set of receiving-centre tuples in [U,U+N) satisfying every divisibility
G(i,p) | z(i)-1+w(i,p). `mem_assignments` proves that full description.
The combined receiver modulus D(i) is the actual product of its modules.
Empty groups have modulus one and are retained.

`ShortIntervalCongruences.card_common_residue_le` proves that a finite set
of centres in a length-N interval with a common residue modulo q has at most
floor(N/q)+1 elements. The proof subtracts the attained least centre and
injects all other centres into their actual quotient range. It covers every
interval position and even the degenerate q=0 case.

For coprime groups, the proved finite lcm/product identity combines all
congruences. `card_fibre_le` gives at most floor(N/D(i))+1 possible centres,
without an assumed CRT count. The actual Cartesian-product cardinality
then bounds receiving tuples by prod_i(1+N/D(i)).

## Proved finite modulus cost

If N>=10, every D(i)>=1 and prod_i D(i)<=9*N^2, then at most two D(i)
exceed N. `ModerateModuli.large_card_le_two` proves this: three such entries
would force a product at least (N+1)^3>9*N^2.

For a real cap A>=1 and D(i)<=A*N,

`1+N/D(i) <= (if D(i)>N then A else 1) * 2*N/D(i)`.

Multiplying the proved termwise inequalities and retaining the exact count
of large modules gives a factor at most A^2.
`product_cost_le` proves the complete finite inequality. With A=6*B,
`card_assignments_le_moderate` therefore proves

`card(assignments) <= 36*B^2*2^h*N^h / prod_i D(i)`,

where h is the number of receivers. This h is separate from the source's
prime-assignment exponent m=ceil(2*log(3N)/log(Y)). The source receiver
count has h=r-1. All coprimality, positivity, product and cap assumptions
are displayed certificate data; none is a target counting estimate.

## Remaining obligations

The actual anchor kernels still need to be shown to produce a covering
family of such certificates, with their correct product, coprimality and
source-dependent bounds. The source anchor/offset count and the (r*B)^m
prime-assignment factor remain to be proved. The weighted series over all
orders and the uniform growing-order asymptotic also remain open.

Thus the receiving-cost theorem alone does not prove the full first source
bound, nor the weighted second conclusion. It adds no completed numbered
result and does not confirm a new mathematical improvement.

## Inputs and validation

No additional Paper C source is ported. Mathlib at
`9d581dfff2e41de989072ea63abf3daf69311520` supplies natural division,
finite lcm/product identities, Cartesian-product cardinalities and finite
product inequalities. All displayed congruence and cost estimates are proved
in this project.

The full Lean v4.36.0-rc2 build passed (8,851 jobs), followed by the actual
axiom audit of all 2,047 project theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Completed coverage remains
31 / 167. No Palomar registration is made.

All 320 distinct coverage/finding declaration names were checked directly by Lean.
