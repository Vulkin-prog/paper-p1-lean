# All-pair finite reconstruction toward main15.13

Source: main_sections/exact_transfer.tex:887. The unconditional finite mechanism and large-boundary tail are proved; the complete fixed-order implication is still in progress.

Main15.13 is now IN PROGRESS with its unconditional exact finite
reconstruction and unconditional large-boundary tail. Its complete
implication from the254 fixed connected-activity estimates is NOT yet
claimed. This checkpoint does not add a completed numbered result.

The literal all-pair class D2 on ANY finite actual ground G is constructed:
I is retained when its original square-class spaces are direct, or its
nullity equals that of one contained pair. Every pair of G is allowed,
including incompatible pairs and pairs with zero covariance. Heredity,
empty-set membership and retention of every pair are proved. For a
positive dyadic ground, every first excluded prefix has positive nullity
at most2L, and every subfamily has compatible nullity at most2L.
This is the full2L boundary, not the smaller good-pair boundary from T17.5.

UnrestrictedRetainedExpansion proves the exact inverse-centering expansion
on this class:

  q(I) = product_I p_x + sum_(e subset I, |e|=2) c(e)*product_(I minus e) p_x.

No positivity or compatibility premise is imposed. If a marginal is zero,
the actual centered coefficient vanishes by the already proved zero-mass
argument. Otherwise the full-support relation criterion proves that all
centered coefficients of size at least3 vanish on a retained family.
A primitive original family has c(I)=q(I)-product_I p_x, including the
incompatible case q(I)=0, and product_I p_x<=|c(I)|. Canonical nullity
additivity separately proves that every primitive family is connected;
its compatible nullity is at mostL on the positive dyadic ground.

AllPairPolynomialExpansion proves an exact finite commutative-ring
identity, retaining EVERY signed pair weight. Specialization identifies
the all-pair reference with the full heterogeneous Bernoulli product plus
its signed covariance corrections. SecondOrderRetainedReference proves
that its difference from the actual D2 retained polynomial is precisely
the negative discarded sum of the independent and signed pair terms.
In particular, no incompatible covariance is replaced by a joint event
probability and no equal-marginal reduction is used.

SecondOrderIndependentDeficit charges the independent mass of discarded
families to primitive sources of size at least3 and failed extensions of
a contained pair. For the latter, nonretention itself proves failure of
directness after compression. The exact complement map is injective in
every source fiber. Arbitrary u>=0, arbitrary finite source ground and all
cardinalities are covered; the primitive independent weight is bounded by
its actual centered activity even for incompatible systems.
SecondOrderPositiveMass removes the empty coefficient and the ENTIRE
one-pair contribution before applying the actual canonical-component
generator. The resulting finite probability bound holds for EVERY K.

SecondOrderStoppedLaw.finite_bound is an unconditional bound for the
actual ORIGINAL normalized count law, at any positive dyadic ground,
L>0 and arbitrary K. Write A=sum_pairs 4|c(e)|, T=sum_(connected C,
3<=|C|<=K,compatible-nullity<=2L) 2^|C|*|c(C)|, P=sum_(primitive D,
|D|>=3)2^|D|*|c(D)|, D=the literal all-pair failed-extension deficit
at weight2, and M=sum_x2p_x. Then its exact checked bound is

  distance(Law Z_G, embed B2) <=
    2 exp(M)*P +16 D + exp(M)*(exp(A+T)-1-A) +largeBoundaryMass.

All quantities on the right are explicitly defined finite actual sums.
The original law is transported through an actual containing finite
cylinder and the exact stopped expansion, whose suffix remains positive.
No eventwise polynomial is treated as a probability law.

SecondOrderBoundaryCutoff evaluates the already defined least cutoff at
N^2. It is PROVED to be o(log N), and the log-budget tail is then N^-6.
The literal2L boundary costs O_C(N^2), giving the unconditional final
large-boundary bound2^(2C)*N^-4, uniformly for all G in the dyadic block.
All irregular windows, exact heterogeneous marginals, zero masses and
incompatible systems are retained. No growing-order moment premise is
used for this tail.

This checkpoint adds9 modules,36 theorems and10 definitions. Coverage
remains87/167 unconditional and30 conditional; confirmed mathematical
improvements remain146. These are exact proof constructions and do not
receive a new correction identifier. The next step is to insert the
source254 fixed connected-activity hypotheses, combine the proved tails,
pair activity and pair deficits, and perform the existing sharp analytic
conversion. Main15.13 stays in progress until that implication is checked.
No dependency download, source-byte change, Paper C port, hidden axiom
or Palomar registration is introduced.

The main15.13 JSON row records the direct validation and exact proof commit.
