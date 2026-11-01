# The fixed-kernel branch of T5.1 and a divisor-grouped congruence count

This checkpoint proves the first actual prescribed-kernel bound in
T5.1, together with an alternative finite congruence-count ingredient
for its second bound. Full T5.1 is still in progress; coverage remains
56/167. The stronger first-branch shift scope and proof simplification
are P1-MATH-0053.

Source: `p13:short:quadratic`, companion T5.1, page 31,
`companion_sections/short_supports.tex:9`; original statement hash
`98eb59430167ea84a4dd75c36b107f990646c6c2f47783b8292f95e2659899bb`.

## Actual canonical kernels, including the square case

`QuadraticKernelFibres` uses the existing canonical squarefree part
of n(n+h), with every prime of odd exponent, including 2. The actual
canonical square part gives

    n(n+h) = q*v^2,
    (2n+h)^2 - 4q*v^2 = h^2.

For n>0, q and v are proved positive. The actual embedding into the
quadratic equation is injective through its first coordinate. All
coefficient, coordinate and right-hand-side heights are derived from
polynomial bounds on n and h. In particular q does not require a
separately assumed coefficient-height bound. The already proved
uniform positive quadratic count includes q=1 and its factorizable
equation; no nonsquare exception is omitted.

For every fixed natural K and epsilon>0, one threshold before X,h,q
and the finite solution set proves that a fixed kernel has at most
N^epsilon positive n<=X, whenever 0<h, X<=N^K and h<=N^K.
The shift may therefore have polynomial height in this first branch.

## A prescribed divisor and the first actual count

An actual kernel set with q<2Q and e|q, e>0, injects into the positive
integers q/e<=floor(2Q/e). Thus its size is at most floor(2Q/e),
without a separate additive one. Combining this exact finite bound
with the actual fixed-kernel fibres and absorbing the constant 2
proves

    #n <= N^epsilon * Q/e.

`PrescribedQuadraticKernelCount.values` is the literal finite set of
positive n<=X with Q<=sf(n(n+h))<2Q and prescribed e dividing that
actual kernel. Its count has one common threshold before every
X,h,Q,e. No squarefreeness premise on e is needed in the proof;
divisibility and positivity suffice for this branch.

This is the source first exponent beta-delta at Q=N^beta,
e=N^delta. It does not extend the second branch to polynomial shifts.

## Direct congruence counting through gcd groups

`SplitQuadraticCongruences` counts actual positive n<=X for which
M divides n(n+h), with M,h>0. Group by g=gcd(M,n), so g is an
actual divisor of M. Cancellation in the integer congruence proves
M/g divides n+h. The constructed quotient pair satisfies

    (M/g)*b - g*a = h,     g*a=n.

The already proved exact linear-fibre step and gcd divisibility then
give at most X*h/M+1 points in each g-group. The resulting finite bound is

    #n <= tau(M)*(X*h/M+1).

For polynomial-height M and polylogarithmic positive h, the existing
uniform divisor estimate and a proved logarithmic-power bound give

    #n <= N^epsilon*(X/M+1),

uniformly in the actual modulus, shift, upper endpoint and finite
root set. This proof does not classify prime-power roots or invoke
a CRT counting assertion. Its divisor cost tau(M) suffices for the
required subpolynomial factor; no comparison with the source's
different finite h*2^omega(M) bound is asserted.

## Remaining scope at this historical checkpoint

The second T5.1 branch still needs the actual square-part size range,
the sum over its values and the resulting second exponent. Their
combination with the first branch and the final affine exponent are
not yet claimed. This checkpoint adds no new unproved literature
input, Paper C port, manuscript revision or Palomar registration.

The subsequent [complete counting checkpoint](QUADRATIC_KERNEL_COMPLETE_COUNTS_ALIGNMENT.md)
closes both counts and their min/affine consequences. Its range qualification
explains why the literal numbered statement is still not counted as complete.
