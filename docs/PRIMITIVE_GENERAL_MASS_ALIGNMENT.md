# Elementary fixed-order primitive weight

Source: main Proposition 15.5, `p13:transfer:primitive`,
`main_sections/exact_transfer.tex:219`, page 41. This result is
**in progress**: all fixed orders r>=5 are proved, but r=4 is open.
Companion T4.3 is also in progress for the precisely scoped preparation below.
Coverage remains 72/167.

## Effective minimal nullity

`PrimitiveNullity.delete_bound` proves the exact one-coordinate nullity
bound by the deleted nullity plus the actual local rank, for finite
families of finite binary subspaces in an arbitrary ambient module.
No finite-dimensional ambient assumption is needed. For a family with
every proper subfamily direct, `minimal_bound` bounds full nullity by
every local rank. `PrimitiveWindowMass.primitive_nullity_le` combines
this with the actual effective window rank bound, giving rho<=L.

The weight is exactly (product of actual infinite marginals) times 2^rho.
Actual original infinite joint mass is at most this weight, including
affinely incompatible systems. The actual absolute centered coefficient
is at most the same weight on every nonempty admissible family, by the
proved full-support Fourier formula. Every local relation is retained
once in the effective spaces.

## Complete elementary bound at each fixed order

`PrimitiveWindowMass.primitive_mass_le` gives the finite comparison

    total primitive weight <=2^L * independent primitive mass.

`PrimitiveGeneralMass.binary_factor` proves the actual critical-band
2^L<=2^C N bound. The completed main 10.2 independent mass estimate then
gives `uniform_mass`:

    sum_primitive (product p_x) 2^rho <=N^(1-r/2+epsilon).

The threshold is before L, the dyadic subfamily and all actual primitive
subpopulations. Every fixed r>=2 is covered. `actual_joint_submass` and
`actual_centered_submass` identify the corresponding actual infinite
probability and absolute centered sums. The latter uses precisely local
admissibility p_x>0. No homogeneous probability substitution is made.

## Both main 15.5 bounds from r=5 onwards

For every integer r>=5, elementary algebra gives

    1-r/2 <=-4/3,     1-r/2 <=-2r/(r+2).

`main_15_5_from_five` proves both displayed source bounds for EVERY
primitive subpopulation, so the second bound needs no rho>=eta L
restriction in this range. This replaces the dense-certificate argument
for every fixed r>=5. The proof simplification and stronger exponent are
recorded as P1-MATH-0073. The unresolved r=4 case is the only missing
fixed order in main 15.5. No uniformity over a growing range of orders
is claimed: each fixed r retains its own threshold.

At r>=4 the elementary exponent also implies -4/5 for the unordered
heterogeneous primitive weight (`from_four`). This is useful preparation
for companion T4.3. Its literal separated ordered nominal p^r population
has not yet been identified by a weighted enumeration formula, and its
r=3 arithmetic estimate is still open. It is not counted complete.

No new external theorem, literature estimate, Paper C source, manuscript
revision or Palomar registration is introduced.
