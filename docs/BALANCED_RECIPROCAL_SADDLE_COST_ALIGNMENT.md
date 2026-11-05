# Uniform balanced reciprocal saddle cost with a negligible quadratic Ei error

Source rechecked: complete companion T19.15 reciprocal/dyadic statement and proof, companion_sections/limits_appendix.tex lines1138-1194. The analytic cost inequality is distinguished from the still unresolved fine reciprocal equivalent.

The actual hard-saddle cost is now bounded uniformly over every positive logarithmic pivot cutoff, with an error negligible at the fine scale nu. For every epsilon>0 there is one H0 before all H>=H0 and all v>0 such that 2V-epsilon*nu <= v+H*u/v-Ei(u), where u=saddleParameter(1,H), V=saddleCutoff(1,H) and nu=H/V. This is an internal analytic bound, with no ordinary EIP input. The moving weighted pivot partition remains subsequent work.

finite_cost_lower first proves the exact finite inequality 2V-E^2/(4V) <= v+V(V+E)/v-E for every V>0,E>=0,v>0. The proof handles both v<=V and v>=V by explicit squares. No square-root approximation, restriction E<=V or cutoff-dependent threshold is used. balanced_identity proves H*u=V(V+Ei(u)) from the actual root equation, preserving the standard Ei normalization.

tendsto_ei_div_nu proves Ei(u)/nu ->1. tendsto_nu_div_cutoff proves nu/V ->0 from the actual saddle-cost factor. Their exact product identity gives tendsto_quadratic_error: Ei(u)^2/(V*nu) ->0. uniform_cost_lower combines eventual Ei positivity and this limit with the finite inequality. Its threshold is selected before every positive v, so it applies to a growing collection of logarithmic bands without selecting a threshold after those bands.

This result supplies the balanced-cost ingredient for a fine reciprocal upper estimate, together with checkpoint475's uniform exact-endpoint Euler estimate. The full weighted partition, uniform counting error and o(nu) transport are not yet claimed. Complete T19.15/T19.16 retain the explicit fine ordinary EIP input. Their leading coefficient2 limits and the qualitative deterministic/randomized all-anchor obstructions remain internal; full T19.17 still requires the stronger almost-all census and1-o(1) coefficient. General geometry, full quadratic-degree BCN and optimal strong-triangle weights retain their separate unresolved scopes.

P1-MATH-0476 adds one module, six theorems and no definitions. Coverage remains147 proved,17 conditional and3 in_progress out of167, with164 completed. The project records474 improvements and two statement-scope corrections. No new axiom, dependency download or Palomar submission is introduced.
