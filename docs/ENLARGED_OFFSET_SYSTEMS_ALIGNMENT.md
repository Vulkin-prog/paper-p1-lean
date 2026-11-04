# Enlarged offset systems and the corrected alignment scope

Follow-up to [P1-MATH-0162](ASYMMETRIC_ALIGNMENT_SCOPE.md), preparing companion T1.10.

The necessary correction P1-MATH-0162 now has checked geometric
preparation for enlarged offsets. EnlargedGridAlignment proves that two
bounded affine grid points at actual offset radius W force the enlarged
source alignment when W<=R*(L+1) and 2W<=(L+1)^3. An actual exact match
between widths Dold and Dnew forces radius max(Dold,Dnew). Radius
monotonicity is also proved. These facts retain the original cubic slope
height; the displacement radius is the part that follows the offsets.

EnlargedOffsetRegime gives ONE critical scale threshold for every
W<=R*(L+1), with W< N, W<=(L+1)^2 and 2W<=(L+1)^3. The enlarged
nonalignment therefore excludes every low-degree affine grid branch,
without changing the original critical length. EnlargedNonalignedRootHostCount
then proves the general N^(1/2+epsilon) root count under the existing
chosen-source surface-cover and normalized curve inputs. Arbitrary
nonzero integer coefficients of the specified polynomial height,
disjoint nonempty root lists and every larger system are retained.

EnlargedDegreeOneRootHostCount proves N^epsilon for degree-(a,1)
systems with any positive a. It needs enlarged nonalignment ONLY for
a=1. For a>=2 the repeated-left degree exclusion works without it.
The existing ordinary surface-cover and affine curve consequences of
the normalized curve property remain explicit unproved arguments.
No square-class independence is imposed in either of these enlarged
nonaligned root counts.

EnlargedRootPatterns counts ALL actual offset and small-prime code
patterns at every polynomial offset width W+1<=(L+1)^J. Their number
is N^epsilon, while their coefficient height is polynomial in N whenever
the small-prime cutoff stays O(L+1). Coefficient heights are uniform
even before the offset range, number of equations and degree cap.
EnlargedSmoothGeneralHostCount and EnlargedSmoothDegreeOneHostCount
sum these actual pools at every fixed enlarged width, proving the
half-power and subpower bounds with one constant and threshold before
the actual systems and centres. No supplied host bound is an input.

This is preparation for the corrected T1.10, not its complete profile
estimate: the actual unequal-block graph reduction, sparse support and
weighted summation remain. Its literal radius-one version is still
disproved, and the enlarged-radius31/24 assertion stays unproved.
Coverage remains87/167 unconditional and48 conditional. Findings remain
161 improvements and1 statement-scope correction. No original source
edit, new external input, Paper C port or dependency download occurs.

The result ledger records exact verification and proof commits.
