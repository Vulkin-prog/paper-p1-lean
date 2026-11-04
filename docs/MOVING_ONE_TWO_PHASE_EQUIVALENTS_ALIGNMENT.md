# Uniform moving-parity equivalents of the actual finite one-to-two channel sums

Companion T21.1, arithmetic_consequences.tex:26, including the distinct positive B and signed L parity equivalents. Original source and statement hashes remain preserved.

The distinct positive and signed channel phases needed in T21.1 are now proved as uniform relative equivalents, with the actual residue chosen AFTER the threshold.

OneTwoChannelPhase defines the positive leading word as(2+r)/4*B*2^k for B=L+1=2k+r, and the signed leading word as(s+1)/4*L*2^m for L=2m+s. Both main terms are proved positive in the relevant length range. The definitions use the actual quotient and remainder of the moving length, rather than fixing a residue in advance.

The exact unsigned identity proved in P1-MATH-0207 gives an explicit normalized formula. Its constant-over-k and geometric lower-degree terms tend to zero. The existing signed normalization applies at height two and gives the distinct signed residue limit. Each finite channel sum and its corresponding leading word have the same positive normalized limit, so their ratio tends to1 on each parity class.

The two parity classes are then assembled using a finite-set eventual quantifier. A single L0 precedes EVERY length L>=L0 and gives both relative errors at most any prescribed epsilon>0. The common critical-window geometry transports this to one ambient threshold that precedes every critical length. No fixed-parity or fixed-offset assumption remains in the final uniform statement.

P1-MATH-0211 records these finite-channel moving-phase equivalents. The actual complete positive/signed main-term error was proved in P1-MATH-0210. Its transfer to relative equivalents still needs the lower growth bound and the negligible lower-endpoint factor. Global rational-code identification and the dyadic positive assertions also remain. T21.1 stays in progress. Coverage remains88 proved and70 conditional out of167, with nine incomplete results. There are210 improvements and one statement-scope correction. No external input, new axiom, dependency, compiler change or original manuscript edit is introduced. Palomar remains deferred.
