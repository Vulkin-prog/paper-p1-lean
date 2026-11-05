module

public import PaperP1.Asymptotics.FineOrdinaryReciprocalLower
public import PaperP1.Asymptotics.FineSaddleConclusionsFromLower

/-! # Complete internal proofs of companion T19.15 and T19.16

The ordinary reciprocal fine lower estimate, all upper estimates, and
all actual forcing/profile transports are supplied by internal proofs.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FineSaddleTheorems

open SaddleParameters SaddleScales ReciprocalOddPivots DyadicOddPivots

theorem companion_T19_15 (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      ((N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) ≤ pivotSum N ∧
        pivotSum N ≤ (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N))) ∧
      ((N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) ≤ dyadicSum N ∧
        dyadicSum N ≤ (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N))) :=
  FineSaddleConclusionsFromLower.companion_T19_15 FineOrdinaryReciprocalLower.lowerInput ε hε

theorem companion_T19_16 (C : ℝ) : SignedSaddleCostTheorem.Conclusion C :=
  FineSaddleConclusionsFromLower.companion_T19_16 FineOrdinaryReciprocalLower.lowerInput C


end PaperP1.FineSaddleTheorems
