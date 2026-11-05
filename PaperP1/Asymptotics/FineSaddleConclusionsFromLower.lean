module

public import PaperP1.Analysis.OrdinaryReciprocalPrimeLowerInput
public import PaperP1.Asymptotics.SignedSaddleCostInternalProfile
public import PaperP1.Asymptotics.FineSignedCostUpper

/-! # Complete fine saddle conclusions under only the ordinary lower estimate

All upper estimates and geometric profiles are proved internally. The
remaining fine ordinary lower estimate is an explicit theorem argument.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FineSaddleConclusionsFromLower

open SaddleParameters SaddleScales ReciprocalOddPivots DyadicOddPivots
  OrdinaryReciprocalPrimeLowerInput

theorem companion_T19_15 (hLower : LowerInput) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      ((N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) ≤ pivotSum N ∧
        pivotSum N ≤ (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N))) ∧
      ((N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) ≤ dyadicSum N ∧
        dyadicSum N ≤ (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N))) :=
  ReciprocalOddPivotDyadicScale.companion_T19_15 (eipInput_of_lower hLower) ε hε

theorem companion_T19_16 (hLower : LowerInput) (C : ℝ) : SignedSaddleCostTheorem.Conclusion C :=
  SignedSaddleCostInternalProfile.companion_T19_16 (eipInput_of_lower hLower) C

end PaperP1.FineSaddleConclusionsFromLower
