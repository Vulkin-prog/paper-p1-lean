module

public import PaperP1.Asymptotics.SignedSaddleCostTheorem
public import PaperP1.Asymptotics.EnlargedRawValueProfile

/-! # The full prescribed signed forcing cost needs only the ordinary EIP input

The moving-width raw profile is proved internally, before the requested
logarithmic error. The unformalized ordinary reciprocal-prime asymptotic
is kept as the explicit argument hinput.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedSaddleCostInternalProfile

open Filter PaperP1.SaddleParameters PaperP1.SaddleScales PaperP1.OrdinaryReciprocalPrimeInput
  PaperP1.SignedPrivateDyadicField PaperP1.SignedPrivateField PaperP1.SignedSaddleExcess
  PaperP1.SignedSaddleCostTheorem

theorem companion_T19_16 (hinput : EIPInput) (C : ℝ) : Conclusion C := by
  obtain ⟨NP, hP⟩ :=
    EnlargedRawValueProfile.uniform_profile C (1 / 12) (by norm_num)
  obtain ⟨NW, hW⟩ := uniform_width C
  have hBoth (ε : ℝ) (hε : 0 < ε) : ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) ≤ specifiedCost N L ∧
        specifiedCost N L ≤ Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N)) := by
    obtain ⟨NL, hLower⟩ := SignedPrescribedSaddleLower.uniform_actual_lower hinput C ε hε
    obtain ⟨NU, hUpper⟩ := SignedSaddleCostUpper.uniform_upper_from_profile hinput C
      widthConstant widthConstant_pos ε hε
    refine ⟨max NL (max NU (max NP NW)), ?_⟩
    intro N hN L hL hcrit
    rw [specifiedCost_eq (by omega) hL]
    refine ⟨hLower N (by omega) L hL hcrit, hUpper N (by omega) L (excess N) hL hcrit
      (hW N (by omega) L hcrit) ?_⟩
    simpa only [CriticalRawValueProfile.mass, CriticalRawValueProfileUnderInputs.mass,
      show (3 : ℝ) / 2 + 1 / 12 = 19 / 12 by norm_num] using hP N (by omega) L hcrit
  refine ⟨hBoth, ?_, uniform_power_obstruction hinput C⟩
  intro ε hε
  obtain ⟨N₀, h⟩ := hBoth ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hL hcrit
  exact log_error_of_sandwich (h N hN L hL hcrit).1 (h N hN L hL hcrit).2

end PaperP1.SignedSaddleCostInternalProfile
