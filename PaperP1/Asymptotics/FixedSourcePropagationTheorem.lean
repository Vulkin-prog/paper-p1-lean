module

public import PaperP1.Asymptotics.FixedExceptionalMass
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Main Proposition 6.3: conditional sums, actual propagation and exceptional seed mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedSourcePropagationTheorem

open Finset PaperP1.Arithmetic PaperP1.PrescribedTupleMass PaperP1.WindowFamilyConditional
  PaperP1.Model.InfiniteRademacher

local instance fixedSourcePropagationTheoremMeasurableF2 : MeasurableSpace F₂ := ⊤

/-- The full source statement, with r=s+k and one threshold before every
source tuple, compatible affine prescription and actual extension family. -/
theorem main_6_3 (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2 * N)) → ∀ b : Fin s → Fin L → F₂,
        0 < infiniteRademacherMeasure.real {ω | sourceEvent x L b ω} → ∀ c : ℕ → Fin L → F₂,
          (∑ z ∈ Ico N (2 * N) \ univ.image x, conditionalProbability x L b z (c z)) ≤ (N : ℝ) ^ ε) ∧
      (∀ c : ℕ → Fin L → F₂, ∀ F : Finset (Fin s → ℕ),
        (∀ x ∈ F, ∀ i, x i ∈ Ico N (2 * N)) →
          (∑ y ∈ TupleExtensions.distinctMore (Ico N (2 * N)) F k, joint L c y) ≤
            (N : ℝ) ^ ε * ∑ x ∈ F, joint L c x) ∧
      (∑ x ∈ FixedExceptionalMass.badFamilies N L (s + k),
        Model.InfiniteStarts.infiniteFamilyJointMoment L x) ≤ K * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NC, hNC⟩ := FixedSourceConditionalSum.fresh_conditional_sum s hs C ε hε
  obtain ⟨NP, hNP⟩ := FixedOrderMassPropagation.main_6_3_propagation s hs k C ε hε
  obtain ⟨K, hK, NE, hNE⟩ := FixedExceptionalMass.bad_original_mass (s + k) (by omega) C ε hε
  obtain ⟨NG, hNG⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨K, hK, max NC (max NP (max NE NG)), ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have h := (hNG N (by omega) L hband).2.1; omega
  exact ⟨hNC N (by omega) L hband, hNP N (by omega) L hband, hNE N (by omega) L hL hband⟩

end PaperP1.FixedSourcePropagationTheorem
