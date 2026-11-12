module

public import PaperP1.Asymptotics.FixedArityHomogeneousMass

/-! # V2 Lemma 2.4: the finite envelope and its uniform nominal comparison

The finite assertions allow inconsistent prescriptions and zero marginals.
The eventual comparison retains 2^|I| explicitly, even for growing families.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.V2HomogeneousEnvelope

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem finite_domination (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (hne : I.Nonempty) :
    HomogeneousRunMass.probability L I =
      (∏ x ∈ I, (2 ^ Module.finrank F₂ (squareClassSpace x L) : ℝ)⁻¹) *
        (2 ^ relativeNullityOn (fun x ↦ squareClassSpace x L) I : ℝ) ∧
    PrimitiveWindowMass.weight L I ≤ HomogeneousRunMass.probability L I ∧
    infiniteJointMoment L I ≤ HomogeneousRunMass.probability L I ∧
    |infiniteCenteredCoefficient L I| ≤ HomogeneousRunMass.probability L I := by
  refine ⟨?_, HomogeneousEffectiveWeights.weight_le L hL I,
    HomogeneousRunMass.actual_joint_le L hL I, HomogeneousEffectiveWeights.centered_le L hL I hne⟩
  simpa only [HomogeneousEffectiveWeights.singleton_rank] using HomogeneousEffectiveWeights.factor L I

theorem uniform_nominal_comparison (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ I : Finset ℕ, I ⊆ dyadicBlock N →
        HomogeneousRunMass.probability L I ≤
          (2 : ℝ) ^ I.card * PrimitiveNominalMass.weight L I := by
  obtain ⟨N₀, hN₀, h⟩ := FixedArityHomogeneousMass.uniform_nominal_cap C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband I hI
  exact FixedArityHomogeneousMass.point_le_nominal L I
    (fun x hx ↦ (h N hN L hband).2 x (hI hx))

end PaperP1.V2HomogeneousEnvelope
