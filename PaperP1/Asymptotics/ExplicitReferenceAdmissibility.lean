module

public import PaperP1.Asymptotics.FiniteChannelHierarchyBounds
public import PaperP1.Asymptotics.ActualReferenceAdmissibility

/-! # Unconditional probability status of every fixed-height explicit reference

The literal finite channel coefficient is used throughout. Its comparison
with the actual cumulant and all count-law approximation rates are separate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExplicitReferenceAdmissibility

open MeasureTheory PaperP1.FiniteChannelHierarchy PaperP1.FiniteChannelHierarchyBounds

theorem uniform_probabilities (C : ℝ) (h : ℕ) (hh : 3 ≤ h) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < coefficient N L h ∧ coefficient N L h < nominalMean N L ∧
        AtomicSignedLaw.IsProbability (QuadraticPoisson.reference (nominalMean N L) (coefficient N L h)) ∧
        AtomicSignedLaw.IsProbability (CompletedLaw.toSignedMeasure
          (HermiteReference.reference (nominalMean N L) (coefficient N L h))) := by
  let m := ((2 : ℝ) ^ C)⁻¹
  let M := (2 : ℝ) ^ C
  have hm : 0 < m := by dsimp [m]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let δ := min (m / 2) (m ^ 2 / (M + 1))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨NS, hNS, hsmall⟩ := uniform_small C h hh δ hδ
  obtain ⟨NP, hNP, hpositive⟩ := FiniteChannelHierarchyBounds.uniform_positive C h hh
  refine ⟨max NS NP, by omega, ?_⟩
  intro N hN L hband
  have hα := hpositive N (by omega) L hband
  have hαsmall := hsmall N (by omega) L hband
  have hhalf : coefficient N L h ≤ m / 2 := hαsmall.trans (min_le_left _ _)
  have hquad : coefficient N L h ≤ m ^ 2 / (M + 1) := hαsmall.trans (min_le_right _ _)
  obtain ⟨hml, hmu⟩ := nominal_bounds (by omega : 2 ≤ N) hband
  have hgap : coefficient N L h < nominalMean N L := by linarith only [hm, hhalf, hml]
  refine ⟨hα, hgap, ActualReferenceAdmissibility.quadratic_of_bounds hm hM hml hmu hα.le hquad, ?_⟩
  refine ⟨HermiteReference.law _ _ hα.le hgap.le, ?_⟩
  exact (HermiteReference.actual_signed_reference _ _ hα.le hgap.le).symm

theorem uniform_two_channel_probabilities (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < twoChannelCoefficient N L ∧ twoChannelCoefficient N L < nominalMean N L ∧
        AtomicSignedLaw.IsProbability (QuadraticPoisson.reference (nominalMean N L) (twoChannelCoefficient N L)) ∧
        AtomicSignedLaw.IsProbability (CompletedLaw.toSignedMeasure
          (HermiteReference.reference (nominalMean N L) (twoChannelCoefficient N L))) := by
  obtain ⟨N₀, hN₀, hbound⟩ := uniform_probabilities C 4 (by decide)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  have h := hbound N hN L hband
  simpa only [coefficient_four N L (by omega : 0 < N)] using h

theorem explicit_mass_formula (μ α : ℝ) (hμ : 0 < μ) (k : ℕ) :
    QuadraticPoisson.reference μ α {k} =
      Real.exp (-μ) * μ ^ k / (k.factorial : ℝ) *
        (1 + α / 2 * (((k : ℝ) * ((k : ℝ) - 1)) / μ ^ 2 - 2 * (k : ℝ) / μ + 1)) := by
  rw [QuadraticPoisson.reference_singleton μ α hμ k]
  congr 1
  field_simp
  ring

theorem two_channel_mass_formula (N L : ℕ) (hN : 0 < N) (k : ℕ) :
    QuadraticPoisson.reference (nominalMean N L) (twoChannelCoefficient N L) {k} =
      Real.exp (-(nominalMean N L)) * (nominalMean N L) ^ k / (k.factorial : ℝ) *
        (1 + twoChannelCoefficient N L / 2 *
          (((k : ℝ) * ((k : ℝ) - 1)) / (nominalMean N L) ^ 2 -
            2 * (k : ℝ) / nominalMean N L + 1)) := by
  have hμ : 0 < nominalMean N L := by unfold nominalMean; positivity
  exact explicit_mass_formula _ _ hμ k

end PaperP1.ExplicitReferenceAdmissibility
