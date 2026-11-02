module

public import PaperP1.Model.InfiniteColoredBits
public import PaperP1.Model.InfiniteColoredCylinder
public import PaperP1.Model.ColoredWindowConditional

/-! # Literal conditional source and target probabilities in the infinite colored replica space -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InfiniteColoredConditional

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Model PaperP1.InfiniteColoredBits

local instance infiniteColoredConditionalMeasurableF2 : MeasurableSpace F₂ := ⊤
local instance infiniteColoredConditionalDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def sourceEvent {κ : Type*} {s : ℕ} (Y L : ℕ) (x : Fin s → ℕ) (color : Option (Fin s) → κ)
    (b : Fin s → Fin L → F₂) (ω : InfiniteColoredSamples.Sample κ) : Prop :=
  ∀ i, bits Y (x i) L (color (some i)) ω = b i

def conditionalProbability {κ : Type*} [Fintype κ] {s : ℕ} (Y L : ℕ) (x : Fin s → ℕ)
    (z : ℕ) (color : Option (Fin s) → κ) (b : Fin s → Fin L → F₂) (c : Fin L → F₂) : ℝ :=
  (InfiniteColoredSamples.measure κ).real {ω | sourceEvent Y L x color b ω ∧ bits Y z L (color none) ω = c} /
    (InfiniteColoredSamples.measure κ).real {ω | sourceEvent Y L x color b ω}

theorem source_restrict {κ : Type*} {s M Y L : ℕ} (x : Fin s → ℕ)
    (color : Option (Fin s) → κ) (b : Fin s → Fin L → F₂)
    (hcut : ∀ i, x i + L ≤ M) (ω : InfiniteColoredSamples.Sample κ) :
    sourceEvent Y L x color b ω ↔
      ∀ i, ColoredPrimeSamples.start M Y (x i) L (color (some i)) (InfiniteColoredSamples.restrict κ M ω) = b i := by
  simp only [sourceEvent]
  simp_rw [bits_restrict (hcut _)]

theorem source_mass_eq {κ : Type*} [Fintype κ] {s M Y L z : ℕ} (x : Fin s → ℕ)
    (color : Option (Fin s) → κ) (b : Fin s → Fin L → F₂) (hcut : ∀ i, x i + L ≤ M) :
    (InfiniteColoredSamples.measure κ).real {ω | sourceEvent Y L x color b ω} =
      CompatibleSourcePrescriptions.sourceMass (ColoredWindowConditional.systems M Y L x z color) b := by
  have heq : {ω | sourceEvent Y L x color b ω} =
      {ω | ∀ i, ColoredPrimeSamples.start M Y (x i) L (color (some i)) (InfiniteColoredSamples.restrict κ M ω) = b i} := by
    ext ω
    exact source_restrict x color b hcut ω
  rw [heq, InfiniteColoredCylinder.event κ M (fun σ ↦
    ∀ i, ColoredPrimeSamples.start M Y (x i) L (color (some i)) σ = b i)]
  unfold CompatibleSourcePrescriptions.sourceMass
  apply UniformFubini.congr
  intro σ
  simp only [ColoredWindowConditional.systems]

theorem conditional_eq {κ : Type*} [Fintype κ] {s M Y L z : ℕ} (x : Fin s → ℕ)
    (color : Option (Fin s) → κ) (b : Fin s → Fin L → F₂) (c : Fin L → F₂)
    (hcut : ∀ i, x i + L ≤ M) (hz : z + L ≤ M) :
    conditionalProbability Y L x z color b c = ColoredWindowConditional.conditionalProbability M Y L x z color b c := by
  have heq : {ω | sourceEvent Y L x color b ω ∧ bits Y z L (color none) ω = c} =
      {ω | (∀ i, ColoredPrimeSamples.start M Y (x i) L (color (some i)) (InfiniteColoredSamples.restrict κ M ω) = b i) ∧
        ColoredPrimeSamples.start M Y z L (color none) (InfiniteColoredSamples.restrict κ M ω) = c} := by
    ext ω
    simp only [Set.mem_ofPred_eq, source_restrict x color b hcut ω, bits_restrict hz]
  unfold conditionalProbability
  rw [heq, InfiniteColoredCylinder.event κ M (fun σ ↦
    (∀ i, ColoredPrimeSamples.start M Y (x i) L (color (some i)) σ = b i) ∧
      ColoredPrimeSamples.start M Y z L (color none) σ = c), source_mass_eq (z := z) x color b hcut]
  unfold ColoredWindowConditional.conditionalProbability CompatibleSourcePrescriptions.conditionalProbability
  congr 1
  apply UniformFubini.congr
  intro σ
  simp only [ColoredWindowConditional.systems]
  by_cases h : (∀ i, ColoredPrimeSamples.start M Y (x i) L (color (some i)) σ = b i) ∧
      ColoredPrimeSamples.start M Y z L (color none) σ = c <;> simp only [h, ite_false]

theorem homogeneous_domination {κ : Type*} [Fintype κ] {s M Y L z : ℕ} (x : Fin s → ℕ)
    (color : Option (Fin s) → κ) (b : Fin s → Fin L → F₂) (c : Fin L → F₂)
    (hcut : ∀ i, x i + L ≤ M) (hz : z + L ≤ M)
    (hsource : 0 < (InfiniteColoredSamples.measure κ).real {ω | sourceEvent Y L x color b ω}) :
    conditionalProbability Y L x z color b c ≤
      WindowFamilyConditional.conditionalProbability x L (fun _ ↦ 0) z 0 := by
  have hfinite : 0 < CompatibleSourcePrescriptions.sourceMass
      (ColoredWindowConditional.systems M Y L x z color) b := by
    rwa [← source_mass_eq (z := z) x color b hcut]
  obtain ⟨a, ha⟩ := (CompatibleSourcePrescriptions.source_mass_pos_iff _ b).mp hfinite
  rw [conditional_eq x color b c hcut hz, ColoredWindowConditional.conditional_of_witness M Y L x z color b c a ha]
  exact ColoredWindowConditional.infinite_homogeneous_domination x color a c hcut hz

end PaperP1.InfiniteColoredConditional
