module

public import PaperP1.Model.ColoredPrimeSamples
public import PaperP1.Affine.FactorConditionalKernel
public import PaperP1.Model.WindowFamilyConditional
public import PaperP1.Affine.CompatibleSourcePrescriptions

/-! # Every colored conditional atom is dominated by its merged homogeneous atom -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ColoredWindowConditional

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.ColoredPrimeSamples

local instance coloredWindowConditionalTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance coloredWindowConditionalMeasurableF2 : MeasurableSpace F₂ := ⊤

abbrev systems {κ : Type*} {s : ℕ} (M Y L : ℕ) (x : Fin s → ℕ) (z : ℕ)
    (color : Option (Fin s) → κ) : Option (Fin s) → Sample κ M →ₗ[F₂] (Fin L → F₂) :=
  fun i ↦ match i with
    | none => start M Y z L (color none)
    | some j => start M Y (x j) L (color (some j))

def mass {κ : Type*} [Fintype κ] {s : ℕ} (M Y L : ℕ) (x : Fin s → ℕ) (z : ℕ)
    (color : Option (Fin s) → κ) (a : Sample κ M) (b : Fin L → F₂) : ℝ :=
  FamilyConditionalMass.mass (systems M Y L x z color) a b

theorem merged_domination {κ : Type*} [Fintype κ] {s : ℕ} (M Y L : ℕ) (x : Fin s → ℕ) (z : ℕ)
    (color : Option (Fin s) → κ) (a : Sample κ M) (b : Fin L → F₂) :
    mass M Y L x z color a b ≤ FamilyConditionalMass.mass (WindowFamilyConditional.systems M L x z) 0 0 := by
  apply FactorConditionalKernel.mass_le_merged_homogeneous _ _ (diagonal κ M).dualMap
  intro i
  cases i with
  | none => exact start_relation_factor M Y z L (color none)
  | some j => exact start_relation_factor M Y (x j) L (color (some j))

theorem infinite_homogeneous_domination {κ : Type*} [Fintype κ] {s M Y L z : ℕ}
    (x : Fin s → ℕ) (color : Option (Fin s) → κ) (a : Sample κ M) (b : Fin L → F₂)
    (hcut : ∀ i, x i + L ≤ M) (hz : z + L ≤ M) :
    mass M Y L x z color a b ≤ WindowFamilyConditional.conditionalProbability x L (fun _ ↦ 0) z 0 := by
  have h := merged_domination M Y L x z color a b
  have heq := WindowFamilyConditional.conditional_eq_mass x (0 : SampleSpace M) (0 : Fin L → F₂) hcut hz
  simp only [map_zero] at heq
  rwa [← heq] at h

def conditionalProbability {κ : Type*} [Fintype κ] {s : ℕ} (M Y L : ℕ)
    (x : Fin s → ℕ) (z : ℕ) (color : Option (Fin s) → κ)
    (b : Fin s → Fin L → F₂) (c : Fin L → F₂) : ℝ :=
  CompatibleSourcePrescriptions.conditionalProbability (systems M Y L x z color) b c

theorem conditional_of_witness {κ : Type*} [Fintype κ] {s : ℕ} (M Y L : ℕ)
    (x : Fin s → ℕ) (z : ℕ) (color : Option (Fin s) → κ)
    (b : Fin s → Fin L → F₂) (c : Fin L → F₂) (a : Sample κ M)
    (ha : ∀ i, start M Y (x i) L (color (some i)) a = b i) :
    conditionalProbability M Y L x z color b c = mass M Y L x z color a c :=
  CompatibleSourcePrescriptions.conditional_of_witness _ b c a ha

end PaperP1.ColoredWindowConditional
