module

public import PaperP1.Model.SmallPrimeFiltration
public import PaperP1.Model.ColoredRelativeFormula

/-! # The exact replica formula for actual infinite-measure conditional expectations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InfiniteReplicaFormula

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.ColoredReplicaMass PaperP1.UniformFubini PaperP1.Model.InfiniteRademacher
  PaperP1.SmallPrimeFiltration PaperP1.RelativeSignIndependence
  PaperP1.Probability.InfiniteCylinderTransfer PaperP1.Probability.CylinderExpectations

local instance infiniteReplicaFormulaTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance infiniteReplicaFormulaMeasurableF2 : MeasurableSpace F₂ := ⊤
local instance infiniteReplicaFormulaDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def conditionalBlock {ι κ : Type*} (Y L : ℕ) (x : ι → ℕ) (color : ι → κ)
    (b : ι → Fin L → F₂) (k : κ) : InfiniteSample → ℝ :=
  condExp (primeFiltration Y) infiniteRademacherMeasure
    (fun ω ↦ if ∀ i, color i = k → infiniteStartBits (x i) L ω = b i then (1 : ℝ) else 0)

theorem integral_eq_finite {ι κ : Type*} [Fintype κ] {M Y L : ℕ} (hYM : Y ≤ M)
    (x : ι → ℕ) (color : ι → κ) (b : ι → Fin L → F₂) (hcut : ∀ i, x i + L ≤ M) :
    (∫ ω, (∏ k, conditionalBlock Y L x color b k ω) ∂infiniteRademacherMeasure) =
      average (fun σ : SampleSpace M ↦ ∏ k, blockProbability Y L x color b k σ) := by
  classical
  have h (k : κ) : (fun ω : InfiniteSample ↦ blockProbability Y L x color b k (restrictToFinite M ω)) =ᵐ[infiniteRademacherMeasure]
      conditionalBlock Y L x color b k := by
    have h := SmallPrimeConditioning.block_condExp Y L x color b k hcut
    rw [SmallPrimeFiltration.filtration_eq hYM] at h
    exact h
  have hall : ∀ᵐ ω ∂infiniteRademacherMeasure, ∀ k, blockProbability Y L x color b k (restrictToFinite M ω) =
      conditionalBlock Y L x color b k ω := ae_all_iff.mpr h
  calc
    _ = ∫ ω, (∏ k, blockProbability Y L x color b k (restrictToFinite M ω)) ∂infiniteRademacherMeasure := by
      apply integral_congr_ae
      filter_upwards [hall] with ω hω
      exact prod_congr rfl (fun k _ ↦ (hω k).symm)
    _ = _ := infiniteCylinder_integral M (fun σ ↦ ∏ k, blockProbability Y L x color b k σ)

theorem exact_relative_formula {ι κ : Type*} [Fintype ι] [Fintype κ] {M Y L : ℕ} (hYM : Y ≤ M)
    (x : ι → ℕ) (color : ι → κ) (b : ι → Fin L → F₂) (hcut : ∀ i, x i + L ≤ M) :
    (∫ ω, (∏ k, conditionalBlock Y L x color b k ω) ∂infiniteRademacherMeasure) =
      (if Compatible (jointSystem M Y L x color) (jointRhs b) then (1 : ℝ) else 0) *
      (∏ i, infiniteRademacherMeasure.real {ω | infiniteStartBits (x i) L ω = b i}) *
      (2 ^ relativeNullity (ColoredRelativeFormula.rows M Y L x color) : ℝ) := by
  rw [integral_eq_finite hYM x color b hcut, ColoredRelativeFormula.exact_relative_formula]
  simp_rw [infiniteStartBits_atom_eq_finite (hcut _)]

theorem regular_formula {ι κ : Type*} [Fintype ι] [Fintype κ] {M Y L : ℕ} (hYM : Y ≤ M)
    (x : ι → ℕ) (color : ι → κ) (b : ι → Fin L → F₂) (hcut : ∀ i, x i + L ≤ M)
    (hregular : ∀ i, Module.finrank F₂ (effectiveRowSpace (startSystem M (x i) L)) = L) :
    (∫ ω, (∏ k, conditionalBlock Y L x color b k ω) ∂infiniteRademacherMeasure) =
      ((2 ^ L : ℝ)⁻¹) ^ Fintype.card ι *
      (if Compatible (jointSystem M Y L x color) (jointRhs b) then (1 : ℝ) else 0) *
      (2 ^ relativeNullity (ColoredRelativeFormula.rows M Y L x color) : ℝ) := by
  rw [integral_eq_finite hYM x color b hcut]
  exact ColoredRelativeFormula.regular_formula M Y L x color b hregular

end PaperP1.InfiniteReplicaFormula
