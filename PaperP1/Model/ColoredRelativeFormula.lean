module

public import PaperP1.Model.ColoredReplicaMass
public import PaperP1.Affine.FamilyEventMass
public import PaperP1.Affine.UniformPrecomposition
public import PaperP1.Affine.IndependentRows

/-! # Replica formulas with exact heterogeneous marginals and the effective relative kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ColoredRelativeFormula

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.ColoredPrimeSamples
  PaperP1.ColoredReplicaMass PaperP1.UniformFubini

local instance coloredRelativeFormulaTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance coloredRelativeFormulaDecidable (P : Prop) : Decidable P := Classical.propDecidable P

abbrev rows {ι κ : Type*} (M Y L : ℕ) (x : ι → ℕ) (color : ι → κ) :=
  fun i ↦ effectiveRowSpace (start M Y (x i) L (color i))

theorem select_surjective {κ : Type*} (M Y : ℕ) (k : κ) : Function.Surjective (select M Y k) := by
  intro σ
  refine ⟨diagonal κ M σ, ?_⟩
  exact LinearMap.congr_fun (select_diagonal M Y k) σ

theorem local_mass_eq {κ : Type*} [Fintype κ] (M Y L x : ℕ) (k : κ) (b : Fin L → F₂) :
    uniformSolutionMass (start M Y x L k) b = uniformSolutionMass (startSystem M x L) b :=
  UniformPrecomposition.mass_eq (select M Y k) (select_surjective M Y k) (startSystem M x L) b

theorem compatibility_iff {ι κ : Type*} (M Y L : ℕ) (x : ι → ℕ)
    (color : ι → κ) (b : ι → Fin L → F₂) :
    FamilyEventMass.CompatibleFamily (fun i ↦ start M Y (x i) L (color i)) b ↔
      Compatible (jointSystem M Y L x color) (jointRhs b) := by
  constructor
  · rintro ⟨a, ha⟩
    exact LinearMap.mem_range.mpr ⟨a, (joint_system_event M Y L x color b a).mpr ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (joint_system_event M Y L x color b a).mp ha⟩

theorem exact_relative_formula {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M Y L : ℕ) (x : ι → ℕ) (color : ι → κ) (b : ι → Fin L → F₂) :
    average (fun σ : SampleSpace M ↦ ∏ k, blockProbability Y L x color b k σ) =
      (if Compatible (jointSystem M Y L x color) (jointRhs b) then (1 : ℝ) else 0) *
      (∏ i, uniformSolutionMass (startSystem M (x i) L) (b i)) *
      (2 ^ relativeNullity (rows M Y L x color) : ℝ) := by
  classical
  rw [replica_identity]
  have heq : jointProbability M Y L x color b =
      FamilyEventMass.mass (fun i ↦ start M Y (x i) L (color i)) b := by
    unfold jointProbability FamilyEventMass.mass
    apply UniformFubini.congr
    intro ω
    by_cases h : ∀ i, start M Y (x i) L (color i) ω = b i <;> simp only [h, ite_false]
  rw [heq, FamilyEventMass.exact_marginal_formula]
  simp_rw [local_mass_eq, compatibility_iff]

theorem regular_formula {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M Y L : ℕ) (x : ι → ℕ) (color : ι → κ) (b : ι → Fin L → F₂)
    (hregular : ∀ i, Module.finrank F₂ (effectiveRowSpace (startSystem M (x i) L)) = L) :
    average (fun σ : SampleSpace M ↦ ∏ k, blockProbability Y L x color b k σ) =
      ((2 ^ L : ℝ)⁻¹) ^ Fintype.card ι *
      (if Compatible (jointSystem M Y L x color) (jointRhs b) then (1 : ℝ) else 0) *
      (2 ^ relativeNullity (rows M Y L x color) : ℝ) := by
  classical
  rw [exact_relative_formula]
  have hmass (i : ι) : uniformSolutionMass (startSystem M (x i) L) (b i) = (2 ^ L : ℝ)⁻¹ := by
    simpa only [Fintype.card_fin] using uniformSolutionMass_of_full_effective_rank
      (startSystem M (x i) L) (by simpa only [Fintype.card_fin] using hregular i) (b i)
  simp_rw [hmass]
  by_cases h : Compatible (jointSystem M Y L x color) (jointRhs b) <;> simp [h]

end PaperP1.ColoredRelativeFormula
