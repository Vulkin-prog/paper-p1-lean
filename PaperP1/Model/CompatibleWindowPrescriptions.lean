module

public import PaperP1.Model.WindowFamilyConditional

/-! # Every positive-probability source prescription has an actual cylinder witness -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompatibleWindowPrescriptions

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Probability
  PaperP1.WindowFamilyConditional PaperP1.ConditionalRunProbability
  PaperP1.Model.InfiniteRademacher PaperP1.Probability.InfiniteCylinderTransfer

local instance compatibleWindowPrescriptionsTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance compatibleWindowPrescriptionsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem source_mass_affine {s M L : ℕ} (x : Fin s → ℕ) (b : Fin s → Fin L → F₂)
    (hcut : ∀ i, x i + L ≤ M) :
    infiniteRademacherMeasure.real {ω | sourceEvent x L b ω} =
      uniformSolutionMass (familyStartSystem M L x) (fun p ↦ b p.1 p.2) := by
  have heq : {ω | sourceEvent x L b ω} =
      {ω | familyStartSystem M L x (restrictToFinite M ω) = fun p ↦ b p.1 p.2} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [sourceEvent_restrict x b hcut]
    constructor
    · intro h
      funext p
      exact congrFun (h p.1) p.2
    · intro h i
      funext j
      exact congrFun h (i, j)
  rw [heq, infiniteCylinder_event M (fun σ ↦ familyStartSystem M L x σ = fun p ↦ b p.1 p.2)]
  unfold uniformSolutionMass
  apply congrArg (PaperP1.Algebra.finiteExpectation (cylinderProbability M).weight)
  funext σ
  by_cases h : familyStartSystem M L x σ = (fun p ↦ b p.1 p.2)
  · simp only [h]
  · simp only [h, ite_false]

theorem exists_witness_of_positive {s M L : ℕ} (x : Fin s → ℕ) (b : Fin s → Fin L → F₂)
    (hcut : ∀ i, x i + L ≤ M)
    (hb : 0 < infiniteRademacherMeasure.real {ω | sourceEvent x L b ω}) :
    ∃ a : SampleSpace M, ∀ i, startSystem M (x i) L a = b i := by
  rw [source_mass_affine x b hcut] at hb
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp ((uniformSolutionMass_pos_iff _ _).mp hb)
  refine ⟨a, ?_⟩
  intro i
  funext j
  exact congrFun ha (i, j)

theorem homogeneous_source_positive {s M L : ℕ} (x : Fin s → ℕ) (hcut : ∀ i, x i + L ≤ M) :
    0 < infiniteRademacherMeasure.real {ω | sourceEvent x L (fun _ ↦ 0) ω} := by
  have h := source_mass_pos x (0 : SampleSpace M) hcut
  simpa only [map_zero] using h

end PaperP1.CompatibleWindowPrescriptions
