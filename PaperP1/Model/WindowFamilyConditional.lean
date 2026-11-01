module

public import PaperP1.Affine.FamilyConditionalMass
public import PaperP1.Model.ConditionalRelativeBits
public import PaperP1.Model.SquareClassRelations
public import PaperP1.Model.JointStartSystem
public import PaperP1.Arithmetic.DenseTargetCover

/-! # Actual infinite-measure probabilities after compatible window prescriptions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WindowFamilyConditional

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Probability
  PaperP1.RelativeSignIndependence PaperP1.Model.InfiniteRademacher
  PaperP1.Probability.InfiniteCylinderTransfer PaperP1.ConditionalRunProbability

local instance windowFamilyConditionalTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance windowFamilyConditionalDecidable (P : Prop) : Decidable P := Classical.propDecidable P
local instance windowFamilyConditionalMeasurableF2 : MeasurableSpace F₂ := ⊤

def sourceEvent {s : ℕ} (x : Fin s → ℕ) (L : ℕ) (b : Fin s → Fin L → F₂) (ω : InfiniteSample) : Prop :=
  ∀ i, infiniteStartBits (x i) L ω = b i

def conditionalProbability {s : ℕ} (x : Fin s → ℕ) (L : ℕ) (b : Fin s → Fin L → F₂)
    (z : ℕ) (c : Fin L → F₂) : ℝ :=
  infiniteRademacherMeasure.real {ω | sourceEvent x L b ω ∧ infiniteStartBits z L ω = c} /
    infiniteRademacherMeasure.real {ω | sourceEvent x L b ω}

theorem conditionalProbability_nonneg {s L z : ℕ} (x : Fin s → ℕ) (b : Fin s → Fin L → F₂)
    (c : Fin L → F₂) : 0 ≤ conditionalProbability x L b z c :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

abbrev systems {s : ℕ} (M L : ℕ) (x : Fin s → ℕ) (z : ℕ) :
    Option (Fin s) → SampleSpace M →ₗ[F₂] (Fin L → F₂) :=
  fun i ↦ match i with
    | none => startSystem M z L
    | some j => startSystem M (x j) L

theorem sourceEvent_restrict {s M L : ℕ} (x : Fin s → ℕ) (b : Fin s → Fin L → F₂)
    (hcut : ∀ i, x i + L ≤ M) (ω : InfiniteSample) :
    sourceEvent x L b ω ↔ ∀ i, startSystem M (x i) L (restrictToFinite M ω) = b i := by
  simp only [sourceEvent, startSystem_restrict_eq (hcut _)]

theorem oldSpace_event {s M L z : ℕ} (x : Fin s → ℕ) (a v : SampleSpace M) :
    effectiveEvent (FamilyConditionalMass.oldSpace (systems M L x z)) a v ↔
      ∀ i, startSystem M (x i) L v = startSystem M (x i) L a := by
  change effectiveEvent (⨆ i, startFamilySpace M L x i) a v ↔ _
  rw [← effectiveRowSpace_familyStartSystem, effectiveRowEvent_iff]
  constructor
  · intro h i
    funext j
    exact congrFun h (i, j)
  · intro h
    funext p
    exact congrFun (h p.1) p.2

theorem source_mass {s M L z : ℕ} (x : Fin s → ℕ) (a : SampleSpace M)
    (hcut : ∀ i, x i + L ≤ M) :
    infiniteRademacherMeasure.real {ω | sourceEvent x L (fun i ↦ startSystem M (x i) L a) ω} =
      oldObservationMass (FamilyConditionalMass.oldSpace (systems M L x z)) a := by
  have heq : {ω | sourceEvent x L (fun i ↦ startSystem M (x i) L a) ω} =
      {ω | effectiveEvent (FamilyConditionalMass.oldSpace (systems M L x z)) a (restrictToFinite M ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [sourceEvent_restrict x _ hcut, oldSpace_event]
  rw [heq, infiniteCylinder_event]
  rfl

theorem source_mass_pos {s M L : ℕ} (x : Fin s → ℕ) (a : SampleSpace M)
    (hcut : ∀ i, x i + L ≤ M) :
    0 < infiniteRademacherMeasure.real {ω | sourceEvent x L (fun i ↦ startSystem M (x i) L a) ω} := by
  rw [source_mass (z := 0) x a hcut]
  exact oldObservationMass_pos _ _

theorem conditional_eq_mass {s M L z : ℕ} (x : Fin s → ℕ) (a : SampleSpace M)
    (c : Fin L → F₂) (hcut : ∀ i, x i + L ≤ M) (hz : z + L ≤ M) :
    conditionalProbability x L (fun i ↦ startSystem M (x i) L a) z c =
      FamilyConditionalMass.mass (systems M L x z) a c := by
  have heq : {ω | sourceEvent x L (fun i ↦ startSystem M (x i) L a) ω ∧ infiniteStartBits z L ω = c} =
      {ω | effectiveEvent (FamilyConditionalMass.oldSpace (systems M L x z)) a (restrictToFinite M ω) ∧
        startSystem M z L (restrictToFinite M ω) = c} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [sourceEvent_restrict x _ hcut, oldSpace_event, startSystem_restrict_eq hz]
  unfold conditionalProbability FamilyConditionalMass.mass conditionalAffineMass
  rw [heq, infiniteCylinder_event M (fun σ ↦
    effectiveEvent (FamilyConditionalMass.oldSpace (systems M L x z)) a σ ∧ startSystem M z L σ = c),
    source_mass (z := z) x a hcut]
  congr 1
  apply congrArg (PaperP1.Algebra.finiteExpectation (cylinderProbability M).weight)
  funext σ
  by_cases h : effectiveEvent (FamilyConditionalMass.oldSpace (systems M L x z)) a σ ∧ startSystem M z L σ = c
  · simp only [systems, h]
  · simp only [systems, h, ite_false]

theorem increment_eq_loss {s M L z : ℕ} (x : Fin s → ℕ)
    (hcut : ∀ i, x i + L ≤ M) (hz : z + L ≤ M) :
    FamilyConditionalMass.increment (systems M L x z) =
      DenseTargetRegularization.loss (DenseTargetCover.extended x z) L := by
  have hfull : ∀ i, DenseTargetCover.extended x z i + L ≤ M := by
    intro i
    rcases i with _ | i
    · exact hz
    · exact hcut i
  have hF := relativeNullity_squareClassFamily_eq_rows M L (DenseTargetCover.extended x z) hfull
  have hS := relativeNullity_squareClassFamily_eq_rows M L x hcut
  have hsystems : systems M L x z = fun i ↦ startSystem M (DenseTargetCover.extended x z i) L := by
    funext i
    cases i <;> rfl
  rw [hsystems]
  change relativeNullity (startFamilySpace M L (DenseTargetCover.extended x z)) -
    relativeNullity (startFamilySpace M L x) = _
  rw [← hF, ← hS]
  rfl

theorem conditional_nonneg {s M L z : ℕ} (x : Fin s → ℕ) (a : SampleSpace M)
    (c : Fin L → F₂) (hcut : ∀ i, x i + L ≤ M) (hz : z + L ≤ M) :
    0 ≤ conditionalProbability x L (fun i ↦ startSystem M (x i) L a) z c := by
  rw [conditional_eq_mass x a c hcut hz]
  exact FamilyConditionalMass.mass_nonneg _ _ _

theorem conditional_le_one {s M L z : ℕ} (x : Fin s → ℕ) (a : SampleSpace M)
    (c : Fin L → F₂) (hcut : ∀ i, x i + L ≤ M) (hz : z + L ≤ M) :
    conditionalProbability x L (fun i ↦ startSystem M (x i) L a) z c ≤ 1 := by
  rw [conditional_eq_mass x a c hcut hz]
  exact FamilyConditionalMass.mass_le_one _ _ _

theorem conditional_le_nominal {s M L z : ℕ} (x : Fin s → ℕ) (a : SampleSpace M)
    (c : Fin L → F₂) (hcut : ∀ i, x i + L ≤ M) (hz : z + L ≤ M) (hzpos : 0 < z)
    (hrel : Module.finrank F₂ (WindowRelationCode.windowRelationCode (z - 1) (L + 1)) ≤ 1) :
    conditionalProbability x L (fun i ↦ startSystem M (x i) L a) z c ≤
      2 * (2 ^ DenseTargetRegularization.loss (DenseTargetCover.extended x z) L : ℝ) / (2 ^ L : ℝ) := by
  have hlocal := LocalRunRank.squareClass_rank_add_relation_rank (L := L) hzpos
  have hrow := finrank_squareClassSpace_eq_effectiveRows hz
  have hdefectStart : L ≤ Module.finrank F₂ (effectiveRowSpace (startSystem M z L)) + 1 := by omega
  have hdefect : Fintype.card (Fin L) ≤
      Module.finrank F₂ (effectiveRowSpace (systems M L x z none)) + 1 := by
    simpa only [Fintype.card_fin] using hdefectStart
  have hmass := FamilyConditionalMass.mass_le_nominal (systems M L x z) a c 1 hdefect
  rw [increment_eq_loss x hcut hz] at hmass
  rw [conditional_eq_mass x a c hcut hz]
  simpa only [pow_one, Fintype.card_fin] using hmass

end PaperP1.WindowFamilyConditional
