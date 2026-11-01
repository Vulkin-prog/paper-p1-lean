module

public import PaperP1.Asymptotics.FixedWindowBranching
public import PaperP1.Probability.FairBinaryCube
public import PaperP1.Model.JointMonotonicity

/-! # Exact branching of actual joint start probabilities after all old raw values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.JointBranchingEvents

open Finset MeasureTheory ProbabilityTheory PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.Probability PaperP1.Model.InfiniteRademacher PaperP1.Model.InfiniteStarts
  PaperP1.RelativeSignIndependence PaperP1.ConditionalRelativeBits PaperP1.OldValuePrimeBudget
  PaperP1.FixedWindowBranching PaperP1.BranchingExceptional
  PaperP1.Probability.InfiniteCylinderTransfer

local instance jointBranchingMeasurableF2 : MeasurableSpace F₂ := ⊤
local instance jointBranchingDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def oldField (R : Finset ℕ) (v : R → F₂) (n : ℕ) : F₂ := if hn : n ∈ R then v ⟨n, hn⟩ else 0

def oldAllowed (A : Finset ℕ) (L : ℕ) : Set (rawValues A L → F₂) :=
  {v | ∀ x ∈ A, StartEvent (oldField (rawValues A L) v) x L}

def jointEvent (A : Finset ℕ) (L : ℕ) : Set InfiniteSample :=
  {ω | ∀ x ∈ A, StartEvent (infiniteValueBit ω) x L}

theorem oldField_infinite {R : Finset ℕ} {n : ℕ} (hn : n ∈ R) (ω : InfiniteSample) :
    oldField R (infiniteOldBits R ω) n = infiniteValueBit ω n := by
  simp only [oldField, dite_eq_left hn, infiniteOldBits]

theorem startEvent_congr {g₁ g₂ : ℕ → F₂} {x L : ℕ} (hL : 0 < L)
    (heq : ∀ n ∈ Ico (x - 1) (x + L), g₁ n = g₂ n) : StartEvent g₁ x L ↔ StartEvent g₂ x L := by
  have hp := heq (x - 1) (mem_Ico.mpr ⟨le_rfl, by omega⟩)
  have hb := heq x (mem_Ico.mpr ⟨by omega, by omega⟩)
  constructor
  · rintro ⟨hboundary, hflat⟩
    refine ⟨by simpa only [hp, hb] using hboundary, ?_⟩
    intro j hj
    calc
      _ = g₁ (x + j) := (heq _ (mem_Ico.mpr ⟨by omega, by omega⟩)).symm
      _ = g₁ x := hflat j hj
      _ = _ := hb
  · rintro ⟨hboundary, hflat⟩
    refine ⟨by simpa only [hp, hb] using hboundary, ?_⟩
    intro j hj
    calc
      _ = g₂ (x + j) := heq _ (mem_Ico.mpr ⟨by omega, by omega⟩)
      _ = g₂ x := hflat j hj
      _ = _ := hb.symm

theorem oldAllowed_preimage {A : Finset ℕ} {L : ℕ} (hL : 0 < L) :
    infiniteOldBits (rawValues A L) ⁻¹' oldAllowed A L = jointEvent A L := by
  ext ω
  have hiff (x : ℕ) (hx : x ∈ A) :
      StartEvent (oldField (rawValues A L) (infiniteOldBits (rawValues A L) ω)) x L ↔
        StartEvent (infiniteValueBit ω) x L :=
    startEvent_congr hL (fun n hn ↦ oldField_infinite (mem_biUnion.mpr ⟨x, hx, hn⟩) ω)
  constructor
  · intro h x hx
    exact (hiff x hx).mp (h x hx)
  · intro h x hx
    exact (hiff x hx).mpr (h x hx)

theorem measurable_jointEvent (A : Finset ℕ) {L : ℕ} (hL : 0 < L) : MeasurableSet (jointEvent A L) := by
  rw [← oldAllowed_preimage hL]
  exact (measurable_infiniteOldBits _) ((Set.to_countable _).measurableSet)

theorem infiniteJointMoment_eq_probability (A : Finset ℕ) {L : ℕ} (hL : 0 < L) :
    infiniteJointMoment L A = infiniteRademacherMeasure.real (jointEvent A L) := by
  unfold infiniteJointMoment
  have heq : (fun ω ↦ ∏ x ∈ A, (indicatorValue (infiniteStartIndicator x L ω) : ℝ)) =
      (jointEvent A L).indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    rw [indicator_product_eq_indicator]
    simp [infiniteStartIndicator, jointEvent, Set.indicator_apply]
  rw [heq]
  change (∫ ω, (jointEvent A L).indicator (1 : InfiniteSample → ℝ) ω ∂infiniteRademacherMeasure) = _
  exact integral_indicator_one (measurable_jointEvent A hL)

theorem startBits_eq_rhs_iff (x : ℕ) {L : ℕ} (hL : 0 < L) (ω : InfiniteSample) :
    infiniteStartBits x L ω = startRhs L ↔ StartEvent (infiniteValueBit ω) x L := by
  rw [← startSystem_restrict_eq (M := x + L) le_rfl ω, startSystem_eq_startRhs_iff _ hL]
  exact startAt_restrictToFinite_iff (M := x + L) ω le_rfl

theorem retained_joint_factor {N L x : ℕ} {A : Finset ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hA : A ⊆ dyadicBlock N) (hx : x ∈ dyadicBlock N) (hnot : x ∉ badStarts N L (rawValues A L)) :
    infiniteJointMoment L (insert x A) = (2 ^ L : ℝ)⁻¹ * infiniteJointMoment L A := by
  obtain ⟨hfair, hind, _⟩ := retained_independent hN hA x hx hnot
  have hnew : infiniteStartBits x L ⁻¹' {startRhs L} = {ω | StartEvent (infiniteValueBit ω) x L} := by
    ext ω
    exact startBits_eq_rhs_iff x hL ω
  have hprob : infiniteRademacherMeasure.real (infiniteStartBits x L ⁻¹' {startRhs L}) = (2 ^ L : ℝ)⁻¹ := by
    rw [← map_measureReal_apply (measurable_infiniteStartBits x L) (measurableSet_singleton (startRhs L)), hfair]
    simpa only [FairBinaryCube.measure, Fintype.card_fin] using FairBinaryCube.real_singleton (startRhs L)
  have heq := hind.measure_inter_preimage_eq_mul {startRhs L} (oldAllowed A L)
    (measurableSet_singleton _) ((Set.to_countable _).measurableSet)
  have hreal := congrArg ENNReal.toReal heq
  rw [ENNReal.toReal_mul] at hreal
  change infiniteRademacherMeasure.real (infiniteStartBits x L ⁻¹' {startRhs L} ∩
      infiniteOldBits (rawValues A L) ⁻¹' oldAllowed A L) =
    infiniteRademacherMeasure.real (infiniteStartBits x L ⁻¹' {startRhs L}) *
      infiniteRademacherMeasure.real (infiniteOldBits (rawValues A L) ⁻¹' oldAllowed A L) at hreal
  rw [hprob, oldAllowed_preimage hL, hnew] at hreal
  have hset : {ω | StartEvent (infiniteValueBit ω) x L} ∩ jointEvent A L = jointEvent (insert x A) L := by
    ext ω
    simp only [jointEvent, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_mem_insert]
  rw [hset] at hreal
  simpa only [infiniteJointMoment_eq_probability _ hL] using hreal

end PaperP1.JointBranchingEvents
