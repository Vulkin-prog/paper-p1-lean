module

public import PaperP1.Model.ConditionalRunProbability
public import PaperP1.Model.RelativeSignIndependence

/-! # The full new relative vector is fair and independent of every old raw value -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConditionalRelativeBits

open MeasureTheory ProbabilityTheory Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.Algebra PaperP1.Probability PaperP1.ConditionalRunRank PaperP1.ConditionalWindowRank
  PaperP1.ConditionalRunProbability PaperP1.RelativeSignIndependence
  PaperP1.Model.InfiniteRademacher PaperP1.Model.InfiniteStarts
  PaperP1.Probability.InfiniteCylinderTransfer PaperP1.Probability.CylinderExpectations

local instance conditionalRelativeDecidable (P : Prop) : Decidable P := Classical.propDecidable P
local instance conditionalRelativeMeasurableF2 : MeasurableSpace F₂ := ⊤

def finiteOldBits {M : ℕ} (R : Finset ℕ) (a : SampleSpace M) : R → F₂ := fun n ↦ valueBit a n.val

def infiniteOldBits (R : Finset ℕ) (ω : InfiniteSample) : R → F₂ := fun n ↦ infiniteValueBit ω n.val

def conditionalWordProbability {M : ℕ} (R : Finset ℕ) (a : SampleSpace M) (x L : ℕ) (b : Fin L → F₂) : ℝ :=
  infiniteRademacherMeasure.real {ω | infiniteOldEvent R a ω ∧ infiniteStartBits x L ω = b} /
    infiniteRademacherMeasure.real {ω | infiniteOldEvent R a ω}

theorem oldBits_restrict {M : ℕ} {R : Finset ℕ} (hR : ∀ n ∈ R, n ≤ M) (ω : InfiniteSample) :
    finiteOldBits R (restrictToFinite M ω) = infiniteOldBits R ω := by
  funext n
  exact valueBit_restrictToFinite_eq_infiniteValueBit ω (hR n.val n.property)

theorem measurable_infiniteOldBits (R : Finset ℕ) : Measurable (infiniteOldBits R) := by
  have heq : infiniteOldBits R = (finiteOldBits R : SampleSpace (R.sup id) → R → F₂) ∘ restrictToFinite (R.sup id) := by
    funext ω
    exact (oldBits_restrict (fun n hn ↦ le_sup (f := id) hn) ω).symm
  rw [heq]
  exact Measurable.of_discrete.comp (measurable_restrictToFinite _)

theorem oldEvent_iff_bits {M : ℕ} (R : Finset ℕ) (a : SampleSpace M) (ω : InfiniteSample) :
    infiniteOldEvent R a ω ↔ infiniteOldBits R ω = finiteOldBits R a := by
  constructor
  · intro h
    funext n
    exact h n.val n.property
  · intro h n hn
    exact congrFun h ⟨n, hn⟩

theorem conditionalWordProbability_eq_affine {M x L : ℕ} {R : Finset ℕ}
    (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M) (a : SampleSpace M) (b : Fin L → F₂) :
    conditionalWordProbability R a x L b = conditionalAffineMass (oldRows M R) a (startSystem M x L) b := by
  have heq : {ω | infiniteOldEvent R a ω ∧ infiniteStartBits x L ω = b} =
      {ω | finiteOldEvent R a (restrictToFinite M ω) ∧ startSystem M x L (restrictToFinite M ω) = b} := by
    ext ω
    simp only [Set.mem_ofPred_eq, oldEvent_restrict hR, startSystem_restrict_eq hcut]
  unfold conditionalWordProbability conditionalAffineMass
  rw [heq, ConditionalRunProbability.infiniteCylinder_event M (fun σ ↦ finiteOldEvent R a σ ∧ startSystem M x L σ = b),
    observation_probability hR]
  congr 1
  apply congrArg (finiteExpectation (cylinderProbability M).weight)
  funext σ
  simp only [oldRows_event_iff]
  split_ifs <;> rfl

theorem conditionalWordProbability_nominal {M x L : ℕ} {R : Finset ℕ}
    (hx : 0 < x) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M) (a : SampleSpace M)
    (hcard : (supportedIndices R (x - 1) (L + 1)).card ≤ 1) (b : Fin L → F₂) :
    conditionalWordProbability R a x L b = (2 ^ L : ℝ)⁻¹ := by
  rw [conditionalWordProbability_eq_affine hcut hR]
  have hzero : Module.finrank F₂ ((oldRows M R).comap (relationMap (startSystem M x L))) = 0 := by
    rw [row_kernel_finrank hx hcut hR]
    exact conditionalNullity_eq_zero_of_card_le_one hcard
  simpa only [Fintype.card_fin] using
    conditionalAffineMass_nominal_of_kernel_zero (oldRows M R) a (startSystem M x L) b hzero

theorem joint_atom_factor {M x L : ℕ} {R : Finset ℕ}
    (hx : 0 < x) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M)
    (hcard : (supportedIndices R (x - 1) (L + 1)).card ≤ 1) (b : Fin L → F₂) (d : R → F₂) :
    infiniteRademacherMeasure.real {ω | infiniteStartBits x L ω = b ∧ infiniteOldBits R ω = d} =
      (2 ^ L : ℝ)⁻¹ * infiniteRademacherMeasure.real {ω | infiniteOldBits R ω = d} := by
  by_cases hd : ∃ a : SampleSpace M, finiteOldBits R a = d
  · obtain ⟨a, ha⟩ := hd
    have h := conditionalWordProbability_nominal hx hcut hR a hcard b
    unfold conditionalWordProbability at h
    have heq : {ω | infiniteOldEvent R a ω ∧ infiniteStartBits x L ω = b} =
        {ω | infiniteStartBits x L ω = b ∧ infiniteOldBits R ω = d} := by
      ext ω
      simp only [Set.mem_ofPred_eq, oldEvent_iff_bits, ha, and_comm]
    have heqOld : {ω | infiniteOldEvent R a ω} = {ω | infiniteOldBits R ω = d} := by
      ext ω
      simp only [Set.mem_ofPred_eq, oldEvent_iff_bits, ha]
    have hpos := observation_probability_pos hR a
    rw [heqOld] at hpos
    rw [heq, heqOld] at h
    exact (div_eq_iff hpos.ne').mp h
  · have hnone (ω : InfiniteSample) : infiniteOldBits R ω ≠ d := by
      intro hω
      exact hd ⟨restrictToFinite M ω, (oldBits_restrict hR ω).trans hω⟩
    have hOld : {ω | infiniteOldBits R ω = d} = ∅ := by ext ω; simp only [Set.mem_ofPred_eq, Set.notMem_empty, iff_false]; exact hnone ω
    have hJoint : {ω | infiniteStartBits x L ω = b ∧ infiniteOldBits R ω = d} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.notMem_empty, iff_false, not_and]
      exact fun _ ↦ hnone ω
    rw [hOld, hJoint]
    simp

theorem map_joint_eq_fair_prod_old {M x L : ℕ} {R : Finset ℕ}
    (hx : 0 < x) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M)
    (hcard : (supportedIndices R (x - 1) (L + 1)).card ≤ 1) :
    infiniteRademacherMeasure.map (fun ω ↦ (infiniteStartBits x L ω, infiniteOldBits R ω)) =
      (Measure.pi (fun _ : Fin L ↦ coordinateMeasure)).prod (infiniteRademacherMeasure.map (infiniteOldBits R)) := by
  apply Measure.ext_of_singleton
  rintro ⟨b, d⟩
  apply (measureReal_eq_measureReal_iff).mp
  rw [map_measureReal_apply ((measurable_infiniteStartBits x L).prodMk (measurable_infiniteOldBits R))
    (measurableSet_singleton (b, d))]
  have hpre : (fun ω ↦ (infiniteStartBits x L ω, infiniteOldBits R ω)) ⁻¹' {(b, d)} =
      {ω | infiniteStartBits x L ω = b ∧ infiniteOldBits R ω = d} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_ofPred_eq]
  rw [hpre, joint_atom_factor hx hcut hR hcard b d, ← Set.singleton_prod_singleton, measureReal_prod_prod,
    map_measureReal_apply (measurable_infiniteOldBits R) (measurableSet_singleton d)]
  congr 1
  rw [Measure.real, Measure.pi_singleton]
  simp [coordinateMeasure, Measure.uniformOfFinset_apply_singleton, ZMod.card]

theorem map_new_eq_fair {M x L : ℕ} {R : Finset ℕ}
    (hx : 0 < x) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M)
    (hcard : (supportedIndices R (x - 1) (L + 1)).card ≤ 1) :
    infiniteRademacherMeasure.map (infiniteStartBits x L) = Measure.pi (fun _ : Fin L ↦ coordinateMeasure) := by
  have h := congrArg (fun μ : Measure ((Fin L → F₂) × (R → F₂)) ↦ μ.map Prod.fst)
    (map_joint_eq_fair_prod_old hx hcut hR hcard)
  rw [Measure.map_map measurable_fst ((measurable_infiniteStartBits x L).prodMk (measurable_infiniteOldBits R)),
    Measure.map_fst_prod] at h
  have hunit : (infiniteRademacherMeasure.map (infiniteOldBits R)) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_infiniteOldBits R) MeasurableSet.univ]
    simp
  rw [hunit, one_smul] at h
  exact h

theorem independent_of_old {M x L : ℕ} {R : Finset ℕ}
    (hx : 0 < x) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M)
    (hcard : (supportedIndices R (x - 1) (L + 1)).card ≤ 1) :
    IndepFun (infiniteStartBits x L) (infiniteOldBits R) infiniteRademacherMeasure := by
  apply (indepFun_iff_map_prod_eq_prod_map_map (measurable_infiniteStartBits x L).aemeasurable
    (measurable_infiniteOldBits R).aemeasurable).mpr
  rw [map_new_eq_fair hx hcut hR hcard]
  exact map_joint_eq_fair_prod_old hx hcut hR hcard

end PaperP1.ConditionalRelativeBits
