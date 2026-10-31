module

public import PaperP1.Model.JointStartProbability
public import PaperP1.Model.InfiniteStarts
public import PaperP1.Affine.Subfamilies

/-!
# Actual joint and centered coefficients of finite infinite-model families

Both coefficients are Bochner integrals under the infinite prime-sign law.
Finite-cylinder transport proves the exact compatible joint mass and the
heterogeneous inclusion-exclusion identity used in article Lemma 4.3.
-/

@[expose] public noncomputable section

open scoped BigOperators
open MeasureTheory
open PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Probability
open PaperP1.Model.InfiniteRademacher
open PaperP1.Probability.InfiniteCylinderTransfer
open PaperP1.Probability.CylinderExpectations

namespace PaperP1.Model.InfiniteStarts

local instance infiniteJointMeasurableF2 : MeasurableSpace F₂ := ⊤
local instance infiniteJointDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def infiniteJointMoment (L : ℕ) (I : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ I, (indicatorValue (infiniteStartIndicator x L ω) : ℝ) ∂infiniteRademacherMeasure

def infiniteCenteredCoefficient (L : ℕ) (I : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ I, ((indicatorValue (infiniteStartIndicator x L ω) : ℝ) - infiniteMarginal x L)
    ∂infiniteRademacherMeasure

theorem infiniteJointMoment_nonneg (L : ℕ) (I : Finset ℕ) : 0 ≤ infiniteJointMoment L I := by
  apply integral_nonneg
  intro ω
  exact indicator_product_nonneg (fun x => infiniteStartIndicator x L) I ω

@[simp]
theorem infiniteJointMoment_empty (L : ℕ) : infiniteJointMoment L ∅ = 1 := by
  simp [infiniteJointMoment]

theorem finiteJointMoment_eq_startFamily (M L : ℕ) (I : Finset ℕ) :
    finiteJointMoment (cylinderProbability M) (fun x => startIndicator x L) I =
      startFamilyJointMoment M L (fun x : I => x.val) := by
  unfold finiteJointMoment startFamilyJointMoment
  congr 1
  funext ω
  symm
  rw [Finset.univ_eq_attach]
  exact Finset.prod_attach I (fun x => (indicatorValue (startIndicator x L ω) : ℝ))

theorem infiniteJointMoment_eq_finite (M L : ℕ) (I : Finset ℕ)
    (hcut : ∀ x ∈ I, x + L ≤ M) :
    infiniteJointMoment L I = finiteJointMoment (cylinderProbability M) (fun x => startIndicator x L) I := by
  unfold infiniteJointMoment finiteJointMoment
  have hprod (ω : InfiniteSample) :
      (∏ x ∈ I, (indicatorValue (infiniteStartIndicator x L ω) : ℝ)) =
      ∏ x ∈ I, (indicatorValue (startIndicator x L (restrictToFinite M ω)) : ℝ) := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [startIndicator_restrict_eq ω (hcut x hx)]
  simp_rw [hprod]
  exact infiniteCylinder_integral M (fun σ =>
    ∏ x ∈ I, (indicatorValue (startIndicator x L σ) : ℝ))

theorem infiniteJointMoment_eq_startFamily (M L : ℕ) (I : Finset ℕ)
    (hcut : ∀ x ∈ I, x + L ≤ M) :
    infiniteJointMoment L I = startFamilyJointMoment M L (fun x : I => x.val) := by
  rw [infiniteJointMoment_eq_finite M L I hcut, finiteJointMoment_eq_startFamily]

theorem infiniteJointMoment_pos_iff_jointCompatible (M L : ℕ) (I : Finset ℕ) (hL : 0 < L)
    (hcut : ∀ x ∈ I, x + L ≤ M) :
    0 < infiniteJointMoment L I ↔
      Compatible (familyStartSystem M L (fun x : I => x.val)) (familyStartRhs L) := by
  rw [infiniteJointMoment_eq_startFamily M L I hcut, startFamilyJointMoment_pos_iff M L _ hL]

theorem infiniteJointMoment_exact_of_pos (M L : ℕ) (I : Finset ℕ) (hL : 0 < L)
    (hcut : ∀ x ∈ I, x + L ≤ M) (hq : 0 < infiniteJointMoment L I) :
    infiniteJointMoment L I = (∏ x ∈ I, infiniteMarginal x L) *
      (2 ^ relativeNullityOn (fun x => squareClassSpace x L) I : ℝ) := by
  have hpos : 0 < startFamilyJointMoment M L (fun x : I => x.val) := by
    rwa [← infiniteJointMoment_eq_startFamily M L I hcut]
  have h := startFamilyJointMoment_squareClass_of_pos M L (fun x : I => x.val) hL
    (fun x => hcut x.val x.property) hpos
  rw [← infiniteJointMoment_eq_startFamily M L I hcut] at h
  have hprod : (∏ x : I, exactMarginal (cylinderProbability M)
      (fun y => startIndicator y L) x.val) = ∏ x ∈ I, infiniteMarginal x L := by
    calc
      _ = ∏ x : I, infiniteMarginal x.val L := by
        apply Finset.prod_congr rfl
        intro x _
        exact (infiniteMarginal_eq_finite (hcut x.val x.property)).symm
      _ = _ := by
        rw [Finset.univ_eq_attach]
        exact Finset.prod_attach I (fun x => infiniteMarginal x L)
  rw [hprod] at h
  simpa only [relativeNullityOn, squareClassFamilySpace, mul_comm] using h

theorem infiniteCenteredCoefficient_eq_transform (M L : ℕ) (I : Finset ℕ)
    (hcut : ∀ x ∈ I, x + L ≤ M) :
    infiniteCenteredCoefficient L I =
      centeredCoefficient (fun x => infiniteMarginal x L) (infiniteJointMoment L) I := by
  unfold infiniteCenteredCoefficient
  have hprod (ω : InfiniteSample) :
      (∏ x ∈ I, ((indicatorValue (infiniteStartIndicator x L ω) : ℝ) - infiniteMarginal x L)) =
      ∏ x ∈ I, ((indicatorValue (startIndicator x L (restrictToFinite M ω)) : ℝ) -
        infiniteMarginal x L) := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [startIndicator_restrict_eq ω (hcut x hx)]
  simp_rw [hprod]
  rw [infiniteCylinder_integral M (fun σ =>
    ∏ x ∈ I, ((indicatorValue (startIndicator x L σ) : ℝ) - infiniteMarginal x L))]
  change centeredMoment (cylinderProbability M).weight
    (fun x σ => indicatorValue (startIndicator x L σ)) (fun x => infiniteMarginal x L) I = _
  rw [centeredMoment_eq_centeredCoefficient]
  unfold centeredCoefficient
  apply Finset.sum_congr rfl
  intro A hA
  have hq := infiniteJointMoment_eq_finite M L A
    (fun x hx => hcut x (Finset.mem_powerset.mp hA hx))
  rw [hq]
  rfl

end PaperP1.Model.InfiniteStarts
