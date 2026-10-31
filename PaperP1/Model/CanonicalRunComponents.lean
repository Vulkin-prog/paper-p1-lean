module

public import PaperP1.Model.StartPartitionTransfer
public import PaperP1.Affine.PartitionNullity
public import PaperP1.Model.InfiniteStartFourier
public import PaperP1.Model.InfiniteJointMoments

/-!
# Article Lemma 4.4: canonical direct run components

The partition is constructed from the effective square-class spaces. It is
the unique finest direct partition. The actual infinite-model joint and
centered moments factor over its parts, and relative nullity is additive.
-/

@[expose] public noncomputable section

open scoped BigOperators
open MeasureTheory
open PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Probability
open PaperP1.Model.InfiniteRademacher
open PaperP1.Probability.InfiniteCylinderTransfer
open PaperP1.Probability.CylinderExpectations

namespace PaperP1.Model.InfiniteStarts

local instance canonicalRunMeasurableF2 : MeasurableSpace F₂ := ⊤

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def infiniteFamilyJointMoment (L : ℕ) (g : ι → ℕ) : ℝ :=
  ∫ ω, ∏ i, (indicatorValue (infiniteStartIndicator (g i) L ω) : ℝ) ∂infiniteRademacherMeasure

omit [DecidableEq ι] in
theorem infiniteFamilyJointMoment_eq_finite (M L : ℕ) (g : ι → ℕ)
    (hcut : ∀ i, g i + L ≤ M) :
    infiniteFamilyJointMoment L g = startFamilyJointMoment M L g := by
  unfold infiniteFamilyJointMoment startFamilyJointMoment
  have hprod (ω : InfiniteSample) :
      (∏ i, (indicatorValue (infiniteStartIndicator (g i) L ω) : ℝ)) =
      ∏ i, (indicatorValue (startIndicator (g i) L (restrictToFinite M ω)) : ℝ) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [startIndicator_restrict_eq ω (hcut i)]
  simp_rw [hprod]
  exact infiniteCylinder_integral M (fun σ =>
    ∏ i, (indicatorValue (startIndicator (g i) L σ) : ℝ))

theorem infiniteFamilyJointMoment_partition (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (hp : ∀ i, 0 < infiniteMarginal (g i) L)
    (P : Finpartition (Finset.univ : Finset ι))
    (hP : RelationDirectPartition (squareClassFamilySpace L g) P) :
    infiniteFamilyJointMoment L g = ∏ C : P.parts,
      infiniteFamilyJointMoment L (fun i : C.val => g i.val) := by
  have hc := infiniteAdmissibleCompatibility M L g hL hcut hp
  have hrow := relationDirect_squareClass_to_rows M L g hcut P hP
  rw [infiniteFamilyJointMoment_eq_finite M L g hcut,
    startFamilyJointMoment_partition M L g hL hc P hrow]
  apply Finset.prod_congr rfl
  intro C _
  symm
  exact infiniteFamilyJointMoment_eq_finite M L (fun i : C.val => g i.val) (fun i => hcut i.val)

theorem infiniteFamilyCenteredMoment_partition (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (hp : ∀ i, 0 < infiniteMarginal (g i) L)
    (P : Finpartition (Finset.univ : Finset ι))
    (hP : RelationDirectPartition (squareClassFamilySpace L g) P) :
    infiniteFamilyCenteredMoment L g = ∏ C : P.parts,
      infiniteFamilyCenteredMoment L (fun i : C.val => g i.val) := by
  have hc := infiniteAdmissibleCompatibility M L g hL hcut hp
  have hrow := relationDirect_squareClass_to_rows M L g hcut P hP
  rw [infiniteFamilyCenteredMoment_eq_finite M L g hcut,
    startFamilyCenteredMoment_partition M L g hL hc P hrow]
  apply Finset.prod_congr rfl
  intro C _
  symm
  exact infiniteFamilyCenteredMoment_eq_finite M L (fun i : C.val => g i.val) (fun i => hcut i.val)

def canonicalRunPartition (L : ℕ) (g : ι → ℕ) : Finpartition (Finset.univ : Finset ι) :=
  canonicalRelationPartition (squareClassFamilySpace L g)

def CanonicalRunPartitionConclusion (L : ℕ) (g : ι → ℕ)
    (P : Finpartition (Finset.univ : Finset ι)) : Prop :=
  BlockDirectPartition (squareClassFamilySpace L g) P ∧
  (∀ Q, BlockDirectPartition (squareClassFamilySpace L g) Q → P ≤ Q) ∧
  infiniteFamilyJointMoment L g =
    (∏ C : P.parts, infiniteFamilyJointMoment L (fun i : C.val => g i.val)) ∧
  infiniteFamilyCenteredMoment L g =
    (∏ C : P.parts, infiniteFamilyCenteredMoment L (fun i : C.val => g i.val)) ∧
  relativeNullity (squareClassFamilySpace L g) =
    ∑ C : P.parts, relativeNullity (fun i : C.val => squareClassSpace (g i.val) L)

/-- The complete conclusion of article Lemma 4.4 for any finite admissible
indexed family. A finite cutoff is constructed inside the proof. -/
theorem canonical_run_components (L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hp : ∀ i, 0 < infiniteMarginal (g i) L) :
    ∃! P : Finpartition (Finset.univ : Finset ι), CanonicalRunPartitionConclusion L g P := by
  let M := Finset.univ.sup fun i => g i + L
  have hcut : ∀ i, g i + L ≤ M := fun i => Finset.le_sup (f := fun i => g i + L) (Finset.mem_univ i)
  have hrel := canonicalRelationPartition_respects (squareClassFamilySpace L g)
  have hdir := canonicalRelationPartition_direct (squareClassFamilySpace L g)
  refine ⟨canonicalRunPartition L g, ⟨hdir, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro Q hQ
    exact canonicalRelationPartition_le_direct (squareClassFamilySpace L g) Q hQ
  · exact infiniteFamilyJointMoment_partition M L g hL hcut hp _ hrel
  · exact infiniteFamilyCenteredMoment_partition M L g hL hcut hp _ hrel
  · exact relativeNullity_canonical_additive (squareClassFamilySpace L g)
  · intro Q hQ
    exact le_antisymm (hQ.2.1 _ hdir)
      (canonicalRelationPartition_le_direct (squareClassFamilySpace L g) Q hQ.1)

theorem infiniteJointMoment_eq_family_subtype (L : ℕ) (I : Finset ℕ) :
    infiniteJointMoment L I = infiniteFamilyJointMoment L (fun x : I => x.val) := by
  unfold infiniteJointMoment infiniteFamilyJointMoment
  congr 1
  funext ω
  symm
  rw [Finset.univ_eq_attach]
  exact Finset.prod_attach I (fun x => (indicatorValue (infiniteStartIndicator x L ω) : ℝ))

theorem infiniteCenteredCoefficient_eq_family_subtype (L : ℕ) (I : Finset ℕ) :
    infiniteCenteredCoefficient L I = infiniteFamilyCenteredMoment L (fun x : I => x.val) := by
  unfold infiniteCenteredCoefficient infiniteFamilyCenteredMoment
  congr 1
  funext ω
  symm
  rw [Finset.univ_eq_attach]
  exact Finset.prod_attach I (fun x =>
    (indicatorValue (infiniteStartIndicator x L ω) : ℝ) - infiniteMarginal x L)

theorem canonical_run_components_finset (L : ℕ) (I : Finset ℕ) (hL : 0 < L)
    (hp : ∀ x ∈ I, 0 < infiniteMarginal x L) :
    ∃! P : Finpartition (Finset.univ : Finset I),
      CanonicalRunPartitionConclusion L (fun x : I => x.val) P :=
  canonical_run_components L _ hL (fun i => hp i.val i.property)

end PaperP1.Model.InfiniteStarts
