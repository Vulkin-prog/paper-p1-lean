module

public import PaperP1.Asymptotics.LateFiniteCore
public import PaperP1.Model.CommonRunMoments
public import PaperP1.Model.FinitePartMoments
public import PaperP1.Model.CanonicalSquareClasses
public import PaperP1.Affine.CanonicalPartConnected
public import PaperP1.Model.CompatibleNullityBound

/-! # An actual connected family with the original infinite-model moments -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LateOriginalCore

open Finset Filter PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Affine PaperP1.PrimeCylinderScale PaperP1.LatePrimePopulation
  PaperP1.LatePrimeRankDensity PaperP1.LatePeelingOrder PaperP1.PrivateCoreMoments

local instance lateOriginalCoreTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def ComponentConclusion (q : ℕ) (I : Finset ℕ) : Prop :=
  I ⊆ population q ∧ I.Nonempty ∧
  canonicalRunPartition (q - 1) (fun i : I ↦ i.val) = ⊤ ∧
  runCompatibleNullity (q - 1) I = runRelativeNullity (q - 1) I ∧
  0 < infiniteJointMoment (q - 1) I ∧
  ((q - 1 : ℕ) : ℝ) / LatePeelingDensity.densityEnvelope q ≤ I.card ∧
  ((q - 1 : ℕ) : ℝ) ^ 2 / LatePeelingDensity.densityEnvelope q - (q - 1 : ℕ) ≤
    runRelativeNullity (q - 1) I ∧
  (1 - loss q) * infiniteJointMoment (q - 1) I ≤ infiniteCenteredCoefficient (q - 1) I ∧
  0 < infiniteCenteredCoefficient (q - 1) I ∧
  ∀ (H : ℝ) e, e ∈ GoodEdgeCompression.goodEdges H (size q) (q - 1) → ¬e ⊆ I

theorem actual_component :
    ∀ᶠ q : ℕ in atTop, Nat.Prime q → ∃ I : Finset ℕ, ComponentConclusion q I := by
  filter_upwards [LateFiniteCore.actual_component] with q hqCore
  intro hq
  obtain ⟨B, hB, C, hsize, hnull, hqC, hmass, hcC⟩ := hqCore hq
  let I := FinitePartImage.image C.val
  have hI : I ⊆ population q := (FinitePartImage.image_subset C.val).trans hB
  have hCne := (canonicalRelationPartition (fun i : B ↦ spaces q i.val)).nonempty_of_mem_parts C.property
  let : Nonempty C.val := nonempty_coe_sort.mpr hCne
  have hcut : ∀ i : C.val, i.val.val + (q - 1) ≤ LatePrimeRankDensity.cutoff q :=
    fun i ↦ local_cutoff (hB i.val.property)
  have hrows := CanonicalPartConnected.part_connected (fun i : B ↦ spaces q i.val) C.property
  have hsquare : canonicalRelationPartition (fun i : C.val ↦ squareClassSpace i.val.val (q - 1)) = ⊤ :=
    (CanonicalSquareClasses.connected_iff_rows (LatePrimeRankDensity.cutoff q) (q - 1)
      (fun i : C.val ↦ i.val.val) hcut).mpr hrows
  have hconnected : canonicalRunPartition (q - 1) (fun i : I ↦ i.val) = ⊤ :=
    FinitePartImage.connected_image (fun x ↦ squareClassSpace x (q - 1)) C.val hsquare
  have hqI : 0 < infiniteJointMoment (q - 1) I := population_positive hq hI
  have hnullity : runRelativeNullity (q - 1) I =
      relativeNullityOn (fun i : B ↦ spaces q i.val) C.val := by
    calc
      _ = relativeNullity (squareClassFamilySpace (q - 1) (fun i : I ↦ i.val)) := rfl
      _ = relativeNullity (startFamilySpace (LatePrimeRankDensity.cutoff q) (q - 1)
          (fun i : I ↦ i.val)) :=
        relativeNullity_squareClassFamily_eq_rows _ _ _ (fun i ↦ local_cutoff (hI i.property))
      _ = relativeNullityOn (spaces q) I := rfl
      _ = _ := (FinitePartImage.nullity_image (spaces q) C.val).symm
  have hL : 0 < q - 1 := by have h := hq.two_le; omega
  have hcommon : ∀ i : C.val, startSystem (LatePrimeRankDensity.cutoff q) i.val.val (q - 1)
      (LatePrimeWindows.sample (size q) q hq) = startRhs (q - 1) :=
    fun i ↦ common_equations hq (hB i.val.property)
  have hjoint : infiniteJointMoment (q - 1) I =
      componentJoint (spaces q) (fun _ ↦ LatePrimeWindows.sample (size q) q hq) C.val := by
    rw [FinitePartMoments.joint_image]
    exact CommonRunMoments.infinite_joint_common _ _ _ hL hcut _ hcommon
  have hcentered : infiniteCenteredCoefficient (q - 1) I =
      componentCentered (spaces q) (fun _ ↦ LatePrimeWindows.sample (size q) q hq) C.val := by
    rw [FinitePartMoments.centered_image]
    exact CommonRunMoments.infinite_centered_common _ _ _ hL hcut _ hcommon
  refine ⟨I, hI, FinitePartImage.image_nonempty hCne, hconnected,
    runCompatibleNullity_eq_of_positive_joint _ _ hqI, hqI, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [I, FinitePartImage.card_image] using hsize
  · rwa [hnullity]
  · rwa [hjoint, hcentered]
  · rwa [hcentered]
  · intro H e he hsub
    exact population_no_good_pair hq.two_le he (hsub.trans hI)

end PaperP1.LateOriginalCore
