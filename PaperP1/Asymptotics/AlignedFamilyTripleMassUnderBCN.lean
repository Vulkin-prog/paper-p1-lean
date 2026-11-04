module

public import PaperP1.Asymptotics.SharpThirdActivityUnderInputs

/-! # Main14.3 as a subpopulation of the full sharp connected triple bound

This proof explicitly uses the existing BCN premise through the global
weak/no-exact sector. It makes no claim of a finite-geometry-only proof.
No regularity, private normalization or separation restriction is imposed
on the original population; zero joint events are retained exactly.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedFamilyTripleMassUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def families (N L : ℕ) (F : Finset (ℕ × ℕ)) : Finset (Finset ℕ) :=
  (connectedFamilies (dyadicBlock N) L 3).filter fun T ↦
    ∃ ab ∈ F, ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ EnlargedPairGeometry.Geometric ab.1 ab.2 x y L

def mass (N L : ℕ) (F : Finset (ℕ × ℕ)) : ℝ :=
  ∑ T ∈ families N L F, infiniteJointMoment L T

theorem positive_filter_eq (N L : ℕ) (F : Finset (ℕ × ℕ)) :
    (∑ T ∈ (families N L F).filter (fun T ↦ 0 < infiniteJointMoment L T), infiniteJointMoment L T) = mass N L F := by
  apply sum_subset (filter_subset _ _)
  intro T hT hnot
  have hz : ¬0 < infiniteJointMoment L T := fun hh ↦ hnot (mem_filter.mpr ⟨hT, hh⟩)
  exact le_antisymm (le_of_not_gt hz) (infiniteJointMoment_nonneg L T)

theorem article_14_3 (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 1 ≤ Q ∧ ∃ p : (ab : FiniteInteriorUnitEdges.channels Q) → FiniteCompressedInteriorMass.Parameters,
      (∀ ab, FiniteCompressedInteriorMass.Hypotheses (p ab) ab.val.2 (ε / 8)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (ℕ × ℕ),
        mass N L F ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨Q, hQ, p, hu⟩ := SharpThirdActivityUnderInputs.uniform_joint_mass c κ hc hBCN C ε hε
  refine ⟨Q, hQ, p, ?_⟩
  intro hgeo
  obtain ⟨N₀, hN₀, hU⟩ := hu hgeo
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hcrit F
  exact hU N hN L hcrit (dyadicBlock N) Subset.rfl (families N L F) (filter_subset _ _)

end PaperP1.AlignedFamilyTripleMassUnderBCN
